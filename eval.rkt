#lang racket
(require racket/hash)
(require "general.rkt")
(require "ast.rkt")
(require "lattice.rkt")
(require "test.rkt")

; AAC, local store, global stack store
; set!, cons, vector 

(random-seed 111) ; deterministic random

(define (env-lookup ρ x)
  (hash-ref ρ x))

(define (env-addresses ρ)
  (list->set (hash-values ρ)))

(define (env-bind ρ x a)
  (hash-set ρ x a))

(define (store-lookup σ a)
  (hash-ref σ a))

(struct clo (lam ρ) #:transparent
  #:property prop:custom-write (lambda (v p w?)
                                 (fprintf p "<clo ~a>" («lam»-l (clo-lam v)))))
(struct prim (name proc) #:methods gen:equal+hash ((define equal-proc (lambda (s1 s2 requal?)
                                                                        (equal? (prim-name s1) (prim-name s2))))
                                                   (define hash-proc (lambda (s rhash) (equal-hash-code (prim-name s))))
                                                   (define hash2-proc (lambda (s rhash) (equal-secondary-hash-code (prim-name s))))))
(struct addr (a) #:transparent)


(define (touches d)
  (if (set? d)
      (for/fold ((as (set))) ((v d)) (set-union as (touches v)))
      (match d
        ((clo _ ρ) (env-addresses ρ))
        ((addr a) (set a))
        ((cons x y) (set-union (touches x) (touches y)))
        (_ (set)))))
(define (reachable A σ γ)
  (let loop ((A A) (R (set)))
    (if (set-empty? A)
        R
        (let ((a (set-first A)))
          (if (set-member? R a)
              (loop (set-rest A) R)
              (let* ((v (γ (store-lookup σ a)))
                     (T (touches v)))
                (loop (set-union (set-rest A) T) (set-add R a))))))))


(define (make-evaluator lattice alloc monotonic-store)
  (define α (lattice-α lattice))
  (define γ (lattice-γ lattice))
  (define ⊥ (lattice-⊥ lattice))
  (define ⊤ (lattice-⊤ lattice))
  (define ⊑ (lattice-⊑ lattice))
  (define ⊔ (lattice-⊔ lattice))
  (define true? (lattice-true? lattice))
  (define false? (lattice-false? lattice))
  (define α-eq? (lattice-eq? lattice))
    
  (define (store-alloc σ a v)
    (if (hash-has-key? σ a) 
        (let* ((current (hash-ref σ a))
               (updated (⊔ current v)))
          (if (equal? current updated)
              σ
              (hash-set σ a updated)))
        (hash-set σ a v)))
          
  (define (store-update σ a v)
    (let* ((current (hash-ref σ a))
           (updated (⊔ current v)))
      (if (equal? current updated)
          σ
          (hash-set σ a updated))))

  (define (alloc-literal e σ κ)
    (define (alloc-helper e)
      (if (pair? e)
          (let ((car-v (alloc-helper (car e))))
            (let ((cdr-v (alloc-helper (cdr e))))
              (let ((a (alloc e e)))
                (set! σ (store-alloc σ a (α (cons car-v cdr-v))))
                (α (addr a)))))
          (α e)))
    (κ (alloc-helper e) σ))

  (define (apply-proc d-clo d-rands σ κ)
    (match-let (((clo («lam» _ x e0) ρ) d-clo))
      (define (bind-loop x vs ρ σ)
        (match x
          ('()
           (eval* e0 ρ σ κ))
          ((cons x xs)
           (let* ((a (alloc x))
                  (ρ* (env-bind ρ («id»-x x) a))
                  (σ* (store-alloc σ a (car vs))))
                 (bind-loop xs (cdr vs) ρ* σ*)))))
      (bind-loop x d-rands ρ σ)))

  (define cache (hash))

  (define (eval* e ρ σ κ)
    (match e
      ((«lit» _ d) 
       (κ (α d) σ))
      ((«id» _ x)
       (let ((a (env-lookup ρ x)))
         (κ (store-lookup σ a) σ)))
      ((«lam» _ _ _)
       (let ((cl (clo e ρ)))
         (κ (α cl) σ)))
      ((«quo» _ atom)
       (κ (α atom) σ))
      ((«if» _ e0 e1 e2)
       (eval* e0 ρ σ
              (lambda (d σ)
                (when (true? d)
                  (eval* e1 ρ σ κ))
                (when (false? d)
                  (eval* e2 ρ σ κ)))))
      ((«let» _ x e0 e1)
       (eval* e0 ρ σ
              (lambda (d σ)
                (let* ((a (alloc x))
                       (ρ* (env-bind ρ («id»-x x) a))
                       (σ* (store-alloc σ a d)))
                  (eval* e1 ρ* σ* κ)))))
      ((«letrec» _ x e0 e1)
       (let* ((a (alloc x))
              (ρ* (env-bind ρ («id»-x x) a))
              (σ* (store-alloc σ a ⊥)))
         (eval* e0 ρ* σ*
                (lambda (d σ)
                  (let* ((a (env-lookup ρ* («id»-x x)))
                         (σ* (store-update σ a d)))
                    (eval* e1 ρ* σ* κ))))))
      ((«set!» _ x e0)
       (eval* e0 ρ σ
              (lambda (d σ)
                (let* ((a (env-lookup ρ («id»-x x)))
                       (σ* (store-update σ a d)))
                  (κ (α 'undefined) σ*)))))
      ((«quo» _ e0)
       (alloc-literal e0 σ κ))
      ((«app» _ rator rands)
       (eval* rator ρ σ
              (lambda (d-rator σ)
                (let rands-loop ((rands rands) (d-rands '()) (σ σ))
                  (if (null? rands)
                      (let ((d-rands (reverse d-rands)))
                        (for ((w (in-set (γ d-rator))))
                             (match w
                               ((clo _ _)
                                (let* ((key (list e w rands σ))
                                       (value (hash-ref cache key #f)))
                                  (if value
                                      (apply κ value)
                                      (apply-proc w d-rands σ
                                                  (lambda args
                                                    (set! cache (hash-set cache key args))
                                                    (apply κ args))))))
                               ((prim name proc)
                                (proc e d-rands σ κ))
                               ((prim2 _ proc)
                                (κ (apply proc d-rands) σ)))))
                      (eval* (car rands) ρ σ
                             (lambda (d-rand σ)
                               (rands-loop (cdr rands) (cons d-rand d-rands) σ))))))))))
    
  (lambda (e κ)
      (let ((global (lattice-global lattice))
            (compiled-e (compile e)))
        (set! conc-alloc-counter 0)
        (let loop ((global global) (ρ (hash)) (σ (hash)))
          (match global
            ('()
             (let* ((ρ* (↓ ρ (free compiled-e)))
                    (R (reachable (env-addresses ρ*) σ γ))
                    (σ* (↓ σ R)))
               (eval* compiled-e ρ* σ* κ)))
            ((cons (cons x v) r)
             (let* ((a (conc-alloc))
                    (ρ* (env-bind ρ x a))
                    (σ* (store-alloc σ a v)))
               (loop r ρ* σ*)))))))
  ) ; make-evaluator


;; allocators
(define conc-alloc-counter 0)
(define conc-alloc
  (lambda _
    (set! conc-alloc-counter (add1 conc-alloc-counter))
    conc-alloc-counter))

(define (mono-alloc x)
  x)
;;

(define conc-evaluator (make-evaluator conc-lattice conc-alloc #f))
(define type-evaluator (make-evaluator type-lattice mono-alloc #t))

(define (perform-eval e evaluator ⊥ ⊔)
  (let ((result ⊥))
    (evaluator e
               (lambda (d σ)
                 (set! result (⊔ result d))))
    result))
  
(define (conc-eval e)
  (perform-eval e conc-evaluator conc-⊥ conc-⊔))
                    
(define (type-eval e)
  (perform-eval e type-evaluator type-⊥ type-⊔))

(define (flow-test . ens)
  (when (null? ens)
    (set! ens '(fac fib fib-mut blur eta mj09 gcipd kcfa2 kcfa3 rotate loop2 sat collatz rsa primtest factor nqueens)))
  (define (perform name e)
   (match-let (((ko d σ) (type-eval e)))
      (printf "~a ~a\n"
              (~a name #:min-width 12)
              (~a d))))
  (for-each (lambda (en) (perform en (eval en)))
            ens))

(define (server-flow-test)
    (apply flow-test '(fac fib fib-mut blur eta mj09 gcipd kcfa2 kcfa3 rotate loop2
                           sat collatz rsa primtest factor nqueens dderiv mceval))); boyer))))-