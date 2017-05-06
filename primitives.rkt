  (define (prim-pair e rands σ ι κ)
    (if (= (length rands) 1)
        (let ((v (for/fold ((v ⊥)) ((w (γ (car rands))))
                   (match w
                     ((addr a)
                      (for/fold ((v v)) ((ww (γ (store-lookup σ a))))
                        (⊔ v (α (pair? ww)))))
                     (_ (α #f))))))
          (set (transition (ko v σ ι κ))))
        (set)))

(define (prim-vector-length e rands σ ι κ)
  (if (= (length rands) 1)
      (let* ((global (lattice-global lattice))
             (add-proc (lambda (x y)
                         (for/fold ((result ⊥)) ((prim2 (γ (cdr (assoc "+" global)))))
                           (⊔ result ((prim2-proc prim2) x y)))))
             (lt-proc (lambda (x y)
                        (for/fold ((result ⊥)) ((prim2 (γ (cdr (assoc "<" global)))))
                          (⊔ result ((prim2-proc prim2) x y))))))
        (let ((v (for/fold ((v ⊥)) ((w (γ (car rands))))
                   (match w
                     ((addr a)
                      (for/fold ((v v)) ((ww (γ (store-lookup σ a))))
                        (if (hash? ww)
                            (⊔ v (for/fold ((n (α 0))) ((i (in-set (hash-keys ww))))
                                   (let ((ii (add-proc i (α 1))))
                                     (if (lt-proc ii n)
                                         n
                                         ii))))
                            v)))
                     (_ v)))))
          (set (transition (ko v σ ι κ)))))
      (set)))

(define (prim-vector-copy e rands σ ι κ)
  (if (= (length rands) 1)
      (let* ((v (for/fold ((v (hash))) ((w (γ (car rands))))
                  (match w
                    ((addr a)
                     (for/fold ((v v)) ((ww (γ (store-lookup σ a))))
                       (if (hash? ww)
                           (hash-union v ww #:combine/key (lambda (k v0 v) (⊔ v0 v)))
                           v)))
                    (_ v))))
             (a-copy (alloc e e))
             (σ* (store-alloc σ a-copy (α v))))
        (set (transition (ko (α (addr a-copy)) σ* ι κ))))
      (set)))
      
  (define (prim-to-string e rands σ ι κ)
    (define (helper v seen)
      (match v
        ((addr a)
         (if (set-member? seen a)
             (set (transition (ko (α (~a v)) σ ι κ)))
             (begin
               (apply set-union (set-map (γ (store-lookup σ a)) (lambda (w) (helper w (set-add seen a))))))))
        ((cons v1 v2)
         (let ((s1 (helper v1 seen))
               (s2 (helper v2 seen)))
           (for*/set ((sσ1 s1) (sσ2 s2))
             (transition (ko (α (~a (cons (car sσ1) (car sσ2)))) σ ι κ)))))
        (_ (set (transition (ko (α (~a v)) σ ι κ))))))
    (if (= (length rands) 1)
        (apply set-union (set-map (γ (car rands)) (lambda (w) (helper w (set)))))
        (set)))

  (define (eq?-helper v1 v2)
    (match* (v1 v2)
      (((addr a1) (addr a2))
       (α (equal? a1 a2)))
      ((_ _) (α-eq? v1 v2))))

  (define (prim-eq? e rands σ ι κ)
    (if (= (length rands) 2)
        (let* ((w1 (γ (car rands)))
               (w2 (γ (cadr rands)))
               (v (for*/fold ((v ⊥)) ((v1 w1) (v2 w2)) (⊔ v (eq?-helper v1 v2)))))
          (set (transition (ko v σ ι κ)))) 
        (set)))

  (define (prim-error e rands σ ι κ)
    (set))