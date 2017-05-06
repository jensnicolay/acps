(let ((env '()))
  (let ((=-proc (lambda (p)
                  (let ((v1 (car p)))
                    (let ((v2 (cadr p)))
                      (= v1 v2))))))
    (let ((=-binding (cons '= =-proc)))
      (let ((env (cons =-binding env)))
        (let ((+-proc (lambda (p)
                        (let ((v1 (car p)))
                          (let ((v2 (cadr p)))
                            (+ v1 v2))))))
          (let ((+-binding (cons '+ +-proc)))
            (let ((env (cons +-binding env)))
              (let ((--proc (lambda (p)
                              (let ((v1 (car p)))
                                (let ((v2 (cadr p)))
                                  (- v1 v2))))))
                (let ((--binding (cons '- --proc)))
                  (let ((env (cons --binding env)))
                    (let ((<-proc (lambda (p)
                                    (let ((v1 (car p)))
                                      (let ((v2 (cadr p)))
                                        (< v1 v2))))))
                      (let ((<-binding (cons '< <-proc)))
                        (let ((env (cons <-binding env)))
                          (letrec ((evaluate (lambda (e)
                                               (let ((c-symbol? (symbol? e)))
                                                 (if c-symbol?
                                                     (let ((binding (assoc e env)))
                                                       (cdr binding))
                                                     (let ((c-pair? (pair? e)))
                                                       (if c-pair?
                                                           (let ((first (car e)))
                                                             (let ((c-lambda? (eq? first 'lambda)))
                                                               (if c-lambda?
                                                                   (cons e env)
                                                                   (let ((c-let? (eq? first 'let)))
                                                                     (if c-let?
                                                                         (let ((binding (caadr e)))
                                                                           (let ((x (car binding)))
                                                                             (let ((e0 (cadr binding)))
                                                                               (let ((e1 (caddr e)))
                                                                                 (let ((v (evaluate e0)))
                                                                                   (let ((binding (cons x v)))
                                                                                     (let ((extended1 (cons binding env)))
                                                                                       (let ((u (set! env extended1)))
                                                                                         (evaluate e1))))))))) ;end let
                                                                         (let ((c-set!? (eq? first 'set!)))
                                                                           (if c-set!?
                                                                               (let ((x (cadr e)))
                                                                                 (let ((e0 (caddr e)))
                                                                                   (let ((v (evaluate e0)))
                                                                                     (let ((binding (assoc x env)))
                                                                                       (let ((u (set-cdr! binding v)))
                                                                                         v))))) ;end set!
                                                                               (let ((c-if? (eq? first 'if)))
                                                                                 (if c-if?
                                                                                     (let ((e0 (cadr e)))
                                                                                       (let ((v (evaluate e0)))
                                                                                         (if v
                                                                                             (let ((e1 (caddr e)))
                                                                                               (evaluate e1))
                                                                                             (let ((e2 (cadddr e)))
                                                                                               (evaluate e2))))) ;end if
                                                                                     (let ((operator (car e)))
                                                                                       (let ((operands (cdr e)))
                                                                                         (let ((rator (evaluate operator)))
                                                                                           (let ((rands (map evaluate operands)))
                                                                                             (let ((c-closure? (pair? rator)))
                                                                                               (if c-closure?
                                                                                                   (let ((lam (car rator)))
                                                                                                     (let ((static (cdr rator)))
                                                                                                       (let ((params (cadr lam)))
                                                                                                         (let ((e0 (caddr lam)))
                                                                                                           (let ((restore-env2 env))
                                                                                                             (letrec ((bind (lambda (params rands)
                                                                                                                              (let ((c-null? (null? params)))
                                                                                                                                (if c-null?
                                                                                                                                    (let ((v (evaluate e0)))
                                                                                                                                      (let ((u (set! env restore-env2)))
                                                                                                                                        v))
                                                                                                                                    (let ((var (car params)))
                                                                                                                                      (let ((value (car rands)))
                                                                                                                                        (let ((binding (cons var value)))
                                                                                                                                          (let ((extended2 (cons binding static)))
                                                                                                                                            (let ((u (set! env extended2)))
                                                                                                                                              (let ((params2 (cdr params)))
                                                                                                                                                (let ((rands2 (cdr rands)))
                                                                                                                                                  (bind params2 rands2)))))))))))))
                                                                                                             (bind params rands))))))) ;end clo
                                                                                                   (rator rands))))))) ;end app
                                                                                     ))))))))) ;end pair
                                                           e)))))))
                            (let ((program '(let ((fib #f)) (let ((u (set! fib (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))))) (fib 3)))))
                              (evaluate program)
                            )))))))))))))))