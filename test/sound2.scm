(let ((make-c (lambda (x) (lambda () x))))
  (let ((c1 (make-c 123)))
    (let ((c2 (make-c "hehe")))
      (let ((u (c1)))
        (c2)))))