(letrec ((_ack0 (lambda (_m1 _n2) (let ((_p3 (= _m1 0))) (if _p3 (+ _n2 1) (let ((_p4 (= _n2 0))) (if _p4 (let ((_p5 (- _m1 1))) (_ack0 _p5 1)) (let ((_p6 (- _m1 1))) (let ((_p7 (- _n2 1))) (let ((_p8 (_ack0 _m1 _p7))) (_ack0 _p6 _p8))))))))))) (let ((_p9 (_ack0 3 9))) (equal? _p9 4093)))