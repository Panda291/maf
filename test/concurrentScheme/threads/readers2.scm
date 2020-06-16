;; Example taken from Optimal Dynamic Partial Order Reduction, Figure 3
(let* ((x 0) (y 0) (z 0)
       (p (lambda () (set! x 1)))
       (q (lambda () y x))
       (z (lambda () z x))
       (t1 (spawn (p)))
       (t2 (spawn (q)))
       (t3 (spawn (z))))
  (join t1)
  (join t2))
