;; Example taken from Dynamic Partial Order Reduction, Figure 1
;; Expected result: #t
(let* ((size 128)
       (max 4)
       (table (make-vector size 0))
       (thread (lambda (tid)
                 (letrec ((hash (lambda (w) (modulo (* w 7) size)))
                          (process (lambda (m)
                                     (if (< m max)
                                         (letrec ((w (+ (* 11 (+ m 1)) tid))
                                                  (update (lambda (h)
                                                            (if (cas-vector table h 0 w)
                                                                #t
                                                                (update (modulo (+ h 1) size))))))
                                           (update (hash w))
                                           (process (+ m 1)))
                                         #t))))
                   (process 0))))
       (t1 (spawn (thread 1)))
       (t2 (spawn (thread 2)))
       (t3 (spawn (thread 3)))
       (t4 (spawn (thread 4))))
  (join t1)
  (join t2)
  (join t3)
  (join t4)
  #t)
