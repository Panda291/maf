;; Example taken from Dynamic Partial Order Reduction, Figure 7
;; Expected result: #t
(let* ((numblocks 26)
       (numinode 32)
       (locki (vector (new-lock) (new-lock) (new-lock) (new-lock) (new-lock)
                      (new-lock) (new-lock) (new-lock) (new-lock) (new-lock)
                      (new-lock) (new-lock) (new-lock) (new-lock) (new-lock)
                      (new-lock) (new-lock) (new-lock) (new-lock) (new-lock)
                      (new-lock) (new-lock) (new-lock) (new-lock) (new-lock)
                      (new-lock) (new-lock) (new-lock) (new-lock) (new-lock)
                      (new-lock) (new-lock)))
       (inode (make-vector numinode 0))
       (lockb (vector (new-lock) (new-lock) (new-lock) (new-lock) (new-lock)
                      (new-lock) (new-lock) (new-lock) (new-lock) (new-lock)
                      (new-lock) (new-lock) (new-lock) (new-lock) (new-lock)
                      (new-lock) (new-lock) (new-lock) (new-lock) (new-lock)
                      (new-lock) (new-lock) (new-lock) (new-lock) (new-lock)
                      (new-lock)))
       (busy (make-vector numblocks #f))
       (thread (lambda (tid)
                 (letrec ((i (modulo tid numinode))
                          (process (lambda (b)
                                     (acquire (vector-ref lockb b))
                                     (if (not (vector-ref busy b))
                                         (begin
                                           (vector-set! busy b #t)
                                           (vector-set! inode i (+ b 1))
                                           (release (vector-ref lockb b)))
                                         (begin
                                           (release (vector-ref lockb b))
                                           (process (modulo (+ b 1) numblocks)))))))
                   (acquire (vector-ref locki i))
                   (if (= (vector-ref inode i) 0)
                       (process (modulo (* i 2) numblocks)))
                   (release (vector-ref locki i)))))
       (t1 (spawn (thread 1)))
       (t2 (spawn (thread 2))))
  (join t1)
  (join t2)
  #t)
