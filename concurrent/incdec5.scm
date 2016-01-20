(letrec ((counter 0)
         (lock (new-lock))
         (inc (lambda ()
                (acquire lock)
                (set! counter (+ counter 1))
                (release lock)))
         (dec (lambda ()
                (acquire lock)
                (set! counter (- counter 1))
                (release lock)))
         (t1 (spawn (inc)))
         (t2 (spawn (dec)))
         (t3 (spawn (inc)))
         (t4 (spawn (dec)))
         (t5 (spawn (inc))))
  (join t1)
  (join t2)
  (join t3)
  (join t4)
  (join t5)
  (= counter 1))
