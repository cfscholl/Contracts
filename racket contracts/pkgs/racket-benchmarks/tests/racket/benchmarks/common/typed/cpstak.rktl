;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; File:         cpstak.sch
; Description:  continuation-passing version of TAK
; Author:       Will Clinger
; Created:      20-Aug-87
; Modified:     3-May-10 (Vincent St-Amour)
; Language:     Typed Scheme
; Status:       Public Domain
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; CPSTAK -- A continuation-passing version of the TAK benchmark.
;;; A good test of first class procedures and tail recursion.

(: cpstak (Integer Integer Integer -> Integer))
(define (cpstak x y z)
  (: tak (Integer Integer Integer (Integer -> Integer) -> Integer))
  (define (tak x y z k)
    (if (not (< y x))
        (k z)
        (tak (- x 1)
             y
             z
             (lambda (v1)
               (tak (- y 1)
                    z
                    x
                    (lambda (v2)
                      (tak (- z 1)
                           x
                           y
                           (lambda (v3)
                             (tak v1 v2 v3 k)))))))))
  (tak x y z (lambda (a) a)))

;;; call: (cpstak 18 12 6)

(let ((input (with-input-from-file "input.txt" read)))
  (time (let: loop : Integer
              ((n : Integer 20) (v : Integer 0))
              (if (zero? n)
                  v
                  (loop (- n 1)
                        (cpstak 18 12 (if input 2 0)))))))
