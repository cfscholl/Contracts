#lang racket/base
(require racket/contract/base)


(printf "one layer of wrapping\n")
(define fc
  (contract
   (-> integer? integer?)
   (λ (x) x)
   'pos 'neg))
(collect-garbage) (collect-garbage) (collect-garbage)
(time
 (for ([x (in-range 3000000)])
   (fc 1)))

(printf "ten layers of wrapping\n")
(define ffc
  (let loop ([n 10])
    (cond
      [(zero? n) (λ (x) x)]
      [else (contract
             (-> integer? integer?)
             (loop (- n 1))
             'pos 'neg)])))

(collect-garbage) (collect-garbage) (collect-garbage)
(time
 (for ([x (in-range 100000)])
   (ffc 1)))