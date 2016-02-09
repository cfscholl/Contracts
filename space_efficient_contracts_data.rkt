#lang racket
;  _________                           _________                __                        __          
; /   _____/__________    ____  ____   \_   ___ \  ____   _____/  |_____________    _____/  |_  ______
; \_____  \\____ \__  \ _/ ___\/ __ \  /    \  \/ /  _ \ /    \   __\_  __ \__  \ _/ ___\   __\/  ___/
; /        \  |_> > __ \\  \__\  ___/  \     \___(  <_> )   |  \  |  |  | \// __ \\  \___|  |  \___ \ 
;/_______  /   __(____  /\___  >___  >  \______  /\____/|___|  /__|  |__|  (____  /\___  >__| /____  >
;        \/|__|       \/     \/    \/          \/            \/                 \/     \/          \/ 
;
; Experiments for designing space-efficient contracts
; Christophe Scholliers, Christophe.Scholliers@UGent.be
(require racket/contract/base)

(define (blame x)  (error "Blaming " x)) 
; A structure to represent a flat contract
; flat/c : (α → boolean) → contract α
(struct flat/c (predicate))
; ho/c : contract α × contract β → contract (α → β)
(struct ho/c (dom rng))

(struct multi-ho/c (dom rng pos))
(struct multi-flat/c (proj-list flat/c-list))

; Impersonator property for saving the contract
(define-values (->-c has-->c? get-->-c)
  (make-impersonator-property '->-c))

; Impersonator property for saving the wrapped function
(define-values (->-w has-->w? get-->-w)
  (make-impersonator-property '->-w))

; contract α × α × symbol × symbol → α
(define (guard ctc val pos neg)
  (cond
    ; We do not change anything about the normal
    ; flat contracts
    [(flat/c? ctc)
     (if ((flat/c-predicate ctc) val) val (blame pos))]
    ; If it is a higher-order contract
    ; wrap the function so that we can later
    ; join the contract defined over it 
    [(ho/c? ctc)
     (let ([dom (ho/c-dom ctc)]
           [rng (ho/c-rng ctc)])
       (if (procedure? val)
           ;return a *wrapped* function 
           (let ((wrapped-once (get/build-wrapped-once val)))
             (chaperone-procedure* wrapped-once
                                    #f
                                    ->-w  wrapped-once
                                    ->-c  (guard-f-ho/c val ctc pos neg)))
           (blame pos)))]))

; Helper function for wrapping a (possibly) contracted function
; Important here is that we unwrap one layer in case it was already wrapped !
(define (get/build-wrapped-once f)
  ;if it is already contracted don't wrap it again
  (if (has-->w? f)
      ; Peel off one layer (note that this the outer layer)
      (get-->-w f)
      ; Otherwise wrap it once, this never gets removed
      ; anymore
      (chaperone-procedure* f wrapper)))

; This function applies function
; contracts over a contracted function
(define wrapper
  (λ (chap arg)
    (let*  ([ctc (get-->-c chap)]
            [dom (multi-ho/c-dom ctc)]
            [rng (multi-ho/c-rng ctc)])
      (values
       ; creating a new lambda for each application is probably
       ; not such a great idea :D maybe we need to change
       ; the interface of chaperone-procedure* ?
       (λ (result) (guard-multi/c rng result))
       (guard-multi/c dom arg)))))

; This only happens at the initial guarding of a higher-order contract
; two cases are possible we guard an already contracted function
; or the function didn't have any contract over it
(define (guard-f-ho/c f ctc pos neg)
  ; Create a new multi-ho-contract out of the contract
  (let ([new-multi (ho/c->multi-ho/c ctc pos neg)])
    (if (not (has-->c? f))
        new-multi
        (join-multi-ho/c new-multi  (get-->-c f)))))


; Make a projection out of a predicate and the blame label
(define (proj pred pos)
  (λ (val)
    (if (pred val) val (blame pos))))

; Convert a higher-order contract to a multi-higher-order contract
; Conversion consists of simultaneously copying
; the structure of the higher-order contract and propagating the
; blame labels to the leafs.
; At the leafs we convert flat/c to multi-flat/c
(define (ho/c->multi-ho/c ctc pos neg)
  (cond
    ; the flat/c are replaced by a multi-flat/c
    [(flat/c? ctc)
     (multi-flat/c
      (list (proj (flat/c-predicate ctc) pos))
      (list ctc))]
    ; copy structure and propagate blame
    [(ho/c? ctc)
     (let ([dom (ho/c-dom ctc)]
           [rng (ho/c-rng ctc)])
       (multi-ho/c (ho/c->multi-ho/c dom neg pos)
                   (ho/c->multi-ho/c rng pos neg)
                   pos))]))


; helper function for computing the join of two multi-flat contracts
(define (zip l1 l2) (map   (lambda (e1 e2) (cons e1 e2)) l1 l2))

; very weak implies function, we just check whether they are the same
(define (implies? c1 c2)
  (eq? c1 c2))

; checks whether the contract c is already implied by one of the
; contracts in the contract_list
(define (implied-by-one? contract_list c)
  (foldr (lambda (e a) (or (implies? e c) a)) #f contract_list))

; join two multi-flat contracts
(define (multi-flat/c-join new-multi old-multi)
  (let* ([new-proj-list (multi-flat/c-proj-list new-multi)]
        [new-flat-list (multi-flat/c-flat/c-list new-multi)]
        [old-proj-list (multi-flat/c-proj-list old-multi)]        
        [old-flat-list (multi-flat/c-flat/c-list old-multi)]
        [not-implied
         (filter (lambda (cp)
                   (not (implied-by-one? new-flat-list (car cp))))
                 (zip old-flat-list old-proj-list))])
    (multi-flat/c (append new-proj-list (map cdr not-implied))
                  (append new-flat-list (map car not-implied)))))

; join two multi-ho/c 
(define (join-multi-ho/c new-multi old-multi)
  (if (multi-ho/c? old-multi)
      (multi-ho/c (join-multi-ho/c (multi-ho/c-dom new-multi) (multi-ho/c-dom old-multi))
                  (join-multi-ho/c (multi-ho/c-rng old-multi) (multi-ho/c-rng new-multi))
                  (multi-ho/c-pos new-multi))
      (multi-flat/c-join new-multi old-multi)))

; Apply a list of projections over a value
; Note that for our purpose it is important
; to fold left otherwise blame could be assigned
; in the wrong order
; [a -> (Maybe a) ] -> a -> (Maybe a)
(define  (apply-proj-list proj-list val)
  (foldl (lambda (f v) (f v)) val proj-list))

; Apply a multi contract over a value
(define (guard-multi/c ctc val)
  (cond
    ; We are at the leafs apply the projection list
    [(multi-flat/c? ctc)
     (let ([proj-list (multi-flat/c-proj-list ctc)])
       (apply-proj-list proj-list val))]
    ; It is a higher-order multi-contract
    [(multi-ho/c? ctc)
     (let ([pos (multi-ho/c-pos ctc)])
       ; return a chaperoned function (again joinable)
       (if (procedure? val)
           (let ((wrapped-once (get/build-wrapped-once val)))
              (chaperone-procedure* wrapped-once
                                    #f
                                    ->-w  wrapped-once
                                    ->-c  (guard-f-multi/c val ctc)))
             (blame pos)))]))

; Guard a function f with a multi-ho/c
; either the function f is clean and does not
; have a contract already
; otherwise the function has a multi-ho/c
; and we join the two contract together 
(define (guard-f-multi/c f multi)
  (if (not (has-->c? f))
      multi
      (join-multi-ho/c multi  (get-->-c f))))


(module+ test
  (require (for-syntax racket/syntax syntax/parse))
  (require rackunit)
  
  (define-syntax-rule (check-blame e1 e2)
    (check-equal? 
     (with-handlers ([exn:fail?  (λ (exn) (exn-message  exn))])  e1)
     e2))
  
  (define (contractTimes f c n)
    (if (= n 0)
        f
        (contractTimes (guard c f "positive" "negative") c (- n 1))))
  
  (define (cleanup)
    (collect-garbage)
    (collect-garbage)
    (collect-garbage))
  
  (define fc
    (contract
     (-> integer? integer?)
     (λ (x) x)
     'pos 'neg))
  
  (define int? (flat/c (lambda (x) (integer? x))))
  (define fc-space-efficient
    (guard
     (ho/c int? int?)
     (λ (x) x)
     'pos 'neg))
  
  (define (apply-x-times f x)
    (time
     (for ([x (in-range x)])
       (f 1))))
  
  (define ffc
    (let loop ([n 10])
      (cond
        [(zero? n) (λ (x) x)]
        [else (contract
               (-> integer? integer?)
               (loop (- n 1))
               'pos 'neg)])))
  
  (define (benchmark)
    (cleanup)
    (define testSize 3000000)
    (printf "one layer of wrapping-racket \n")
    (cleanup)
    (apply-x-times fc testSize)
    (printf "one layer of wrapping-space \n")
    (cleanup)
    (apply-x-times fc-space-efficient testSize)
    (printf "ten layers of wrapping-racket \n")
    (cleanup)
    (apply-x-times ffc testSize)
    (cleanup)
    (printf "ten layers of wrapping-space \n")
    (apply-x-times (contractTimes fc-space-efficient (ho/c int? int?) 10) testSize))

  (define (has-num-contracts? f x)
    (check-equal? (has-->c? f) #t)
    (let ([domain/c (multi-ho/c-dom (get-->-c f))]
          [range/c (multi-ho/c-rng (get-->-c f))])
      (check-equal? (length (multi-flat/c-proj-list domain/c))   x)
      (check-equal? (length (multi-flat/c-proj-list range/c))    x)
      (check-equal? (length (multi-flat/c-flat/c-list domain/c)) x)
      (check-equal? (length (multi-flat/c-flat/c-list range/c))  x)))

  ; A contract to check positive numbers 
  (define pos (flat/c (lambda (x) (and (integer? x) (>= x 0)))))
  ; A function contract from pos -> pos
  (define pos->pos (ho/c pos pos))
  ; A function contract from (pos->pos) -> pos
  (define pos->pos->pos (ho/c pos->pos pos))
  ; creating a contracted function 
  (define guarded (guard pos->pos (lambda (x) (* x -2)) "positive" "negative"))

  (define f_1 (guard pos->pos->pos (lambda (f)
                                     (check-equal? (has-->c? f) #t)
                                     ; Check that the already contracted function only has one
                                     ; contract
                                     (has-num-contracts? f 1)
                                     (f 1)) "pos" "neg"))

  (define f_2 (guard pos->pos->pos (lambda (f)
                                     (check-equal? (has-->c? f) #t)
                                     ; Check that the already contracted function only has one
                                     ; contract
                                     (has-num-contracts? f 1)
                                     (f -1)) "pos" "neg"))
  
  (check-blame (f_1 guarded) "Blaming  \"positive\"")
  (check-blame (f_2 guarded) "Blaming  \"pos\"")
  
  ;check whether it has a contract
  (check-equal? (has-->c? guarded) #t)
  ; checking normal blame 
  (check-blame (guarded -34) "Blaming  \"negative\"")
  (check-blame (guarded 34)  "Blaming  \"positive\"")

  ; Reapplying the same contract over the already contracted function
  (define guarded-twice (guard pos->pos guarded "positive2" "negative2"))
  (check-equal? (has-->c? guarded-twice) #t)
  ; Outer wrapper should be applied first for the domain
  (check-blame (guarded-twice -34) "Blaming  \"negative2\"")
  ; Inner wrapper should be applied first for the range
  (check-blame (guarded-twice 34)  "Blaming  \"positive\"")

  ; Get the domain and range contract from the twice contracted function
  (has-num-contracts? guarded-twice 1)
  ; Apply the contract 1000 times 
  (define insanely-contracted (contractTimes guarded-twice pos->pos 1000))
  (has-num-contracts? insanely-contracted 1)
  (println "If there is no red above it *might* be correct :) " )
  (benchmark))










                          
