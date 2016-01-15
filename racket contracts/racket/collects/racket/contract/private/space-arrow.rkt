;  _________                           _________                __                        __          
; /   _____/__________    ____  ____   \_   ___ \  ____   _____/  |_____________    _____/  |_  ______
; \_____  \\____ \__  \ _/ ___\/ __ \  /    \  \/ /  _ \ /    \   __\_  __ \__  \ _/ ___\   __\/  ___/
; /        \  |_> > __ \\  \__\  ___/  \     \___(  <_> )   |  \  |  |  | \// __ \\  \___|  |  \___ \ 
;/_______  /   __(____  /\___  >___  >  \______  /\____/|___|  /__|  |__|  (____  /\___  >__| /____  >
;        \/|__|       \/     \/    \/          \/            \/                 \/     \/          \/ 
;
; Scratchpad for experimenting with space efficient contracts
; Christophe Scholliers 
; Please do not distribute, this code contains huge errors :)

#lang racket/base
(require racket/contract)
(require racket/contract/combinator)
(provide  (rename-out [arrow arrow-space]))


; Some helper functions (probably they are defined already somewhere else ...)
(define (zip3 l1 l2 l3) (map  (lambda (e1 e2 e3) (cons e1 (cons e2 e3))) l1 l2 l3))
(define (unzip l) (foldr (lambda (e l) (cons (cons (car e) (car l)) (cons (cdr e) (cdr l)))) '(()) l))
(define (implied-by-one? cl c) (foldr (lambda (e a) (or (contract-stronger? e c) a)) #f cl))
(define fst car)
(define snd cdr)

; Check a list of projections (there must be an operator for this ...)
(define (apply-projections-list flat-list v neg-list)
  (if (empty? flat-list)
      (lambda (neg-party) v)
      (apply-projections-list (rest flat-list)
                              (((first flat-list) v) (first neg-list))
                              (rest neg-list))))

; A structure to represent a flat *joinable* contract
(struct flat/c (predicate join)
  #:transparent
  #:property prop:flat-contract
  (build-flat-contract-property
   ; This is of course not correct 
   #:stronger (lambda (c1 c2)  #t )
   #:name (lambda (c) 'flat/c-joinable)
   #:first-order (lambda (c) (flat/c-predicate c)) 
   #:val-first-projection
   (λ (c)
     (λ (b)
       (λ (x)
         (lambda (neg)
         (if ((flat/c-predicate c) x)
             x
             (raise-blame-error
              ;find out how to get the contract property
              b x '(expected: "~a" given: "~e") 'todo x))))))))

; A structure for representing flat contract
; consisting of a list of flat contracts
; multi-flat/c

; two lists projections
; and a list of contracts.
(struct multi-flat/c flat/c (list blame-list neg-list)
  #:transparent
  #:property prop:flat-contract
  (build-flat-contract-property
   #:name (lambda (c) 'multi-flat/c)
   #:val-first-projection
   (λ (c)
     ; This blame label is unfortunately not used.
     (λ (b)
       ; Moved out making the projections
       ; so that we don't have to do this over and over again.
       ; Maybe we can even restructure and have the projections
       ; in the constructor ?
       (let ((projections (map  (lambda (p b)
                                ((get/build-val-first-projection p) b))
                              (multi-flat/c-list c)
                              (multi-flat/c-blame-list c))))
         (λ (x)
             ; Simply apply all the projections in the list
             (apply-projections-list projections x (multi-flat/c-neg-list c))))))))

; Constructor for multi-flat/c
(define (make-multi-flat/c #:list l
                          #:join [join join-multi-flat/c]
                          #:blame-list bl
                          #:neg-party neg)
  (multi-flat/c 'none join l bl neg))

; Join based on stronger.
; this got ugly really fast !
; As it turns out that we usually need the contract
; together with the blame we should probably refactor here 
(define (join-multi-flat/c fl1 fl2)
  (let* ((cl1 (multi-flat/c-list fl1))
         (neg1 (multi-flat/c-neg-list fl1))
         (bl1 (multi-flat/c-blame-list fl1))
         (cbl2 (zip3 (multi-flat/c-list fl2) (multi-flat/c-blame-list fl2) (multi-flat/c-neg-list fl2)))
         (not-implied (unzip (filter (lambda (cb) (not (implied-by-one? cl1 (fst cb)))) cbl2))))
    (if (empty? (fst not-implied))
          fl1
        (begin
          (make-multi-flat/c #:list        (append cl1   (fst not-implied))
                             #:blame-list  (append bl1   (fst (unzip (cdr not-implied))))
                             #:neg-party   (append neg1  (snd (unzip (cdr not-implied)))))))))

; Constructor for simple flat contracts
(define (make-flat/c #:predicate p #:join [join join-flat/c])
  (flat/c p join))

; Join two normal flat contracts
; Putting them into a list and use the normal join
(define (join-flat/c f1 f2 blame1 blame2)
  ; Completely wrong now ...
  (if (contract-stronger? f1 f2)
      (make-multi-flat/c #:list (list f1)    #:blame-list (list blame1) )
      (make-multi-flat/c #:list (list f1 f2) #:blame-list (list blame1 blame2))))

; Struct for representing arrow contracts
(struct arrow  (dom rng)
  #:property prop:chaperone-contract
  (build-chaperone-contract-property
   #:name
   (λ (arr) (arrow-name arr))
   #:val-first-projection
   (λ (arr) (arrow-val-first-proj arr))))

; The dom and range of an arrow projection will already have blame filled in.
(struct arrow-proj (dom-proj rng-proj flat-list-arrow))

; Helper function for showing the name of the contract
(define (arrow-name arr)
  `(-> , (arrow-dom arr)
       , (arrow-rng arr)))

; Helper function for wrapping a (possibly) contracted function 
(define (get/build-wrapped-once f neg-party)
  ;if it is already contracted don't wrap it again
  (if (has-contract? f)
      ; Peel off one layer
      (get-->-w f)
      ; Otherwise wrap it in a chaperone 
      (chaperone-procedure* f
                            (λ (chap arg)
                              (let*  ((contract (get-->-c chap))
                                      (dom/c (arrow-proj-dom-proj contract))
                                      (rng/c (arrow-proj-rng-proj contract)))
                                ;(printf "neg party == ~s \n" neg-party)
                                (values
                                 (λ (result) ((rng/c result) neg-party))
                                 ((dom/c arg) neg-party)))))))

; Creates a new arrow contract with multi-flat/c
(define (make-multi-flat contract blame neg-party)
  (if (not (arrow? contract))
      (make-multi-flat/c #:list        (list contract)
                         #:neg-party   (list neg-party)
                         #:blame-list  (list blame    ))
      (arrow (make-multi-flat (arrow-dom contract) (blame-swap blame) neg-party)
             (make-multi-flat (arrow-rng contract)  blame neg-party))))

; Join two arrow contracts having multi-flat/c
(define (join-arrows arrow1 arrow2)
  (if (arrow? arrow1)
      (arrow (join-arrows (arrow-dom arrow2) (arrow-dom arrow1))
             (join-arrows (arrow-rng arrow1) (arrow-rng arrow2)))
      ((flat/c-join arrow1) arrow2 arrow1)))

(define (make-dom-proj arr blame)
  ((get/build-val-first-projection (arrow-dom arr))
   (blame-add-context blame "the argument of" #:swap? #t)))

(define (make-rng-proj arr blame)
  ((get/build-val-first-projection (arrow-rng arr))
   (blame-add-context blame "the range of")))

(define (make-projection arr blame neg-party)
  (let ((dom+proj (make-dom-proj arr blame))
        (rng+proj (make-rng-proj arr blame)))
    (arrow-proj dom+proj rng+proj (make-multi-flat arr blame neg-party) )))

; Helper function for joining 
(define (join-arrow-contracts arr f blame neg-party)
  (if (not (has-->c? f))
      ; Create the first projections
      (make-projection arr blame neg-party)
      ; The value has a contract which should be an arrow-proj
      (let*  ((inner-arrow-proj (get-->-c f))
              (new-mf (make-multi-flat arr blame neg-party))
              (old-mf (arrow-proj-flat-list-arrow inner-arrow-proj))
              (new-arrow (join-arrows new-mf old-mf))
              (dom+proj (make-dom-proj new-arrow blame))
              (rng+proj (make-rng-proj new-arrow blame)))
        (arrow-proj dom+proj rng+proj new-arrow))))      

;; Impersonator property for saving the wrapped function
(define-values (->-w has-->w? get-->-w)
  (make-impersonator-property '->-w))

;; Impersonator property for saving the contract tree
(define-values (->-c has-->c? get-->-c)
  (make-impersonator-property '->-c))

(define (arrow-val-first-proj arr)
  (λ (blame)
    (λ (f)
      ; Should be done differently in the "real" implemenation
      ; This is actually checking the first order contracts ...
      (if (and (procedure? f)
               (procedure-arity-includes? f 1))

          (λ (neg-party)
            (let ((wrapped-once (get/build-wrapped-once f neg-party)))
              ;Now we wrap the wrapped-once a second time  
              (chaperone-procedure* wrapped-once
                                    ;
                                    #f
                                    ; Save the wrapped function 
                                    ->-w  wrapped-once
                                    ; Set the blame and contract properties of the last wrapped function
                                    ->-c  (join-arrow-contracts arr f blame neg-party))))
          
          (λ (neg-party)
            (raise-blame-error
             blame #:missing-party neg-party
             f
             '(expected "a procedure of one argument" given: "~e")
             f))))))

(module+ test
  (require (for-syntax racket/syntax syntax/parse))
  (require rackunit)
  
  (define (between min max) (make-flat/c #:predicate (lambda (val) (and (> val min) (< val max)))))
  (define between_0_10 (between 0 10))
  (define -> arrow)
  ; Special flat contracts
  (define contracted_f  (contract (-> (between 0 10) (between  0 5)) (lambda (x) 9) 'positive 'negative))
  (define contracted_ff (contract (-> (between 0 10) (between  0 5)) contracted_f   'positive2 'negative2))
  ; Normal flat contracts 
  (define contracted_f1 (contract (-> (between/c 0 10) (between/c 0 5)) (lambda (x) 9) 'positive-built-in 'negative-built-in))
  (define contracted_ff2 (contract (-> (between/c 0 10) (between/c 0 5)) contracted_f1 'positive-built-in-2 'negative-built-in-2))
  ; Higher-order function 
  (define contracted_f_ho (contract (-> (between/c 0 10)
                                        (-> (between/c 0 10)
                                            (between/c 0 20)))
                                    (lambda (x) (lambda (y) (+ x y)))
                                    'positive-ho
                                    'negative-ho))
  ; Double Wrapped higher-order function 
  (define contracted_ff_ho (contract (-> (between/c 0 10)
                                         (-> (between/c 0 10)
                                             (between/c 0 20)))
                                     contracted_f_ho
                                     'positive-ho-w
                                     'negative-ho-w))
  
  ;Copy paste from Dan's code
  (define-syntax-rule (check-blame e1 e2)
    (check-equal? 
     (with-handlers ([exn:fail:contract?
                      (λ (exn) (blame-positive (exn:fail:contract:blame-object exn)))])
       e1)
     e2))

  ; Sanity check does normal blame works for simple arrow contracts with custom flat contracts
  (check-blame (contracted_f 10) 'negative)
  (check-blame (contracted_f 5) 'positive)
  ; Does simple blame of the doubly wrapped function works for custom flat contracts 
  (check-blame (contracted_ff 10) 'negative2)
  (check-blame (contracted_ff 5) 'positive)
  ; Check simple blame for the simple arrow contracts with standard flat contracts
  (check-blame (contracted_f1 20) 'negative-built-in)
  (check-blame (contracted_ff2 3) 'positive-built-in)
  ; Check higher-order function blame assignment for standard flat contracts
  (check-blame ((contracted_f_ho 5) 20) 'negative-ho)
  (check-blame ((contracted_ff_ho 5) 20) 'negative-ho-w)
  (display "Done"))


(define (contractTimes f c n)
  (if (= n 0)
      f
      (contractTimes (contract c f 'positive 'negative) c (- n 1))))

;(define wrapped (contractTimes (lambda (x) 9) (arrow (between/c 0 10) (between/c 0 5)) 1000))
;(define test-c-dom (arrow-dom (arrow-proj-flat-list-arrow (get-->-c wrapped))))
;(define c-rng-ff2 (arrow-rng (arrow-proj-flat-list-arrow (get-->-c contracted_ff2))))
;(define blame-rng-ff2 (car (multi-flat/c-blame-list c-rng-ff2)))
;(define neg-rng (car (multi-flat/c-neg-list c-rng-ff2)))
;(newline)
;(display neg-rng)
