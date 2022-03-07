#lang racket
(require redex)

; Top level          :[Stream -> List]
; append(map) nodes  : (append | append-map | delay | goal/subst) -> Stream

; Stream of X
; - (cons X [Stream of X])
; - () -> [Stream of X]
; - ()

(define-language L
  [e ::=      ; Expression
     r
     s]
  [a∞ ::= 
     (σ ... s)
     (σ ...)]
  [s ::= ; Search Tree Node
     (append e e) ; combine results of both subnodes
     (append-map g e) ; combine results of applying g to all nodes in s
     (delay e)
     a∞]
  [r ::=
     (g σ)]
  
  [g ::= ; Goals
     (t =? t) ; unify
     (g ∨ g)  ; disjunction
     (g ∧ g)  ; conjunction
     ;(r x) ; relation call
     ;(∃ x) ; fresh logic var introduction
     ]
  [σ ::= ; Substitution
     ((x c) ...)]
  [t :==
     c
     (t ...)]
  [c :==
     number
     boolean
     string]
  [x ::= variable-not-otherwise-mentioned]
  ; Contexts
 
  [Es ::=
      hole
      (append Es ?)
      (append σ* Es)
      (append-map g Es)
      
      ]
  )



(define red
  (reduction-relation
   L
   #:domain e

   [--> (in-hole Es ((σ_0 ...) ((t =? t) σ_1)))
        (in-hole Es (σ_1 σ_0 ...))
        "unify succeed"]

   [--> (in-hole Es (σ* ((t_1 =? t_2) σ)))
        (in-hole Es ())
        (side-condition (not (equal? (term t_1) (term t_2))))
        "unify fail"]
  
   [--> (σ* (in-hole Es ((g_1 ∨ g_2) σ_2)))
        (σ* (in-hole Es (append (σ* (g_1 σ_2))
                                (() (g_2 σ_2)))))
        "or"]
   [--> (σ* (in-hole Es ((g_1 ∧ g_2) σ_2)))
        (σ* (in-hole Es (append-map g_2
                                    (() (g_1 σ_2)))))
        "and"]
   ; append
   ; Q: does real append really wait for both to resolve before resolving like this?
   [--> (in-hole Es ( (σ_0 ...) (append (σ_1 ...) (σ_2 ...))))
        (σ_0 ... σ_1 ... σ_2 ...)
        "append1"]
 
   ; append-map
   [--> (in-hole Es (append-map g (σ_1 σ_2 ...)))
        (in-hole Es (append (() (g σ_1))
                                        (() (append-map
                                             g
                                             (σ_2 ...)))))
        "append-map1"]
   
   [--> (in-hole Es ((σ_0 ...) (append-map g ())))
        (σ_0 ...)
        "append-map2"]
   ; force delay
   ; TODO: context
   ; seems wrong, should this be Ev?
   #;[--> (in-hole Es ((delay s)))
        (in-hole Es s)
        "force delay"]
   ))

;(redex-match L p (term ((((1 =? 2) ∨ (1 =? 1)) ()))))
;(traces red (term ((((1 =? 2) ∨ (1 =? 1)) ()))))
#;(traces red (term ((append
                   (delay ((1 =? 2) ()))
                   ((1 =? 1) ())))))
(test--> red
         (term (()  ((1 =? 1) ())))
         (term (())))

(test--> red
         (term (()  ((1 =? 2) ())))
         (term ()))

(test--> red
         (term (()  (((1 =? 1) ∨ (1 =? 2)) ())))
         (term (()  (append (() ((1 =? 1) ()))
                            (() ((1 =? 2) ()))))))
#;(traces red (term (() (append (() ((1 =? 1) ()))
                              (() ((1 =? 2) ()))))))

(traces red (term (()  (((1 =? 1) ∨ (1 =? 2)) ()))))
#;(traces red
         (term (()  (((1 =? 1) ∧ (1 =? 2)) ()))))
(traces red (term (()
 (append
  ()
  (()
   (append-map (1 =? 2) ()))))))
#;(traces red
        (term (()
   (append-map (1 =? 2) ()))))
(test-results)