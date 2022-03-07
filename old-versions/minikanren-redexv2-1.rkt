#lang racket
(require redex)
(require redex/reduction-semantics)


; e ::= ≐ | s | ans v e
; p ::= (Γ e)
; minikanren wants to capture the search order

; make sure v subset of e

(define-language L
  ;------------------------------------
  ; Expressions
 
  [Γ ::= (d ...)]  ; Relation Environments

  ; (Γ g) -> (Γ g2) -> (Γ g3) ??
  
  ; ideally we want a:
  ; search tree -> search tree
  ; maybe add s to v
  ; if we instead of using g, had an s?
  
  
  [p ::=
     (Γ e)]      ; Programs
  [d ::= ((r x) g)]  ; Relation definitions
  
  ; Goals
  [g ::=
     T           ; Trivial success
     ⊥           ; Trivial failure
     (t =? t)    ; Syntactic equality
     (g ∨ g)     ; Disjunction
     (g ∧ g)     ; Conjuction
     (r t)       ; Relation call
     ((∃ x)  g)] ; Variable introduction

  ;-------------------------------------
  ; Values and Search Trees

  ; Values
  ;[v ::=
  ;   ·             ; Empty Node
  ;   ((T σ) ∨ v)] ; Answer Disjunct (yuck the letter v and logical or look the same


  ;((g ∨ g) σ) => ((g σ) ∨ (g σ))
  ; copy the number metafunction thingy for logic vars
  ; state is gross though?
  ; maybe σ = (((x y)... counter)
  ; Search Trees
  [s ·
     (g σ)
     (s ∨ s)
     (delay s)]

  [e ::=
     s
     ((T σ) ∨ e)]

  
  ; NOTE: changed from d -> delay because d is already the name for the relation nonterminal
  ;-------------------------------------
  ; Evaluation Contexts
  
  ; Answer Stream
 ; [Ev hole 
  ;     ((T σ) ∨ Ev)]
  [Ev hole
      (Γ Ev)
      ((T σ) ∨ Ev)]
  ; Search Tree
  [Es hole
       (Es ∨ s)]
  
  ; Goal
  [Eg hole
       (Eg ∧ g)]


  ;Terms
  [t c
     x
     (t t...)]

  ;Other
  [r variable-not-otherwise-mentioned] ; to account for arbitrary relation names
  [x variable-not-otherwise-mentioned] ; to account for arbitrary parameter names
  [c number
     symbol
     boolean
     string]
  [σ (((t t) ...) natural)]
  )


;                                                                                            
;                            ;                                     ;;                        
;    ;;;;;                    ;                                    ;;                        
;    ;   ;;                   ;                         ;;                                   
;    ;    ;;                  ;                         ;;                                   
;    ;    ;;    ;;;;      ;;; ;    ;    ;      ;;;;   ;;;;;;;    ;;;;       ;;;;     ; ;;;   
;    ;    ;;   ;;  ;;    ;;  ;;    ;    ;    ;;   ;     ;;          ;      ;;  ;;    ;;  ;;  
;    ;    ;    ;    ;   ;;    ;    ;    ;    ;          ;;          ;      ;    ;    ;    ;  
;    ;;;;;    ;;    ;;  ;;    ;    ;    ;    ;          ;;          ;     ;;    ;;   ;    ;  
;    ;  ;     ;;;;;;;;  ;;    ;    ;    ;   ;;          ;;          ;     ;;    ;;   ;    ;  
;    ;  ;;    ;;        ;;    ;    ;    ;    ;          ;;          ;     ;;    ;;   ;    ;  
;    ;   ;;    ;        ;;    ;    ;    ;    ;          ;;          ;     ;;    ;    ;    ;  
;    ;    ;    ;;   ;    ;;  ;;    ;   ;;    ;;   ;      ;  ;       ;      ;;  ;;    ;    ;  
;    ;    ;;    ;;;;      ;;; ;    ;;;; ;     ;;;;;      ;;;;;   ;;;;;;     ;;;;     ;    ;  
;                                                                                            
;                                                                                            
;                                                                                            
;                                                                                            
;                                                                                            
;                                                                                            

(define Γ0 '())
(define σ0 '(() 0))
(define σ-sm '(((1 1)) 0)) ; small example, intentionally not really correct

(define red
  (reduction-relation
   L
   #:domain p
   [--> (in-hole Ev (delay s))  ; Ev[d s] => Ev[s] ; Delay Rule
        (in-hole Ev s)
        ]

   ;; rules that dont rewrite the tree (goal rewrites/step goals)
   [--> (in-hole Ev (in-hole Es ((in-hole Eg (g_1 ∨ g_2)) σ_1)))
        (in-hole Ev (in-hole Es ((g_1 σ_1) ∨ (g_2 σ_1))))]

   ;fresh
   ;[--> (in-hole Ev (in-hole Es ((in-hole Eg ((∃ x)  g)) σ_1)))
   ;     (in-hole Ev (in-hole Es ((g_1 σ_1) ∨ (g_2 σ_1))))]     

   ;unification (incorrect, but simple syntactic equality for now)
   ;TODO: use unification metafunction
   [--> (in-hole Ev (in-hole Es ((in-hole Eg (t =? t)) σ_1)))
        (in-hole Ev (in-hole Es ((in-hole Eg T) (extend-σ σ_1 t t))))
        ]
   [--> (in-hole Ev (in-hole Es ((in-hole Eg (t_1 =? t_2)) σ_1)))
        (in-hole Ev (in-hole Es ((in-hole Eg ⊥) ,σ0)))
        (side-condition (not (equal? (term t_1) (term t_2))))
        ]

   [--> (in-hole Ev (in-hole Es ((in-hole Eg (⊥ ∧ g)) σ_1)))
        (in-hole Ev (in-hole Es ((in-hole Eg ⊥) ,σ0)))
        "False AND"]

   [--> (in-hole Ev (in-hole Es ((in-hole Eg (T ∧ g)) σ_1)))
        (in-hole Ev (in-hole Es ((in-hole Eg T) σ_1)))
        "True AND"]

        
   [--> (in-hole Ev (in-hole Es (T σ)))
        (in-hole Ev ((T σ) ∨ (in-hole Es ·)))
        "reroot"
        ]
   [--> (in-hole Ev (in-hole Es (⊥ σ)))
        (in-hole Ev (in-hole Es ·))
        "prune fail"
        ]
   [--> (in-hole Ev (in-hole Es (· ∨ s)))
        (in-hole Ev (in-hole Es s))]
   ))

(define-metafunction L
  extend-σ : σ t t -> σ
  [(extend-σ σ t_1 t_2)

   ,(list (cons (list (term t_1) (term t_2)) (first (term σ)))
          (second (term σ)))

   ])

(define-metafunction L
  Σ : number ... -> number
  [(Σ number ...)
   ,(apply + (term (number ...)))])

(define-metafunction L
  [(different t_1 t_1) #f]
  [(different t_1 t_2) #t])

; Starting off with an easy rule that doesn't need metafunctions

;(redex-match L g (term (delay (T σ))))

;(redex-match L p (term [· (delay (T σ))]))
;                       ^ "·" is not a Γ (line 30)? hmm


; Delays are forced
(test--> 
   red
   (term [,Γ0 (delay (T ,σ0))]) 
   (term [,Γ0 (T ,σ0)]))

; Goal disjunctions reduce to disjunction of search tree nodes
(test--> 
   red
   (term [,Γ0 ((T ∨ ⊥) ,σ0)]) 
   (term [,Γ0 ((T ,σ0) ∨ (⊥ ,σ0))]))

; Unification (fake)
(test--> 
   red
   (term [,Γ0 ((1 =? 1) ,σ0)]) 
   (term [,Γ0 (T (((1 1)) 0))]))

(test--> 
   red
   (term [,Γ0 ((1 =? 2) ,σ0)]) 
   (term [,Γ0 (⊥ ,σ0)]))

; (False And ???) short circuiting
(test--> 
   red
   (term [,Γ0 ((⊥ ∧ T) ,σ-sm)]) 
   (term [,Γ0 (⊥ ,σ0)]))

; (True And ???) simplification
(test--> 
   red
   (term [,Γ0 ((T ∧ T) ,σ0)]) 
   (term [,Γ0 (T ,σ0)]))




;; Search tree

; Reroot
(test--> 
   red
   (term [,Γ0 (T ,σ0)])
   (term [,Γ0 ((T ,σ0) ∨ ·)]))

; Prune fail
(test--> 
   red
   (term [,Γ0 (⊥ ,σ0)])
   (term [,Γ0 ·]))

; Prune empty
(test--> 
   red
   (term [,Γ0 ((· ∨ (T ,σ0)) ∨ (T ,σ0))])
   (term [,Γ0 ((T ,σ0) ∨ (T ,σ0))]))

; Really odd test, not sure why reroot is adding a dot instead of swapping
(test--> 
   red
   (term [,Γ0 ((T ,σ0) ∨ (· ∨ (T ,σ0)))])
   (term [,Γ0 ((T ,σ0) ∨ (T ,σ0))]))
;; TODO: test with a non trivial rhs goal

(test--> 
   red
   (term [,Γ0 ((T ,σ0) ∨ (T ,σ0))])
   (term [,Γ0 ((T ,σ0) ∨ ((T ,σ0) ∨ ·))]))

(stepper red (term [,Γ0 ((T ,σ0) ∨ (· ∨ (T ,σ0)))]))
; Q1: Should we have σ in the language somewhere?
; Q2: What are some examples of p? Seems like I'm getting confused on that part :/
;(redex-match L r (term caro))
(redex-match L d (term ((caro x) T)))
(redex-match L t (term 10))  
(test-results)
;(traces red (term [,Γ0 ((T ,σ0) ∨ (· ∨ (T ,σ0)))]))