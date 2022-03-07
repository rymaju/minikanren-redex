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
     ;(g ∧ g)     ; Conjuction (see Eg
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
     ;(s ∨ s)
     (delay s)]

  [e ::=
     ·
     Es
     ((T σ) ∨ e)]

  
  ; NOTE: changed from d -> delay because d is already the name for the relation nonterminal
  ;-------------------------------------
  ; Evaluation Contexts
  
  ; Answer Stream
 ; [Ev hole 
  ;     ((T σ) ∨ Ev)]
  [Ev  hole
      ;e
      ((T σ) ∨ Ev)]
  ; Search Tree
  [Es hole
      ;s
       (Es ∨ s)]
  
  ; Goal
  [Eg hole
      g
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
  [σ (((x y) ...) natural)]
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


(define red
  (reduction-relation
   L
   #:domain p
   [--> (in-hole Ev (delay s))  ; Ev[d s] => Ev[s] ; Delay Rule
        (in-hole Ev s)
        ]))
; Starting off with an easy rule that doesn't need metafunctions

;(redex-match L g (term (delay (T σ))))

;(redex-match L p (term [· (delay (T σ))]))
;                       ^ "·" is not a Γ (line 30)? hmm
; Will fail
(define Γ0 '())
(define σ0 '(() 0))
(redex-match L p (term (in-hole Ev (delay s))))
(test--> 
   red
   (term [,Γ0 (delay (T ,σ0))]) 
   (term [,Γ0 (T ,σ0)]))

; Q1: Should we have σ in the language somewhere?
; Q2: What are some examples of p? Seems like I'm getting confused on that part :/
;(redex-match L r (term caro))
(test-results)

(redex-match L d (term ((caro x) T)))
(redex-match L t (term 10))  