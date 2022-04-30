#lang racket
(require redex redex/gui)
(require redex/reduction-semantics)

  ; copy the number metafunction thingy for logic vars
  ; maybe σ = (((x y) ... counter)


;; It might be clearer to think about this as though the query is
;; instead the one and only call to an initial, implicitly define
;; defrel called "main".

(define-language L
  [p ::= (Γ e)]  ; Programs
  [Γ (d ...)]    ; Relation Environments
  [d (r x g)]    ; Relations

  ;------------------------------------
  ; Expressions
  [e ::=
     ()
     s
     ((⊤ σ) ∨ e)]

  ; Search Trees
  [s ()
     (g σ)
     (s + s)
     (s × g)
     (delay s)]

  ; Goals
  [g ⊤           ; Trivial success
     ⊥           ; Trivial failure
     (t =? t)    ; Syntactic equality
     (g ∨ g)     ; Disjunction
     (g ∧ g)     ; Conjuction
     (r t)       ; Relation call
     (∃ x g)]    ; Variable introduction

  ;Terms
  [t c
     x
     (t : t)]

  ;Other
  [r variable-not-otherwise-mentioned] ; to account for arbitrary relation names
  [x variable-not-otherwise-mentioned] ; to account for arbitrary parameter names
  [c number
     symbol
     boolean
     string]
  [σ ((x t) ...)] ;; Not modeling fresh variable introduction

  ;-------------------------------------
  ; Values
  [v              ; Empty Node
     ((⊤ σ) + v)] ; Answer Disjunct (yuck the letter v and logical or look the same

  ;-------------------------------------
  ; Evaluation Contexts
  [EΓ (Γ hole)]

  ; Answer Stream
  [Ev hole
      ((⊤ σ) + Ev)]

  ; Search Tree
  [Es hole
      (Es + s)
      (Es × g)]

  ; Goal
  [Eg hole
      (Eg ∧ g)
      (Eg ∨ g)])

(define red
  (reduction-relation L
    #:domain e

    [--> (in-hole Ev (in-hole Es ((g_1 ∨ g_2) σ)))
         (in-hole Ev (in-hole Es ((g_1 σ) + (g_2 σ))))
         "distribute subst in disj"]

    [--> (in-hole Ev (in-hole Es ((g_1 ∧ g_2) σ)))
         (in-hole Ev (in-hole Es ((g_1 σ) × g_2)))
         "distribute subst over conj"]

    [--> (in-hole Ev (in-hole Es (((⊤ σ_1) + (g_2 σ_2)) × g)))
         (in-hole Ev (in-hole Es (((⊤ σ_1) × g) + ((g_2 σ_2) × g))))
         "distribute disj ans over conj"]

    [--> (in-hole Ev (in-hole Es (((⊤ σ_1) + s) + s_2)))
         (in-hole Ev (in-hole Es ((⊤ σ_1) + (s + s_2))))
         "reassociate disj"]

    [--> (in-hole Ev (delay s))
         (in-hole Ev s)
         "invoke delay"]

    [--> (in-hole Ev (in-hole Es ((⊤ σ) × g)))
         (in-hole Ev (in-hole Es (g σ)))
         "bring subst to 2nd conjunct"]

    [--> (in-hole Ev (in-hole Es ((⊥ σ) × g)))
         (in-hole Ev (in-hole Es (⊥ σ)))
         "prune failure conjuncts"]

    [--> (in-hole Ev (in-hole Es ((⊥ σ) + s)))
         (in-hole Ev (in-hole Es s))
         "prune failure disjuncts"]

    [--> (⊥ σ)
         ()
         "prune bald failure"]

    
    ;; Consider, if we separate answer streams from search tree
    ;; disjuncts, then we would need some rule to "move into the
    ;; answer stream."
    
    ;; Need to actually implement the fresh nodes, fresh vars and subst for them

    [--> (in-hole Ev (in-hole Es ((t_1 =? t_2) σ)))
         (in-hole Ev (in-hole Es (⊤ σ)))
         ;; faking it
         ;; How do I actually implement a unification here?
         (side-condition (equal? (term t_1) (term t_2)))
         "unify succeed"]

    [--> (in-hole Ev (in-hole Es ((t_1 =? t_2) σ)))
         (in-hole Ev (in-hole Es (⊥ σ)))
         ;; faking it
         ;; How do I actually implement a unification here?
         (side-condition (not (equal? (term t_1) (term t_2))))
         "unify fails"]

    [--> (in-hole Ev (in-hole Es ((r t) σ)))
         (in-hole Ev (in-hole Es (delay (g σ))))
         ;; How do I hard-code a fake relation definition here?
         ;; How do I actually execute the lookup and subst through behavior here?
         ;; (judgment-holds (lookup-and-subst-through r Γ t g))
         ;; should find definition of r in Γ (of the form `(x g)`), subst through t for x, and use that as the body w/gamma
         "substitute through and add subst"]

    [--> (in-hole Ev (in-hole Es ((delay s) ∧ g)))
         (in-hole Ev (in-hole Es (delay (s ∧ g))))
         "propagate delay through conj"]

    [--> (in-hole Ev (in-hole Es ((delay s_1) + s_2)))
         (in-hole Ev (in-hole Es (delay (s_2 + s_1))))
         "propagate delay through disj, and flip"]

    ;; I think this is right because it's the equivalent in prolog of
    ;; a choice point with failure at the end, for no more results.
    ;; We prune it here rather than leaving it, but could do either
    [--> (in-hole Ev (in-hole Es ((⊤ σ) + (⊥ σ_2))))
         (in-hole Ev (in-hole Es (⊤ σ)))
         "prune failure from end"]))

(test-->
 red
 (term ((7 =? 7) ()))
 (term (⊤ ())))

(test-->
 red
 (term ((7 =? 7) ((x 2))))
 (term (⊤ ((x 2)))))

(test-->>
 red
 (term ((⊤ ((x 3)))
        +
        ((⊤ ((x 3)))
         +
         ((⊤ ((x 3)))
          +
          (((9 =? 9) ((x 3)))
           +
           ((17 =? 17) ((x 3))))))))

 (term ((⊤ ((x 3)))
        +
        ((⊤ ((x 3)))
         +
         ((⊤ ((x 3)))
          +
          ((⊤ ((x 3)))
           +
           (⊤ ((x 3)))))))))

(test-->>
 red
 (term
  ((delay ((7 =? 7) ((x 3)))) + (delay ((8 =? 8) ((x 4))))))
 (term ((⊤ ((x 3))) + (⊤ ((x 4))))))

(test-->>
 red
 (term ((6 =? 7) ((x 3))))
 (term ()))

(test-->>
 red
 (term ((⊥ ()) + (⊤ ((x 3)))))
 (term (⊤ ((x 3)))))

(test-->>
 red
 (term ((⊤ ((x 3))) + (⊥ ())))
 (term (⊤ ((x 3)))))

(test-->>
 red
 (term (((delay ((7 =? 7) ((x 3))))
         + (delay ((8 =? 8) ((x 4)))))
        + ((9 =? 9) ((x 9)))))
 (term ((⊤ ((x 9)))
        + ((⊤ ((x 3)))
           + (⊤ ((x 4)))))))


;; This asymmetry mirrors prolog's behavior re: choice points.
#|
?- 7 = 7 ; 6 = 7.
   true
;  false.
?- 6 = 7; 7 = 7.
   true.
?- 
|#
(test-->>
 red
 (term (((6 =? 7) ∨ (7 =? 7)) ((x 3))))
 (term (⊤ ((x 3)))))

(test-->>
 red
 (term (((7 =? 7) ∨ (6 =? 7)) ((x 3))))
 (term (⊤ ((x 3)))))

(traces red (term (((((⊤
                       ∧ (7 =? 7))
                      ∨ ((8 =? 8)
                         ∧ (9 =? 9)))
                     ∧ ((⊤
                         ∧ (7 =? 7))
                        ∨ ((8 =? 8)
                           ∧ (9 =? 9))))
                    ∨ (((⊤
                         ∧ (7 =? 7))
                        ∨ ((8 =? 8)
                           ∧ (9 =? 9)))
                       ∧ ((⊤
                           ∧ (7 =? 7))
                          ∨ ((8 =? 8)
                             ∧ (9 =? 9)))))
                   ((x 3)))))

;; (traces red (term (((((⊤
;;                        ∧ (7 =? 7))
;;                       ∨ ((8 =? 8)
;;                          ∧ (9 =? 9)))
;;                      ∧ ((⊥
;;                          ∨ (7 =? 7))
;;                         ∨ ((8 =? 8)
;;                            ∧ (9 =? 9))))
;;                     ∨ (((⊥
;;                          ∨ (7 =? 7))
;;                         ∨ ((8 =? 8)
;;                            ∧ (9 =? 9)))
;;                        ∧ ((⊤
;;                            ∧ (7 =? 7))
;;                           ∨ ((8 =? 8)
;;                              ∧ (9 =? 9)))))
;;                    ((x 3)))))

;; (traces red (term
;;              ((((⊤ ((x 3)))
;;                 ∨
;;                 ((8 =? 8)
;;                  ((x 3))))
;;                ∧
;;                ((7 =? 7)
;;                 ∨
;;                 (9 =? 9)))
;;               ∨
;;               ((17 =? 17)
;;                ((x 3))))))


(test-results)

