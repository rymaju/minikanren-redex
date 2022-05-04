#lang racket
(require redex redex/gui)
(require redex/reduction-semantics)

;; Consider, if we separate answer streams from search tree
;; disjuncts, then we would need some rule to "move into the
;; answer stream."

;; It might be clearer to think about this as though the query is
;; instead the one and only call to an initial, implicitly define
;; defrel called "main".

; copy the number metafunction thingy for logic vars
; maybe σ = (((x y) ... counter)

(define-language L
  [p ::= (prog Γ e)] ; Programs, Relation Environments, and Relations
  [Γ ((r b) ...)]    ; 
  [b (lam x g)]          ;
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
     o ;; for other, change to make c constant and i number 
     x
     (t : t)]

  ;Other
  [r variable-not-otherwise-mentioned] ; to account for arbitrary relation names
  [x variable-not-otherwise-mentioned] ; to account for arbitrary parameter names
  [c number]
  [o symbol
     boolean
     string]
  [σ (state sub c)] ;; Not modeling fresh variable introduction
  [sub ((x t) ...)]
  
  ;-------------------------------------
  ; Values
  [v ()        ; Empty Node
     (⊤ σ)     ; Singleton Node
     ((⊤ σ) + v)] ; Answer Disjunct (yuck the letter v and logical or look the same

  ;-------------------------------------
  ; Evaluation Contexts
  [EΓ (prog Γ hole)]

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
      (Eg ∨ g)]
  #:binding-forms
  (∃ x g #:refers-to x)
  (lam x g #:refers-to x)
  (prog ((r b) ...) #:refers-to (shadow r ...) e #:refers-to (shadow r ...)))

(define red
  (reduction-relation L
    #:domain p

    [--> (in-hole EΓ (in-hole Ev (in-hole Es ((g_1 ∨ g_2) σ))))
         (in-hole EΓ (in-hole Ev (in-hole Es ((g_1 σ) + (g_2 σ)))))
         "distribute subst in disj"]

    [--> (in-hole EΓ (in-hole Ev (in-hole Es ((g_1 ∧ g_2) σ))))
         (in-hole EΓ (in-hole Ev (in-hole Es ((g_1 σ) × g_2))))
         "distribute subst over conj"]

    [--> (in-hole EΓ (in-hole Ev (in-hole Es (((⊤ σ_1) + (g_2 σ_2)) × g))))
         (in-hole EΓ (in-hole Ev (in-hole Es (((⊤ σ_1) × g) + ((g_2 σ_2) × g)))))
         "distribute disj ans over conj"]

    [--> (in-hole EΓ (in-hole Ev (in-hole Es (((⊤ σ_1) + s) + s_2))))
         (in-hole EΓ (in-hole Ev (in-hole Es ((⊤ σ_1) + (s + s_2)))))
         "reassociate disj"]

    [--> (in-hole EΓ (in-hole Ev (delay s)))
         (in-hole EΓ (in-hole Ev s))
         "invoke delay"]

    [--> (in-hole EΓ (in-hole Ev (in-hole Es ((⊤ σ) × g))))
         (in-hole EΓ (in-hole Ev (in-hole Es (g σ))))
         "bring subst to 2nd conjunct"]

    [--> (in-hole EΓ (in-hole Ev (in-hole Es ((⊥ σ) × g))))
         (in-hole EΓ (in-hole Ev (in-hole Es (⊥ σ))))
         "prune failure conjuncts"]

    [--> (in-hole EΓ (in-hole Ev (in-hole Es ((⊥ σ) + s))))
         (in-hole EΓ (in-hole Ev (in-hole Es s)))
         "prune failure disjuncts"]
    
    ;; Need to actually implement the fresh nodes, fresh vars and subst for them

    ;; Need some way to describe the gensym'd values and the non-gensym'd values
    [--> (in-hole EΓ (in-hole Ev (in-hole Es ((∃ x g) σ))))
         (in-hole EΓ (in-hole Ev (in-hole Es (g σ)))) ;; (in-hole Ev (in-hole Es (g_1 (state sub c_1))))
         "fresh subst"
         ;; (where c_1 (term 5))
         ;; (where g_1 (term (7 =? 7)))
         ]

    [--> (in-hole EΓ (in-hole Ev (in-hole Es ((t_1 =? t_2) σ))))
         (in-hole EΓ (in-hole Ev (in-hole Es (⊤ σ))))
         ;; faking it
         ;; How do I actually implement a unification here?
         (side-condition (equal? (term t_1) (term t_2)))
         "unify succeed"]

    [--> (in-hole EΓ (in-hole Ev (in-hole Es ((t_1 =? t_2) σ))))
         (in-hole EΓ (in-hole Ev (in-hole Es (⊥ σ))))
         ;; faking it
         ;; How do I actually implement a unification here?
         (side-condition (not (equal? (term t_1) (term t_2))))
         "unify fails"]

    [--> (in-hole EΓ (in-hole Ev (in-hole Es ((r t) σ))))
         (in-hole EΓ (in-hole Ev (in-hole Es (delay (g σ)))))
         ;; How do I hard-code a fake relation definition here?
         ;; How do I actually execute the lookup and subst through behavior here?
         ;; (judgment-holds (lookup-and-subst-through r Γ t g))
         ;; should find definition of r in Γ (of the form `(x g)`), subst through t for x, and use that as the body w/gamma
         "substitute through and add subst"]

    [--> (in-hole EΓ (in-hole Ev (in-hole Es ((delay s) ∧ g))))
         (in-hole EΓ (in-hole Ev (in-hole Es (delay (s ∧ g)))))
         "propagate delay through conj"]

    [--> (in-hole EΓ (in-hole Ev (in-hole Es ((delay s_1) + s_2))))
         (in-hole EΓ (in-hole Ev (in-hole Es (delay (s_2 + s_1)))))
         "propagate delay through disj, and flip"]

    ;; I think this is right because it's the equivalent in prolog of
    ;; a choice point with failure at the end, for no more results.
    ;; We prune it here rather than leaving it, but could do either
    [--> (in-hole EΓ (in-hole Ev ((⊤ σ) + (⊥ σ_2))))
         (in-hole EΓ (in-hole Ev ((⊤ σ) + ())))
         "prune failure from end"]

    [--> (in-hole EΓ (in-hole Ev (⊥ σ)))
         (in-hole EΓ (in-hole Ev ()))
         "prune bald failure"]))

;; (redex-match 
;;  L
;;  s            
;;  (term 
;;   (⊤
;;    (state
;;     ((x 3))
;;     0))))

;; (redex-match? L (in-hole Es hole)
;;  (apply-reduction-relation
;;   red (term ((7 =? 7) (state () 0)))))

;; (pretty-print "Below is the term we expect to produce.")
;; (term (⊤ (state () 0)))

;; (pretty-print "Here is the test where we claim we produce it.")
;; (test--> 
;;  red
;;  (term ((∃ x (7 =? 7)) (state () 0)))
;;  (term (⊤ (state () 0))))

;; (pretty-print "Curiously, though, the first goes to the second, and
;; the second goes to the third.")
;; (test--> 
;;  red
;;  (term ((∃ x (7 =? 7)) (state () 0)))
;;  (term ((7 =? 7) (state () 0))))
;; (test--> 
;;  red
;;  (term ((7 =? 7) (state () 0)))
;;  (term (⊤ (state () 0))))

;; (pretty-print "Curiously, though, traces says otherwise. Watch.")
;; (traces
;;  red
;;  (term ((∃ x (7 =? 7)) (state () 0))))

;; (pretty-print "This seems to go wrong at the existential reduction---a
;; consequence of \"fresh subst\" or how and where we apply it. If we add
;; extra layers, it always fails, returning instead the result of the
;; first reduction.")
;; (test-->
;;  red
;;  (term ((∃ y (∃ z (∃ x (7 =? 7)))) (state () 0)))
;;  (term (⊤ (state () 0))))

;; (traces
;;  red
;;  (term ((∃ y (∃ z (∃ x (7 =? 7)))) (state () 0))))

;; (pretty-print "Deceptively, it *looks* like we get an extra set of
;; parens, and like that would explain the failure. But I don't think
;; that's the real problem.")
;; (apply-reduction-relation*
;;  red
;;  (term ((∃ x (7 =? 7)) (state () 0))))

;; (pretty-print "I think somehow that we're getting those extra parens
;; because it's giving back a list of answers, maybe")


(redex-match? L g (term (∃ x (x =? 7))))
(redex-match? L σ (term (state () 0)))
(redex-match? L s (term ((∃ x (x =? 7)) (state () 0))))
(redex-match? L e (term ((∃ x (x =? 7)) (state () 0))))

;; Instead I am getting an extra set of parens around this one.
;; '(((7 =? 7) (state () 0)))
(test-->
 red
 (term (prog ()  ((7 =? 7) (state () 0))))
 (term (prog ()  (⊤ (state () 0)))))

(test-->
 red
 (term (prog ()  ((∃ x ⊤) (state () 0))))
 (term (prog ()  (⊤ (state () 0)))))

(traces
 red
 (term (prog ()  ((∃ x (7 =? 7)) (state () 0)))))

(test-->
 red
 (term (prog ()  ((7 =? 7) (state ((x 2)) 0))))
 (term (prog ()  (⊤ (state ((x 2)) 0)))))

(test-->>
 red
 (term (prog ()  ((⊤ (state ((x 3)) 0))
         +
         ((⊤ (state ((x 3)) 0))
          +
          ((⊤ (state ((x 3)) 0))
           +
           (((9 =? 9) (state ((x 3)) 0))
            +
            ((17 =? 17) (state ((x 3)) 0))))))))

 (term (prog ()  ((⊤ (state ((x 3)) 0))
         +
         ((⊤ (state ((x 3)) 0))
          +
          ((⊤ (state ((x 3)) 0))
           +
           ((⊤ (state ((x 3)) 0))
            +
            (⊤ (state ((x 3)) 0)))))))))

(test-->>
 red
 (term
  (prog ()  ((delay ((7 =? 7) (state ((x 3)) 0))) + (delay ((8 =? 8) (state ((x 4)) 0))))))
 (term (prog ()  ((⊤ (state ((x 3)) 0)) + (⊤ (state ((x 4)) 0))))))

(test-->>
 red
 (term (prog ()  ((6 =? 7) (state ((x 3)) 0))))
 (term (prog ()  ())))

(test-->>
 red
 (term (prog ()  ((⊥ (state () 0)) + (⊤ (state ((x 3)) 0)))))
 (term (prog ()  (⊤ (state ((x 3)) 0)))))

(test-->>
 red
 (term (prog ()  ((⊤ (state ((x 3)) 0)) + (⊥ (state ((x 4)) 0)))))
 (term (prog ()  ((⊤ (state ((x 3)) 0)) + ()))))

(test-->>
 red
 (term (prog ()  (((delay ((7 =? 7) (state ((x 3)) 0)))
          + (delay ((8 =? 8) (state ((x 4)) 0))))
         + ((9 =? 9) (state ((x 9)) 0)))))
 (term (prog ()  ((⊤ (state ((x 9)) 0))
         + ((⊤ (state ((x 3)) 0))
            + (⊤ (state ((x 4)) 0)))))))


;; This asymmetry mirrors prolog's behavior re: choice oints.
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
 (term (prog ()  (((6 =? 7) ∨ (7 =? 7)) (state ((x 3)) 0))))
 (term (prog ()  (⊤ (state ((x 3)) 0)))))

(test-->>
 red
 (term (prog ()  (((7 =? 7) ∨ (6 =? 7)) (state ((x 3)) 0))))
 (term (prog ()  ((⊤ (state ((x 3)) 0)) + ()))))

(test-->> red (term (prog ()  (((((⊤
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
                      (state ((x 3)) 0))))
          (term 
           (prog ()  ((⊤ (state ((x 3)) 0))
             +
             ((⊤ (state ((x 3)) 0))
              +
              ((⊤ (state ((x 3)) 0))
               +
               ((⊤ (state ((x 3)) 0))
                +
                ((⊤ (state ((x 3)) 0))
                 +
                 ((⊤ (state ((x 3)) 0))
                  +
                  ((⊤ (state ((x 3)) 0))
                   +
                   (⊤
                    (state
                     ((x 3))
                     0))))))))))))

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
;;                    (state ((x 3)) 0))))

;; (traces red (term
;;              ((((⊤ (state ((x 3)) 0))
;;                 ∨
;;                 ((8 =? 8)
;;                  (state ((x 3)) 0)))
;;                ∧
;;                ((7 =? 7)
;;                 ∨
;;                 (9 =? 9)))
;;               ∨
;;               ((17 =? 17)
;;                (state ((x 3)) 0)))))


(test-results)
 
