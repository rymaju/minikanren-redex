#lang racket
(require redex redex/gui)
(require redex/reduction-semantics)
(require rackunit)


;; Need to fix the real-subst fake-subst situation, and make sure that
;; I have some solution for what to do when I fail a unification.

;; Consider, if we separate answer streams from search tree
;; disjuncts, then we would need some rule to "move into the
;; answer stream."

;; It might be clearer to think about this as though the query is
;; instead the one and only call to an initial, implicitly define
;; defrel called "main".

(define-language L
  [p ::= (prog Γ e)] ; Programs, Relation Environments, and Relations
  [Γ ((r_!_ x g) ...)] ;  I think this ensures that 'ri's are distinct
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
     o ;; for other, change to make c constant and i natural 
     x
     (t : t)]

  ;Other
  [r variable-not-otherwise-mentioned] ; to account for arbitrary relation names
  [x variable-not-otherwise-mentioned] ; to account for arbitrary parameter names
  [c natural]
  [o symbol
     boolean
     string]
  [σ (state sub c)] ;; Not modeling fresh variable introduction
  [sub true-sub #f]
  [true-sub ((x t) ...) #f]
  
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
  (prog ((r x g #:refers-to x) ...) #:refers-to (shadow r ...) e #:refers-to (shadow r ...)))

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

    [--> (in-hole EΓ (in-hole Ev (in-hole Es (((⊤ σ) + s) + s_2))))
         (in-hole EΓ (in-hole Ev (in-hole Es ((⊤ σ) + (s + s_2)))))
         "reassociate disj"]

    [--> (in-hole EΓ (in-hole Ev (delay s)))
         (in-hole EΓ (in-hole Ev s))
         "invoke delay"]

    [--> (in-hole EΓ (in-hole Ev (in-hole Es ((⊤ σ) × g))))
         (in-hole EΓ (in-hole Ev (in-hole Es (g σ))))
         "bring subst to 2nd conjunct"]

    [--> (in-hole EΓ (in-hole Ev (in-hole Es ((⊥ #f) × g))))
         (in-hole EΓ (in-hole Ev (in-hole Es (⊥ #f))))
         "prune failure conjuncts"]

    [--> (in-hole EΓ (in-hole Ev (in-hole Es ((⊥ #f) + s))))
         (in-hole EΓ (in-hole Ev (in-hole Es s)))
         "prune failure disjuncts"]

    [--> (in-hole EΓ (in-hole Ev (in-hole Es ((∃ x g) (state sub c)))))
         (in-hole EΓ (in-hole Ev (in-hole Es ((substitute g x c) (state sub ,(add1 (term c)))))))
         "fresh subst"]

    [--> (prog ((r_0 x_0 g_0) ... (r_1 x_1 g_1) (r_2 x_2 g_2) ...) (in-hole Ev (in-hole Es ((r_1 t) σ))))
         (prog ((r_0 x_0 g_0) ... (r_1 x_1 g_1) (r_2 x_2 g_2) ...) (in-hole Ev (in-hole Es (delay ((substitute g_1 x_1 t) σ)))))
         "substitute through and add delay"]

         ;; How do I actually implement a unification here?
    [--> (in-hole EΓ (in-hole Ev (in-hole Es ((t_1 =? t_2) (state sub c)))))
         (in-hole EΓ (in-hole Ev (in-hole Es (state (⊤ (unify (walk t_1 sub) (walk t_2 sub) sub)) c))))
         (where ((x t) ...) (unify (walk t_1 sub) (walk t_2 sub) sub))
         "unify succeed"]

         ;; How do I actually implement a unification here?
    [--> (in-hole EΓ (in-hole Ev (in-hole Es ((t_1 =? t_2) (state sub c)))))
         (in-hole EΓ (in-hole Ev (in-hole Es (⊥ #f))))
         (where #f (unify (walk t_1 sub) (walk t_2 sub) sub))
         "unify fails"]

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

(define-metafunction L
  unify : t t sub -> ?sub
  [(unify x x sub) sub]
  [(unify x t sub) (ext x t sub)]
  [(unify t x sub) (ext x t sub)]
  [(unify (t_1a : t_1b) (t_2a : t_2b) sub)
   (unify t_1b t_2b sub_1)
   (where sub_1 (unify t_1a t_2a sub))]
  [(unify t t sub) sub]
  [(unify _ _ _) #f])

(define-metafunction L
  walk : t sub -> t
  [(walk x (name sub (_ ... [x t] _ ...))) (walk t sub)]
  [(walk t _) t])

(define-metafunction L
  ext : x t sub -> ?sub
  [(ext x t sub) ([x t] ,@(term sub))
   (side-condition (not (term (occurs? x t sub))))]
  [(ext _ _ _) #f])

(define-relation L
  occurs? ⊆ x × t × sub
  [(occurs? x (t : _) sub) (occurs? x t sub)]
  [(occurs? x (_ : t) sub) (occurs? x t sub)]
  [(occurs? x x sub)])

(redex-match? L sub (term ()))

;; (redex-match? L g (term (∃ x (x =? 7))))
;; (redex-match? L σ (term (state () 0)))
;; (redex-match? L s (term ((∃ x (x =? 7)) (state () 0))))
;; (redex-match? L e (term ((∃ x (x =? 7)) (state () 0))))

(test-->>
 red
 (term (prog () ((7 =? 7) (state () 0))))
 (term (prog () (⊤ (state () 0)))))

;; (test-->>
;;  red
;;  (term (prog () ((∃ x ⊤) (state () 0))))
;;  (term (prog () (⊤ (state () 0)))))

(redex-match L
  (prog ((r_0 x_0 g_0) ... (r_1 x_1 g_1) (r_2 x_2 g_2) ...) (in-hole Ev (in-hole Es ((r_1 t) σ))))
  (term (prog ((foo x (7 =? 7))) ((foo 7) (state () 0)))))

(apply-reduction-relation* red (term (prog ((foo x (7 =? 7))) ((foo 7) (state () 0)))))

(module+ test
  (test-true "Small relation lookup matches reduction pattern"
   (redex-match? L
     (prog ((r_0 x_0 g_0) ... (r_1 x_1 g_1) (r_2 x_2 g_2) ...) (in-hole Ev (in-hole Es ((r_1 t) σ))))
     (term (prog ((foo x (7 =? 7))) ((foo 7) (state () 0)))))))

(test-->> 
 red
 #:equiv (curry alpha-equivalent? L)
 (term (prog ((foo x (7 =? 7))) ((foo 7) (state () 0))))
 (term (prog ((foo x (7 =? 7))) (⊤ (state () 0)))))

(traces
 red
 (term (prog ((foo x (7 =? 7))) ((foo 7) (state () 0)))))

(traces
 red
 (term (prog () ((∃ x (7 =? 7)) (state () 0)))))

(test-->>
 red
 #:equiv (curry alpha-equivalent? L)
 (term (prog () ((7 =? 7) (state ((x 2)) 0))))
 (term (prog () (⊤ (state ((x 2)) 0)))))

(test-->>
 red
 #:equiv (curry alpha-equivalent? L)
 (term (prog () ((⊤ (state ((x 3)) 0))
         +
         ((⊤ (state ((x 3)) 0))
          +
          ((⊤ (state ((x 3)) 0))
           +
           (((9 =? 9) (state ((x 3)) 0))
            +
            ((17 =? 17) (state ((x 3)) 0))))))))

 (term (prog () ((⊤ (state ((x 3)) 0))
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
  (prog () ((delay ((7 =? 7) (state ((x 3)) 0))) + (delay ((8 =? 8) (state ((x 4)) 0))))))
 (term (prog () ((⊤ (state ((x 3)) 0)) + (⊤ (state ((x 4)) 0))))))

(test-->>
 red
 (term (prog () ((6 =? 7) (state ((x 3)) 0))))
 (term (prog () ())))

(test-->>
 red
 (term (prog () ((⊥ (state () 0)) + (⊤ (state ((x 3)) 0)))))
 (term (prog () (⊤ (state ((x 3)) 0)))))

(test-->>
 red
 (term (prog () ((⊤ (state ((x 3)) 0)) + (⊥ (state ((x 4)) 0)))))
 (term (prog () ((⊤ (state ((x 3)) 0)) + ()))))

(test-->>
 red
 (term (prog () (((delay ((7 =? 7) (state ((x 3)) 0)))
          + (delay ((8 =? 8) (state ((x 4)) 0))))
         + ((9 =? 9) (state ((x 9)) 0)))))
 (term (prog () ((⊤ (state ((x 9)) 0))
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
 (term (prog () (((6 =? 7) ∨ (7 =? 7)) (state ((x 3)) 0))))
 (term (prog () (⊤ (state ((x 3)) 0)))))

(test-->>
 red
 (term (prog () (((7 =? 7) ∨ (6 =? 7)) (state ((x 3)) 0))))
 (term (prog () ((⊤ (state ((x 3)) 0)) + ()))))

(test-->>
 red
 (term (prog () (((((⊤
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
  (prog () ((⊤ (state ((x 3)) 0))
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
 
