#lang racket
(require redex redex/gui)
(require redex/reduction-semantics)
(require rackunit)
(check-redundancy #t)
(current-traced-metafunctions 'all)

;; Consider, if we separate answer streams from search tree
;; disjuncts, then we would need some rule to "move into the
;; answer stream."

;; I could also think about this as though the query is instead the
;; one and only call to an initial, implicitly define defrel called
;; "main".

(define-language L
  [p ::= (prog Γ e)] ; Programs, Relation Environments, and Relations
  [Γ ((r_!_ x g) ...)] ; Ensure that 'ri's are distinct
  ;------------------------------------
  ; Expressions
  [e ::=
     ()
     s
     ((⊤ σ) ∨ e)]

  ; Search Trees
  [s ()
     (⊥ #f)
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
     o ;; for "other", change to make c constant and n natural 
     x
     (t : t)]

  ;Other
  [r (variable-prefix r:)] ; to account for arbitrary relation names
  [x (variable-prefix x:)] ; to account for arbitrary parameter names
  [c natural]
  [o symbol ; Why isn't this working
     boolean
     string]
  [σ (state sub c)] ;; Not modeling fresh variable introduction
  [sub ((natural t) ...)]
  [maybe-sub sub #f]
  
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

(default-language L)

(module+ test

;; FAILS
;; "bald symbols are terms"
;; (redex-match? L t (term cat))

"bald numbers are terms"
(redex-match? L t (term 5))

"booleans are terms"
(redex-match? L t (term #t))

"strings are terms"
(redex-match? L t (term "cat"))

"a fresh call over an equation is a goal"
(redex-match? L g (term (∃ x:x (x:x =? "seven"))))

(redex-match? L sub (term ()))

(redex-match? L σ (term (state () 0)))

"A goal w/a state is a search tree"
(redex-match? L s (term ((∃ x:x (x:x =? "seven")) (state () 0))))

"A goal w/a state is a query expression"
(redex-match? L e (term ((∃ x:x (x:x =? "seven")) (state () 0))))

(redex-match? L
 p
 (term 
  (prog ((r:add x:x (x:x =? "cat"))) ())))

"matching a small unify program with symbol constants"
(redex-match? L p (term (prog () (("cat" =? "cat") (state () 0)))))

"matching a small unify program with symbol constants and non-empty subst"
(redex-match? L 
 p              
 (term (prog () (("seven" =? "seven") (state ((2 "fish")) 0)))))

"matching a program w a relation"
(redex-match?
 L
 p
 (term 
  (prog ((add x:x (x:x =? "cat"))) (⊤ (state () 0)))))

"matching a full program with a relation call"
(redex-match?
 L
 p
 (term 
  (prog ((r:add x:x (x:x =? "cat"))) ((r:add "dog") (state () 0)))))

"Small relation lookup matches reduction pattern"
(redex-match? L 
 (prog ((r_0 x_0 g_0) ... (r_1 x_1 g_1) (r_2 x_2 g_2) ...) (in-hole Ev (in-hole Es ((r_1 t) σ))))
 (term (prog ((r:foo x:x ("seven" =? "seven"))) ((r:foo "seven") (state () 0)))))

)

(define-metafunction L
  unify : t t sub -> maybe-sub
  [(unify natural_1 natural_1 sub) sub]
  [(unify natural t sub) (ext natural t sub)]
  [(unify t natural sub) (ext natural t sub)]
  [(unify (t_1a : t_1b) (t_2a : t_2b) sub)
   (unify t_1b t_2b sub_1)
   (where sub_1 (unify t_1a t_2a sub))]
  [(unify t_1 t_1 sub) sub]
  [(unify _ _ _) #f])

(define-metafunction L
  walk : t sub -> t
  [(walk natural (name sub (_ ... [natural t] _ ...))) (walk t sub)]
  [(walk t _) t])

(define-metafunction L
  ext : natural t sub -> maybe-sub
  [(ext natural t sub) ([natural t] ,@(term sub))
   (side-condition (not (term (occurs? natural t sub))))]
  [(ext _ _ _) #f])

(define-relation L
  occurs? ⊆ natural × t × sub
  [(occurs? natural (t : _) sub) (occurs? natural t sub)]
  [(occurs? natural (_ : t) sub) (occurs? natural t sub)]
  [(occurs? natural_1 natural_1 sub)])


(module+ test
  
(test-equal
 (term (unify 0 0 ()))
 (term ()))

(test-equal
 (term (unify 0 "cat" ()))
 (term ((0 "cat"))))

(test-equal
 (term (unify "cat" 0 ()))
 (term ((0 "cat"))))

(test-equal
 (term (walk 0 ((1 "cat") (0 "dog"))))
 (term "dog"))

(test-equal
 (term (walk 0 ((1 "cat") (0 1))))
 (term "cat"))

)

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
         "relcall and add delay"]

    [--> (in-hole EΓ (in-hole Ev (in-hole Es ((t_1 =? t_2) (state sub c)))))
         (in-hole EΓ (in-hole Ev (in-hole Es (⊤ (state (unify (walk t_1 sub) (walk t_2 sub) sub) c)))))
         (where ((x t) ...) (unify (walk t_1 sub) (walk t_2 sub) sub))
         "unify succeed"]

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
    ;; [--> (in-hole EΓ (in-hole Ev ((⊤ σ) + (⊥ #f))))
    ;;      (in-hole EΓ (in-hole Ev (⊤ σ)))
    ;;      "prune failure from end"]

    [--> (in-hole EΓ (in-hole Ev (⊥ #f)))
         (in-hole EΓ (in-hole Ev ()))
         "prune bald failure"]))


(test-->>
 red
 (term (prog () (("seven" =? "seven") (state () 0))))
 (term (prog () (⊤ (state () 0)))))

(test-->>
 red
 (term (prog () ((∃ x:x ⊤) (state () 0))))
 (term (prog () (⊤ (state () 1)))))

(apply-reduction-relation* red (term (prog ((r:foo x:x ("seven" =? "seven"))) ((r:foo "seven") (state () 0)))))

(test-->> 
 red
 #:equiv alpha-equivalent?
 (term (prog ((r:foo x:x ("seven" =? "seven"))) ((r:foo "seven") (state () 0))))
 (term (prog ((r:foo x:x ("seven" =? "seven"))) (⊤ (state () 0)))))

;; (traces
;;  red
;;  (term (prog ((r:foo x:x ("seven" =? "seven"))) ((r:foo "seven") (state () 0)))))

;; This is a state mid-run 
;; (traces
;;  red
;;  (term (prog () ((∃ x:x ("seven" =? "seven")) (⊤ (state () 0)))))

;; This is a state mid-run 
;; (traces
;;  red
;;  (term (prog () ((∃ x:x ("seven" =? "seven")) (⊤ (state () 0))))))


(test-->>
 red
 #:equiv alpha-equivalent?
 (term (prog () (("seven" =? "seven") (state ((2 "fish")) 0))))
 (term (prog () (⊤ (state ((2 "fish")) 0)))))

  ;; Tests substitution doesn't subst constants 


(test-->>
 red
 #:equiv alpha-equivalent?
 (term 
  (prog ((r:add x:x (x:x =? "cat"))) ((r:add "dog") (state () 0))))
 (term 
  (prog ((r:add x:x (x:x =? "cat"))) ())))

(module+ test
  (test-->>
   red
   #:equiv alpha-equivalent?
   (term (prog () ((⊤ (state ((3 "fish")) 0))
                   +
                   ((⊤ (state ((3 "fish")) 0))
                    +
                    ((⊤ (state ((3 "fish")) 0))
                     +
                     ((("nine" =? "nine") (state ((3 "fish")) 0))
                      +
                      (("seventeen" =? "seventeen") (state ((3 "fish")) 0))))))))

   (term (prog () ((⊤ (state ((3 "fish")) 0))
                   +
                   ((⊤ (state ((3 "fish")) 0))
                    +
                    ((⊤ (state ((3 "fish")) 0))
                     +
                     ((⊤ (state ((3 "fish")) 0))
                      +
                      (⊤ (state ((3 "fish")) 0)))))))))

  (test-->>
   red
   (term
    (prog () ((delay (("seven" =? "seven") (state ((3 "fish")) 0))) + (delay (("eight" =? "eight") (state ((4 "fish")) 0))))))
   (term (prog () ((⊤ (state ((3 "fish")) 0)) + (⊤ (state ((4 "fish")) 0))))))

  (test-->>
   red
   (term (prog () (("six" =? "seven") (state ((3 "fish")) 0))))
   (term (prog () ())))

  (test-->>
   red
   (term (prog () ((⊥ #f) + (⊤ (state ((3 "fish")) 0)))))
   (term (prog () (⊤ (state ((3 "fish")) 0)))))

  (test-->>
   red
   (term (prog () ((⊤ (state ((3 "fish")) 0)) + (⊥ #f))))
   (term (prog () ((⊤ (state ((3 "fish")) 0)) + ()))))

  (test-->>
   red
   (term (prog () ((⊤ (state ((3 "fish")) 0)) + (⊥ #f))))
   (term (prog () ((⊤ (state ((3 "fish")) 0)) + ()))))


  (test-->>
   red
   (term (prog () (((delay (("seven" =? "seven") (state ((3 "fish")) 0)))
                    + (delay (("eight" =? "eight") (state ((4 "fish")) 0))))
                   + (("nine" =? "nine") (state ((9 "fish")) 0)))))
   (term (prog () ((⊤ (state ((9 "fish")) 0))
                   + ((⊤ (state ((3 "fish")) 0))
                      + (⊤ (state ((4 "fish")) 0)))))))


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
   (term (prog () ((("six" =? "seven") ∨ ("seven" =? "seven")) (state ((3 "fish")) 0))))
   (term (prog () (⊤ (state ((3 "fish")) 0)))))

  ;; (test-->>
  ;;  red
  ;;  (term (prog () ((("seven" =? "seven") ∨ ("six" =? "seven")) (state ((3 "fish")) 0))))
  ;;  (term (prog () ((⊤ (state ((3 "fish")) 0))))))

  (test-->>
   red
   (term (prog () (((((⊤
                       ∧ ("seven" =? "seven"))
                      ∨ (("eight" =? "eight")
                         ∧ ("nine" =? "nine")))
                     ∧ ((⊤
                         ∧ ("seven" =? "seven"))
                        ∨ (("eight" =? "eight")
                           ∧ ("nine" =? "nine"))))
                    ∨ (((⊤
                         ∧ ("seven" =? "seven"))
                        ∨ (("eight" =? "eight")
                           ∧ ("nine" =? "nine")))
                       ∧ ((⊤
                           ∧ ("seven" =? "seven"))
                          ∨ (("eight" =? "eight")
                             ∧ ("nine" =? "nine")))))
                   (state ((3 "fish")) 0))))
   (term 
    (prog () ((⊤ (state ((3 "fish")) 0))
              +
              ((⊤ (state ((3 "fish")) 0))
               +
               ((⊤ (state ((3 "fish")) 0))
                +
                ((⊤ (state ((3 "fish")) 0))
                 +
                 ((⊤ (state ((3 "fish")) 0))
                  +
                  ((⊤ (state ((3 "fish")) 0))
                   +
                   ((⊤ (state ((3 "fish")) 0))
                    +
                    (⊤
                     (state
                      ((3 "fish"))
                      0))))))))))))


  (test-->>
   red
   #:equiv alpha-equivalent?
   (term 
    (prog ((add x (∃ a
                     (∃ d
                        ((x =? (a : d))
                         ∧ (((a =? z)
                             ∧ (d =? (s : z)))
                            ∨ (∃ a2
                                 (∃ d2
                                    (((a : d) =? ((s : a2) : (s : d2)))
                                     ∧ (add (a2 : d2)))))))))))
          ((∃ y (y =? y))
           (state () 0))))
   (term (prog ((add x (∃ a
                          (∃ d
                             ((x =? (a : d))
                              ∧ (((a =? z)
                                  ∧ (d =? (s : z)))
                                 ∨ (∃ a2
                                      (∃ d2
                                         (((a : d) =? ((s : a2) : (s : d2)))
                                          ∧ (add (a2 : d2)))))))))))
               (state () 0))))


  (test-->>
   red
   #:equiv alpha-equivalent?
   (term 
    (prog ((add x (∃ a (a =? x))))
          ((∃ y (add ((s : z) : y)))
           (state () 0))))
   (term (prog ((add x (∃ a (a =? x))))
               (state () 0))))

  ;; Questionable test right now 
  (test-->>
   red
   #:equiv alpha-equivalent?
   (term 
    (prog 
     ((add x (∃ a
                (∃ d
                   (x =? (a : d))))))
     ((∃ y (add ((s : (s : (s : z))) : y)))
      (state () 0))))
   (term (prog
          ((add x (∃ a (∃ d (x =? (a : d))))))
          (state ((d y) (a (s : (s : (s : z))))) 3))))

  (redex-match? L p
                (term (prog ((add x (∃ a
                                       (∃ d
                                          ((x =? (a : d))
                                           ∧ (((a =? z)
                                               ∧ (d =? (s : z)))
                                              ∨ (∃ a2
                                                   (∃ d2
                                                      (((a : d) =? ((s : a2) : (s : d2)))
                                                       ∧ (add (a2 : d2)))))))))))
                            ((∃ y (add ((s : (s : (s : z))) : y))) (state () 0)))))

  (test-->>
   red
   (term
    (prog
     ((add x
           (∃ a
              (∃ d ((x =? (a : d))
                    ∧
                    (((a =? z)
                      ∧ (d =? (s : z)))
                     ∨ (∃ a2
                          (∃ d2
                             (((a : d) =? ((s : a2) : (s : d2)))
                              ∧ (add (a2 : d2)))))))))))
     ((∃ y (add ((s : (s : (s : z))) : y))) (state () 0))))
   (term (prog () ())))

  ;; (traces red (term (((((⊤
  ;;                        ∧ ("seven" =? "seven"))
  ;;                       ∨ (("eight" =? "eight")
  ;;                          ∧ ("nine" =? "nine")))
  ;;                      ∧ ((⊥
  ;;                          ∨ ("seven" =? "seven"))
  ;;                         ∨ (("eight" =? "eight")
  ;;                            ∧ ("nine" =? "nine"))))
  ;;                     ∨ (((⊥
  ;;                          ∨ ("seven" =? "seven"))
  ;;                         ∨ (("eight" =? "eight")
  ;;                            ∧ ("nine" =? "nine")))
  ;;                        ∧ ((⊤
  ;;                            ∧ ("seven" =? "seven"))
  ;;                           ∨ (("eight" =? "eight")
  ;;                              ∧ ("nine" =? "nine")))))
  ;;                    (state ((x 3)) 0))))

  ;; (traces red (term
  ;;              ((((⊤ (state ((x 3)) 0))
  ;;                 ∨
  ;;                 (("eight" =? "eight")
  ;;                  (state ((x 3)) 0)))
  ;;                ∧
  ;;                (("seven" =? "seven")
  ;;                 ∨
  ;;                 ("nine" =? "nine")))
  ;;               ∨
  ;;               (("seventeen" =? "seventeen")
  ;;                (state ((x 3)) 0)))))
  
  )


(test-results)
 
