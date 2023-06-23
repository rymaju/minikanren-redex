#lang racket
(require redex)

; Top level          :[Stream -> List]
; append(map) nodes  : (append | append-map | delay | goal/subst) -> Stream

; Stream of X
; - (cons∞ X [Stream of X])
; - () -> [Stream of X]
; - ()

(define-language L
  [p :== {Γ e}]
  [Γ :== ((r (x ...) g) ...)]
  
  [e ::=     ; Expression
     a∞]     ; and this is the final "result"
  [a∞ ::=
      ()
      (cons∞ σ a∞)
      (delay e)
      s] ; technically an "s" is a stream of σ., just not fully computed yet
  [s ::= ; Search Tree Node
     (append e e) ; combine results of both subnodes
     (append-map g e) ; combine results of applying g to all nodes in s
     (g σ)
     ]
  [g ::= ; Goals
     (t =? t) ; unify
     (g ∨ g)  ; disjunction
     (g ∧ g)  ; conjunction
     (r t ...) ; relation call
     (∃ x g) ; fresh logic var introduction
     ;(conde (g ...) ...)
     ]
  [σ :== (subst natural)] ; pair of substitutions and logic variable counter
  [subst ::= ; Substitution
     ((φ t) ...)]
  [t :==
     c
     (cons t t)
     '()]
  [ls :== (t ...)] ;; only used for metafunction, use cons for making lists
  [c :==
     number
     boolean
     string
     x
     φ]
  [r ::= variable-not-otherwise-mentioned] ; relation name
  [x ::= variable-not-otherwise-mentioned] ; variable name
  [φ ::= (var natural)]                    ; logic variable

  [E ::=
      hole
      (in-hole (Γ hole) E)
      (append E e)
      (append-map g E) ;these two are possibly redunant
      (cons∞ σ E)
      ]
  [Etop ::=
      (in-hole (Γ hole) Etop)
      (cons∞ σ Etop)
      hole]
  )



(define red
  (reduction-relation
   L
   #:domain p
   
   [--> (in-hole E ((t_1 =? t_2) σ))
        (in-hole E (unify-terms t_1 t_2 σ))
        "unify terms"]
  
   [--> (in-hole E ((g_1 ∨ g_2) σ))
        (in-hole E (append (g_1 σ)
                            (g_2 σ)))
        "or"]
   
   [--> (in-hole E ((g_1 ∧ g_2) σ))
        (in-hole E (append-map g_2
                                (g_1 σ)))
        "and"]
   ; append
   [--> (in-hole E (append () a∞))
        (in-hole E a∞)
        "append | null case"]
   [--> (in-hole E (append (cons∞ σ a∞_1) a∞_2))
        (in-hole E (cons∞ σ
                          (append a∞_1 a∞_2)))
        "append | pair case"]
   [--> (in-hole E (append (delay e) a∞))
        (in-hole E (delay (append a∞ e)))
        "append | delay case"]
 
   ; append-map
   [--> (in-hole E (append-map g ()))
        (in-hole E ())
        "append-map | null case"]
   
   [--> (in-hole E (append-map g (cons∞ σ a∞)))
        (in-hole E (append (g σ)
                            (append-map g a∞)))
        "append-map | pair case"]

   [--> (in-hole E (append-map g (delay e)))
        (in-hole E (delay (append-map g e)))
        "append-map | delay case"]

   [--> (in-hole Etop (delay e))
        (in-hole Etop e)
        "force suspension"]

   [--> (Γ (in-hole E ((r t ...) σ)))
        (Γ (in-hole E (delay ((call/relation Γ r (t ...)) σ))))
        "relation call"]

  
   [--> (in-hole E ((∃ x g) σ))
        (in-hole E (delay (call/fresh g σ x)))
        "fresh"]
   ))


;Metafunctions
;--------------------------------------

(define var? (redex-match? L φ))
;(define pair? (redex-match? L (cons t t)))
(define cons? (redex-match? L (cons _ _)))

(define (mk-eqv? a b) (or (eqv? a b)
                          (and (equal? a ''()) (equal? b ''()))

                          (and (var? a) (var? b) (= (second a) (second b)))))

(define (walk v s)
  (let [(a (and (var? v) (assoc v s)))]
    (cond
      [(pair? a) (walk (second a) s)]
      [else v])))

(define (occurs? x v s)
  (let [(v (walk v s))]
    (cond
      [(var? v) (mk-eqv? v x)]
      [(cons? v)
       (or (occurs? x (second v) s)
           (occurs? x (third v) s))]
      [else #f])))

  
(define (ext-s x v s)
  (cond
    [(occurs? x v s) #f]
    [else (term ,(cons (list x v) s))]))

(define (unify u v s)
  (let [(u (walk u s)) (v (walk v s))]
    
    (cond
      [(mk-eqv? u v) s]
      [(var? u) (ext-s u v s)]
      [(var? v) (ext-s v u s)]
      [(and (cons? u) (cons? v))
       (let [(s (unify (second u) (second v) s))]
         (and s
              (unify (third u) (third v) s)))]
      [else #f])))

#;(unify '(cons (var 2) (var 4)) '(cons "a" '())
        '())
;'(((var 4) '()) ((var 2) "a"))


(define-metafunction L
  unify-terms : t t σ -> a∞
  [(unify-terms t_1 t_2 σ)
   ,(let [(s (unify (term t_1) (term t_2) (first (term σ))))]
      (if s
          (term (cons∞ (,s ,(second (term σ))) ()))
          (term ())))])




;, call was (unify-terms (cons (var 1) (var 2)) (cons 1 (cons 2 (quote ()))) (() 4))
(define (naive-subst body bindings)
  (match body
    [`(,a . ,d) `(,(naive-subst a bindings) . ,(naive-subst d bindings))]
    [else (let ([val (assv body bindings)])
            (if val (cdr val) body))]))

; (naive-subst '(a (b (c a d))) '((a . 1) (b . 2) (c . 3)))
; -> (1 (2 (3 1 d)))

(define-metafunction L
  call/relation : Γ r (t ...) -> any
  [(call/relation Γ r ls)
   ,(let* [(matching-relation (assv (term r) (term Γ)))
           (body (if matching-relation
                     (third matching-relation)
                     (error "Unbound reference to relation" (term r))))
           (params (second matching-relation))
           (subst-body (naive-subst body
                                    (map cons params (term ls))))]
      subst-body)])

(define-metafunction L
  call/fresh : g σ x -> (g σ)
  [(call/fresh g σ x)
   ,(let* [(substitution (first (term σ)))
           (logic-var-num (second (term σ)))
           (logic-var (term (var ,logic-var-num)))
           (subst-g (naive-subst (term g)
                                 (list (cons (term x) logic-var))))]
      (term (,subst-g (,substitution ,(add1 logic-var-num)))))])

; --------------------------------------------



; Test append/append-map
#;(traces red (term (() (((2 =? 2) ∧ (1 =? 1)) (() 0)))))

; Test unification
; (traces red (term (() (((cons (var 0) (cons (var 1) '())) =? (cons 1 (cons 2 '()))) (() 0)))))

; Test that delay works (minimal)
;(traces red (term (() (append (delay ((1 =? 1) ())) ((1 =? 1) ())))))

; Test that delay works in top level list of answers
#;(traces red (term (() (append
                       (append ((1 =? 1) (() 0)) (delay ((1 =? 1) (() 0))))
                       ((1 =? 1) (() 0))))))

; test relation calls (simple)
#;(traces red (term (((nullo (ls) (ls =? ())))
                     ((nullo ()) ()))))
; test relation calls (nested)
#;(traces red (term (((nullo (ls) (ls =? '())))
                   (((nullo 1) ∨ (nullo '())) (() 0)))))
#;(traces red (term (((conso (a d ls) (ls =? `(\,a \,d))))
                   ((conso 1 '(2) x) ()))))

#;(traces red (term (()
                   ((∃ y (y =? 1)) (() 0)))))
(define Γ/appendo
  '(
    (appendo (l t out)
             (
              ((l =? '()) ∧ (t =? out))
              ∨
              (∃ a (∃ d (∃ res
                           (((cons a d) =? l)
                            ∧
                            (((cons a res) =? out)
                             ∧
                             (appendo d t res)
                             ))
                           )))
              ))
    ))
;(redex-match L Γ Γ/appendo)
(traces red
          (term (,Γ/appendo
                 ((appendo (var 0)
                           (var 1)   
                           (cons 1 2))

                  (() 2))))
          )
#;(traces red
          (term (,Γ/appendo
                 ((appendo '()
                           (cons 3 '())
                           (var 0))

                  (() 1))))

          
          )

(apply-reduction-relation* red
                           (term (()
                                  ((((var 0) =? 1) ∨ ((var 0) =? 2))

                                   (() 1)))))
(apply-reduction-relation* red
                           (term (()
                                  ((((var 0) =? 1) ∨ ((var 0) =? (cons 1 2)))

                                   (() 1)))))

(test-->>E red
           (term (,Γ/appendo
                  ((appendo '()
                            (var 0)
                            (cons "a" '()))

                   (() 1))))
           (term (,Γ/appendo
                  (cons∞ ((((var 0) (cons "a" '()))) 1) ()))))
(test-->> red
          (term (,Γ/appendo
                 ((appendo (var 0)
                           '()
                           (cons "a" '()))

                  (() 1))))
          (term (,Γ/appendo
                 (cons∞ ; really the same as above, reification would normalize the result
                  ((((var 2) '())
                    ((var 3) '())
                    ((var 1) "a")
                    ((var 0) (cons (var 1) (var 2))))
                   4)
                  ()))))


(apply-reduction-relation* red
                           (term (,Γ/appendo
                                  ((appendo (var 0)
                                            (var 1)
                                            (cons 1 (cons 2 (cons 3 '()))))
                                   (() 2)))))
 
(test-->> red
          (term (() (('() =? '()) (() 0))))
          (term (() (cons∞ (() 0) ()))))

#;(append-map
   (appendo
    (var 3)
    (var 1)
    (var 4))
   (((cons (var 2) (var 4))
     =?
     (cons "a" '()))
    ((((var 0)
       (cons
        (var 2)
        (var 3))))
     5)))
(test-results)

