#lang racket
(require redex)

; Top level          :[Stream -> List]
; append(map) nodes  : (append | append-map | delay | goal/subst) -> Stream

; Stream of X
; - (cons∞ X [Stream of X])
; - () -> [Stream of X]
; - ()

(define-language L
  [e ::=      ; Expression
     (g σ)   ; turns into...
     a∞]     ; and this is the final "result"
  [a∞ ::=
      ()
      (cons∞ σ a∞)
      (delay e)
      s] ; technically an "s" is a stream of subst., just not fully computed yet
  [s ::= ; Search Tree Node
     (append e e) ; combine results of both subnodes
     (append-map g e) ; combine results of applying g to all nodes in s
     ]
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

  [E ::=
      hole
      (append E e)
      (append a∞ E)
      (append-map g E)
      (cons∞ σ E)
      ]
  )



(define red
  (reduction-relation
   L
   #:domain e

   #;[--> (in-hole E ((t =? t) σ))
        (in-hole E (cons∞ σ ()))
        "unify succeed"]

   #;[--> (in-hole E ((t_1 =? t_2) σ))
        (in-hole E ())
        (side-condition (not (equal? (term t_1) (term t_2))))
        "unify fail"]
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
   ))


;Metafunctions
;--------------------------------------

(define var? symbol?)

(define (walk v s)
  (local [(define a (and (var? v) (assv v s)))]
    (cond
      [(pair? a)(walk (cdr a) s)]
      [else v])))

(define (occurs? x v s)
  (let [(v (walk v s))]
    (cond
      [(var? v) (eqv? v x)]
      [(pair? v)
       (or (occurs? x (car v) s)
           (occurs? x (cdr v) s))]
      [else #f])))

(define (ext-s x v s)
  (cond
    [(occurs? x v s) #f]
    [else (cons `(,x . ,v) s)]))

(define (unify u v s)
  (let [(u (walk u s)) (v (walk v s))]
    (cond
      [(eqv? u v) s]
      [(var? u) (ext-s u v s)]
      [(var? v) (ext-s v u s)]
      [(and (pair? u) (pair? v))
       (let [(s (unify (car u) (car v) s))]
         (and s
              (unify (cdr u) (cdr v) s)))]
      [else #f])))

(define-metafunction L
  unify-terms : t t σ -> a∞
  [(unify-terms t_1 t_2 σ)
   ,(let [(s (unify (term t_1) (term t_2) (term σ)))]
      (if s (term (cons∞ ,s ())) (term ())))])

; --------------------------------------------



(traces red (term (((2 =? 2) ∧ (1 =? 1)) ())))

;(traces red (term (((1 2 3) =? (1 2 3)) ())))



(test-results)