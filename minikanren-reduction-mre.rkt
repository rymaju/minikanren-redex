#lang racket
(require redex/gui)
(require redex/reduction-semantics)

;; Here is a little language.

(define-language L [f ⊤ (◇ f)])

;; We have only one reduction rule, to removes the diamond modality

(define red
  (reduction-relation L
    #:domain f
    [--> (◇ f) f "Manifest"]))

;; Below is a term we expect to produce.

(term ⊤)

;; Here is the failing test where we claim we produce it.

(test--> 
 red
 (term (◇ (◇ ⊤)))
 (term ⊤))

;; However, traces says we should succeed. Watch.

(traces
 red
 (term (◇ (◇ ⊤))))

;; Curiously, though, the first goes to the second, and
;; the second goes to the third.

(test--> 
 red
 (term (◇ (◇ ⊤)))
 (term (◇ ⊤)))

(test--> 
 red
 (term (◇ ⊤))
 (term ⊤))

;; It seems to go wrong at the diamond modality reduction---a
;; consequence of "fresh subst" or how and where we apply it. If we
;; add extra layers, it always fails, returning instead the result of
;; the first reduction.

(test-->
 red
 (term (◇ (◇ (◇ ⊤))))
 (term ⊤))

;; Even though, again, traces works just fine. 

(traces
 red
 (term (◇ (◇ (◇ ⊤)))))

;; Deceptively, it *looks* like we get an extra set of parens, and
;; like that would explain the failure. But I don't think that's the
;; real problem. 

(apply-reduction-relation*
 red
 (term (◇ ⊤)))

;; I think somehow that we're getting those extra parens because it's
;; giving back a list of answers, maybe

(first
 (apply-reduction-relation
  red
  (first
   (apply-reduction-relation
    red
    (first
     (apply-reduction-relation
      red
      (term (◇ (◇ (◇ ⊤))))))))))

;; We successively use this reduction relation, each time
;; producing the one and only value.

;; Is this a Redex bug? It seems too superficial for me to be the
;; first one to notice it.


