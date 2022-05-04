#lang racket
(require redex/gui)
(require redex/reduction-semantics)

(define-language L [g ⊤ p (◇ g)])

(define red
  (reduction-relation L
    #:domain g
    [--> (◇ g) g "Manifest"]
    [--> p ⊤ "triviality"]))

(pretty-print "we successively use this reduction relation, each time
producing the one and only value.")
(first
 (apply-reduction-relation
  red
  (first
   (apply-reduction-relation
    red
    (first
     (apply-reduction-relation
      red
      (first
       (apply-reduction-relation
        red
        (term (◇ (◇ (◇ p))))))))))))

(pretty-print "Below is the term we expect to produce.")
(term ⊤)

(pretty-print "Here is the failing test where we claim we produce it.")
(test--> 
 red
 (term (◇ p))
 (term ⊤))

(pretty-print "However, traces says we should succeed. Watch.")
(traces
 red
 (term (◇ p)))

(pretty-print "Curiously, though, the first goes to the second, and
the second goes to the third.")
(test--> 
 red
 (term (◇ p))
 (term p))

(test--> 
 red
 (term p)
 (term ⊤))

(pretty-print "This seems to go wrong at the existential reduction---a
consequence of \"fresh subst\" or how and where we apply it. If we add
extra layers, it always fails, returning instead the result of the
first reduction.")
(test-->
 red
 (term (◇ (◇ (◇ p))))
 (term ⊤))

(traces
 red
 (term (◇ (◇ (◇ p)))))

(pretty-print "Deceptively, it *looks* like we get an extra set of
parens, and like that would explain the failure. But I don't think
that's the real problem.")
(apply-reduction-relation*
 red
 (term (◇ p)))

(pretty-print "I think somehow that we're getting those extra parens
because it's giving back a list of answers, maybe")

