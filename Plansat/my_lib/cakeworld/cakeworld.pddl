(define (domain cakeworld)
(:requirements :strips :negative-preconditions)
(:predicates (have_c ?x)
             (have_e ?x) )

(:action eat_c
  :parameters (?ob)
  :precondition (have_c ?ob)
  :effect (and (have_e ?ob) (not(have_c ?ob)))
)
(:action bake_c
  :parameters  (?ob)
  :precondition (not(have_c ?ob))
  :effect (have_c ?ob)
)
)
                      
