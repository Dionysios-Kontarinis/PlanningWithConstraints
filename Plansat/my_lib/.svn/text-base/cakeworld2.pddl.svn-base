(define (domain cakeworld2)
(:requirements :strips :negative-preconditions)
(:predicates (donthave_c ?x)
             (donthave_e ?x) )

(:action eat_c
  :parameters (?ob)
  :precondition (not(donthave_c ?ob))
  :effect (and (not(donthave_e ?ob)) (donthave_c ?ob) )
)
(:action bake_c
  :parameters  (?ob)
  :precondition (donthave_c ?ob)
  :effect (not(donthave_c ?ob))
)
)