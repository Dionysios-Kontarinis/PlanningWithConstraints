(define (problem cakeworld2_pb1)
   (:domain cakeworld2)
   (:requirements :strips :negative-preconditions)
   (:objects only_cake)
   (:init (donthave_c only_cake) (donthave_e only_cake) )
   (:goal  (not(donthave_e only_cake))   )
)