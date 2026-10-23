import Containers.Basic
import Containers.Directed
import Containers.CoKleisli
import SocialNetwork.Graph

/-!
# Certification

`#print axioms` on the headline results. CI runs this file and fails if the output
mentions `sorryAx` (a `sorry` reached the result) or if any report is missing (a
name that failed to resolve — a vacuous "proof"). A clean report lists only Lean's
foundational axioms (`propext`, `Classical.choice`, `Quot.sound`), or none at all.

This development has **no Mathlib dependency** and is `sorry`-free: the container
extension is a functor, container morphisms correspond exactly to natural
transformations, the directed container is a comonad, and the concrete social-network
graph carries that comonad structure with its laws proved.
-/

-- Container extension is a functor
#print axioms Containers.Ext.map_id
#print axioms Containers.Ext.map_comp

-- Container morphisms ≃ natural transformations of extensions (representation iso)
#print axioms Containers.ExtNatTrans.toMorphism_toExtNatTrans

-- Directed container is a comonad (co-Kleisli associativity of extend)
#print axioms Containers.DirectedContainer.extend_extend

-- The social network graph itself satisfies the comonad laws
#print axioms SocialNetwork.coassoc
#print axioms SocialNetwork.extend_extend
