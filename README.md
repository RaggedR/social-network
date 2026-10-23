# social-network

[![Lean CI](https://github.com/RaggedR/social-network/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/RaggedR/social-network/actions/workflows/lean_action_ci.yml)

A social network modelled as a **directed-container comonad** — the same categorical
structure (`Ext`, `extend`, `counit`) that underlies the rest of the container-theory
work, instantiated on a social graph.

- **`lean/`** — a self-contained Lean 4 formalization (no Mathlib): the container
  extension is a functor, container morphisms correspond exactly to natural
  transformations, the directed container is a comonad, and the concrete social-graph
  instance (`socialDCont`) satisfies the comonad laws. **CI-certified** — the badge is
  green only when `#print axioms` confirms the headline theorems (`Ext.map_id/comp`,
  `ExtNatTrans.toMorphism_toExtNatTrans`, `DirectedContainer.extend_extend`,
  `SocialNetwork.coassoc`, `SocialNetwork.extend_extend`) reach no `sorry`. They
  reduce to only `Quot.sound`.
- **`src/`, `app/`** — Haskell implementation.
- **`social-network-ghani.pdf`** — accompanying write-up (with Neil Ghani).

See also the broader container-theory program (`macbeth-seed`) and the Lean index in
`start-here`.
