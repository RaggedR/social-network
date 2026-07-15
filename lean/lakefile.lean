import Lake
open Lake DSL

package «social-network» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «Containers» where
  roots := #[`Containers.Basic, `Containers.Directed, `Containers.CoKleisli]

@[default_target]
lean_lib «SocialNetwork» where
  roots := #[`SocialNetwork.Graph]
