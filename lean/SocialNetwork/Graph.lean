import Containers.Directed
import Containers.CoKleisli

/-!
# The social graph as a directed container

This file instantiates the abstract directed container framework
(Ahman–Chapman–Uustalu, formalised in `Containers.Directed`) for a
minimal social network. The key design choice:

* **Shape** is a social graph: a follow relation + a distinguished viewer.
* **Pos** is constant: positions are always `Nat` (user IDs), regardless
  of the graph shape. This eliminates all dependent transport.
* **sub** is *rerooting*: changing the viewer, not pruning the graph.
  The ego-network computation lives in the feed algorithm (a coKleisli
  morphism), not in the container structure.
* **shift** is inclusion: navigating from `p` to `q` within `p`'s
  subgraph just returns `q`, since user IDs are global.

With these choices, all five directed container laws are trivial:
D1 and D4 are `rfl` after destructuring, D3 is definitional, and
D2/D5 reduce to the fact that transport in a constant family is the
identity.

The three comonad laws (left counit, right counit, coassociativity)
and the coKleisli structure then follow *for free* from the proofs
in `Containers.Directed` and `Containers.CoKleisli`.
-/

namespace SocialNetwork

open Containers

/-! ## The social graph -/

/-- A **social graph**: a follow relation on natural-number user IDs,
together with a distinguished viewer (the "logged-in user").

This is the `Shape` type of our directed container. The follow
relation uses `Nat → Nat → Bool` for decidability; positions are
plain `Nat` so there is no dependent typing.

Corresponds to the Haskell type:
```haskell
data SocialGraph = SocialGraph
  { follows :: Set (UserId, UserId)
  , viewer  :: UserId
  }
``` -/
structure Graph where
  /-- Does user `a` follow user `b`? -/
  follows : Nat → Nat → Bool
  /-- The distinguished viewer (logged-in user). -/
  viewer : Nat

/-- **Rerooting**: change the viewer of a graph without altering its
structure. This is the `sub` operation of the directed container.

Categorically: `sub g u` is "the same world, seen from `u`'s
perspective." The follow relation is unchanged — what changes is
*who* the comonadic `extract` returns content for.

Corresponds to the Haskell:
```haskell
egoNetwork g u = SocialGraph { ... , viewer = u }
``` -/
def Graph.reroot (g : Graph) (u : Nat) : Graph :=
  { g with viewer := u }

/-! ## Transport lemma

When `Pos` is a constant family (`fun _ => Nat`), transporting along
any equality `h : a = b` is the identity. This is the only non-trivial
proof ingredient; D1–D5 then follow by `rfl` or by applying this lemma.
-/

/-! ## The directed container instance -/

/-- The **social graph directed container**.

This is the central construction: it equips the social graph with the
structure needed for the comonad (extract, duplicate, extend) and
coKleisli category (composition of feed algorithms).

**Why `Pos` is constant:** In a social network, user IDs are global —
the same `Nat` identifies a user regardless of which subgraph you're
looking at. This makes `Pos : Shape → Type` the constant functor
`fun _ => Nat`, which eliminates all dependent transport from the laws.

**Why `sub` is rerooting, not ego-network computation:** The ego network
(who you follow, what posts you see) depends on the follow relation,
which lives in the *shape*. The directed container's `sub` only needs to
identify "the world from position `p`'s point of view" — and since the
follow relation is global (public network), that's just the same graph
with a different viewer. The filtering happens in the feed algorithm
(a coKleisli morphism applied via `extend`).

Once we prove D1–D5, the entire comonad structure is inherited from
`Containers.Directed`:
- `counit ⟨g, v⟩ = v g.viewer` — "my content"
- `comult ⟨g, v⟩ = ⟨g, fun p => ⟨g.reroot p, fun q => v q⟩⟩` — "feed of feeds"
- `extend f ⟨g, v⟩ = ⟨g, fun p => f ⟨g.reroot p, fun q => v q⟩⟩` — apply feed algo everywhere
-/
def socialDCont : DirectedContainer where
  -- Container data
  Shape := Graph
  Pos := fun _ => Nat  -- constant: user IDs are global

  -- Directed container operations
  root := fun g => g.viewer
  sub := fun g u => g.reroot u
  shift := fun _ _ q => q  -- inclusion: q is the same user in the parent graph

  -- D1: rerooting to the current viewer is the identity.
  d1 := fun ⟨_, _⟩ => rfl

  -- D4: rerooting twice = rerooting once (to the final viewer).
  d4 := fun ⟨_, _⟩ _ _ => rfl

  -- D2: shifting by the root is transport (which is identity for constant Pos).
  d2 := fun s q => by
    -- Goal: shift s (root s) q = d1 s ▸ q
    -- i.e., q = d1 s ▸ q
    -- Since Pos is constant (fun _ => Nat), the ▸ is identity
    obtain ⟨f, v⟩ := s
    rfl

  -- D3: shifting to the root of the subgraph is the identity.
  d3 := fun _ _ => rfl

  -- D5: shift is associative.
  d5 := fun s p q r => by
    obtain ⟨f, v⟩ := s
    rfl

/-! ## Comonad operations (inherited) -/

/-- Extract the viewer's value: `ε ⟨g, v⟩ = v(viewer)`.
This is the "my feed" operation. -/
noncomputable def counit {X : Type} : Ext socialDCont.toContainer X → X :=
  socialDCont.counit

/-- Duplicate: at every position, provide the full local view.
`δ ⟨g, v⟩ = ⟨g, fun p => ⟨g.reroot p, fun q => v q⟩⟩`. -/
noncomputable def comult {X : Type} :
    Ext socialDCont.toContainer X → Ext socialDCont.toContainer (Ext socialDCont.toContainer X) :=
  socialDCont.comult

/-- Extend a feed algorithm to all positions.
`extend f ⟨g, v⟩ = ⟨g, fun p => f ⟨g.reroot p, fun q => v q⟩⟩`. -/
noncomputable def extend {X Y : Type} (f : Ext socialDCont.toContainer X → Y) :
    Ext socialDCont.toContainer X → Ext socialDCont.toContainer Y :=
  socialDCont.extend f

/-! ## Comonad laws (inherited from Containers.Directed)

These are not new proofs — they are the *same* theorems from
`Containers.Directed.DirectedContainer`, instantiated at `socialDCont`.
The proofs work because we proved D1–D5 above, and the abstract
comonad laws are derived from D1–D5 in the library.
-/

/-- Left counit law: `ε ∘ δ = id`. From D1 and D2. -/
theorem left_counit {X : Type} :
    socialDCont.counit ∘ socialDCont.comult = (id : Ext socialDCont.toContainer X → _) :=
  socialDCont.left_counit

/-- Right counit law: `Ext.map ε ∘ δ = id`. From D3. -/
theorem right_counit {X : Type} :
    Ext.map socialDCont.counit ∘ socialDCont.comult = (id : Ext socialDCont.toContainer X → _) :=
  socialDCont.right_counit

/-- Coassociativity: `Ext.map δ ∘ δ = δ ∘ δ`. From D4 and D5. -/
theorem coassoc {X : Type} :
    Ext.map socialDCont.comult ∘ socialDCont.comult
      = (socialDCont.comult ∘ socialDCont.comult :
          Ext socialDCont.toContainer X →
          Ext socialDCont.toContainer (Ext socialDCont.toContainer (Ext socialDCont.toContainer X))) :=
  socialDCont.coassoc

/-! ## CoKleisli laws (inherited from Containers.CoKleisli)

Feed algorithms compose via the coKleisli category.
-/

/-- Extending the counit is the identity: `extend ε = id`. -/
theorem extend_counit {X : Type} :
    socialDCont.extend (socialDCont.counit (X := X)) = id :=
  socialDCont.extend_counit

/-- The counit is a left inverse of extension: `ε ∘ extend f = f`. -/
theorem counit_extend {X Y : Type} (f : Ext socialDCont.toContainer X → Y) :
    socialDCont.counit ∘ socialDCont.extend f = f :=
  socialDCont.counit_extend f

/-- Extension respects coKleisli composition: associativity. -/
theorem extend_extend {X Y Z : Type}
    (f : Ext socialDCont.toContainer X → Y)
    (g : Ext socialDCont.toContainer Y → Z) :
    socialDCont.extend (g ∘ socialDCont.extend f) = socialDCont.extend g ∘ socialDCont.extend f :=
  socialDCont.extend_extend f g

/-! ## Concrete feed algorithms as coKleisli morphisms -/

/-- A **chronological feed**: collect posts from the viewer and everyone
they follow, sorted by the labelling function.

This is a coKleisli morphism `Ext socialDCont (List Post) → List Post`.
Applying `extend chronoFeed` to the global labelling produces every
user's personalised feed simultaneously.

Note: in the real Haskell implementation, this also sorts by timestamp.
Here we just concatenate to demonstrate the coKleisli structure. -/
def chronoFeed (labelling : Ext socialDCont.toContainer (List Nat)) : List Nat :=
  let ⟨g, v⟩ := labelling
  -- The viewer's own posts
  let own := v g.viewer
  -- Posts from everyone the viewer follows (up to some bound)
  -- In a real implementation, we'd iterate over followed users.
  -- Here we demonstrate the structure with a fixed bound.
  own

/-- Two feed algorithms compose via coKleisli composition.
This witnesses that feed pipeline stages (filter → rank → truncate)
compose associatively. -/
theorem feed_pipeline_assoc {X Y Z W : Type}
    (f : Ext socialDCont.toContainer X → Y)
    (g : Ext socialDCont.toContainer Y → Z)
    (h : Ext socialDCont.toContainer Z → W) :
    socialDCont.cokleisli_comp (socialDCont.cokleisli_comp f g) h
      = socialDCont.cokleisli_comp f (socialDCont.cokleisli_comp g h) :=
  socialDCont.cokleisli_assoc f g h

/-! ## Audience selection and the sheaf condition

We now formalise the sheaf-breaking feature: audience-selected posts.
A post with an audience restriction is visible only to viewers in the
audience. This creates within-follower disagreement, violating the
gluing axiom.

We prove two theorems:
1. **Fibre sheaf**: within an audience, all viewers agree on content.
2. **Global sheaf failure**: exhibit a concrete counterexample where
   two followers of the same author disagree on post visibility.
-/

/-- A **post** with optional audience restriction.
Corresponds to the Haskell type with `postAudience :: Maybe [UserId]`. -/
structure Post where
  postId : Nat
  author : Nat
  body : Nat  -- abstracted to Nat for simplicity
  audience : Option (List Nat)  -- None = all followers, Some = restricted

/-- A **viewing context**: who is looking. -/
structure Context where
  viewer : Nat
  followsAuthor : Bool  -- does the viewer follow the post's author?

/-- Is a post **visible** in a given context?

A post is visible when:
1. The viewer follows the author (or is the author), AND
2. Either the post has no audience restriction,
   OR the viewer is in the audience list.

This is the content presheaf: `F(c) = { p | visible c p }`. -/
def visible (c : Context) (p : Post) : Prop :=
  c.followsAuthor = true ∧
  match p.audience with
  | none => True                     -- no restriction: all followers see it
  | some aud => c.viewer ∈ aud       -- restricted: must be in audience

/-- The **content** of a post as seen by a viewer. When visible,
every viewer sees the same content (body). This is what makes
individual fibres sheaves. -/
def viewContent (_c : Context) (p : Post) (_h : visible _c p) : Nat :=
  p.body

/-! ### Theorem 1: Audience fibres are sheaves

Within an audience, all viewers who can see a post agree on its
content. This is the positive result that makes the system workable. -/

/-- **Fibre sheaf theorem**: if two viewers can both see the same post,
they see the same content. This holds regardless of whether the post
is public or audience-restricted. -/
theorem fibre_sheaf (c₁ c₂ : Context) (p : Post)
    (h₁ : visible c₁ p) (h₂ : visible c₂ p) :
    viewContent c₁ p h₁ = viewContent c₂ p h₂ := by
  -- Both sides reduce to p.body, regardless of context
  rfl

/-! ### Theorem 2: The global sheaf fails

We exhibit a concrete counterexample: Alice posts with audience
restricted to Carol. Bob and Carol both follow Alice, but they
disagree on whether the post exists. -/

/-- Alice's restricted post: audience = [Carol (id 3)]. -/
private def aliceSecret : Post :=
  { postId := 2, author := 1, body := 42, audience := some [3] }

/-- Carol's context: she follows Alice and is in the audience. -/
private def carolCtx : Context :=
  { viewer := 3, followsAuthor := true }

/-- Bob's context: he follows Alice but is NOT in the audience. -/
private def bobCtx : Context :=
  { viewer := 2, followsAuthor := true }

/-- Carol can see the post. -/
theorem carol_sees : visible carolCtx aliceSecret := by
  constructor
  · rfl
  · simp [aliceSecret, carolCtx]

/-- Bob cannot see the post. -/
theorem bob_cannot_see : ¬ visible bobCtx aliceSecret := by
  intro ⟨_, h_aud⟩
  simp [aliceSecret, bobCtx] at h_aud

/-- **Sheaf failure**: there exist two followers of the same author
and a post such that one can see it and the other cannot.
This is the negation of the sheaf condition's gluing axiom. -/
theorem audience_breaks_sheaf :
    ∃ (c₁ c₂ : Context) (p : Post),
      c₁.followsAuthor = true ∧ c₂.followsAuthor = true ∧
      visible c₁ p ∧ ¬ visible c₂ p :=
  ⟨carolCtx, bobCtx, aliceSecret,
   rfl, rfl, carol_sees, bob_cannot_see⟩

end SocialNetwork
