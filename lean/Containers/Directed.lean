import Containers.Basic

/-!
# Directed containers and the comonad they induce

This file builds on `Containers.Basic`. It defines **directed containers**
(Ahman–Chapman–Uustalu, *When is a container a comonad?*) and shows that the
extension `Ext C` of a directed container `C` carries a comonad structure, with
each comonad law deduced from one directed-container law.

A directed container equips a container `⟨S, P⟩` with a root `o(s) ∈ P s`, a
sub-shape `s ↓ p ∈ S` for each position, and a shift `p ⊕ q ∈ P s` combining a
position `p ∈ P s` with a position `q ∈ P (s ↓ p)`. The five laws D1–D5 make
each `P s` a "monoid over the base" and let the sub-shapes nest coherently.

The comonad data on `D := Ext C` is

* `counit ⟨s, v⟩ = v (o s)`;
* `comult ⟨s, v⟩ = ⟨s, fun p => ⟨s ↓ p, fun q => v (p ⊕ q)⟩⟩`.

The three comonad laws are then:

* **left counit** `counit ∘ comult = id` — from D1 (shapes) and D2 (values);
* **right counit** `map counit ∘ comult = id` — from D3;
* **coassociativity** `map comult ∘ comult = comult ∘ comult` — from D4 (shapes)
  and D5 (values).

Because the laws relate positions living in *different* fibres `P s`, several of
them carry an explicit transport along a shape equality: D2 transports along D1,
and D5 transports along D4. This is the genuinely dependent content of the
calculation, isolated in the helper `Ext.ext_eq`.

Everything is `Type`-level, Lean 4 core, no Mathlib.
-/

namespace Containers

/-- Extensionality for elements of `Ext C X` whose shapes are related by an
equality `hs : s₁ = s₂`: the two dependent pairs agree when their labellings
agree after transporting positions along `hs`. This packages the dependent
`Sigma` reasoning used throughout the comonad verification. -/
theorem Ext.ext_eq {C : Container} {X : Type} {s₁ s₂ : C.Shape}
    (hs : s₁ = s₂) {v₁ : C.Pos s₁ → X} {v₂ : C.Pos s₂ → X}
    (hv : ∀ q : C.Pos s₁, v₁ q = v₂ (hs ▸ q)) :
    (⟨s₁, v₁⟩ : Ext C X) = ⟨s₂, v₂⟩ := by
  subst hs
  have hvv : v₁ = v₂ := funext hv
  rw [hvv]

/-- A **directed container** extends a container with a root, a sub-shape
operation, and a shift, subject to laws D1–D5. Laws D2 and D5 transport
positions along the shape equalities D1 and D4 respectively. -/
structure DirectedContainer extends Container where
  /-- The root position `o(s) ∈ P s`. -/
  root : (s : Shape) → Pos s
  /-- The sub-shape `s ↓ p ∈ S` sitting under position `p`. -/
  sub : (s : Shape) → Pos s → Shape
  /-- The shift `p ⊕ q ∈ P s`, combining `p ∈ P s` and `q ∈ P (s ↓ p)`. -/
  shift : (s : Shape) → (p : Pos s) → Pos (sub s p) → Pos s
  /-- D1: the sub-shape under the root is the shape itself. -/
  d1 : ∀ s, sub s (root s) = s
  /-- D4: sub-shapes nest along the shift. -/
  d4 : ∀ (s : Shape) (p : Pos s) (q : Pos (sub s p)),
    sub s (shift s p q) = sub (sub s p) q
  /-- D2: shifting by the root is the identity (transported along D1). -/
  d2 : ∀ (s : Shape) (q : Pos (sub s (root s))), shift s (root s) q = d1 s ▸ q
  /-- D3: shifting by the root of the sub-shape is the identity. -/
  d3 : ∀ (s : Shape) (p : Pos s), shift s p (root (sub s p)) = p
  /-- D5: the shift is associative (the right argument transported along D4). -/
  d5 : ∀ (s : Shape) (p : Pos s) (q : Pos (sub s p)) (q' : Pos (sub (sub s p) q)),
    shift s (shift s p q) ((d4 s p q).symm ▸ q') = shift s p (shift (sub s p) q q')

namespace DirectedContainer

variable (D : DirectedContainer) {X : Type}

/-- The comonad **counit** `ε ⟨s, v⟩ = v (o s)`. -/
def counit : Ext D.toContainer X → X :=
  fun p => p.2 (D.root p.1)

/-- The comonad **comultiplication**
`δ ⟨s, v⟩ = ⟨s, fun p => ⟨s ↓ p, fun q => v (p ⊕ q)⟩⟩`. -/
def comult : Ext D.toContainer X → Ext D.toContainer (Ext D.toContainer X) :=
  fun p => ⟨p.1, fun q => ⟨D.sub p.1 q, fun r => p.2 (D.shift p.1 q r)⟩⟩

/-- **Left counit law** `ε ∘ δ = id`. The shape equation is D1; the value
equation is D2. -/
theorem left_counit :
    D.counit ∘ D.comult = (id : Ext D.toContainer X → Ext D.toContainer X) := by
  funext p
  obtain ⟨s, v⟩ := p
  show (⟨D.sub s (D.root s), fun r => v (D.shift s (D.root s) r)⟩ : Ext D.toContainer X)
      = ⟨s, v⟩
  exact Ext.ext_eq (D.d1 s) (fun q => congrArg v (D.d2 s q))

/-- **Right counit law** `(map ε) ∘ δ = id`. The shapes are unchanged; the value
equation is D3. -/
theorem right_counit :
    Ext.map D.counit ∘ D.comult = (id : Ext D.toContainer X → Ext D.toContainer X) := by
  funext p
  obtain ⟨s, v⟩ := p
  show (⟨s, fun q => v (D.shift s q (D.root (D.sub s q)))⟩ : Ext D.toContainer X) = ⟨s, v⟩
  exact Ext.ext_eq rfl (fun q => congrArg v (D.d3 s q))

/-- **Coassociativity** `(map δ) ∘ δ = δ ∘ δ`. The inner shapes agree by D4; the
deepest values agree by D5 (transported along D4). -/
theorem coassoc :
    Ext.map D.comult ∘ D.comult
      = (D.comult ∘ D.comult :
          Ext D.toContainer X → Ext D.toContainer (Ext D.toContainer (Ext D.toContainer X))) := by
  funext p
  obtain ⟨s, v⟩ := p
  show (⟨s, fun p => ⟨D.sub s p, fun q =>
            ⟨D.sub (D.sub s p) q, fun r => v (D.shift s p (D.shift (D.sub s p) q r))⟩⟩⟩
          : Ext D.toContainer (Ext D.toContainer (Ext D.toContainer X)))
      = ⟨s, fun p => ⟨D.sub s p, fun q =>
            ⟨D.sub s (D.shift s p q), fun r => v (D.shift s (D.shift s p q) r)⟩⟩⟩
  apply Ext.ext_eq rfl
  intro p
  apply Ext.ext_eq rfl
  intro q
  exact Ext.ext_eq (D.d4 s p q).symm (fun r => (congrArg v (D.d5 s p q r)).symm)

end DirectedContainer

end Containers
