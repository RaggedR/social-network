import Containers.Directed

/-!
# CoKleisli structure and strength for directed container comonads

This file extends `Directed.lean` with the coKleisli operations and the
canonical strength of a directed container comonad.

* `extend` — the coKleisli extension: given `f : W(X) → Y`, produce
  `W(X) → W(Y)` by applying `f` at every position (via `duplicate`).
* `cokleisli_comp` — composition in the coKleisli category:
  `g .* f = g ∘ extend f`.
* `strength` — the canonical strength `W(A × B) → A × W(B)`.

## Main results

* `extend_counit` — `extend ε = id`
* `counit_extend` — `ε ∘ extend f = f`
* `extend_extend` — `extend (g ∘ extend f) = extend g ∘ extend f`
* `strength_natural` — the strength is natural in both variables
* `strength_counit` — `(id × ε) ∘ σ = ε`

Everything is `Type`-level, Lean 4 core, no Mathlib.
-/

namespace Containers

namespace DirectedContainer

variable (D : DirectedContainer)

/-! ### CoKleisli extension -/

/-- The **coKleisli extension** of `f : Ext D X → Y`. -/
def extend {X Y : Type} (f : Ext D.toContainer X → Y) :
    Ext D.toContainer X → Ext D.toContainer Y :=
  fun p => ⟨p.1, fun q => f ⟨D.sub p.1 q, fun r => p.2 (D.shift p.1 q r)⟩⟩

/-- Extension equals `map f ∘ comult`, definitionally. -/
theorem extend_eq_map_comult {X Y : Type} (f : Ext D.toContainer X → Y) :
    D.extend f = Ext.map f ∘ D.comult := by
  rfl

/-- **`extend ε = id`**: extending the counit is the identity. From D3. -/
theorem extend_counit {X : Type} :
    D.extend (D.counit (X := X)) = id := by
  funext ⟨s, v⟩
  exact Ext.ext_eq rfl (fun q => congrArg v (D.d3 s q))

/-- **`ε ∘ extend f = f`**: the counit is a left inverse of extension.
From D1 and D2. -/
theorem counit_extend {X Y : Type} (f : Ext D.toContainer X → Y) :
    D.counit ∘ D.extend f = f := by
  funext ⟨s, v⟩
  show f ⟨D.sub s (D.root s), fun r => v (D.shift s (D.root s) r)⟩ = f ⟨s, v⟩
  congr 1
  exact Ext.ext_eq (D.d1 s) (fun q => congrArg v (D.d2 s q))

/-- **`extend (g ∘ extend f) = extend g ∘ extend f`**: extension respects
coKleisli composition (associativity law). From D4 and D5. -/
theorem extend_extend {X Y Z : Type}
    (f : Ext D.toContainer X → Y)
    (g : Ext D.toContainer Y → Z) :
    D.extend (g ∘ D.extend f) = D.extend g ∘ D.extend f := by
  funext ⟨s, v⟩
  apply Ext.ext_eq rfl
  intro q
  -- Both sides apply g to a pair; we need to show the pairs are equal.
  -- LHS: g ⟨sub s q, fun r => f ⟨sub (sub s q) r, fun t => v (shift s q (shift (sub s q) r t))⟩⟩
  -- RHS: g ⟨sub s q, fun r => f ⟨sub s (shift s q r), fun t => v (shift s (shift s q r) (d4⁻¹ ▸ t))⟩⟩
  -- These agree by D4 (shapes) and D5 (values).
  simp only [Function.comp, extend]
  congr 1
  apply Ext.ext_eq rfl
  intro r
  congr 1
  exact Ext.ext_eq (D.d4 s q r).symm
    (fun t => (congrArg v (D.d5 s q r t)).symm)

/-! ### CoKleisli composition -/

/-- **CoKleisli composition**: `g .* f = g ∘ extend f`. -/
def cokleisli_comp {X Y Z : Type}
    (f : Ext D.toContainer X → Y)
    (g : Ext D.toContainer Y → Z) :
    Ext D.toContainer X → Z :=
  g ∘ D.extend f

/-- Right unit: `f .* ε = f`. -/
theorem cokleisli_comp_counit {X Y : Type}
    (f : Ext D.toContainer X → Y) :
    D.cokleisli_comp (D.counit) f = f := by
  unfold cokleisli_comp
  rw [extend_counit]
  rfl

/-- Left unit: `ε .* f = f`. -/
theorem cokleisli_counit_comp {X Y : Type}
    (f : Ext D.toContainer X → Y) :
    D.cokleisli_comp f D.counit = f := by
  unfold cokleisli_comp
  exact D.counit_extend f

/-- CoKleisli composition is **associative**. -/
theorem cokleisli_assoc {X Y Z W : Type}
    (f : Ext D.toContainer X → Y)
    (g : Ext D.toContainer Y → Z)
    (h : Ext D.toContainer Z → W) :
    D.cokleisli_comp (D.cokleisli_comp f g) h
      = D.cokleisli_comp f (D.cokleisli_comp g h) := by
  unfold cokleisli_comp
  show h ∘ D.extend (g ∘ D.extend f) = h ∘ D.extend g ∘ D.extend f
  rw [D.extend_extend f g]

/-! ### Strength -/

/-- The **canonical strength** `σ : W(A × B) → A × W(B)`. -/
def strength (A B : Type) :
    Ext D.toContainer (A × B) → A × Ext D.toContainer B :=
  fun ⟨s, v⟩ => ((v (D.root s)).1, ⟨s, fun q => (v q).2⟩)

/-- Strength is natural in `A`: `(f × id) ∘ σ = σ ∘ W(f × id)`. -/
theorem strength_natural_left {A A' B : Type} (f : A → A') :
    (fun p : A × Ext D.toContainer B => (f p.1, p.2)) ∘ D.strength A B
      = D.strength A' B ∘ Ext.map (fun ab : A × B => (f ab.1, ab.2)) := by
  funext ⟨s, v⟩
  rfl

/-- Strength is natural in `B`: `(id × W(g)) ∘ σ = σ ∘ W(id × g)`. -/
theorem strength_natural_right {A B B' : Type} (g : B → B') :
    (fun p : A × Ext D.toContainer B => (p.1, Ext.map g p.2)) ∘ D.strength A B
      = D.strength A B' ∘ Ext.map (fun ab : A × B => (ab.1, g ab.2)) := by
  funext ⟨s, v⟩
  rfl

/-- Strength interacts with counit: `(id × ε) ∘ σ = ε`. -/
theorem strength_counit {A B : Type} :
    (fun p : A × Ext D.toContainer B => (p.1, D.counit p.2)) ∘ D.strength A B
      = D.counit (X := A × B) := by
  funext ⟨s, v⟩
  rfl

end DirectedContainer

end Containers
