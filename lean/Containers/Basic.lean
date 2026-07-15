/-!
# Containers, their extensions, and morphisms

This file develops the basic theory of *containers* (Abbott, Altenkirch,
Ghani) using only Lean 4 core — no Mathlib dependency.

A container is a type of *shapes* together with, for each shape, a type of
*positions*. Its *extension* is the polynomial (dependent-pair) functor it
induces on `Type`. Container morphisms induce natural transformations between
extensions, and — this is the representation theorem — every natural
transformation arises this way, uniquely.

Everything here is `Type`-level (a single universe) to keep the development
self-contained and fast to compile.
-/

namespace Containers

/-- A **container** is a type of shapes together with a position family. -/
structure Container where
  Shape : Type
  Pos : Shape → Type

/-- The **extension** of a container `C` at a type `X`: a shape together with a
labelling of its positions by elements of `X`. This is the polynomial functor
`Σ s : Shape, Pos s → X`. -/
def Ext (C : Container) (X : Type) : Type :=
  (s : C.Shape) × (C.Pos s → X)

/-- Functorial action of `Ext C` on a function `f : X → Y`: relabel positions. -/
def Ext.map {C : Container} {X Y : Type} (f : X → Y) :
    Ext C X → Ext C Y :=
  fun p => ⟨p.1, fun i => f (p.2 i)⟩

/-- Functor law: `Ext.map id = id`. -/
theorem Ext.map_id {C : Container} {X : Type} :
    Ext.map (C := C) (id : X → X) = id := by
  funext p
  rfl

/-- Functor law: `Ext.map (g ∘ f) = Ext.map g ∘ Ext.map f`. -/
theorem Ext.map_comp {C : Container} {X Y Z : Type} (f : X → Y) (g : Y → Z) :
    Ext.map (C := C) (g ∘ f) = Ext.map g ∘ Ext.map f := by
  funext p
  rfl

/-- A **morphism of containers** `C ⇒ D`: a map on shapes, together with a
*contravariant* map on positions (pulling `D`-positions over the image shape
back to `C`-positions). -/
structure ContainerMorphism (C D : Container) where
  onShapes : C.Shape → D.Shape
  onPos : (s : C.Shape) → D.Pos (onShapes s) → C.Pos s

/-- A container morphism induces, at every type `X`, a map between extensions.
Collectively these form a natural transformation `Ext C ⟹ Ext D`. -/
def ContainerMorphism.toNat {C D : Container} (φ : ContainerMorphism C D)
    (X : Type) : Ext C X → Ext D X :=
  fun p => ⟨φ.onShapes p.1, fun i => p.2 (φ.onPos p.1 i)⟩

/-- The induced family is **natural**: it commutes with `Ext.map`. -/
theorem ContainerMorphism.toNat_natural {C D : Container}
    (φ : ContainerMorphism C D) {X Y : Type} (f : X → Y) :
    Ext.map f ∘ φ.toNat X = φ.toNat Y ∘ Ext.map f := by
  funext p
  rfl

/-! ## The representation theorem

Container morphisms `C ⇒ D` are in bijection with natural transformations
`Ext C ⟹ Ext D`. We package a natural transformation as a `Type`-indexed
family of maps satisfying the naturality square, and exhibit the bijection.

The key idea: a natural transformation is determined by where it sends the
*generic* element of `Ext C (C.Pos s)`, namely `⟨s, id⟩`. Evaluating the
component at `X := C.Pos s` on `⟨s, id⟩` recovers the shape map and (using
naturality / the Yoneda-style argument) the position map. -/

/-- A natural transformation between the extensions of two containers, bundled
with its naturality law. -/
structure ExtNatTrans (C D : Container) where
  component : (X : Type) → Ext C X → Ext D X
  natural : ∀ {X Y : Type} (f : X → Y),
    Ext.map f ∘ component X = component Y ∘ Ext.map f

/-- Forward direction: every container morphism gives a natural transformation
of extensions. -/
def ContainerMorphism.toExtNatTrans {C D : Container}
    (φ : ContainerMorphism C D) : ExtNatTrans C D where
  component := φ.toNat
  natural := fun f => φ.toNat_natural f

/-- Backward direction: recover a container morphism from a natural
transformation by probing it at the generic element `⟨s, id⟩`. -/
def ExtNatTrans.toMorphism {C D : Container} (η : ExtNatTrans C D) :
    ContainerMorphism C D where
  onShapes := fun s => (η.component (C.Pos s) ⟨s, id⟩).1
  onPos := fun s => (η.component (C.Pos s) ⟨s, id⟩).2

/-- One half of the bijection: starting from a container morphism, building a
natural transformation, and reading a morphism back, returns the original.
This direction is purely computational. -/
theorem ContainerMorphism.toExtNatTrans_toMorphism {C D : Container}
    (φ : ContainerMorphism C D) :
    φ.toExtNatTrans.toMorphism = φ := by
  cases φ
  rfl

/-- The other half of the bijection: every natural transformation is the one
induced by `η.toMorphism`. This is the substantive content of the
representation theorem — it requires the naturality law to reconstruct the
component at an *arbitrary* type from its value at `C.Pos s`.

The argument: for `p = ⟨s, g⟩ : Ext C X`, apply `η.natural g` to the generic
element `⟨s, id⟩ : Ext C (C.Pos s)` (note `Ext.map g ⟨s, id⟩ = ⟨s, g⟩`), which
rewrites `η.component X ⟨s, g⟩` into `Ext.map g (η.component (C.Pos s) ⟨s, id⟩)`,
and the latter is by definition `η.toMorphism.toNat X ⟨s, g⟩`. Together with
`toExtNatTrans_toMorphism` this gives the full bijection (representation
theorem). Fully proved — no `sorry`. -/
theorem ExtNatTrans.toMorphism_toExtNatTrans {C D : Container}
    (η : ExtNatTrans C D) :
    η.toMorphism.toExtNatTrans.component = η.component := by
  funext X p
  obtain ⟨s, g⟩ := p
  -- `η.natural g` applied at the generic element `⟨s, id⟩`:
  have hg := congrFun (η.natural g) (⟨s, id⟩ : Ext C (C.Pos s))
  -- Unfold the function compositions in `hg`.
  simp only [Function.comp] at hg
  -- `Ext.map g ⟨s, id⟩` reduces to `⟨s, g⟩` definitionally; rewrite `hg`
  -- through that identity. The goal's right-hand side
  -- `η.toMorphism.toExtNatTrans.component X ⟨s, g⟩` is by definition
  -- `Ext.map g (η.component (C.Pos s) ⟨s, id⟩)`, so the `show` lines them up.
  have hmap : (Ext.map g (⟨s, id⟩ : Ext C (C.Pos s))) = (⟨s, g⟩ : Ext C X) := rfl
  rw [hmap] at hg
  show Ext.map g (η.component (C.Pos s) ⟨s, id⟩) = η.component X ⟨s, g⟩
  exact hg

end Containers
