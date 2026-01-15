/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CuTe Lean Project

Pointed finite sets for CuTe categorical framework.
-/

import Mathlib.Data.Fin.Basic

/-!
# Pointed Finite Sets

This file defines pointed finite sets `Fin₀ n` and morphisms between them.
These form the underlying structure for tuple morphisms in the CuTe framework.

## Main Definitions

* `Fin₀ n` - The pointed finite set `{*, 0, 1, ..., n-1}` represented as `Option (Fin n)`
* `Fin₀Hom` - Basepoint-preserving maps between pointed finite sets

## Notation

We use `Option (Fin n)` where:
- `none` represents the basepoint `*`
- `some i` represents the element `i ∈ {0, ..., n-1}`
-/

namespace CuTe

/-! ### Pointed Finite Sets -/

/-- Pointed finite set with n+1 elements: {*, 0, 1, ..., n-1}.
    Represented as `Option (Fin n)` where `none` is the basepoint. -/
abbrev Fin₀ (n : ℕ) := Option (Fin n)

namespace Fin₀

/-- The basepoint of Fin₀ n -/
def point {n : ℕ} : Fin₀ n := none

/-- Inject a Fin n element into Fin₀ n -/
def inject {n : ℕ} (i : Fin n) : Fin₀ n := some i

/-- Check if an element is the basepoint -/
def isPoint {n : ℕ} (x : Fin₀ n) : Bool := x.isNone

/-- The size of the pointed set (including basepoint) -/
def card (n : ℕ) : ℕ := n + 1

instance {n : ℕ} : Inhabited (Fin₀ n) := ⟨point⟩

instance {n : ℕ} : DecidableEq (Fin₀ n) := inferInstance

end Fin₀

/-! ### Morphisms of Pointed Finite Sets -/

/-- A morphism of pointed finite sets is a basepoint-preserving function.
    `f : Fin₀Hom m n` satisfies `f none = none`. -/
structure Fin₀Hom (m n : ℕ) where
  /-- The underlying function -/
  toFun : Fin₀ m → Fin₀ n
  /-- The basepoint is preserved -/
  map_point : toFun none = none

namespace Fin₀Hom

variable {m n p : ℕ}

instance : CoeFun (Fin₀Hom m n) (fun _ => Fin₀ m → Fin₀ n) := ⟨Fin₀Hom.toFun⟩

/-- The identity morphism -/
def id : Fin₀Hom n n where
  toFun := _root_.id
  map_point := rfl

/-- Composition of morphisms -/
def comp (g : Fin₀Hom n p) (f : Fin₀Hom m n) : Fin₀Hom m p where
  toFun := g.toFun ∘ f.toFun
  map_point := by simp [f.map_point, g.map_point]

@[simp]
theorem id_apply (x : Fin₀ n) : (id : Fin₀Hom n n) x = x := rfl

@[simp]
theorem comp_apply (g : Fin₀Hom n p) (f : Fin₀Hom m n) (x : Fin₀ m) :
    (comp g f) x = g (f x) := rfl

theorem comp_assoc (h : Fin₀Hom p q) (g : Fin₀Hom n p) (f : Fin₀Hom m n) :
    comp (comp h g) f = comp h (comp g f) := rfl

theorem id_comp (f : Fin₀Hom m n) : comp id f = f := rfl

theorem comp_id (f : Fin₀Hom m n) : comp f id = f := rfl

/-- A morphism is injective away from the basepoint if distinct non-basepoint
    elements map to distinct elements. -/
def InjectiveAwayFromPoint (f : Fin₀Hom m n) : Prop :=
  ∀ i j : Fin m, f (some i) = f (some j) → f (some i) ≠ none → i = j

instance (f : Fin₀Hom m n) : Decidable (InjectiveAwayFromPoint f) := by
  unfold InjectiveAwayFromPoint
  infer_instance

/-- Check injectivity computationally -/
def isInjectiveAwayFromPoint (f : Fin₀Hom m n) : Bool :=
  decide (InjectiveAwayFromPoint f)

/-! ### Constructing morphisms -/

/-- Create a morphism from a partial function (defaulting to basepoint) -/
def ofPartial (f : Fin m → Option (Fin n)) : Fin₀Hom m n where
  toFun
    | none => none
    | some i => f i
  map_point := rfl

/-- The constant morphism sending everything to basepoint -/
def const : Fin₀Hom m n where
  toFun _ := none
  map_point := rfl

/-- Create a morphism from a total function on indices -/
def ofFun (f : Fin m → Fin n) : Fin₀Hom m n where
  toFun
    | none => none
    | some i => some (f i)
  map_point := rfl

@[simp]
theorem ofFun_apply_some (f : Fin m → Fin n) (i : Fin m) :
    (ofFun f) (some i) = some (f i) := rfl

@[simp]
theorem ofFun_apply_none (f : Fin m → Fin n) :
    (ofFun f) none = none := rfl

end Fin₀Hom

/-! ### Examples -/

section Examples

-- Identity morphism
#check (Fin₀Hom.id : Fin₀Hom 3 3)

-- Morphism from function
def exampleMorphism : Fin₀Hom 2 3 := Fin₀Hom.ofFun (fun i => ⟨i.val, by omega⟩)

#eval exampleMorphism (some ⟨0, by omega⟩)  -- some 0
#eval exampleMorphism (some ⟨1, by omega⟩)  -- some 1
#eval exampleMorphism none                   -- none

end Examples

end CuTe
