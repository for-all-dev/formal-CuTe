/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CuTe Lean Project

Category Tuple for CuTe layouts.
-/

import CuTe.Category.Fin0
import CuTe.Layout.Defs

/-!
# Category Tuple

This file defines the category **Tuple** whose objects are tuples of positive integers
and morphisms are dimension-preserving maps over pointed finite sets.

## Main Definitions

* `Tuple` - Objects are `List ℕ+` (tuples of positive integers)
* `TupleMorphism` - Morphisms between tuples respecting dimensions

## References

* [Categorical Foundations for CuTe Layouts](https://research.colfax-intl.com/categorical-foundations-for-cute-layouts/)
-/

namespace CuTe

/-! ### Tuple Objects -/

/-- A tuple is a list of positive integers representing dimension sizes. -/
abbrev Tuple := List ℕ+

namespace Tuple

/-- The size (product of all dimensions) of a tuple -/
def size (S : Tuple) : ℕ := S.foldl (fun acc s => acc * s.val) 1

/-- The rank (number of dimensions) of a tuple -/
def rank (S : Tuple) : ℕ := S.length

/-- Get the i-th dimension safely -/
def getDim (S : Tuple) (i : ℕ) (default : ℕ+ := 1) : ℕ+ :=
  List.getD S i default

/-- The empty tuple (scalar) -/
def scalar : Tuple := []

instance : Inhabited Tuple := ⟨scalar⟩

end Tuple

/-! ### Tuple Morphisms -/

/-- A morphism in the category Tuple from S to T consists of:
    - A pointed finite set morphism α : Fin₀(|S|) → Fin₀(|T|)
    - Dimension preservation: α(i) = j ≠ * implies S[i] = T[j]
    - Injectivity away from basepoint -/
structure TupleMorphism (S T : Tuple) where
  /-- The underlying pointed set morphism -/
  map : Fin₀Hom S.length T.length
  /-- Dimension preservation: non-basepoint images must match dimensions -/
  dim_preserve : ∀ i : Fin S.length, ∀ j : Fin T.length,
    map (some i) = some j → S.getDim i = T.getDim j
  /-- Injectivity: distinct non-basepoint elements map to distinct elements -/
  injective : Fin₀Hom.InjectiveAwayFromPoint map

namespace TupleMorphism

variable {S T U V : Tuple}

/-- The identity morphism on a tuple -/
def id (S : Tuple) : TupleMorphism S S where
  map := Fin₀Hom.id
  dim_preserve := by
    intro i j heq
    simp only [Fin₀Hom.id, Fin₀Hom.id_apply] at heq
    cases heq
    rfl
  injective := by
    intro i j heq _
    simp only [Fin₀Hom.id, Fin₀Hom.id_apply] at heq
    exact Option.some_injective _ heq

/-- Composition of tuple morphisms -/
def comp (g : TupleMorphism T U) (f : TupleMorphism S T) : TupleMorphism S U where
  map := Fin₀Hom.comp g.map f.map
  dim_preserve := by
    intro i k heq
    simp only [Fin₀Hom.comp, Fin₀Hom.comp_apply, Function.comp_apply] at heq
    -- f maps i to some j or none
    match hfi : f.map (some i) with
    | none =>
      rw [hfi, g.map.map_point] at heq
      cases heq
    | some j =>
      rw [hfi] at heq
      have h1 := f.dim_preserve i j hfi
      have h2 := g.dim_preserve j k heq
      rw [h1, h2]
  injective := by
    intro i₁ i₂ heq hne
    simp only [Fin₀Hom.comp, Function.comp_apply] at heq hne
    -- The composition of injective (away from basepoint) maps is injective
    match hf1 : f.map (some i₁), hf2 : f.map (some i₂) with
    | none, _ =>
      rw [hf1, g.map.map_point] at hne
      exact absurd rfl hne
    | some j₁, none =>
      rw [hf1, hf2, g.map.map_point] at heq
      cases hg : g.map (some j₁) <;> simp_all
    | some j₁, some j₂ =>
      simp only [hf1, hf2] at heq hne
      have hj : j₁ = j₂ := g.injective j₁ j₂ heq hne
      subst hj
      have hne' : f.map (some i₁) ≠ none := by simp [hf1]
      have heq' : f.map (some i₁) = f.map (some i₂) := by simp [hf1, hf2]
      exact f.injective i₁ i₂ heq' hne'

@[simp]
theorem id_comp (f : TupleMorphism S T) : comp (id T) f = f := by
  cases f
  simp only [comp, id, Fin₀Hom.comp, Fin₀Hom.id]
  rfl

@[simp]
theorem comp_id (f : TupleMorphism S T) : comp f (id S) = f := by
  cases f
  simp only [comp, id, Fin₀Hom.comp, Fin₀Hom.id]
  rfl

theorem comp_assoc (h : TupleMorphism U V) (g : TupleMorphism T U) (f : TupleMorphism S T) :
    comp (comp h g) f = comp h (comp g f) := by
  simp only [comp, Fin₀Hom.comp]
  rfl

/-! ### Constructing Morphisms -/

/-- A morphism that projects all dimensions to the basepoint -/
def zero (S T : Tuple) : TupleMorphism S T where
  map := Fin₀Hom.const
  dim_preserve := by simp [Fin₀Hom.const]
  injective := by
    intro i j heq hne
    simp [Fin₀Hom.const] at hne

/-- Check if a morphism sends index i to the basepoint -/
def sendsToBasepoint (f : TupleMorphism S T) (i : Fin S.length) : Bool :=
  f.map (some i) == none

/-! ### Layout Function from Morphism -/

/-- Compute the stride for dimension i given the morphism.
    If α(i) = j, stride = t₁ · t₂ · ... · t_{j-1}
    If α(i) = *, stride = 0 -/
def strideAt (f : TupleMorphism S T) (i : Fin S.length) : ℕ :=
  match f.map (some i) with
  | none => 0
  | some j =>
    -- Product of T[0] * T[1] * ... * T[j-1]
    (List.range j.val).foldl (fun acc k =>
      if hk : k < T.length then acc * (T.getDim k).val else acc) 1

/-- Convert a tuple morphism to a flat layout -/
def toLayout (f : TupleMorphism S T) : FlatLayout :=
  (List.finRange S.length).map fun i =>
    ⟨S.getDim i.val, f.strideAt i⟩

end TupleMorphism

/-! ### Examples -/

section Examples

-- Example tuple (2, 3)
def S_23 : Tuple := [2, 3]

#eval Tuple.size S_23  -- 6
#eval Tuple.rank S_23  -- 2

-- The identity morphism
def idMorph : TupleMorphism S_23 S_23 := TupleMorphism.id S_23

-- Check the layout from identity morphism
-- Should give [(2, 1), (3, 2)] for a 2x3 layout
#eval idMorph.toLayout

end Examples

end CuTe
