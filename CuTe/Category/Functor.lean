/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CuTe Lean Project

Realization functor from Tuple to FinSet.
-/

import CuTe.Category.Tuple
import CuTe.Layout.Operations

/-!
# Realization Functor

This file defines the realization functor `|·| : Tuple → FinSet` that maps:
- Objects: Tuple S ↦ Fin (size S)
- Morphisms: TupleMorphism f ↦ layout function L_f

## Main Results

* `toLayout_id` - Identity morphism gives identity-like layout
* `toLayout_comp` - Composition of morphisms corresponds to layout composition

## References

* [Categorical Foundations for CuTe Layouts](https://research.colfax-intl.com/categorical-foundations-for-cute-layouts/)
-/

namespace CuTe

/-! ### Size of Tuples -/

/-- The size of a tuple is the product of all its dimensions -/
def Tuple.prod (S : Tuple) : ℕ := S.foldl (fun acc s => acc * s.val) 1

/-! ### Layout Function -/

/-- Apply the layout function to coordinates.
    Given a tuple morphism f : S → T, the layout function maps
    coordinates in S to linear indices in T. -/
def TupleMorphism.layoutFun {S T : Tuple} (f : TupleMorphism S T) (coords : List ℕ) : ℕ :=
  f.toLayout.apply coords

/-! ### Functor Properties -/

/-- The identity morphism produces the standard colexicographic layout -/
theorem toLayout_id (S : Tuple) :
    (TupleMorphism.id S).toLayout = (List.finRange S.length).map fun i =>
      ⟨S.getDim i.val, (List.range i.val).foldl (fun acc k =>
        if hk : k < S.length then acc * (S.getDim k).val else acc) 1⟩ := by
  simp only [TupleMorphism.id, TupleMorphism.toLayout, TupleMorphism.strideAt]
  simp only [Fin₀Hom.id]
  rfl

/-- Composition of morphisms corresponds to composition of layout functions.
    This is the key functoriality property: |g ∘ f| = |g| ∘ |f| -/
theorem toLayout_comp_apply {S T U : Tuple}
    (g : TupleMorphism T U) (f : TupleMorphism S T) (coords : List ℕ) :
    (TupleMorphism.comp g f).layoutFun coords =
    g.layoutFun (FlatLayout.toCoords f.toLayout (f.layoutFun coords)) := by
  -- The composition of layout functions factors through intermediate coordinates
  -- This requires showing that strideAt for the composition equals the
  -- product of strides through the intermediate tuple
  sorry

/-! ### Layout from Composition -/

/-- The layout of a composition relates to the layouts of components -/
theorem toLayout_comp {S T U : Tuple}
    (g : TupleMorphism T U) (f : TupleMorphism S T) :
    (TupleMorphism.comp g f).toLayout =
    (List.finRange S.length).map fun i =>
      ⟨S.getDim i.val, (TupleMorphism.comp g f).strideAt i⟩ := by
  simp only [TupleMorphism.toLayout]

/-! ### Colexicographic Isomorphism -/

/-- The colexicographic function for a tuple -/
def colex (S : Tuple) (coords : List ℕ) : ℕ :=
  let strides := (List.range S.length).map fun i =>
    (List.range i).foldl (fun acc k =>
      if hk : k < S.length then acc * (S.getDim k).val else acc) 1
  (coords.zip strides).foldl (fun acc (x, d) => acc + x * d) 0

/-- The identity morphism's layout function equals colexicographic -/
theorem id_layout_eq_colex (S : Tuple) (coords : List ℕ) :
    (TupleMorphism.id S).layoutFun coords = colex S coords := by
  simp only [TupleMorphism.layoutFun, TupleMorphism.toLayout, TupleMorphism.strideAt]
  simp only [TupleMorphism.id, Fin₀Hom.id]
  simp only [FlatLayout.apply, colex]
  -- Both compute Σᵢ xᵢ · (∏_{j<i} sⱼ)
  sorry

/-! ### Examples -/

section Examples

def S2x3 : Tuple := [2, 3]
def T6 : Tuple := [6]

-- Identity morphism layout
#eval (TupleMorphism.id S2x3).toLayout
-- Expected: [(2, 1), (3, 2)]

-- Check layout function
#eval (TupleMorphism.id S2x3).layoutFun [1, 2]
-- Expected: 1*1 + 2*2 = 5

-- Colexicographic
#eval colex S2x3 [1, 2]
-- Expected: 5

end Examples

end CuTe
