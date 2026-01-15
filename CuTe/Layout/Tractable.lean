/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CuTe Lean Project

Tractability predicate for CuTe layouts.
-/

import CuTe.Layout.Order
import Mathlib.Algebra.Divisibility.Basic

/-!
# Tractable Layouts

This file defines the tractability predicate for layouts. A layout is tractable
if it can be represented as a morphism in the category Tuple.

## Definition

A flat layout `L = (s₁, ..., sₘ) : (d₁, ..., dₘ)` is **tractable** when for all pairs `(i, j)`:

```
(sᵢ : dᵢ) ⪯ (sⱼ : dⱼ) ∧ dᵢ ≠ 0 ∧ dⱼ ≠ 0  →  sᵢ · dᵢ ∣ dⱼ
```

## Main Definitions

* `IsTractable` - The tractability predicate
* `IsNonDegenerate` - The non-degeneracy predicate (shape = 1 → stride = 0)

## References

* [Categorical Foundations for CuTe Layouts](https://research.colfax-intl.com/categorical-foundations-for-cute-layouts/)
-/

namespace CuTe

namespace ShapeStridePair

/-- Check the tractability condition between two pairs:
    If `p ≤ q` and both have non-zero strides, then `p.shape * p.stride` divides `q.stride`.

    Note: The condition only applies to DISTINCT pairs when p ≤ q in the lexicographic order.
    When p = q, the condition is trivially satisfied.
    Reference: Python implementation uses `i != j` check. -/
def tractablePair (p q : ShapeStridePair) : Bool :=
  -- Same pair - trivially tractable
  if p == q then true
  -- Zero stride means no constraint
  else if p.stride = 0 || q.stride = 0 then true
  -- p comes before q (smaller stride) - check divisibility
  else if p.stride < q.stride then
    q.stride % (p.shapeNat * p.stride) = 0
  -- Same stride, p.shape ≤ q.shape - check divisibility
  else if p.stride = q.stride && p.shapeNat ≤ q.shapeNat then
    q.stride % (p.shapeNat * p.stride) = 0
  else
    true -- p > q, no constraint from p to q

/-- The tractability condition as a proposition -/
def TractablePair (p q : ShapeStridePair) : Prop :=
  blt p q || p == q →  -- p ≤ q in the ordering
  p.stride ≠ 0 →
  q.stride ≠ 0 →
  (p.shapeNat * p.stride) ∣ q.stride

instance instDecidableTractablePair (p q : ShapeStridePair) : Decidable (TractablePair p q) := by
  unfold TractablePair
  infer_instance

end ShapeStridePair

namespace FlatLayout

/-! ### Non-degeneracy as a Prop -/

/-- A layout is non-degenerate if shape = 1 implies stride = 0.

    Dimensions of size 1 contribute nothing to indexing and should have zero stride. -/
def IsNonDegenerate (L : FlatLayout) : Prop :=
  ∀ p : ShapeStridePair, p ∈ L → p.shape = 1 → p.stride = 0

instance (L : FlatLayout) : Decidable (IsNonDegenerate L) := by
  unfold IsNonDegenerate
  infer_instance

/-! ### Tractability -/

/-- A flat layout is tractable when for all pairs (i, j):
    if `sᵢ : dᵢ ⪯ sⱼ : dⱼ` and both strides are non-zero,
    then `sᵢ · dᵢ` divides `dⱼ`.

    This condition ensures the layout can be represented as a tuple morphism. -/
def IsTractable (L : FlatLayout) : Prop :=
  ∀ p : ShapeStridePair, p ∈ L →
  ∀ q : ShapeStridePair, q ∈ L →
  ShapeStridePair.TractablePair p q

/-- Decidable tractability check -/
def isTractable (L : FlatLayout) : Bool :=
  L.all fun p => L.all fun q => ShapeStridePair.tractablePair p q

instance (L : FlatLayout) : Decidable (IsTractable L) := by
  unfold IsTractable
  infer_instance

/-- A layout is valid if it is both non-degenerate and tractable -/
def IsValid (L : FlatLayout) : Prop :=
  IsNonDegenerate L ∧ IsTractable L

def isValid (L : FlatLayout) : Bool :=
  isNonDegenerate L && isTractable L

/-! ### Compactness -/

/-- A layout is compact (contiguous) if it covers exactly [0, size) in memory -/
def isCompact (L : FlatLayout) : Bool :=
  let sorted := L.sort
  -- A layout is compact if, after sorting, each dimension's stride equals
  -- the product of all shapes with smaller strides
  let rec check (expectedStride : ℕ) : List ShapeStridePair → Bool
    | [] => true
    | p :: ps => p.stride == expectedStride && check (expectedStride * p.shapeNat) ps
  check 1 sorted
end FlatLayout

/-! ### Examples and tests -/

section Examples

/-- Helper to create a layout for testing -/
def mkLayout (pairs : List (ℕ × ℕ)) : FlatLayout :=
  pairs.filterMap fun (s, d) => ShapeStridePair.mk? s d

-- Test: Tractable layout [(2,1), (3,2)]
-- 2*1=2 divides 2, so it's tractable
#eval FlatLayout.isTractable (mkLayout [(2, 1), (3, 2)])  -- Should be true

-- Test: Non-tractable layout [(2,1), (3,3)]
-- 2*1=2 does not divide 3, so it's not tractable
#eval FlatLayout.isTractable (mkLayout [(2, 1), (3, 3)])  -- Should be false

-- Test: Non-degenerate layout
#eval FlatLayout.isNonDegenerate (mkLayout [(2, 1), (3, 2)])  -- Should be true

-- Test: Degenerate layout (shape 1 with non-zero stride)
#eval FlatLayout.isNonDegenerate (mkLayout [(1, 5)])  -- Should be false

-- Test: Compact layout
#eval FlatLayout.isCompact (mkLayout [(2, 1), (3, 2)])  -- Should be true

-- Test: Non-compact layout
#eval FlatLayout.isCompact (mkLayout [(2, 1), (3, 4)])  -- Should be false (gap)

end Examples

end CuTe
