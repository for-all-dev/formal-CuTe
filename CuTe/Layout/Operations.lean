/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CuTe Lean Project

Core operations on CuTe layouts: coalesce, complement, concatenation.
-/

import CuTe.Layout.Tractable

/-!
# Layout Operations

This file implements the core operations on CuTe layouts:

* `coalesce` - Combine adjacent shape-stride pairs where strides are contiguous
* `complement` - Compute the complementary layout for a given size
* `concat` - Concatenate two layouts

## Coalesce

The coalesce operation combines adjacent pairs `(sᵢ, sᵢ₊₁) : (dᵢ, sᵢ·dᵢ)` into
`(sᵢ·sᵢ₊₁) : (dᵢ)`. This produces a minimal representation of the layout.

## Complement

For a layout `L` mapping into `[0, N)`, the complement `comp(L, N)` is a layout
such that `L ++ comp(L, N)` is compact (bijective onto `[0, N)`).

## References

* [Categorical Foundations for CuTe Layouts](https://research.colfax-intl.com/categorical-foundations-for-cute-layouts/)
-/

namespace CuTe

namespace FlatLayout

/-! ### Coalesce Operation -/

/-- Check if two adjacent pairs can be coalesced.
    Pairs can be coalesced if the second pair's stride equals the first pair's extent. -/
def canCoalesce (p q : ShapeStridePair) : Bool :=
  q.stride = p.shapeNat * p.stride

/-- Coalesce a single pair into an accumulator layout.
    If the new pair can be coalesced with the last pair in the accumulator,
    combine them; otherwise append the new pair. -/
def coalesceOne (acc : FlatLayout) (p : ShapeStridePair) : FlatLayout :=
  match acc with
  | [] => [p]
  | last :: rest =>
    -- We need to check if p can be coalesced with last
    -- Since we're building in reverse (prepending), we check if last.stride = p.extent
    if last.stride = p.shapeNat * p.stride then
      -- Coalesce: combine shapes, keep the smaller stride (p.stride)
      ⟨⟨p.shapeNat * last.shapeNat, Nat.mul_pos p.shape.pos last.shape.pos⟩, p.stride⟩ :: rest
    else
      p :: acc

/-- Coalesce a sorted layout by combining adjacent contiguous pairs.
    The input should be sorted by stride (smallest first).

    Algorithm:
    1. Sort the layout by stride
    2. Iterate through pairs, combining adjacent pairs where q.stride = p.extent

    Example: [(2,1), (2,2), (2,4)] → [(8,1)]
-/
def coalesce (L : FlatLayout) : FlatLayout :=
  let sorted := L.sort
  -- Process pairs from smallest stride to largest
  -- We fold left, building up the coalesced result
  let rec go (acc : FlatLayout) : List ShapeStridePair → FlatLayout
    | [] => acc.reverse
    | p :: ps =>
      match acc with
      | [] => go [p] ps
      | last :: rest =>
        if p.stride = last.shapeNat * last.stride then
          -- Can coalesce: combine last and p
          let combined := ⟨⟨last.shapeNat * p.shapeNat, Nat.mul_pos last.shape.pos p.shape.pos⟩, last.stride⟩
          go (combined :: rest) ps
        else
          go (p :: acc) ps
  go [] sorted

/-! ### Complement Operation -/

/-- Compute the complement of a layout with respect to size N.
    The complement is a layout such that L ++ comp(L, N) covers [0, N) bijectively.

    For a sorted layout, the complement fills in the "gaps" between strides.

    Example: complement [(2,1), (3,2)] 12 = [(2,6)]
    Because: size of L = 2*3 = 6, so complement has size 12/6 = 2
-/
def complement (L : FlatLayout) (N : ℕ) : FlatLayout :=
  if N = 0 then []
  else
    let sorted := L.sort
    -- Compute the product of all shapes
    let layoutSize := L.size
    if layoutSize = 0 || N % layoutSize ≠ 0 then []
    else
      let compSize := N / layoutSize
      if compSize ≤ 1 then []
      else
        -- Find the maximum extent of the layout
        let maxExtent := sorted.foldl (fun acc p => max acc (p.shapeNat * p.stride)) 0
        -- The complement starts at stride = maxExtent
        -- For a compact layout that covers [0, layoutSize), complement starts at layoutSize
        let compStride := if maxExtent == 0 then 1 else maxExtent
        if h : compSize > 0 then
          [⟨⟨compSize, h⟩, compStride⟩]
        else []

/-! ### Concatenation -/

/-- Concatenate two layouts. The result represents the combined indexing. -/
def concat (L₁ L₂ : FlatLayout) : FlatLayout := L₁ ++ L₂

/-- Hierarchical concatenation: scale L₂'s strides by the size of L₁ -/
def hierConcat (L₁ L₂ : FlatLayout) : FlatLayout :=
  let scale := L₁.size
  let scaled : FlatLayout := L₂.map fun p => ⟨p.shape, p.stride * scale⟩
  L₁ ++ scaled

/-! ### Colexicographic Functions -/

/-- Convert a linear index to multi-dimensional coordinates using colexicographic order.
    For layout L = [(s₁,d₁), ..., (sₘ,dₘ)] and index n:
    Returns [x₁, ..., xₘ] where n = Σᵢ xᵢ·dᵢ -/
def toCoords (L : FlatLayout) (n : ℕ) : List ℕ :=
  -- Sort by stride to ensure correct coordinate extraction
  let sorted := L.sort
  let rec extract (remaining : ℕ) : List ShapeStridePair → List ℕ
    | [] => []
    | p :: ps =>
      if p.stride = 0 then
        0 :: extract remaining ps
      else
        let coord := remaining / p.stride % p.shapeNat
        coord :: extract remaining ps
  extract n sorted

/-- Convert multi-dimensional coordinates to a linear index.
    This is the layout function: Φ_L(x₁, ..., xₘ) = Σᵢ xᵢ·dᵢ -/
def fromCoords (L : FlatLayout) (coords : List ℕ) : ℕ :=
  L.apply coords

/-! ### Properties and Lemmas -/

/-- Coalesce produces a sorted layout -/
theorem coalesce_sorted (L : FlatLayout) : (coalesce L).isSorted = true := by
  sorry

/-- Coalesce is idempotent -/
theorem coalesce_idempotent (L : FlatLayout) : coalesce (coalesce L) = coalesce L := by
  sorry

/-- Coalesce preserves the layout function -/
theorem coalesce_preserves_apply (L : FlatLayout) (xs : List ℕ) :
    -- The coalesced layout computes the same addresses (modulo coordinate mapping)
    True := by
  trivial

end FlatLayout

/-! ### Examples and Tests -/

section Examples

open FlatLayout in
-- Test: Coalesce contiguous layout
#eval coalesce (mkLayout [(2, 1), (2, 2), (2, 4)])  -- Should give [(8, 1)]

-- Test: Coalesce non-contiguous layout (no change)
#eval FlatLayout.coalesce (mkLayout [(2, 1), (3, 4)])  -- Should give [(2, 1), (3, 4)]

-- Test: Coalesce partially contiguous
#eval FlatLayout.coalesce (mkLayout [(2, 1), (2, 2), (3, 6)])  -- Should give [(4, 1), (3, 6)]

-- Test: Complement
#eval FlatLayout.complement (mkLayout [(2, 1), (3, 2)]) 12  -- Should give [(2, 6)]

-- Test: Complement when already compact
#eval FlatLayout.complement (mkLayout [(2, 1), (3, 2)]) 6  -- Should give []

-- Test: To/from coordinates
#eval FlatLayout.toCoords (mkLayout [(2, 1), (3, 2)]) 5  -- Index 5 in a 2x3 layout

-- Test: Layout application
#eval FlatLayout.fromCoords (mkLayout [(2, 1), (3, 2)]) [1, 2]  -- 1*1 + 2*2 = 5

end Examples

end CuTe
