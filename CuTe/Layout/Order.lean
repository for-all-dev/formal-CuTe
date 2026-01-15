/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CuTe Lean Project

Ordering relation on shape-stride pairs for tractability analysis.
-/

import CuTe.Layout.Defs
import Mathlib.Order.Basic
import Mathlib.Data.List.Sort

/-!
# Ordering on Shape-Stride Pairs

This file defines the ordering relation `⪯` on shape-stride pairs used to
characterize tractable layouts.

## Definition

For shape-stride pairs `(s, d)` and `(s', d')`:
```
(s : d) ⪯ (s' : d')  ⟺  d < d' ∨ (d = d' ∧ s ≤ s')
```

This is lexicographic order: compare by stride first, then by shape.
-/

namespace CuTe

namespace ShapeStridePair

/-! ### Lexicographic Ordering -/

/-- The ordering relation on shape-stride pairs:
    `p ≤ q` iff `p.stride < q.stride` or (`p.stride = q.stride` and `p.shape ≤ q.shape`)

    This is lexicographic order comparing stride first, then shape. -/
protected def le (p q : ShapeStridePair) : Prop :=
  p.stride < q.stride ∨ (p.stride = q.stride ∧ p.shape ≤ q.shape)

/-- Strict ordering on shape-stride pairs -/
protected def lt (p q : ShapeStridePair) : Prop :=
  p.stride < q.stride ∨ (p.stride = q.stride ∧ p.shape < q.shape)

instance instLE : LE ShapeStridePair := ⟨ShapeStridePair.le⟩
instance instLT : LT ShapeStridePair := ⟨ShapeStridePair.lt⟩

/-- Decidable ordering -/
instance instDecidableLE (p q : ShapeStridePair) : Decidable (p ≤ q) := by
  unfold LE.le instLE ShapeStridePair.le
  infer_instance

instance instDecidableLT (p q : ShapeStridePair) : Decidable (p < q) := by
  unfold LT.lt instLT ShapeStridePair.lt
  infer_instance

/-- Unpack the `≤` relation into its components -/
theorem le_def (p q : ShapeStridePair) :
    p ≤ q ↔ p.stride < q.stride ∨ (p.stride = q.stride ∧ p.shape ≤ q.shape) :=
  Iff.rfl

/-- Unpack the `<` relation into its components -/
theorem lt_def (p q : ShapeStridePair) :
    p < q ↔ p.stride < q.stride ∨ (p.stride = q.stride ∧ p.shape < q.shape) :=
  Iff.rfl

/-! ### Comparison function for sorting -/

/-- Compare two shape-stride pairs for sorting.
    Returns `lt` if first is smaller, `gt` if larger, `eq` if equal. -/
def cmp (p q : ShapeStridePair) : Ordering :=
  match compare p.stride q.stride with
  | .lt => .lt
  | .gt => .gt
  | .eq => compare p.shape q.shape

instance instOrd : Ord ShapeStridePair := ⟨cmp⟩

/-- Boolean comparison for sorting -/
def blt (p q : ShapeStridePair) : Bool :=
  p.stride < q.stride || (p.stride == q.stride && p.shape < q.shape)

/-! ### Convenience lemmas -/

/-- Smaller stride means smaller pair -/
theorem lt_of_stride_lt {p q : ShapeStridePair} (h : p.stride < q.stride) : p < q := by
  rw [lt_def]; left; exact h

/-- Same stride, smaller shape means smaller pair -/
theorem lt_of_stride_eq_shape_lt {p q : ShapeStridePair}
    (hs : p.stride = q.stride) (hsh : p.shape < q.shape) : p < q := by
  rw [lt_def]; right; exact ⟨hs, hsh⟩

/-- The ordering is reflexive -/
protected theorem le_refl (p : ShapeStridePair) : p ≤ p := by
  rw [le_def]; right; exact ⟨rfl, le_refl _⟩

/-- The ordering is transitive -/
protected theorem le_trans {p q r : ShapeStridePair} (hpq : p ≤ q) (hqr : q ≤ r) : p ≤ r := by
  rw [le_def] at hpq hqr ⊢
  rcases hpq with hd | ⟨heq, hs⟩
  · rcases hqr with hd' | ⟨heq', _⟩
    · left; omega
    · left; omega
  · rcases hqr with hd' | ⟨heq', hs'⟩
    · left; rw [heq]; exact hd'
    · right; exact ⟨heq.trans heq', le_trans hs hs'⟩

/-- The ordering is total -/
protected theorem le_total (p q : ShapeStridePair) : p ≤ q ∨ q ≤ p := by
  rw [le_def, le_def]
  by_cases hd : p.stride < q.stride
  · left; left; exact hd
  · by_cases hd' : q.stride < p.stride
    · right; left; exact hd'
    · have heq : p.stride = q.stride := Nat.le_antisymm (Nat.not_lt.mp hd') (Nat.not_lt.mp hd)
      rcases le_total p.shape q.shape with h | h
      · left; right; exact ⟨heq, h⟩
      · right; right; exact ⟨heq.symm, h⟩

/-- blt is transitive -/
theorem blt_trans {p q r : ShapeStridePair} (hpq : blt p q) (hqr : blt q r) : blt p r := by
  simp only [blt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at *
  rcases hpq with hd | ⟨heq, hs⟩
  · rcases hqr with hd' | ⟨heq', _⟩
    · left; omega
    · left; omega
  · rcases hqr with hd' | ⟨heq', hs'⟩
    · left; rw [heq]; exact hd'
    · right; exact ⟨heq.trans heq', lt_trans hs hs'⟩

end ShapeStridePair

/-! ### Sorting Layouts -/

namespace FlatLayout

/-- Sort a layout by the shape-stride ordering (stride first, then shape) -/
def sort (L : FlatLayout) : FlatLayout :=
  L.mergeSort ShapeStridePair.blt

/-- Check if a layout is sorted -/
def isSorted (L : FlatLayout) : Bool :=
  L.Pairwise (fun p q => !ShapeStridePair.blt q p)

end FlatLayout

end CuTe
