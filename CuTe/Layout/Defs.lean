/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CuTe Lean Project

Core definitions for CuTe layouts based on the categorical foundations paper.
-/

import Mathlib.Data.PNat.Defs
import Mathlib.Data.List.Basic

/-!
# CuTe Layout Definitions

This file defines the core data structures for representing GPU memory layouts
in the CuTe (Collective and Universal Tensor Extensions) framework.

## Main Definitions

* `ShapeStridePair` - A pair `(s, d)` where `s` is a positive shape and `d` is a stride
* `FlatLayout` - A list of shape-stride pairs representing a flat memory layout
* `NestedTuple` - Arbitrarily nested tuples of values (for nested layouts)

## References

* [Categorical Foundations for CuTe Layouts](https://research.colfax-intl.com/categorical-foundations-for-cute-layouts/)
-/

namespace CuTe

/-! ### Shape-Stride Pairs -/

/-- A shape-stride pair `(s, d)` where:
- `s : ℕ+` is the shape (dimension size), always positive
- `d : ℕ` is the stride (memory step), can be 0 for projected dimensions -/
structure ShapeStridePair where
  /-- The shape (dimension size), must be positive -/
  shape : ℕ+
  /-- The stride (memory step between elements) -/
  stride : ℕ
  deriving DecidableEq, Repr

namespace ShapeStridePair

/-- Create a shape-stride pair from natural numbers.
    Returns `none` if shape is 0. -/
def mk? (s d : ℕ) : Option ShapeStridePair :=
  if h : s > 0 then some ⟨⟨s, h⟩, d⟩ else none

/-- Create a shape-stride pair, with proof that shape is positive -/
def mkPos (s : ℕ) (hs : s > 0) (d : ℕ) : ShapeStridePair :=
  ⟨⟨s, hs⟩, d⟩

/-- The shape as a natural number -/
def shapeNat (p : ShapeStridePair) : ℕ := p.shape.val

/-- Product of shape and stride -/
def extent (p : ShapeStridePair) : ℕ := p.shapeNat * p.stride

/-- A pair is trivial if its shape is 1 -/
def isTrivial (p : ShapeStridePair) : Bool := p.shape = 1

/-- A pair is degenerate if shape = 1 but stride ≠ 0 -/
def isDegenerate (p : ShapeStridePair) : Bool :=
  p.shape = 1 && p.stride ≠ 0

instance : ToString ShapeStridePair where
  toString p := s!"({p.shapeNat}, {p.stride})"

end ShapeStridePair

/-! ### Flat Layouts -/

/-- A flat layout is a list of shape-stride pairs.
    Represents a multi-dimensional to 1D memory mapping. -/
def FlatLayout := List ShapeStridePair
  deriving DecidableEq, Repr

namespace FlatLayout

instance : EmptyCollection FlatLayout := ⟨[]⟩

instance : Inhabited FlatLayout := ⟨[]⟩

instance : Membership ShapeStridePair FlatLayout where
  mem L p := List.Mem p L

instance : Append FlatLayout := ⟨List.append⟩

instance : HAppend FlatLayout FlatLayout FlatLayout := ⟨List.append⟩

/-- The empty layout -/
def empty : FlatLayout := []

/-- Number of dimensions in the layout -/
def rank (L : FlatLayout) : ℕ := L.length

/-- Total size (product of all shapes) -/
def size (L : FlatLayout) : ℕ := L.foldl (fun acc p => acc * p.shapeNat) 1

/-- The shapes as a list of positive naturals -/
def shapes (L : FlatLayout) : List ℕ+ := L.map (·.shape)

/-- The shapes as natural numbers -/
def shapesNat (L : FlatLayout) : List ℕ := L.map (·.shapeNat)

/-- The strides as a list -/
def strides (L : FlatLayout) : List ℕ := L.map (·.stride)

/-- Apply the layout function to compute the physical address.
    Given logical coordinates `xs`, computes `Σᵢ xᵢ · dᵢ` -/
def apply (L : FlatLayout) (xs : List ℕ) : ℕ :=
  (L.zip xs).foldl (fun acc (p, x) => acc + x * p.stride) 0

/-- Check if layout is non-degenerate: shape = 1 implies stride = 0 -/
def isNonDegenerate (L : FlatLayout) : Bool :=
  L.all fun p => p.shape ≠ 1 || p.stride = 0

/-- All strides are non-zero -/
def hasNoZeroStrides (L : FlatLayout) : Bool :=
  L.all fun p => p.stride ≠ 0

/-- Create a compact (contiguous) layout from shapes.
    Strides are computed as cumulative products. -/
def compact (shapes : List ℕ+) : FlatLayout :=
  let rec go (acc : ℕ) : List ℕ+ → FlatLayout
    | [] => []
    | s :: ss => ⟨s, acc⟩ :: go (acc * s.val) ss
  go 1 shapes

/-- Create a layout from shape-stride pairs given as natural number tuples -/
def ofPairs (pairs : List (ℕ × ℕ)) : Option FlatLayout :=
  pairs.mapM fun (s, d) => ShapeStridePair.mk? s d

instance : ToString FlatLayout where
  toString L := "(" ++ String.intercalate ", " (L.map toString) ++ ")"

end FlatLayout

/-! ### Nested Tuples -/

/-- Nested tuple structure for representing hierarchical layouts.
    Can contain either leaf values or nested sub-tuples. -/
inductive NestedTuple (α : Type*) where
  /-- A single leaf value -/
  | leaf : α → NestedTuple α
  /-- A tuple of nested sub-structures -/
  | node : List (NestedTuple α) → NestedTuple α
  deriving Repr

namespace NestedTuple

variable {α : Type*}

/-- Flatten a nested tuple into a list of leaf values -/
def flatten : NestedTuple α → List α
  | leaf a => [a]
  | node ts => ts.flatMap flatten

/-- The depth of nesting (1 for leaves, max child depth + 1 for nodes) -/
def depth : NestedTuple α → ℕ
  | leaf _ => 1
  | node [] => 1
  | node ts => 1 + ts.foldl (fun acc t => max acc t.depth) 0

/-- Number of leaf elements -/
def size : NestedTuple α → ℕ
  | leaf _ => 1
  | node ts => ts.foldl (fun acc t => acc + t.size) 0

/-- Map a function over all leaf values -/
def map (f : α → β) : NestedTuple α → NestedTuple β
  | leaf a => leaf (f a)
  | node ts => node (ts.map (map f))

/-- Check if this is a leaf -/
def isLeaf : NestedTuple α → Bool
  | leaf _ => true
  | node _ => false

/-- Create a flat (non-nested) tuple from a list -/
def ofList (xs : List α) : NestedTuple α :=
  node (xs.map leaf)

end NestedTuple

/-- A profile describes the nesting structure using unit markers -/
abbrev Profile := NestedTuple Unit

namespace Profile

/-- Create a profile from a nested tuple (just the structure, not values) -/
def fromNestedTuple (t : NestedTuple α) : Profile :=
  t.map fun _ => ()

/-- Flat profile of given length -/
def flat (n : ℕ) : Profile :=
  NestedTuple.node (List.replicate n (NestedTuple.leaf ()))

end Profile

/-! ### Nested Layouts -/

/-- A nested layout pairs shape-stride pairs with nesting structure -/
def NestedLayout := NestedTuple ShapeStridePair

namespace NestedLayout

/-- Flatten a nested layout to a flat layout -/
def toFlat (L : NestedLayout) : FlatLayout := NestedTuple.flatten L

/-- The profile (nesting structure) of a nested layout -/
def profile (L : NestedLayout) : Profile := Profile.fromNestedTuple L

/-- Create a nested layout from a flat layout (wrapping each pair as a leaf) -/
def ofFlat (L : FlatLayout) : NestedLayout :=
  NestedTuple.node (L.map NestedTuple.leaf)

end NestedLayout

end CuTe
