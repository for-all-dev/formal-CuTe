/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CuTe Lean Project

Category Nest for nested tuple layouts.
-/

import CuTe.Category.Tuple
import CuTe.Layout.Defs

/-!
# Category Nest

This file defines the category **Nest** whose objects are nested tuples
(arbitrarily nested lists of positive integers) and morphisms are
nested tuple morphisms.

## Main Definitions

* `NestObj` - Objects of category Nest (nested tuples with profile)
* `NestMorphism` - Morphisms between nested tuples
* `flatten` - Functor from Nest to Tuple

## References

* [Categorical Foundations for CuTe Layouts](https://research.colfax-intl.com/categorical-foundations-for-cute-layouts/)
-/

namespace CuTe

/-! ### Nested Tuple Objects -/

/-- A nest object consists of a nested tuple together with its profile.
    The profile records the nesting structure. -/
structure NestObj where
  /-- The nested tuple of positive integers -/
  tuple : NestedTuple ℕ+
  /-- The profile (nesting structure) -/
  profile : Profile
  deriving Repr

namespace NestObj

/-- Create a nest object from a flat list (no nesting) -/
def ofFlat (xs : List ℕ+) : NestObj where
  tuple := NestedTuple.node (xs.map NestedTuple.leaf)
  profile := NestedTuple.node (xs.map fun _ => NestedTuple.leaf ())

/-- Create a nest object from a single value -/
def ofScalar (x : ℕ+) : NestObj where
  tuple := NestedTuple.leaf x
  profile := NestedTuple.leaf ()

/-- Convert to a flat Tuple using NestedTuple.flatten -/
def toTuple (n : NestObj) : Tuple := n.tuple.flatten

end NestObj

/-! ### Additional NestedTuple Operations -/

/-- The product of all leaf values in a nested tuple -/
def NestedTuple.prod : NestedTuple ℕ+ → ℕ
  | leaf x => x.val
  | node xs => xs.foldl (fun acc t => acc * t.prod) 1

/-! ### Nested Morphisms -/

/-- A morphism in category Nest.
    This is a placeholder - full implementation requires careful handling
    of the nested structure and profile matching. -/
structure NestMorphism (S T : NestObj) where
  /-- The underlying flat tuple morphism -/
  flatMorphism : TupleMorphism S.toTuple T.toTuple

namespace NestMorphism

/-- Identity morphism -/
def id (S : NestObj) : NestMorphism S S where
  flatMorphism := TupleMorphism.id S.toTuple

/-- Composition of nest morphisms -/
def comp {S T U : NestObj} (g : NestMorphism T U) (f : NestMorphism S T) : NestMorphism S U where
  flatMorphism := TupleMorphism.comp g.flatMorphism f.flatMorphism

end NestMorphism

/-! ### Hierarchical Layout Operations -/

/-- Create a hierarchical layout from nested tuple.
    Each level of nesting creates a new "block" in the layout. -/
def NestedTuple.toHierLayout : NestedTuple ℕ+ → FlatLayout
  | leaf x => [⟨x, 1⟩]
  | node xs =>
    let sublayouts := xs.map toHierLayout
    -- Concatenate with appropriate stride scaling
    let rec buildLayout (acc : FlatLayout) (scale : ℕ) : List FlatLayout → FlatLayout
      | [] => acc
      | L :: Ls =>
        let scaled : FlatLayout := L.map fun p => ⟨p.shape, p.stride * scale⟩
        let newScale := scale * L.size
        buildLayout (List.append acc scaled) newScale Ls
    buildLayout [] 1 sublayouts

/-! ### Examples -/

section Examples

-- Flat tuple [2, 3]
def flat23 : NestObj := NestObj.ofFlat [2, 3]
#eval flat23.toTuple  -- [2, 3]

-- Nested ((2, 3), 4) - a 2x3 block repeated 4 times
def nested234 : NestedTuple ℕ+ :=
  NestedTuple.node [
    NestedTuple.node [NestedTuple.leaf 2, NestedTuple.leaf 3],
    NestedTuple.leaf 4
  ]

#eval nested234.flatten  -- [2, 3, 4]
#eval nested234.prod     -- 24
#eval nested234.size     -- 3 (number of leaves)

-- Hierarchical layout
#eval nested234.toHierLayout

end Examples

end CuTe
