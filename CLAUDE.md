# CuTe Layouts: Categorical Foundations in Lean 4

## Project Overview

This project formalizes the categorical foundations of NVIDIA CuTe (Collective and Universal Tensor Extensions) layouts in Lean 4. The goal is to provide a verified mathematical framework for GPU memory layout operations based on category theory.

**Reference Materials:**
- Paper: "Categorical Foundations for CuTe Layouts" (Colfax Research)
- Python Reference: `github.com/ColfaxResearch/layout-categories`
- PDF: `docs/categories-of-layouts.pdf`

---

## Mathematical Background

### 1. Layouts and Shape-Stride Representation

A **layout** maps multi-dimensional logical coordinates to one-dimensional physical memory addresses. A flat layout is expressed as:

```
L = (s₁, ..., sₘ) : (d₁, ..., dₘ)
```

where:
- `sᵢ` is the **shape** (dimension size) - must be a positive integer
- `dᵢ` is the **stride** (memory step) - can be 0 (indicating projection)

The **layout function** `Φ_L : [0, ∏sᵢ) → ℕ` computes memory addresses:
```
Φ_L(x₁, ..., xₘ) = Σᵢ xᵢ · dᵢ
```

### 2. Ordering on Shape-Stride Pairs

Define the relation `⪯` on pairs:

```
(s : d) ⪯ (s' : d')  ⟺  d < d' ∨ (d = d' ∧ s ≤ s')
```

This ordering is a total preorder used to define tractability.

### 3. Tractable Layouts

A flat layout `L` is **tractable** when for all pairs `(i, j)`:

```
(sᵢ : dᵢ) ⪯ (sⱼ : dⱼ) ∧ dᵢ ≠ 0 ∧ dⱼ ≠ 0  →  sᵢ · dᵢ ∣ dⱼ
```

**Intuition**: Smaller strides must evenly divide into larger strides when scaled by their shapes. This ensures the layout can be represented as a morphism.

### 4. Non-Degeneracy

A layout is **non-degenerate** when:
```
sᵢ = 1  →  dᵢ = 0
```

Dimensions of size 1 contribute nothing to indexing and should have zero stride.

### 5. Standard Form

A tuple morphism is in **standard form** when:
- No superfluous entries (entries not hit by the morphism)
- Entries are consolidated (no redundant dimensions in codomain)

---

## Category Theory Framework

### Category Tuple

**Objects**: Tuples of positive integers `S = (s₁, ..., sₘ)` where `sᵢ ∈ ℤ₊`

**Morphisms**: A morphism `f : S → T` consists of a map `α : {*, 1, ..., m} → {*, 1, ..., n}` satisfying:
1. `α(*) = *` (basepoint preservation)
2. `α` is injective on non-basepoint elements
3. Dimension preservation: `α(i) = j ≠ *  →  sᵢ = tⱼ`

**Composition**: Function composition on underlying maps

**Identity**: Identity map on index sets

### Category Nest

Extends Tuple to nested structures:

**Objects**: Nested tuples `S` with a **profile** `P` (nested tuple of `*` markers indicating structure)

**Morphisms**: Nested tuple morphisms compatible with profile structure

### Realization Functor

`|·| : Tuple → FinSet` maps:
- Objects: `|S| = [0, ∏ᵢsᵢ)` (finite set of indices)
- Morphisms: `|f| = L_f` (the layout function)

**Key Property**:
```
|g ∘ f| = |g| ∘ |f|   (functor preserves composition)
```

---

## Core Operations

### Colexicographic Isomorphism

Maps multi-dimensional indices to linear indices:
```
colex_S(x₁, ..., xₘ) = Σᵢ₌₁ᵐ xᵢ · (s₁ · s₂ · ... · sᵢ₋₁)
                     = x₁ + s₁·x₂ + s₁·s₂·x₃ + ...
```

### Coalesce

Iteratively combines adjacent shape-stride pairs where the stride pattern is contiguous:
```
Replace: (sᵢ, sᵢ₊₁) : (dᵢ, sᵢ·dᵢ)  →  (sᵢ·sᵢ₊₁) : (dᵢ)
```

**Example**:
```
coalesce [(2,1), (2,2), (2,4)] = [(8,1)]
```

### Sort

Arrange shape-stride pairs by the `⪯` ordering (primarily by stride, then by shape).

### Complement

For layout `L` mapping into `[0, N)`, compute `comp(L, N)` such that:
- `L ++ comp(L, N)` is **compact** (covers `[0, N)` bijectively when composed correctly)
- `comp(L, N)` is sorted and coalesced

**Example**:
```
complement [(2,1), (3,2)] 12 = [(2,6)]
```

### Composition

For layouts `A : S → T` and `B : T → U`:
1. Convert to tuple morphisms
2. If directly composable, compose morphisms
3. Otherwise, use **mutual refinement** algorithm:
   - Find common refinement of intermediate tuple
   - Compute pullback and pushforward
   - Derive composed morphism
4. Convert result back to layout

---

## Key Theorems to Prove

### Correspondence Theorem

```lean
theorem correspondence :
  ∀ L : FlatLayout,
    (NonDegenerate L ∧ Tractable L) ↔
    ∃! f : TupleMorphism, StandardForm f ∧ encodeLayout f = L
```

One-to-one bijection between non-degenerate tractable flat layouts and non-degenerate tuple morphisms in standard form.

### Functor Laws

```lean
theorem realization_preserves_id (S : Tuple) :
  layoutFunction (id S) = id

theorem realization_preserves_comp (f : S ⟶ T) (g : T ⟶ U) :
  layoutFunction (g ∘ f) = layoutFunction g ∘ layoutFunction f
```

### Layout Algebra Identities

```lean
-- Complement is an involution (up to coalescing)
theorem complement_involution (L : FlatLayout) (N M : ℕ+) :
  coalesce (complement (complement L N) M) = coalesce L

-- Coalesce is idempotent
theorem coalesce_idempotent (L : FlatLayout) :
  coalesce (coalesce L) = coalesce L

-- Composition associativity
theorem compose_assoc (A B C : FlatLayout) :
  compose (compose A B) C = compose A (compose B C)
```

### Agreement Theorems

Operations on layouts equal operations on morphisms:

```lean
theorem coalesce_agree (f : TupleMorphism) :
  encodeLayout (coalesceMorphism f) = coalesce (encodeLayout f)

theorem complement_agree (f : TupleMorphism) (N : ℕ+) :
  encodeLayout (complementMorphism f N) = complement (encodeLayout f) N

theorem compose_agree (f g : TupleMorphism) :
  encodeLayout (composeMorphism f g) = compose (encodeLayout f) (encodeLayout g)
```

---

## Implementation Guide

### Data Structures

```lean
-- Positive naturals
abbrev PosNat := { n : ℕ // n > 0 }

-- Shape-stride pair
structure ShapeStridePair where
  shape : PosNat
  stride : ℕ
  deriving DecidableEq, Repr

-- Flat layout
def FlatLayout := List ShapeStridePair

-- Nested tuple (inductive)
inductive NestedTuple (α : Type) where
  | leaf : α → NestedTuple α
  | node : List (NestedTuple α) → NestedTuple α

-- Profile (nesting structure marker)
def Profile := NestedTuple Unit

-- Pointed finite set morphism
structure Fin0Morphism (m n : ℕ) where
  toFun : Fin (m + 1) → Fin (n + 1)
  map_zero : toFun 0 = 0
  injective_pos : ∀ i j, i ≠ 0 → j ≠ 0 → toFun i = toFun j → toFun i ≠ 0 → i = j
```

### File Organization

```
CuTe/
├── Layout/
│   ├── Defs.lean        -- ShapeStridePair, FlatLayout, NestedTuple
│   ├── Order.lean       -- ⪯ ordering, decidable instances
│   ├── Tractable.lean   -- IsTractable, NonDegenerate predicates
│   └── Operations.lean  -- coalesce, sort, flatten
├── Category/
│   ├── Fin0.lean        -- Pointed finite sets and morphisms
│   ├── Tuple.lean       -- Category Tuple, objects and morphisms
│   ├── Nest.lean        -- Category Nest for nested tuples
│   └── Functor.lean     -- Realization functor |·| : Tuple → FinSet
├── Morphism/
│   ├── Encode.lean      -- Layout ↔ Morphism bijection
│   ├── Compose.lean     -- Morphism composition
│   ├── Complement.lean  -- Complement morphism operation
│   └── StandardForm.lean-- Canonical representatives
├── Algebra/
│   ├── Colex.lean       -- Colexicographic isomorphism
│   ├── Complement.lean  -- Layout complement operation
│   ├── Division.lean    -- Logical division f ⊘ g
│   ├── Product.lean     -- Logical product f ⊗ g
│   └── Refinement.lean  -- Mutual refinement algorithm
└── Tests/
    └── Agreement.lean   -- Property tests: layout ops = morphism ops
```

### Lean-Specific Conventions

1. **Use `ℕ+` from Mathlib** for positive naturals (`PNat`)
2. **Decidable instances** for all predicates to enable `#eval` testing
3. **Computationally efficient** - operations should compute, not just exist
4. **Structure vs Class**: Use `structure` for data, `class` for mathematical abstractions
5. **Namespacing**: `CuTe.Layout.coalesce`, `CuTe.Category.Tuple.compose`

### Tactics Commonly Needed

- `omega` - Linear arithmetic over naturals
- `simp` - Simplification with lemmas
- `decide` - Decidable propositions
- `induction` - Structural induction on lists/nested tuples
- `ext` - Extensionality for functions
- `constructor` - Build structures
- `rcases` / `obtain` - Destructure hypotheses

### Mathlib Dependencies

```lean
import Mathlib.Data.PNat.Basic           -- Positive naturals
import Mathlib.Data.Fin.Basic            -- Finite types
import Mathlib.Data.List.Basic           -- List operations
import Mathlib.CategoryTheory.Category.Basic  -- Category structure
import Mathlib.CategoryTheory.Functor.Basic   -- Functors
import Mathlib.Order.Basic               -- Orderings
import Mathlib.Algebra.Divisibility.Basic    -- Divisibility
```

---

## Verification Strategy

### Level 1: Computational Verification

Use `#eval` to verify operations match Python reference:

```lean
#eval coalesce [(⟨2,by omega⟩, 1), (⟨2,by omega⟩, 2), (⟨2,by omega⟩, 4)]
-- Expected: [(8, 1)]

#eval isTractable [(⟨2,by omega⟩, 1), (⟨3,by omega⟩, 2)]
-- Expected: true

#eval complement [(⟨2,by omega⟩, 1), (⟨3,by omega⟩, 2)] 12
-- Expected: [(2, 6)]
```

### Level 2: Property Testing

Verify properties hold for random inputs using decidable predicates:

```lean
-- Test tractability is preserved by coalesce
example (L : FlatLayout) (h : isTractable L) : isTractable (coalesce L) := by
  decide  -- If decidable, or prove manually
```

### Level 3: Full Proofs

Prove all key theorems formally in Lean.

---

## Example Reference Implementations

### From Python Reference (`tract/categories.py`)

**Coalesce Algorithm**:
```python
def coalesce(layout):
    result = []
    for s, d in sorted_layout:
        if result and result[-1][1] * result[-1][0] == d:
            result[-1] = (result[-1][0] * s, result[-1][1])
        else:
            result.append((s, d))
    return result
```

**Tractability Check**:
```python
def is_tractable(layout):
    sorted_layout = sorted(layout, key=lambda x: (x[1], x[0]))
    for i, (si, di) in enumerate(sorted_layout):
        for j, (sj, dj) in enumerate(sorted_layout):
            if i != j and di != 0 and dj != 0:
                if (di < dj or (di == dj and si <= sj)):
                    if dj % (si * di) != 0:
                        return False
    return True
```

**Complement Algorithm**:
```python
def complement(layout, N):
    # Find remaining dimensions after layout is applied
    product = 1
    for s, d in layout:
        product *= s
    complement_size = N // product
    # Build complement layout covering remaining indices
    ...
```

---

## Testing Examples from Paper

| Operation | Input | Expected Output |
|-----------|-------|-----------------|
| coalesce | `[(2,1), (2,2), (2,4)]` | `[(8,1)]` |
| coalesce | `[(2,1), (3,4)]` | `[(2,1), (3,4)]` (no change) |
| sort | `[(3,2), (2,1)]` | `[(2,1), (3,2)]` |
| tractable? | `[(2,1), (3,2)]` | `true` |
| tractable? | `[(2,1), (3,3)]` | `false` (2*1=2 does not divide 3) |
| complement | `[(2,1), (3,2)] in 12` | `[(2,6)]` |
| compose | `A=[(2,1)], B=[(2,1)]` | `[(2,1)]` |

---

## LSP Tools Usage

When working on proofs, use these tools frequently:

1. **`lean_goal`**: Check proof state at any line (most important!)
2. **`lean_diagnostic_messages`**: Get compiler errors
3. **`lean_hover_info`**: See types and docs
4. **`lean_local_search`**: Find declarations by name
5. **`lean_loogle`**: Search by type signature (e.g., `List ℕ → ℕ`)
6. **`lean_leansearch`**: Natural language search for lemmas
7. **`lean_multi_attempt`**: Test multiple tactics without editing

**Search Decision Tree**:
1. "Does X exist locally?" → `lean_local_search`
2. "I need a lemma that says X" → `lean_leansearch`
3. "Find lemma with type pattern" → `lean_loogle`
4. "What closes this goal?" → `lean_state_search`

---

## Common Pitfalls

1. **Off-by-one errors**: Remember `Fin n` has elements `0..n-1`
2. **Empty lists**: Handle `[]` case in all operations
3. **Zero strides**: `d = 0` means projection (dimension ignored)
4. **Divisibility**: Use `Nat.dvd` for divisibility checks
5. **Positive naturals**: `PNat` vs `ℕ` - be consistent
6. **Composition order**: `g ∘ f` means "first f, then g"

---

## Success Criteria

1. All core data structures implemented with `DecidableEq`
2. Operations compute correctly (verified via `#eval`)
3. Correspondence theorem proven
4. Functor laws proven
5. Agreement theorems proven
6. Tests match Python reference implementation results

---

## Implementation Status

### Completed (Phase 1: Core Layout Operations)

| File | Contents | Status |
|------|----------|--------|
| `CuTe/Layout/Defs.lean` | `ShapeStridePair`, `FlatLayout`, `NestedTuple`, `Profile` | ✓ |
| `CuTe/Layout/Order.lean` | Lexicographic ordering `⪯`, sorting | ✓ |
| `CuTe/Layout/Tractable.lean` | `IsTractable`, `IsNonDegenerate`, `isCompact` | ✓ |
| `CuTe/Layout/Operations.lean` | `coalesce`, `complement`, `concat`, coordinate ops | ✓ |

### Verified Test Results

```lean
-- All match Python reference implementation:
coalesce [(2,1), (2,2), (2,4)]     = [(8,1)]        ✓
coalesce [(2,1), (3,4)]           = [(2,1), (3,4)]  ✓
coalesce [(2,1), (2,2), (3,6)]    = [(4,1), (3,6)]  ✓
complement [(2,1), (3,2)] 12      = [(2,6)]         ✓
complement [(2,1), (3,2)] 6       = []              ✓
isTractable [(2,1), (3,2)]        = true            ✓
isTractable [(2,1), (3,3)]        = false           ✓
isNonDegenerate [(2,1), (3,2)]    = true            ✓
isNonDegenerate [(1,5)]           = false           ✓
isCompact [(2,1), (3,2)]          = true            ✓
toCoords [(2,1), (3,2)] 5         = [1, 2]          ✓
fromCoords [(2,1), (3,2)] [1,2]   = 5               ✓
```

### Completed (Phase 2: Category Theory)

| File | Contents | Status |
|------|----------|--------|
| `CuTe/Category/Fin0.lean` | Pointed finite sets `Fin₀` as `Option (Fin n)` | ✓ |
| `CuTe/Category/Tuple.lean` | Category Tuple, morphisms, `toLayout` functor | ✓ |
| `CuTe/Morphism/Encode.lean` | `layoutToMorphism`, `morphismToLayout`, tests | ✓ (sorries in proofs) |

#### Phase 2 Test Results

```lean
-- Morphism → Layout (via toLayout)
(TupleMorphism.id [2,3]).toLayout = [(2,1), (3,2)]   ✓

-- Layout → Codomain extraction
layoutToCodomain [(2,1), (3,2)]   = [2, 3]           ✓
layoutToCodomain [(2,0), (3,1)]   = [3]              ✓  -- zero-stride filtered

-- Stride position mapping
findStridePosition [(2,1), (3,2)] 1 = some 0        ✓
findStridePosition [(2,1), (3,2)] 2 = some 1        ✓
findStridePosition [(2,1), (3,2)] 0 = none          ✓

-- Layout map function
layoutMapFun [(2,1), (3,2)] 0 = some 0              ✓
layoutMapFun [(2,1), (3,2)] 1 = some 1              ✓
```

### Next Phase: Proofs and Extensions

| File | Contents | Status |
|------|----------|--------|
| `CuTe/Morphism/Encode.lean` | `dim_preserve` and `injective` proofs | Pending |
| `CuTe/Category/Nest.lean` | Category Nest for nested tuples | Pending |
| `CuTe/Category/Functor.lean` | Realization functor `|·|` | Pending |
| `CuTe/Morphism/Compose.lean` | Morphism composition | Pending |

### Key Theorems

- [ ] `dim_preserve`: Dimension preservation in `layoutToMorphism`
- [ ] `injective`: Injectivity away from basepoint in `layoutToMorphism`
- [ ] Correspondence theorem (tractable layouts ↔ tuple morphisms)
- [ ] Functor laws (`|g ∘ f| = |g| ∘ |f|`)
- [ ] Coalesce preserves layout function
- [ ] Complement involution
- [ ] Agreement theorems (layout ops = morphism ops)
