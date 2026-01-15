# CuTe Layouts in Lean 4

A Lean 4 formalization of [Categorical Foundations for CuTe Layouts](https://research.colfax-intl.com/categorical-foundations-for-cute-layouts/).

## What is CuTe?

CuTe (CUDA Templates) is NVIDIA's tensor layout library. This project formalizes its mathematical foundations: the category **Tuple** whose morphisms correspond to non-degenerate tractable layouts.

## Structure

```
CuTe/
├── Layout/
│   ├── Defs.lean       # ShapeStridePair, FlatLayout, NestedTuple
│   ├── Order.lean      # Lexicographic ordering ⪯
│   ├── Tractable.lean  # Tractability, non-degeneracy predicates
│   └── Operations.lean # coalesce, complement, toCoords
├── Category/
│   ├── Fin0.lean       # Pointed finite sets (Option (Fin n))
│   ├── Tuple.lean      # Category Tuple, TupleMorphism, toLayout
│   ├── Functor.lean    # Realization functor, colex
│   └── Nest.lean       # Nested tuples, hierarchical layouts
└── Morphism/
    └── Encode.lean     # Layout ↔ Morphism bijection
```

## Key Concepts

- **Layout**: List of (shape, stride) pairs `[(s₁,d₁), ..., (sₘ,dₘ)]`
- **Tractable**: Divisibility condition on strides
- **TupleMorphism**: Dimension-preserving pointed set map
- **Correspondence**: Tractable layouts ↔ tuple morphisms

## Building

```bash
lake build
```

## References

- [Paper](https://research.colfax-intl.com/categorical-foundations-for-cute-layouts/)
- [Python reference](https://github.com/ColfaxResearch/layout-categories)
- [CLAUDE.md](./CLAUDE.md) for implementation details
