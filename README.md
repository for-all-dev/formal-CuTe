# CuTe Layouts in Lean 4

A Lean 4 formalization of [Categorical Foundations for CuTe Layouts](https://research.colfax-intl.com/categorical-foundations-for-cute-layouts/).

## What is CuTe?

CuTe (CUDA Templates) is NVIDIA's tensor layout library. This project formalizes its mathematical foundations: the category **Tuple** whose morphisms correspond to non-degenerate tractable layouts.

## Structure

```
CuTe/
├── Layout/           # Core layout types and operations
│   ├── Defs.lean     # ShapeStridePair, FlatLayout
│   ├── Order.lean    # Lexicographic ordering ⪯
│   ├── Tractable.lean# Tractability predicate
│   └── Operations.lean # coalesce, complement
├── Category/         # Categorical framework
│   ├── Fin0.lean     # Pointed finite sets
│   └── Tuple.lean    # Category Tuple, morphisms
└── Morphism/
    └── Encode.lean   # Layout ↔ Morphism bijection
```

## Key Definitions

- **Layout**: List of (shape, stride) pairs defining a memory mapping
- **Tractable**: Strides satisfy divisibility conditions
- **TupleMorphism**: Dimension-preserving map between tuples
- **Correspondence**: Tractable layouts ↔ tuple morphisms in standard form

## Building

```bash
lake build
```

## References

- [Paper](https://research.colfax-intl.com/categorical-foundations-for-cute-layouts/)
- [Python reference](https://github.com/ColfaxResearch/layout-categories)
- [CLAUDE.md](./CLAUDE.md) for implementation details
