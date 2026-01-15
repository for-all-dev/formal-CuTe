# Lean Programming Environment - Complete Setup

This document describes the fully configured Lean programming environment with all available tools and capabilities.

## Project Configuration

- **Lean Version**: 4.26.0
- **Mathlib Version**: v4.26.0
- **Project Name**: CuTe (Computational Theory Environment)

## Available LSP Tools

### 1. Core Navigation Tools

#### `lean_file_outline`
Get a token-efficient overview of a file's structure, including imports and declarations with type signatures.

**Example Usage**:
```
File: CuTe/Examples.lean
- Imports: Mathlib.Tactic, Mathlib.Data.Nat.Basic
- Declarations: greeting, double, double_is_even, factorial, sumList, etc.
```

#### `lean_hover_info`
Get detailed type signatures and documentation for any symbol. Column must be at the START of the identifier.

**Example**:
```
Symbol: double at CuTe/Examples.lean:18:44
Type: double (n : ℕ) : ℕ
```

#### `lean_diagnostic_messages`
Get all compiler errors, warnings, and info messages for a file.

**Status**: ✓ All files compile without errors

### 2. Proof Development Tools

#### `lean_goal`
View proof goals at any position. Omit column to see goals_before and goals_after.

**Example from CuTe/Examples.lean:36**:
```
goals_before: case succ
              n : ℕ
              ih : 0 < factorial n
              ⊢ 0 < factorial (n + 1)

goals_after:  case succ
              n : ℕ
              ih : 0 < factorial n
              ⊢ 0 < factorial n
```

#### `lean_multi_attempt`
Test multiple tactics without modifying the file. Returns goal state for each attempt.

**Example from CuTe/Examples.lean:24**:
Tried: ["simp", "ring", "omega", "rfl"]
- `ring`: ✓ Closes goal
- `omega`: ✓ Closes goal
- `simp`: ✗ Made no progress
- `rfl`: ✗ Not definitionally equal

#### `lean_term_goal`
Get the expected type at a position (useful for term mode).

#### `lean_completions`
Get IDE-style autocompletions at any position in incomplete code.

### 3. Search Tools

#### Local Search

**`lean_local_search`**: Fast search for declarations in the current project and dependencies.

**Example**:
```
Query: "Nat.add"
Result: Nat.add_choose_eq in Mathlib/Data/Nat/Choose/Vandermonde.lean
```

#### Online Search (Rate Limited)

**`lean_leansearch`** (3 requests/30s): Natural language search for Mathlib lemmas.

**Example**:
```
Query: "sum of two even numbers is even"
Results:
- Even.add: ∀ {α : Type} [AddCommSemigroup α] {a b : α}, Even a → Even b → Even (a + b)
- Nat.even_add: ∀ {m n : Nat}, Even (m + n) ↔ (Even m ↔ Even n)
- Int.even_add: ∀ {m n : Int}, Even (m + n) ↔ (Even m ↔ Even n)
```

**`lean_loogle`** (3 requests/30s): Type signature pattern matching.

**Example**:
```
Query: "(?a → ?b) → List ?a → List ?b"
Results:
- List.map: {α β : Type} (f : α → β) (l : List α) : List β
- List.mapTR: {α β : Type} (f : α → β) (as : List α) : List β
```

**`lean_leanfinder`** (10 requests/30s): Semantic search by mathematical concept.

**`lean_state_search`** (3 requests/30s): Find lemmas that could close a specific goal.

**Example**:
```
Goal: n m : ℕ, h : n = m ⊢ m = n
Suggestions: Nat.dist_eq_zero, finCongr_eq_equivCast, Fin.cast_eq_cast, etc.
```

**`lean_hammer_premise`** (3 requests/30s): Get premise suggestions for automation tactics.

**Example Results**: Nat.mul_comm, Nat.mul_assoc, Nat.add_sub_cancel_left, etc.

### 4. Advanced Tools

#### `lean_declaration_file`
Find the file where a symbol is declared (must be present in current file first).

#### `lean_run_code`
Execute standalone Lean code snippets (must include all imports).

#### `lean_build`
Rebuild the project and restart LSP server. **SLOW** - only use when needed (e.g., new imports).

#### `lean_profile_proof`
Profile a theorem to identify performance bottlenecks. Shows per-line timing.

## Example Files

### CuTe/Basic.lean
Simple definitions demonstrating basic functionality.

### CuTe/Examples.lean
Comprehensive examples including:
- Simple definitions and functions
- Theorems with proofs (induction, omega, simp)
- Pattern matching
- Type classes and instances
- Dependent types
- List operations with proofs

**Key Theorems**:
- `double_is_even`: Proves that double of any number is even
- `factorial_pos`: Proves factorial is always positive
- `sumList_append`: Distributive property of list sum
- `replicate_length`: Length property of replicate function

### CuTe/TestSearch.lean
Test file for demonstrating search tools.

## Lean Options

Configured in `lakefile.toml`:
```toml
pp.unicode.fun = true           # Pretty-print `fun a ↦ b`
relaxedAutoImplicit = false     # Strict implicit handling
weak.linter.mathlibStandardSet = true  # Enable Mathlib linters
maxSynthPendingDepth = 3        # Type class synthesis depth
```

## Search Strategy Decision Tree

1. **"Does X exist locally?"** → `lean_local_search`
2. **"I need a lemma that says X"** → `lean_leansearch`
3. **"Find lemma with type pattern"** → `lean_loogle`
4. **"What's the Lean name for concept X?"** → `lean_leanfinder`
5. **"What closes this goal?"** → `lean_state_search`
6. **"What to feed simp?"** → `lean_hammer_premise`

After finding a name: use `lean_local_search` to verify, then `lean_hover_info` for signature.

## Working with Proofs

### Best Practices

1. **Use `lean_goal`** frequently to understand the current proof state
2. **Use `lean_multi_attempt`** to test multiple tactics before committing
3. **Use search tools** to find relevant lemmas before trying to prove from scratch
4. **Check diagnostics** regularly to catch errors early
5. **Profile slow proofs** with `lean_profile_proof` to optimize

### Common Tactics Available

- `rfl`: Reflexivity
- `simp`: Simplification with lemmas
- `omega`: Linear arithmetic
- `ring`: Ring arithmetic
- `induction`: Inductive proofs
- `aesop`: Automated reasoning

## Status Summary

✓ Lean toolchain installed (v4.26.0)
✓ Mathlib dependency configured (v4.26.0)
✓ LSP server running and responsive
✓ All core tools tested and working
✓ Search tools configured (rate limits active)
✓ Example files compile without errors
✓ Proof goal inspection working
✓ Multi-tactic testing functional
✓ Documentation complete

## Next Steps

To use this environment:

1. Edit files in the `CuTe/` directory
2. Use LSP tools to navigate and understand code
3. Use search tools to find relevant Mathlib lemmas
4. Use proof development tools to build and verify proofs
5. Use `lean_build` only when adding new dependencies

**Environment Ready for Development!**
