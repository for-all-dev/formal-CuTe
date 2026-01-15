# Lean LSP Quick Reference

## Most Important Tools (Use These First!)

### 1. `lean_goal` - See Proof State
```
When: During any proof
Usage: Check line number where you want to see goals
Omit column to see before/after transformation
```

### 2. `lean_local_search` - Find Declarations
```
When: Before trying any lemma name
Usage: Search for "Nat.add", "List.map", etc.
Fast and works offline
```

### 3. `lean_leansearch` - Natural Language Search (3/30s)
```
When: "I need a lemma that says..."
Usage: "sum of two even numbers is even"
Returns: Exact lemma names with types
```

### 4. `lean_multi_attempt` - Test Multiple Tactics
```
When: Unsure which tactic to use
Usage: ["simp", "ring", "omega", "aesop"]
Returns: Which ones close the goal
```

### 5. `lean_diagnostic_messages` - Check Errors
```
When: After editing
Usage: See all errors/warnings in a file
Quick sanity check
```

## Search Decision Tree

```
Need to find something?
├─ Is it a local definition? → lean_local_search
├─ Describe in natural language? → lean_leansearch
├─ Have a type pattern? → lean_loogle
├─ Know the concept name? → lean_leanfinder
├─ Want to close a goal? → lean_state_search
└─ Need premises for simp/aesop? → lean_hammer_premise
```

## Common Workflows

### Writing a New Proof
1. Write theorem statement
2. Add `by` and check goal with `lean_goal`
3. Use `lean_leansearch` to find relevant lemmas
4. Use `lean_multi_attempt` to test tactics
5. Check with `lean_diagnostic_messages`

### Stuck on a Goal?
1. Use `lean_goal` to see exact goal state
2. Use `lean_state_search` to find closing lemmas
3. Use `lean_hammer_premise` for simp hints
4. Try `lean_multi_attempt` with ["simp", "omega", "ring", "aesop"]

### Finding a Lemma
1. Try `lean_local_search` first (fast)
2. If not found, use `lean_leansearch` with description
3. Or use `lean_loogle` with type pattern
4. Verify with `lean_hover_info` after finding

### Understanding Code
1. Use `lean_file_outline` for file structure
2. Use `lean_hover_info` on identifiers
3. Use `lean_declaration_file` to find source
4. Use `lean_goal` to understand proof flow

## Rate Limits (Per 30 seconds)
- lean_leansearch: 3 requests
- lean_loogle: 3 requests
- lean_state_search: 3 requests
- lean_hammer_premise: 3 requests
- lean_leanfinder: 10 requests

## Common Tactics Quick Reference

```lean
-- Equality and reflexivity
rfl                    -- Reflexive equality
symm                   -- Symmetry
trans                  -- Transitivity

-- Simplification
simp                   -- Simplify with lemmas
simp [h]              -- Simplify using h
simp only [...]       -- Simplify with specific lemmas

-- Arithmetic
omega                  -- Linear arithmetic solver
ring                   -- Ring arithmetic solver
norm_num               -- Numerical normalization

-- Logic
intro                  -- Introduce hypothesis
apply                  -- Apply a theorem
exact                  -- Provide exact proof term

-- Induction/Recursion
induction n with       -- Structural induction
cases h                -- Case analysis

-- Automation
aesop                  -- Automated reasoning
decide                 -- Decidable propositions
```

## File Locations

- Main library: `CuTe/`
- Examples: `CuTe/Examples.lean`
- Tests: `CuTe/TestSearch.lean`
- Docs: `docs/`

## Tips

- Always use `lean_local_search` before assuming a lemma doesn't exist
- Use `lean_multi_attempt` to explore - it doesn't modify files
- When proof is slow, use `lean_profile_proof` to find bottlenecks
- Check `lean_diagnostic_messages` after any significant changes
- Only use `lean_build` when adding new imports (it's slow!)
- Use `lean_goal` without column to see tactic transformations

## Error Messages

- "no goals to be solved" → Remove unnecessary tactics
- "unsolved goals" → Use `lean_goal` to see remaining goals
- "unknown identifier" → Use `lean_local_search` or `lean_leansearch`
- Timeout → Consider simplifying proof or using `lean_profile_proof`

## Environment Info

- Lean: v4.26.0
- Mathlib: v4.26.0
- Project: CuTe
- LSP: Active and running
