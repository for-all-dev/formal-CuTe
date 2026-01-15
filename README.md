# CuTe - Computational Theory Environment

A Lean 4 project with comprehensive LSP tooling and Mathlib integration for theorem proving and formal verification.

## Overview

This project provides a complete Lean programming environment with:

- **Lean 4.26.0** with **Mathlib v4.26.0**
- Full LSP integration via `lean-lsp-mcp`
- Comprehensive search tools (local and online)
- Proof development and debugging tools
- Example theorems and proofs

## Project Structure

```
CuTe/
├── CuTe/
│   ├── Basic.lean          # Simple definitions
│   ├── Examples.lean       # Comprehensive examples with proofs
│   └── TestSearch.lean     # Search tool demonstrations
├── docs/
│   ├── LeanEnvironment.md  # Complete environment documentation
│   └── QuickReference.md   # Quick reference for LSP tools
├── lakefile.toml           # Lake build configuration
└── lean-toolchain          # Lean version specification
```

## Features

### LSP Tools Available

- **Navigation**: File outlines, hover info, go-to-definition
- **Proof Development**: Goal inspection, multi-tactic testing
- **Search**: Local search, natural language search, type pattern matching
- **Debugging**: Diagnostics, proof profiling
- **Automation**: State search, premise suggestions

### Example Proofs

The `CuTe/Examples.lean` file includes:

- Basic definitions and functions
- Inductive proofs (factorial properties)
- List operations with correctness proofs
- Type class instances
- Dependent types demonstrations

## Quick Start

### First-Time Setup

If this is your first time cloning the repository, follow the setup instructions:

1. **Install Prerequisites**: See `docs/Setup.md` for detailed instructions
2. **Quick Install** (Linux/macOS):
   ```bash
   # Install uv (Python package manager for lean-lsp-mcp)
   curl -LsSf https://astral.sh/uv/install.sh | sh

   # Build the Lean project
   lake build

   # Configure MCP server (if using Claude Code)
   claude mcp add lean-lsp -s project uvx lean-lsp-mcp
   ```

3. **Verify Setup**: Open Claude Code in this directory and ask "What's in CuTe/Examples.lean?"

For complete setup instructions, see `docs/Setup.md`.

### View Available Tools

See `docs/QuickReference.md` for a quick reference of all LSP tools.

### Run Examples

All example files are already compiled and working:

```lean
-- Check the greeting
#check greeting  -- String

-- Evaluate factorial
#eval factorial 5  -- 120

-- Evaluate list sum
#eval sumList [1, 2, 3, 4, 5]  -- 15
```

### Development Workflow

1. **Write a theorem**: Start with the statement
2. **Check goals**: Use `lean_goal` to see proof state
3. **Find lemmas**: Use `lean_leansearch` or `lean_loogle`
4. **Test tactics**: Use `lean_multi_attempt` to try multiple approaches
5. **Verify**: Check with `lean_diagnostic_messages`

## Documentation

- **Setup Guide**: `docs/Setup.md` - First-time setup instructions
- **Quick Reference**: `docs/QuickReference.md` - LSP tools cheat sheet
- **Environment Guide**: `docs/LeanEnvironment.md` - Complete tool documentation
- **Configuration**: `docs/CONFIGURATION.md` - How MCP is configured for this repo

## Configuration

Lean options configured in `lakefile.toml`:
- Unicode pretty-printing enabled
- Strict auto-implicit handling
- Mathlib linter set active
- Optimized type class synthesis

## Status

✓ Environment fully configured and tested
✓ All LSP tools verified working
✓ Example files compile without errors
✓ Search tools tested (rate limits active)
✓ Documentation complete

## Dependencies

- Lean: v4.26.0
- Mathlib: v4.26.0 (leanprover-community)

## Next Steps

Ready for development! Start by:
1. Reading `docs/QuickReference.md`
2. Exploring `CuTe/Examples.lean`
3. Writing your own theorems in the `CuTe/` directory

---

**Environment Status**: Ready for formal verification and theorem proving!
