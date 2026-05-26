# Claude Code Setup for Lean 4

## MCP Servers

The project uses MCP servers configured in `.mcp.json`:

- **[lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp)**: Lean LSP integration for incremental checking, goal display, diagnostics, search, etc.

## Claude Code Plugin

Install the [lean4-skills](https://github.com/cameronfreer/lean4-skills) plugin for guided proving, review, golf, and other Lean workflows:

```bash
claude plugin marketplace add cameronfreer/lean4-skills
claude plugin install lean4
```

## Project Instructions

- `CLAUDE.md` — main project instructions (proof style, workflow, conventions)
- `TACTICS.md` — tactic pitfall log

## Quick Start

```bash
# From repo root
./build.sh

# Or from analysis/ directory
lake exe cache get && lake build

# Build a single file
cd analysis && lake build Analysis.Section_6_1
```
