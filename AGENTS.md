## Project Overview

`SocialChoiceLean` is a formalization of social choice theory using the **Lean 4** proof assistant. It leverages **mathlib4** to provide a rigorous framework for studying voting rules, preference profiles, and social choice axioms.

The project includes:
- **Core Abstractions:** Definitions for `Profile`, `VotingRule`, and preference relations.
- **Voting Rules:** Implementations of various rules including Scoring Rules (Borda, Plurality, Veto) and SplitCycle.
- **Axioms:** Formal definitions of properties like Anonymity, Neutrality, Condorcet consistency, Pareto efficiency, and Monotonicity.
- **Proofs:** Formal verification that specific rules satisfy certain axioms, and proofs of impossibility theorems (e.g., Condorcet Strategyproofness).

### Key Technologies
- **Lean 4:** The primary language and theorem prover.
- **Lake:** The build system and package manager for Lean 4.
- **mathlib4:** The standard mathematical library for Lean 4.

## Project Structure

- `SocialChoice/`: The main library directory.
    - `Profile.lean` / `Margin.lean` / ...: Fundamental definitions for preference profiles and voting rules.
    - `Meta.lean`: Meta-level predicates (`Refines`, `Implies`, etc.) and custom attributes.
    - `ListBallot.lean`: Utilities for handling ballots as lists for counterexamples.
    - `Axioms/`: Formal definitions of social choice properties.
    - `Rules/`: Specific voting rule implementations and their properties.
        - `ScoringRules/`: Borda, Plurality, Veto, etc.
        - `SplitCycle/`: Implementation and properties of the SplitCycle rule.
    - `Impossibilities/`: Formalized impossibility results.
- `lakefile.toml`: Configuration for the Lake build system.
- `lean-toolchain`: Specifies the Lean 4 version used (currently `v4.27.0-rc1`).

## Testing

No testing is required as the project focuses on formal proofs. Verification is done through Lean's type checker.

## Development Conventions

- **Naming:** Follows Lean 4 and mathlib conventions (CamelCase for types, snake_case for definitions and theorems).
- **Axioms:** Axioms are typically defined as predicates on `VotingRule` (e.g., `def Anonymity (f : VotingRule) : Prop`).
- **Mathematical Style:** Uses `Fintype` for finite sets of voters and candidates, and `Finset` for result sets.
- **Modularity:** New rules should be added to `SocialChoice/Rules/`, and their axioms to `SocialChoice/Axioms/`.

Note that `native_decide` is not allowed in this project. You can inspect constructions and proofs of existing counterexamples to see patterns used in this project that avoid `native_decide`.

## Meta-level Infrastructure

The file `SocialChoice/Meta.lean` provides predicates and attributes for reasoning about relationships between rules and axioms.

### Custom Attributes

- `@[scAxiom]`: Tag a definition as a social choice axiom (used for documentation tooling).
- `@[scRule]`: Tag a definition as a voting rule.

Example usage:
```lean
@[scAxiom]
def CondorcetConsistency (f : VotingRule) : Prop := ...

@[scRule]
noncomputable def splitCycle : VotingRule := ...
```

### Meta-level Predicates

- `Refines f g`: Rule `f` refines `g` (f always returns a subset of winners of g). Forms a preorder.
- `PreservedUnderRefinement Z`: Axiom `Z` transfers from coarser to finer rules.
- `PreservedUnderCoarsening Z`: Axiom `Z` transfers from finer to coarser rules.
- `Implies Z₁ Z₂`: Axiom `Z₁` implies axiom `Z₂` for all rules. Forms a preorder.

These enable concise derived proofs. For example, if `schulze` refines `splitCycle` and `CondorcetConsistency` is preserved under refinement, then `CondorcetConsistency schulze` follows from `CondorcetConsistency splitCycle`.

### Naming Conventions for Theorems

- `[rule]_[axiom]`: Direct result, e.g., `splitCycle_condorcetConsistency`
- `[rule]_refines_[rule]`: Refinement, e.g., `schulze_refines_splitCycle`
- `[axiom]_preservedUnderRefinement`: Preservation, e.g., `condorcetConsistency_preservedUnderRefinement`
- `[axiom]_implies_[axiom]`: Implication, e.g., `condorcetConsistency_implies_majorityCriterion`

## Using lean-lsp

The user prefers that agents read files directly from the file system using sed or cat. For long files, it can be judicious to read them in chunks. Avoid using the `lean_file_contents` tool since its output is less readable.

For most other tasks, the user prefers that agents use tools provided by the lean-lsp mcp plugin.

When using lean-lsp for the first time, it is useful to call the `lean_diagnostics` tool to make sure that the Lean server is fully initialized and ready to respond to further requests. Occasionally a second call to `lean_diagnostics` may be needed if the first call returns `"success": false` AND `[]`.

Occasionally lean_diagnostics may be broken (transport closed, stale errors, displaying errors in other files). In that case the agent is allowed to run `lake build [filename]` as a fallback, even though this gives less-detailed output.

### Searching mathlib4

When searching for definitions, the user prefers that agents use the `lean_loogle`, `lean_leansearch`, and `lean_leanfinder` tools provided by the lean-lsp mcp plugin. These tools should be used liberally as they can speed up exploration significantly. There are rate limits of several requests per 30 seconds. Given how agents are implemented, this means that for *every* turn, these rate limits will be available, so can be used. (e.g. if the user entered a message, this will have taken >30s so the rate limits will have reset; if the agent requested diagnostics, this also takes sufficient time to reset limits).

Note: these tools only search mathlib4, not the user's code base. For searching the user's code base, the agent should use `rg` and other command-line tools, or `lean_local_search`.

### Debugging

When debugging Lean code, the user prefers that agents use the `lean_diagnostics` tool provided by the lean-lsp mcp plugin. This tool provides detailed diagnostics about errors in Lean code, which can be very helpful for debugging.

The agent should also be aware of the `lean_hover_info` and `lean_goal` tools.

### Fixing "No goals to be solved" errors

If encountering "No goals to be solved" errors at line X, the most common and easiest fix is to just delete line X, without making changes to any other lines. Only if this fails do we need to consider more complex fixes.

### Fixing unnecessary simpa warnings

When the linter suggests "try `simp` instead of `simpa`", the common fixes are:
- Replace `simpa using h` with `simp [h]` or `simp at h` followed by `exact h`.
- Replace `simpa [lemma] using h` with `simp [lemma]` (or `simp [lemma] at h` + `exact h`) if the goal is already definitional.
- If `simp` makes no progress, keep `simpa` but rewrite the proof to `exact` the lemma or add the missing rewrite to the simp set.

## Exception for Copilot in VS Code

When the user is using GitHub Copilot in VS Code, they prefer that agents do not use the lean-lsp diagnostics tool, and instead use the native `get_errors` tool provided by VS Code. This is much faster (10x faster). However, if these are insufficient to solve the problem, then the agent can revert to using the lean-lsp mcp plugin tools as a fallback.
