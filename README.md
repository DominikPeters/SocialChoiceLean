# SocialChoiceLean

A Lean 4 formalization of single-winner voting theory, including classical impossibility theorems and axiomatic properties of voting rules.

## Overview

This library formalizes key results in social choice theory, where:
- **Input**: Preference profiles (each voter submits a complete linear ordering over candidates)
- **Output**: A set of tied winners (nonempty subset of candidates)

The formalization covers foundational definitions, axiomatic properties of voting rules, specific voting rule implementations, and several landmark impossibility theorems.

## Credits

This package is a "vibe-proving" effort; the code is written mostly by by gpt-5.2, gpt-5.2-codex, and gpt-5.1-codex-max, under the supervision of Dominik Peters, with occasional input from Claude Opus 4.5 and Gemini 3 Flash.

Theorems about the Split Cycle rule were translated from the `Formalized-Voting` lean3 package (https://github.com/chasenorman/Formalized-Voting) described in the paper "[Voting Theory in the Lean Theorem Prover](https://arxiv.org/abs/2110.08453)" by Wesley H. Holliday, Chase Norman, and Eric Pacuit.

## Future Work

* Unify definitions of independence of clones
* Independence of universal bottom -> into own file; prove Black satisfies it
* Additional voting rules: Schulze, Ranked Pairs, Copeland etc.
* More axioms: Smith criterion.
* Set extension infrastructure; strong Fishburn participation / strong Fishburn strategyproofness, implication to resolute participation / resolute strategyproofness after lexicographic tie-breaking. Kelly implies Fishburn type stuff.
* Metric distortion: lower bound 3, upper bounds for various rules.
* Elementary scoring rule characterizations of plurality, veto, and Borda.
* May's theorem
* All scoring elimination rules fail monotonicity.
* Campbell-Kelly theorem on the Condorcet domain.
* Proportional veto core
* Stretch goal: Young's scoring rule characterization.

## Building

This project requires Lean 4 and Mathlib. To build:

```bash
lake exe cache get   # Download Mathlib cache
lake build
```

## Project Structure

```
SocialChoice/
├── Profile.lean              # Core definitions: profiles, preferences, voting rules
├── Meta.lean                 # Meta-level predicates and custom attributes
├── Rank.lean                 # Ranking and position utilities
├── Margin.lean               # Pairwise margin calculations
├── Cycles.lean               # Cycle detection in preference relations
├── ListBallot.lean           # Computational ballot infrastructure
├── Examples.lean             # Concrete profile examples
├── Axioms/                   # Axiomatic properties of voting rules
├── Rules/                    # Specific voting rule implementations
│   ├── ScoringRules/         # Positional scoring rules
│   ├── ScoringElimination/   # Iterated elimination rules
│   ├── SplitCycle/           # Split Cycle rule
│   └── Minimax/              # Minimax rule
└── Impossibilities/          # Impossibility theorems
    ├── GibbardSatterthwaite/ # Gibbard-Satterthwaite theorem
    ├── DugganSchwartz/       # Duggan-Schwartz lemmas
    └── ...                   # Other incompatibility results
```

## Core Definitions

### Profiles and Preferences (`Profile.lean`)

```lean
structure Profile (V A : Type) [Fintype V] [Fintype A] where
  pref : V → LinearOrder A

abbrev VotingRule :=
  ∀ {V A : Type} [Fintype V] [Fintype A], Profile V A → Finset A

def IsVotingRule (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (P : Profile V A), (f P).Nonempty
```

Key predicates:
- `Prefers P v a b`: Voter `v` prefers `a` to `b` in profile `P`
- `TopRank P v c`: Candidate `c` is ranked first by voter `v`
- `BottomRank P v c`: Candidate `c` is ranked last by voter `v`
- `StrictMajority S`: Voter set `S` has more than 50% of all voters

Profile operations:
- `permuteVoters`: Relabel voters by a permutation
- `permuteCandidates`: Relabel candidates by a permutation
- `addVoter`: Add a voter to a profile
- `unionProfiles`: Combine disjoint electorates
- `restrictCandidates`: Restrict to a subset of candidates

### Margins (`Margin.lean`)

```lean
def margin (P : Profile V A) (a b : A) : Int :=
  (votersPreferring P a b).card - (votersPreferring P b a).card

def margin_pos (P : Profile V A) (a b : A) : Prop :=
  0 < margin P a b
```

Key properties proven:
- `margin_antisymmetric`: margin(a,b) = -margin(b,a)
- `self_margin_zero`: margin(a,a) = 0
- `margin_pos_asymm`: margin positivity is asymmetric

## Axioms

The library formalizes the following axiomatic properties of voting rules:

| Axiom | File | Description |
|-------|------|-------------|
| **Resolute** | `Resolute.lean` | Rule always returns exactly one winner |
| **Unanimity** | `Unanimity.lean` | If all voters rank `c` first, `c` wins alone |
| **Anonymity** | `Anonymity.lean` | Relabeling voters doesn't change winners |
| **Neutrality** | `Neutrality.lean` | Relabeling candidates permutes winners accordingly |
| **Pareto Efficiency** | `Pareto.lean` | If everyone prefers `a` to `b`, then `b` cannot win |
| **Condorcet Consistency** | `Condorcet.lean` | The Condorcet winner (if exists) wins alone |
| **Condorcet Loser Avoidance** | `Condorcet.lean` | The Condorcet loser cannot win |
| **Monotonicity** | `Monotonicity.lean` | Improving a winner's position keeps them winning |
| **Majority Criterion** | `Majority.lean` | If a majority ranks `c` first, `c` wins alone |
| **Majority Loser Criterion** | `Majority.lean` | If a majority ranks `c` last, `c` cannot win |
| **Participation** | `Participation.lean` | Adding a voter doesn't hurt their preferred candidates |
| **Reinforcement** | `Reinforcement.lean` | Common winners in disjoint electorates win in union |
| **Dictatorship** | `Dictatorship.lean` | Some voter's top choice always wins |
| **Reversal Symmetry** | `Reversal.lean` | Unique winner on `P` isn't unique winner on reversed `P` |
| **Clone Independence** | `Clones.lean` | Adding clones doesn't change outcomes for non-clones |

### Meta-level Infrastructure (`Meta.lean`)

The library provides predicates for reasoning about relationships between rules and axioms:

| Predicate | Description |
|-----------|-------------|
| `Refines f g` | Rule `f` always returns a subset of `g`'s winners |
| `PreservedUnderRefinement Z` | Axiom `Z` transfers from coarser to finer rules |
| `PreservedUnderCoarsening Z` | Axiom `Z` transfers from finer to coarser rules |
| `Implies Z₁ Z₂` | Axiom `Z₁` implies axiom `Z₂` for all rules |

Custom attributes `@[scAxiom]` and `@[scRule]` tag definitions for documentation tooling.

### Strategyproofness (`Strategyproofness.lean`)

Three variants of strategyproofness are formalized:

```lean
-- For resolute rules: no voter can benefit by misreporting
def ResoluteStrategyproofness (f : VotingRule) (_hf : Resolute f) : Prop :=
  ∀ P v ballot x y,
    f P = {x} → f (updateProfile P v ballot) = {y} → ¬ Prefers P v y x

-- For multi-winner rules (Duggan-Schwartz):
def OptimistStrategyproof (f : VotingRule) : Prop :=
  -- No voter can make their best outcome strictly better

def PessimistStrategyproof (f : VotingRule) : Prop :=
  -- No voter can make their worst outcome strictly better
```

## Voting Rules

### Scoring Rules (`ScoringRules/`)

Generic positional scoring rules where each position earns points:

| Rule | Scoring Vector | Description |
|------|----------------|-------------|
| **Plurality** | (1, 0, 0, ..., 0) | Most first-place votes wins |
| **Borda** | (m-1, m-2, ..., 1, 0) | Points based on rank position |
| **Veto** | (1, 1, ..., 1, 0) | All ranks score except last place |

Properties proven for scoring rules:
- Anonymity
- Neutrality
- Pareto efficiency
- Monotonicity (for strictly decreasing scores)
- Reinforcement

### Elimination Rules (`ScoringElimination/`)

Iterative elimination rules with parallel-universe tie-breaking:

| Rule | Elimination Criterion |
|------|----------------------|
| **Instant Runoff Voting (IRV)** | Eliminate lowest plurality score |
| **Baldwin** | Eliminate lowest Borda score |
| **Coombs** | Eliminate highest last-place votes |

**Theorem**: IRV satisfies the Condorcet loser criterion (`irv_condorcet_loser_criterion`)

### Pairwise Rules

**Split Cycle** (`SplitCycle/`): A defeats B if margin(A,B) > 0 and there's no cycle containing A and B where all margins are at least margin(A,B). Winners are undefeated candidates.

Properties proven:
- Condorcet consistency
- Condorcet loser avoidance
- Pareto efficiency
- Monotonicity
- Reversal symmetry
- Clone independence

**Minimax** (`Minimax/`): Winner minimizes their maximum pairwise loss.

Properties proven:
- Condorcet consistency

## Impossibility Theorems

### Gibbard-Satterthwaite Theorem

**File**: `Impossibilities/GibbardSatterthwaite/Main.lean`

```lean
theorem gibbard_satterthwaite
    (hcardA : 3 ≤ Fintype.card A)
    (f : VotingRule)
    (hf_res : Resolute f)
    (hf_unan : Unanimity f)
    (hf_sp : ResoluteStrategyproofness f hf_res) :
    ∃ d : V, ∀ P : Profile V A, f P = {topChoice P d}
```

**Statement**: With at least 3 candidates, any resolute, unanimous, strategyproof voting rule must be dictatorial.

**Proof structure** (strong induction on number of voters):
- Base case (`BaseCase.lean`): 1 voter case
- Inductive step via voter cloning technique
  - Case 1 (`InductionStepCase1.lean`): Dictator in cloned rule is not the cloned voter
  - Case 2 (`InductionStepCase2.lean`): Dictator is the cloned voter

### Condorcet-Strategyproofness Incompatibility

**File**: `Impossibilities/CondorcetStrategyproofness.lean`

```lean
theorem no_resolute_condorcet_strategyproof_3x3
    (f : VotingRule) (hf : Resolute f) :
    CondorcetConsistency f → ResoluteStrategyproofness f hf → False
```

**Statement**: With 3 voters and 3 candidates, no resolute rule can satisfy both Condorcet consistency and strategyproofness.

**Proof**: Explicit construction using the Condorcet cycle profile.

### Condorcet-Participation Incompatibility

**File**: `Impossibilities/CondorcetParticipation.lean`

```lean
theorem no_resolute_condorcet_participation_m4_n12 :
    ¬ ∃ (f : VotingRule) (hf : Resolute f),
      CondorcetConsistency f ∧ ResoluteParticipation f hf
```

**Statement**: No resolute rule can satisfy both Condorcet consistency and participation.

**Proof**: Computer-aided proof using explicit 12-voter, 4-candidate profiles (following Brandt et al. 2016 / Peters 2019).

### Condorcet-Reinforcement Incompatibility

**File**: `Impossibilities/CondorcetReinforcement.lean`

```lean
theorem no_condorcet_subset_reinforcement_9
    (f : VotingRule) (hf : IsVotingRule f)
    (hcond : CondorcetConsistency f) (hsub : SubsetReinforcement f) : False
```

**Statement**: No voting rule can satisfy both Condorcet consistency and (subset) reinforcement.

**Proof**: Explicit construction using 9-voter, 3-candidate profiles.

### Duggan-Schwartz Lemmas

**File**: `Impossibilities/DugganSchwartz/DownMonotonicity.lean`

```lean
theorem downMonotonicity_of_opt_pess_sp (f : VotingRule)
    (hf_total : IsVotingRule f)
    (hf_opt : OptimistStrategyproof f)
    (hf_pess : PessimistStrategyproof f) :
    DownMonotonicitySingleton f
```

**Statement**: Any voting rule satisfying both optimist and pessimist strategyproofness has down-monotonicity for singleton winners.

This is Lemma 2.4 from Taylor's "The Manipulability of Voting Systems" (2002).

## Computational Infrastructure

### ListBallot (`ListBallot.lean`)

Provides decidable ballot representations for computational verification:

```lean
structure ListBallot (n : Nat) where
  ranking : Fin n → Nat
  isPermutation : ranking.Bijective
```

Key operations:
- `isTopOfList`: Check if candidate is at top
- `prefersInList`: Check pairwise preference
- `countPrefers`: Count voters with given preference
- `marginList`: Compute pairwise margin

Bridge lemmas connect abstract definitions to computational ones:
- `prefers_iff_prefersInList`
- `topRank_iff_isTopOfList`
- `margin_eq_marginList`

### Examples (`Examples.lean`)

Concrete profile constructions demonstrating:
- 3-voter, 3-candidate Condorcet cycle
- 3-voter, 4-candidate Condorcet winner example
- Computational verification using the `decide` tactic

## References

The formalization follows results from:

- Gibbard, A. (1973). Manipulation of voting schemes: A general result. *Econometrica*.
- Satterthwaite, M. (1975). Strategy-proofness and Arrow's conditions. *Journal of Economic Theory*.
- Taylor, A.D. (2002). The manipulability of voting systems. *The American Mathematical Monthly*.
- Brandt, F., Geist, C., & Peters, D. (2016). Optimal bounds for the no-show paradox via SAT solving. *AAMAS*.
- Peters, D. (2019). *Proportionality and Strategyproofness in Multiwinner Elections*. DPhil thesis, Oxford.

## License

MIT License
