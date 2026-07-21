import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Function.Iterate
import SocialChoice.Rank
import SocialChoice.Rules.ScoringRules.Defs

namespace SocialChoice

open Finset
open scoped BigOperators

/-!
# Scoring Elimination Rules

This file defines scoring elimination rules (also known as iterated scoring rules).

The elimination scoring rule associated with a scoring system `s` selects a winning candidate
by repeatedly removing a candidate with the lowest s-score from the profile, until only one
candidate remains, who is the winner.

When there are ties for the lowest score, we use parallel-universe tie-breaking: we recursively
explore all branches by removing each lowest-scoring candidate, and take the union of all
resulting winners.

## Main definitions

* `lowestScoring`: The set of candidates with the minimum score in a profile.
* `scoringEliminationAux`: Auxiliary function implementing the elimination procedure.
* `scoringEliminationRule`: The main voting rule.
-/

-- Compute the set of lowest-scoring candidates
noncomputable def lowestScoring {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (score : Nat → Int) : Finset A := by
  classical
  by_cases h : (Finset.univ : Finset A).Nonempty
  · let minScore : Int :=
      (Finset.univ.image (fun c => scoreCandidate P score c)).min' (by
        simpa [Finset.Nonempty] using h)
    exact (Finset.univ.filter (fun c => scoreCandidate P score c = minScore))
  · exact ∅

lemma lowestScoring_nonempty {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (score : Nat → Int) (hA : (Finset.univ : Finset A).Nonempty) :
    (lowestScoring P score).Nonempty := by
  classical
  simp only [lowestScoring, hA, dite_true]
  let scoreSet := Finset.univ.image (fun c => scoreCandidate P score c)
  have hScoreNonempty : scoreSet.Nonempty := by
    simpa [scoreSet, Finset.Nonempty] using hA.image (fun c => scoreCandidate P score c)
  let minScore := scoreSet.min' hScoreNonempty
  have hMinMem : minScore ∈ scoreSet := Finset.min'_mem scoreSet hScoreNonempty
  rcases Finset.mem_image.mp hMinMem with ⟨c, _, hc⟩
  refine ⟨c, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  -- hc : scoreCandidate P score c = minScore, goal needs the same
  convert hc using 2

lemma lowestScoring_subset {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (score : Nat → Int) :
    lowestScoring P score ⊆ Finset.univ := by
  intro c hc
  exact Finset.mem_univ c

lemma scoreCandidate_le_of_mem_lowestScoring {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (score : Nat → Int) {c e : A}
    (hc : c ∈ lowestScoring P score) :
    scoreCandidate P score c ≤ scoreCandidate P score e := by
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · -- Unfold `lowestScoring` in the nonempty case.
    simp [lowestScoring, hA] at hc
    -- Work with the score-set and its minimum.
    set scoreSet : Finset Int := (Finset.univ.image (fun a : A => scoreCandidate P score a))
    have hScoreNonempty : scoreSet.Nonempty := by
      simpa [scoreSet, Finset.Nonempty] using hA.image (fun a : A => scoreCandidate P score a)
    set minScore : Int := scoreSet.min' hScoreNonempty
    have hcEq : scoreCandidate P score c = minScore := by
      simpa [scoreSet, minScore] using hc
    have heMem : scoreCandidate P score e ∈ scoreSet := by
      refine Finset.mem_image.mpr ?_
      exact ⟨e, by simp, rfl⟩
    have hminle : minScore ≤ scoreCandidate P score e := by
      -- `min'` is below every member.
      simpa [minScore] using (Finset.min'_le (s := scoreSet) (x := scoreCandidate P score e) heMem)
    -- Rewrite `minScore` as `scoreCandidate ... c`.
    simpa [hcEq.symm] using hminle
  · -- Empty candidate set: `lowestScoring` is empty, so membership is impossible.
    simp [lowestScoring, hA] at hc

lemma lowestScoring_iff_forall_le {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (score : Nat → Int)
    (hA : (Finset.univ : Finset A).Nonempty) (c : A) :
    c ∈ lowestScoring P score ↔
      ∀ d : A, scoreCandidate P score c ≤ scoreCandidate P score d := by
  classical
  let scoreSet : Finset Int := Finset.univ.image (fun a => scoreCandidate P score a)
  have hScoreNonempty : scoreSet.Nonempty := by
    simpa [scoreSet, Finset.Nonempty] using hA.image (fun a => scoreCandidate P score a)
  let minScore : Int := scoreSet.min' hScoreNonempty
  constructor
  · intro hc d
    have hc' : scoreCandidate P score c = minScore := by
      simpa [lowestScoring, hA, scoreSet, minScore] using hc
    have hmem : scoreCandidate P score d ∈ scoreSet := by
      exact Finset.mem_image.mpr ⟨d, by simp, rfl⟩
    have hminle : minScore ≤ scoreCandidate P score d :=
      Finset.min'_le scoreSet _ hmem
    simpa [hc'] using hminle
  · intro hle
    have hmem : scoreCandidate P score c ∈ scoreSet := by
      exact Finset.mem_image.mpr ⟨c, by simp, rfl⟩
    have hminle : minScore ≤ scoreCandidate P score c :=
      Finset.min'_le scoreSet _ hmem
    have hmin_mem : minScore ∈ scoreSet := Finset.min'_mem scoreSet hScoreNonempty
    rcases Finset.mem_image.mp hmin_mem with ⟨d, _hd, hdeq⟩
    have hle' : scoreCandidate P score c ≤ minScore := by
      simpa [hdeq] using hle d
    have hmin_eq : scoreCandidate P score c = minScore := le_antisymm hle' hminle
    have hc : c ∈ (Finset.univ.filter (fun a => scoreCandidate P score a = minScore)) := by
      exact Finset.mem_filter.mpr ⟨by simp, hmin_eq⟩
    simpa [lowestScoring, hA, scoreSet, minScore] using hc

-- Cardinality decreases when removing a candidate
-- These are aliases to the generic lemmas in Profile.lean
lemma card_restrict_lt {A : Type} [Fintype A] [DecidableEq A] (c : A) :
    Fintype.card {x : A // x ≠ c} < Fintype.card A :=
  card_subtype_ne_lt c

-- Note: The generic version is `SocialChoice.card_subtype_ne_eq` in Profile.lean.
-- This alias preserves backward compatibility for code using the `A` naming convention.

-- Lift a finset from a subtype back to the original type
noncomputable def liftFinset {A : Type} [DecidableEq A] {p : A → Prop}
    (s : Finset {x : A // p x}) : Finset A := by
  classical
  exact s.image (fun x => x.val)

lemma liftFinset_subset_of_prop {A : Type} [DecidableEq A] {p : A → Prop}
    (s : Finset {x : A // p x}) :
    ∀ x ∈ liftFinset s, p x := by
  intro x hx
  simp only [liftFinset, Finset.mem_image] at hx
  rcases hx with ⟨y, _, rfl⟩
  exact y.property

lemma mem_liftFinset_iff {A : Type} [DecidableEq A] {p : A → Prop}
    (s : Finset {x : A // p x}) (x : A) :
    x ∈ liftFinset s ↔ ∃ y : {x : A // p x}, y ∈ s ∧ y.1 = x := by
  classical
  simp [liftFinset]

lemma mem_liftFinset_iff_subtype {A : Type} [DecidableEq A] {p : A → Prop}
    (s : Finset {x : A // p x}) (x : A) :
    x ∈ liftFinset s ↔ ∃ hx : p x, (⟨x, hx⟩ : {x : A // p x}) ∈ s := by
  classical
  constructor
  · intro hx
    rcases (mem_liftFinset_iff (s := s) (x := x)).1 hx with ⟨y, hy, hyx⟩
    have hx' : p x := by
      simpa [hyx] using y.property
    refine ⟨hx', ?_⟩
    have hy' : y = ⟨x, hx'⟩ := by
      apply Subtype.ext
      simp [hyx]
    simpa [hy'] using hy
  · rintro ⟨hx, hxmem⟩
    exact (mem_liftFinset_iff (s := s) (x := x)).2 ⟨⟨x, hx⟩, hxmem, rfl⟩

lemma not_mem_liftFinset_removed {A : Type} [DecidableEq A] {c : A}
    (s : Finset {x : A // x ≠ c}) : c ∉ liftFinset s := by
  classical
  intro hc
  -- Unfold `liftFinset` directly at the hypothesis.
  dsimp [liftFinset] at hc
  rcases Finset.mem_image.mp hc with ⟨x, _hx, hxval⟩
  exact x.property (by simpa using hxval)

/-!
## Main elimination procedure

We define the elimination procedure using well-founded recursion on the cardinality
of the candidate set.
-/

-- The core elimination procedure, parameterized by candidate type
noncomputable def scoringEliminationAux
    {V : Type} [Fintype V]
    (score : Nat → Nat → Int)
    : ∀ (A : Type) [Fintype A] [DecidableEq A], Profile V A → Finset A :=
  fun A inst_fin inst_dec P => by
    classical
    letI := inst_fin
    letI := inst_dec
    by_cases hcard : Fintype.card A ≤ 1
    · -- Base case: 0 or 1 candidate
      exact Finset.univ
    · -- Recursive case: eliminate lowest-scoring candidates
      push Not at hcard
      let m := Fintype.card A
      let scoreVec := fun r => score m r
      let L := lowestScoring P scoreVec
      have hL : L.Nonempty := by
        apply lowestScoring_nonempty
        have hne : Nonempty A := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card A)
        exact @Finset.univ_nonempty A _ hne
      -- For each lowest-scoring candidate, recursively compute winners
      have hterm : ∀ c : A, Fintype.card {x : A // x ≠ c} < Fintype.card A :=
        fun c => card_restrict_lt c
      exact L.biUnion (fun c => liftFinset (scoringEliminationAux score _ (restrictProfile P c)))
termination_by A inst_fin _ _ => @Fintype.card A inst_fin
decreasing_by
  exact hterm c

lemma liftWinners_scoringEliminationAux_restrictCandidates_congr
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (score : Nat → Nat → Int) (P : Profile V A)
    {p q : A → Prop} [DecidablePred p] [DecidablePred q]
    (h : p = q) :
    liftWinners (scoringEliminationAux score _ (restrictCandidates P p)) =
      liftWinners (scoringEliminationAux score _ (restrictCandidates P q)) := by
  classical
  cases h
  rename_i instP instQ
  have hinst : instP = instQ := Subsingleton.elim _ _
  cases hinst
  rfl

lemma scoringEliminationAux_decidableEq_congr
    {V A : Type} [Fintype V] [Fintype A]
    (score : Nat → Nat → Int) (P : Profile V A)
    (inst1 inst2 : DecidableEq A) :
    @scoringEliminationAux V _ score A _ inst1 P =
      @scoringEliminationAux V _ score A _ inst2 P := by
  classical
  have hinst : inst1 = inst2 := Subsingleton.elim _ _
  cases hinst
  rfl

-- The scoring elimination rule as a VotingRule
noncomputable def scoringEliminationRule (score : Nat → Nat → Int) : VotingRule :=
  fun {V A} _ _ (P : Profile V A) => by
    classical
    exact scoringEliminationAux score A P

end SocialChoice
