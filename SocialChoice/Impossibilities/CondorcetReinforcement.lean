import SocialChoice.Axioms.Condorcet
import SocialChoice.Axioms.Reinforcement
import SocialChoice.Axioms.Participation
import SocialChoice.Examples
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

namespace SocialChoice

open Finset

namespace CondorcetReinforcement

/-- Successor in the 3-cycle 0→1→2→0. -/
def nextCandidate : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0

/-- Predecessor in the 3-cycle 0→2→1→0. -/
def prevCandidate : Fin 3 → Fin 3
  | 0 => 2
  | 1 => 0
  | 2 => 1

lemma prev_ne_self (c : Fin 3) : prevCandidate c ≠ c := by
  fin_cases c <;> decide

lemma perm_block_main (w : Fin 3) :
    [w, prevCandidate w, nextCandidate w].Perm (List.finRange 3) := by
  fin_cases w <;> decide

lemma perm_block_alt (w : Fin 3) :
    [prevCandidate w, w, nextCandidate w].Perm (List.finRange 3) := by
  fin_cases w <;> decide

/-- The two voter subsets: first six voters and last three voters of the 9-electorate. -/
def voters6 : Finset (Fin 9) :=
  (Finset.univ.filter fun v : Fin 9 => v.val < 6)

def voters3 : Finset (Fin 9) :=
  (Finset.univ.filter fun v : Fin 9 => 6 ≤ v.val)

/-- Ballots for the 9-voter profile: 6-voter double cycle plus 3-voter reinforcement block. -/
def ballots9 (w : Fin 3) : Fin 9 → ListBallot 3
  | ⟨0, _⟩ => ListBallot.mk' [0, 1, 2]
  | ⟨1, _⟩ => ListBallot.mk' [0, 1, 2]
  | ⟨2, _⟩ => ListBallot.mk' [1, 2, 0]
  | ⟨3, _⟩ => ListBallot.mk' [1, 2, 0]
  | ⟨4, _⟩ => ListBallot.mk' [2, 0, 1]
  | ⟨5, _⟩ => ListBallot.mk' [2, 0, 1]
  | ⟨6, _⟩ => ListBallot.mk' [w, prevCandidate w, nextCandidate w] (perm_block_main w)
  | ⟨7, _⟩ => ListBallot.mk' [w, prevCandidate w, nextCandidate w] (perm_block_main w)
  | ⟨8, _⟩ => ListBallot.mk' [prevCandidate w, w, nextCandidate w] (perm_block_alt w)

/-- Full profile on the entire electorate (as an Electorate over `Fin 9`). -/
noncomputable def fullProfile (w : Fin 3) :
    Profile (Electorate (Fin 9) (Finset.univ)) (Fin 3) :=
  { pref := fun v => (ballots9 w v.1).toLinearOrder }

/-- Restrict the full profile to the first 6 voters. -/
noncomputable def profile6 (w : Fin 3) : Profile (Electorate (Fin 9) voters6) (Fin 3) :=
  restrictElectorate (fullProfile w) voters6 (by
    intro x hx; exact (Finset.mem_univ x))

/-- The 6-voter cycle profile does not depend on `w`. -/
lemma profile6_const (w : Fin 3) : profile6 w = profile6 0 := by
  ext v
  cases v with
  | mk val hmem =>
      -- Split on the concrete voter index; impossible cases (≥ 6) close by contradiction.
      fin_cases val <;>
        simp [profile6, fullProfile, restrictElectorate, ballots9, voters6] at hmem ⊢ <;> rfl

/-- Restrict the full profile to the last 3 voters. -/
noncomputable def profile3 (w : Fin 3) : Profile (Electorate (Fin 9) voters3) (Fin 3) :=
  restrictElectorate (fullProfile w) voters3 (by
    intro x hx; exact (Finset.mem_univ x))

/-- Restrict to the union (all voters). -/
noncomputable def profileAll (w : Fin 3) : Profile (Electorate (Fin 9) (voters6 ∪ voters3)) (Fin 3) :=
  restrictElectorate (fullProfile w) (voters6 ∪ voters3) (by
    intro x hx; exact (Finset.mem_univ x))

lemma restrictElectorate_nested {U A : Type} [DecidableEq U] [Fintype A]
    {S T W : Finset U} (hST : S ⊆ T) (hTW : T ⊆ W)
    (Q : Profile (Electorate U W) A) :
    restrictElectorate (restrictElectorate Q T hTW) S hST =
      restrictElectorate Q S (by intro x hx; exact hTW (hST hx)) := by
  cases Q
  rfl

lemma restrict_profileAll_v6 (w : Fin 3) :
    restrictElectorate (profileAll w) voters6
        (by intro x hx; exact Finset.mem_union.mpr (Or.inl hx)) =
      profile6 w := by
  unfold profileAll profile6
  have hST : voters6 ⊆ voters6 ∪ voters3 := by
    intro x hx; exact Finset.mem_union.mpr (Or.inl hx)
  have hTW : voters6 ∪ voters3 ⊆ (Finset.univ : Finset (Fin 9)) := by
    intro x hx; exact Finset.mem_univ x
  simpa [hST, hTW] using
    (restrictElectorate_nested (U := Fin 9) (A := Fin 3)
      (S := voters6) (T := voters6 ∪ voters3) (W := Finset.univ) hST hTW (fullProfile w))

lemma restrict_profileAll_v3 (w : Fin 3) :
    restrictElectorate (profileAll w) voters3
        (by intro x hx; exact Finset.mem_union.mpr (Or.inr hx)) =
      profile3 w := by
  unfold profileAll profile3
  have hST : voters3 ⊆ voters6 ∪ voters3 := by
    intro x hx; exact Finset.mem_union.mpr (Or.inr hx)
  have hTW : voters6 ∪ voters3 ⊆ (Finset.univ : Finset (Fin 9)) := by
    intro x hx; exact Finset.mem_univ x
  simpa [hST, hTW] using
    (restrictElectorate_nested (U := Fin 9) (A := Fin 3)
      (S := voters3) (T := voters6 ∪ voters3) (W := Finset.univ) hST hTW (fullProfile w))

private lemma votersPreferring_profile3_eq_filter (w x y : Fin 3) :
    votersPreferring (profile3 w) x y =
      Finset.univ.filter (fun v => prefersInList (ballots9 w v.1).ranking x y) := by
  ext v
  simp only [votersPreferring, Finset.mem_filter, Finset.mem_univ, true_and]
  change Prefers (profileOfListBallots (ballots9 w)) v.1 x y ↔ _
  exact prefers_iff_prefersInList (ballots9 w) v.1 x y

private lemma votersPreferring_profileAll_eq_filter (w x y : Fin 3) :
    votersPreferring (profileAll w) x y =
      Finset.univ.filter (fun v => prefersInList (ballots9 w v.1).ranking x y) := by
  ext v
  simp only [votersPreferring, Finset.mem_filter, Finset.mem_univ, true_and]
  change Prefers (profileOfListBallots (ballots9 w)) v.1 x y ↔ _
  exact prefers_iff_prefersInList (ballots9 w) v.1 x y

lemma reinforcement_block_condorcet (w : Fin 3) :
    CondorcetWinner (profile3 w) w := by
  classical
  intro d hd
  fin_cases w <;> fin_cases d <;> try (cases hd rfl)
  all_goals
    -- Finite computation on the explicit 3-voter block.
    rw [votersPreferring_profile3_eq_filter]
    simp [StrictMajority, voters3, ballots9, prevCandidate, nextCandidate, prefersInList]
    decide +revert

lemma union_condorcet_prev (w : Fin 3) :
    CondorcetWinner (profileAll w) (prevCandidate w) := by
  classical
  intro d hd
  fin_cases w <;> fin_cases d <;> try (cases hd rfl)
  all_goals
    -- Finite computation on the explicit 9-voter profile.
    rw [votersPreferring_profileAll_eq_filter]
    simp [StrictMajority, voters6, voters3, ballots9, prevCandidate, nextCandidate,
      prefersInList]
    decide +revert

/-! ### Main result -/

end CondorcetReinforcement

open CondorcetReinforcement

/-- No Condorcet-consistent rule satisfying subset reinforcement on 9 voters. -/
theorem no_condorcet_subset_reinforcement
    (f : VotingRule) (hf : IsVotingRule f)
    (hcond : CondorcetConsistency f) (hsub : SubsetReinforcement f) : False := by
  classical
  -- Choose a candidate from the 6-voter cycle profile; make that the reinforcement winner.
  obtain ⟨w, hw⟩ := hf (profile6 0)
  have hw6 : w ∈ f (profile6 w) := by
    have hconst : profile6 w = profile6 0 := profile6_const w
    simpa [hconst] using hw
  -- On the 3-voter reinforcement block, w is Condorcet winner.
  have hw_reinf : f (profile3 w) = {w} :=
    hcond (profile3 w) w (reinforcement_block_condorcet w)
  -- Subset reinforcement lifts w to the combined profile.
  have hw_union : w ∈ f (profileAll w) := by
    have hdisj : Disjoint voters6 voters3 := by
      refine Finset.disjoint_left.mpr ?_
      intro v hv6 hv3
      have hv6' : v.val < 6 := (Finset.mem_filter.mp hv6).2
      have hv3' : 6 ≤ v.val := (Finset.mem_filter.mp hv3).2
      exact (Nat.not_lt_of_ge hv3' hv6')
    have hsubset := hsub (V := voters6) (W := voters3) hdisj
      (P := profile6 w) (Q := profile3 w) (R := profileAll w)
      (by
        -- R restricted to voters6 is profile6 w
        simpa using restrict_profileAll_v6 w
      )
      (by
        -- R restricted to voters3 is profile3 w
        simpa using restrict_profileAll_v3 w
      )
    have hw_inter : w ∈ f (profile6 w) ∩ f (profile3 w) := by
      have hw3 : w ∈ f (profile3 w) := by simp [hw_reinf]
      exact Finset.mem_inter.mpr ⟨hw6, hw3⟩
    exact hsubset hw_inter
  -- But Condorcet consistency forces the predecessor to be the unique winner.
  have hcond_union : f (profileAll w) = {prevCandidate w} :=
    hcond (profileAll w) (prevCandidate w) (union_condorcet_prev w)
  have : w = prevCandidate w := by
    have : w ∈ ({prevCandidate w} : Finset (Fin 3)) := by
      simpa [hcond_union] using hw_union
    simpa using this
  have hneq : prevCandidate w ≠ w := prev_ne_self w
  exact hneq (this.symm)

/-- No Condorcet-consistent rule satisfying reinforcement on 9 voters. -/
theorem no_condorcet_reinforcement
    (f : VotingRule) (hf : IsVotingRule f)
    (hcond : CondorcetConsistency f) (hrein : Reinforcement f) : False := by
  apply no_condorcet_subset_reinforcement f hf hcond
  exact reinforcement_subset hrein

end SocialChoice
