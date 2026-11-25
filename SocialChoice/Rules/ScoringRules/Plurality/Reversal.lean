import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Reversal
import SocialChoice.ListBallot
import SocialChoice.Rules.ScoringRules.Plurality.Defs

namespace SocialChoice

open Finset

namespace PluralityReversalCounterexample

def ballotCBA : ListBallot 3 := ListBallot.mk' [2, 1, 0]
def ballotBCA : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballotACB : ListBallot 3 := ListBallot.mk' [0, 2, 1]
def ballotABC : ListBallot 3 := ListBallot.mk' [0, 1, 2]

def ballots : Fin 4 → ListBallot 3
  | 0 => ballotCBA
  | 1 => ballotBCA
  | 2 => ballotACB
  | 3 => ballotABC

noncomputable def profile : Profile (Fin 4) (Fin 3) :=
  profileOfListBallots ballots

private lemma bottomRank_iff_prefersInList {m n : ℕ} (ballots : Fin m → ListBallot n)
    (v : Fin m) (c : Fin n) :
    BottomRank (profileOfListBallots ballots) v c ↔
      ∀ d : Fin n, d ≠ c → prefersInList (ballots v).ranking d c = true := by
  constructor
  · intro h d hd
    exact (prefers_iff_prefersInList ballots v d c).1 (h d hd)
  · intro h d hd
    exact (prefers_iff_prefersInList ballots v d c).2 (h d hd)

private lemma topRank_reverse_profile_iff_bottomRank {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (c : A) :
    TopRank (reverse_profile P) v c ↔ BottomRank P v c := by
  constructor
  · intro h d hd
    simpa using (h d hd)
  · intro h d hd
    simpa using (h d hd)

private lemma votersBottom_profile_0 :
    votersBottom profile (0 : Fin 3) = ({0, 1} : Finset (Fin 4)) := by
  ext v
  simp only [votersBottom, profile, bottomRank_iff_prefersInList, mem_filter, mem_univ, true_and]
  revert v
  decide

private lemma votersBottom_profile_1 :
    votersBottom profile (1 : Fin 3) = ({2} : Finset (Fin 4)) := by
  ext v
  simp only [votersBottom, profile, bottomRank_iff_prefersInList, mem_filter, mem_univ, true_and]
  revert v
  decide

private lemma votersBottom_profile_2 :
    votersBottom profile (2 : Fin 3) = ({3} : Finset (Fin 4)) := by
  ext v
  simp only [votersBottom, profile, bottomRank_iff_prefersInList, mem_filter, mem_univ, true_and]
  revert v
  decide

private lemma topCount_profile_0 : topCount profile (0 : Fin 3) = 2 := by
  rw [topCount, profile, votersTop_eq_filter_isTopOfList]; decide

private lemma topCount_profile_1 : topCount profile (1 : Fin 3) = 1 := by
  rw [topCount, profile, votersTop_eq_filter_isTopOfList]; decide

private lemma topCount_profile_2 : topCount profile (2 : Fin 3) = 1 := by
  rw [topCount, profile, votersTop_eq_filter_isTopOfList]; decide

lemma plurality_profile_eq_singleton : plurality profile = {0} := by
  ext x
  fin_cases x <;>
    simp [plurality, Fin.forall_fin_succ, topCount_profile_0, topCount_profile_1,
      topCount_profile_2]

private lemma votersTop_reverse_profile_eq_votersBottom {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) :
    votersTop (reverse_profile P) c = votersBottom P c := by
  ext v
  simp [votersBottom, topRank_reverse_profile_iff_bottomRank]

private lemma topCount_reverse_profile_0 :
    topCount (reverse_profile profile) (0 : Fin 3) = 2 := by
  simp [topCount, votersTop_reverse_profile_eq_votersBottom, votersBottom_profile_0]

private lemma topCount_reverse_profile_1 :
    topCount (reverse_profile profile) (1 : Fin 3) = 1 := by
  simp [topCount, votersTop_reverse_profile_eq_votersBottom, votersBottom_profile_1]

private lemma topCount_reverse_profile_2 :
    topCount (reverse_profile profile) (2 : Fin 3) = 1 := by
  simp [topCount, votersTop_reverse_profile_eq_votersBottom, votersBottom_profile_2]

lemma reverse_profile_has_0 :
    (0 : Fin 3) ∈ plurality (reverse_profile profile) := by
  simp [plurality, Fin.forall_fin_succ, topCount_reverse_profile_0, topCount_reverse_profile_1,
    topCount_reverse_profile_2]

end PluralityReversalCounterexample

theorem plurality_not_singletonReversalSymmetry : ¬ SingletonReversalSymmetry plurality := by
  intro h
  have hsingle : plurality PluralityReversalCounterexample.profile = {0} :=
    PluralityReversalCounterexample.plurality_profile_eq_singleton
  have hne : ∃ y : Fin 3, (0 : Fin 3) ≠ y := by
    exact ⟨1, by decide⟩
  have hnot :=
    h (P := PluralityReversalCounterexample.profile) (x := (0 : Fin 3)) hne hsingle
  have hw : (0 : Fin 3) ∈ plurality (reverse_profile PluralityReversalCounterexample.profile) :=
    PluralityReversalCounterexample.reverse_profile_has_0
  exact hnot hw

end SocialChoice
