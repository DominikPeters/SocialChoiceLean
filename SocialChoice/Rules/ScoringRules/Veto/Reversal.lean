import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Reversal
import SocialChoice.ListBallot
import SocialChoice.Rules.ScoringRules.Veto.Common
import SocialChoice.Rules.ScoringRules.Veto.Defs

namespace SocialChoice

open Finset
open Classical

namespace VetoReversalCounterexample

def ballot102 : ListBallot 3 := ListBallot.mk' [1, 0, 2]
def ballot201 : ListBallot 3 := ListBallot.mk' [2, 0, 1]

def ballots : Fin 2 → ListBallot 3
  | 0 => ballot102
  | 1 => ballot201

noncomputable def profile : Profile (Fin 2) (Fin 3) :=
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

private lemma veto_score (c : Fin 3) :
    scoreCandidate profile (fun r => vetoScore 3 r) c =
      (if c = (0 : Fin 3) then (2 : Int) else 1) := by
  classical
  fin_cases c
  ·
    have hcard :
        (Finset.univ.filter (fun v => ¬ BottomRank profile v (0 : Fin 3))).card = 2 := by
      have hset :
          (Finset.univ.filter (fun v => ¬ BottomRank profile v (0 : Fin 3))) =
            ({0, 1} : Finset (Fin 2)) := by
        ext v
        fin_cases v <;>
          simp [profile, ballots, bottomRank_iff_prefersInList, prefersInList] <;>
          decide
      simp [hset]
    simpa [vetoScore, hcard] using
      (vetoScore_scoreCandidate_eq_notBottom_card (P := profile) (c := (0 : Fin 3)))
  ·
    have hcard :
        (Finset.univ.filter (fun v => ¬ BottomRank profile v (1 : Fin 3))).card = 1 := by
      have hset :
          (Finset.univ.filter (fun v => ¬ BottomRank profile v (1 : Fin 3))) =
            ({0} : Finset (Fin 2)) := by
        ext v
        fin_cases v <;>
          simp [profile, ballots, bottomRank_iff_prefersInList, prefersInList] <;>
          decide
      simp [hset]
    simpa [vetoScore, hcard] using
      (vetoScore_scoreCandidate_eq_notBottom_card (P := profile) (c := (1 : Fin 3)))
  ·
    have hcard :
        (Finset.univ.filter (fun v => ¬ BottomRank profile v (2 : Fin 3))).card = 1 := by
      have hset :
          (Finset.univ.filter (fun v => ¬ BottomRank profile v (2 : Fin 3))) =
            ({1} : Finset (Fin 2)) := by
        ext v
        fin_cases v <;>
          simp [profile, ballots, bottomRank_iff_prefersInList, prefersInList] <;>
          decide
      simp [hset]
    simpa [vetoScore, hcard] using
      (vetoScore_scoreCandidate_eq_notBottom_card (P := profile) (c := (2 : Fin 3)))

private lemma veto_profile_has_0 : (0 : Fin 3) ∈ veto profile := by
  classical
  have hA : (Finset.univ : Finset (Fin 3)).Nonempty := by
    simp
  have hmax :
      ∀ d : Fin 3,
        scoreCandidate profile (fun r => vetoScore 3 r) d ≤
          scoreCandidate profile (fun r => vetoScore 3 r) (0 : Fin 3) := by
    intro d
    fin_cases d <;>
      simp [veto_score]
  have hmem :
      (0 : Fin 3) ∈ scoringWinners profile (fun r => vetoScore 3 r) := by
    exact
      (scoringWinners_iff_forall_le (P := profile)
        (score := fun r => vetoScore 3 r) (_hA := hA) (c := (0 : Fin 3))).2 hmax
  simpa [veto, scoringRule] using hmem

private lemma veto_profile_not_1 : (1 : Fin 3) ∉ veto profile := by
  intro h
  classical
  have hA : (Finset.univ : Finset (Fin 3)).Nonempty := by
    simp
  have hmem :
      (1 : Fin 3) ∈ scoringWinners profile (fun r => vetoScore 3 r) := by
    simpa [veto, scoringRule] using h
  have hmax :=
    (scoringWinners_iff_forall_le (P := profile)
      (score := fun r => vetoScore 3 r) (_hA := hA) (c := (1 : Fin 3))).1 hmem
  have h0le : (2 : Int) ≤ 1 := by
    simpa [veto_score] using hmax (0 : Fin 3)
  exact (by decide : ¬ ((2 : Int) ≤ 1)) h0le

private lemma veto_profile_not_2 : (2 : Fin 3) ∉ veto profile := by
  intro h
  classical
  have hA : (Finset.univ : Finset (Fin 3)).Nonempty := by
    simp
  have hmem :
      (2 : Fin 3) ∈ scoringWinners profile (fun r => vetoScore 3 r) := by
    simpa [veto, scoringRule] using h
  have hmax :=
    (scoringWinners_iff_forall_le (P := profile)
      (score := fun r => vetoScore 3 r) (_hA := hA) (c := (2 : Fin 3))).1 hmem
  have h0le : (2 : Int) ≤ 1 := by
    simpa [veto_score] using hmax (0 : Fin 3)
  exact (by decide : ¬ ((2 : Int) ≤ 1)) h0le

lemma veto_profile_eq_singleton : veto profile = ({0} : Finset (Fin 3)) := by
  classical
  refine (Finset.eq_singleton_iff_unique_mem).2 ?_
  refine ⟨veto_profile_has_0, ?_⟩
  intro x hx
  fin_cases x
  · rfl
  · exfalso
    exact veto_profile_not_1 hx
  · exfalso
    exact veto_profile_not_2 hx

private lemma bottomRank_reverse_profile_iff_topRank {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (c : A) :
    BottomRank (reverse_profile P) v c ↔ TopRank P v c := by
  constructor
  · intro h d hd
    have h' : Prefers (reverse_profile P) v d c := h d hd
    exact (prefers_reverse_profile (P := P) (v := v) (a := d) (b := c)).1 h'
  · intro h d hd
    have h' : Prefers P v c d := h d hd
    exact (prefers_reverse_profile (P := P) (v := v) (a := d) (b := c)).2 h'

private lemma veto_reverse_score (c : Fin 3) :
    scoreCandidate (reverse_profile profile) (fun r => vetoScore 3 r) c =
      (if c = (0 : Fin 3) then (2 : Int) else 1) := by
  classical
  fin_cases c
  ·
    have hcard :
        (Finset.univ.filter (fun v => ¬ BottomRank (reverse_profile profile) v (0 : Fin 3))).card = 2 := by
      have hset :
          (Finset.univ.filter (fun v => ¬ BottomRank (reverse_profile profile) v (0 : Fin 3))) =
            ({0, 1} : Finset (Fin 2)) := by
        ext v
        fin_cases v <;>
          simp [profile, ballots, bottomRank_reverse_profile_iff_topRank, topRank_iff_isTopOfList,
            isTopOfList] <;>
          decide
      simp [hset]
    simpa [vetoScore, hcard] using
      (vetoScore_scoreCandidate_eq_notBottom_card
        (P := reverse_profile profile) (c := (0 : Fin 3)))
  ·
    have hcard :
        (Finset.univ.filter (fun v => ¬ BottomRank (reverse_profile profile) v (1 : Fin 3))).card = 1 := by
      have hset :
          (Finset.univ.filter (fun v => ¬ BottomRank (reverse_profile profile) v (1 : Fin 3))) =
            ({1} : Finset (Fin 2)) := by
        ext v
        fin_cases v <;>
          simp [profile, ballots, bottomRank_reverse_profile_iff_topRank, topRank_iff_isTopOfList,
            isTopOfList] <;>
          decide
      simp [hset]
    simpa [vetoScore, hcard] using
      (vetoScore_scoreCandidate_eq_notBottom_card
        (P := reverse_profile profile) (c := (1 : Fin 3)))
  ·
    have hcard :
        (Finset.univ.filter (fun v => ¬ BottomRank (reverse_profile profile) v (2 : Fin 3))).card = 1 := by
      have hset :
          (Finset.univ.filter (fun v => ¬ BottomRank (reverse_profile profile) v (2 : Fin 3))) =
            ({0} : Finset (Fin 2)) := by
        ext v
        fin_cases v <;>
          simp [profile, ballots, bottomRank_reverse_profile_iff_topRank, topRank_iff_isTopOfList,
            isTopOfList] <;>
          decide
      simp [hset]
    simpa [vetoScore, hcard] using
      (vetoScore_scoreCandidate_eq_notBottom_card
        (P := reverse_profile profile) (c := (2 : Fin 3)))

lemma reverse_profile_has_0 : (0 : Fin 3) ∈ veto (reverse_profile profile) := by
  classical
  have hA : (Finset.univ : Finset (Fin 3)).Nonempty := by
    simp
  have hmax :
      ∀ d : Fin 3,
        scoreCandidate (reverse_profile profile) (fun r => vetoScore 3 r) d ≤
          scoreCandidate (reverse_profile profile) (fun r => vetoScore 3 r) (0 : Fin 3) := by
    intro d
    fin_cases d <;>
      simp [veto_reverse_score]
  have hmem :
      (0 : Fin 3) ∈
        scoringWinners (reverse_profile profile) (fun r => vetoScore 3 r) := by
    exact
      (scoringWinners_iff_forall_le (P := reverse_profile profile)
        (score := fun r => vetoScore 3 r) (_hA := hA) (c := (0 : Fin 3))).2 hmax
  simpa [veto, scoringRule] using hmem

end VetoReversalCounterexample

theorem veto_not_singletonReversalSymmetry : ¬ SingletonReversalSymmetry veto := by
  intro h
  have hsingle : veto VetoReversalCounterexample.profile = {0} :=
    VetoReversalCounterexample.veto_profile_eq_singleton
  have hne : ∃ y : Fin 3, (0 : Fin 3) ≠ y := by
    exact ⟨1, by decide⟩
  have hnot :=
    h (P := VetoReversalCounterexample.profile) (x := (0 : Fin 3)) hne hsingle
  have hw :
      (0 : Fin 3) ∈ veto (reverse_profile VetoReversalCounterexample.profile) :=
    VetoReversalCounterexample.reverse_profile_has_0
  exact hnot hw

end SocialChoice
