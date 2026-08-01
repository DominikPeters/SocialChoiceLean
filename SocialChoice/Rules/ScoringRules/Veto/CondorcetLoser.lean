import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Condorcet
import SocialChoice.ListBallot
import SocialChoice.Rules.ScoringRules.Veto.Common
import SocialChoice.Rules.ScoringRules.Veto.Defs

namespace SocialChoice

open Finset

/-!
Veto (anti-plurality) violates the Condorcet loser criterion.
Counterexample profile:
  [1,0,2], [2,0,1], [2,1,0]
Candidate 0 is a Condorcet loser but is a veto winner.
-/

private def ballot102 : ListBallot 3 := ListBallot.mk' [1, 0, 2]
private def ballot201 : ListBallot 3 := ListBallot.mk' [2, 0, 1]
private def ballot210 : ListBallot 3 := ListBallot.mk' [2, 1, 0]

private def vetoCondorcetLoserBallots : Fin 3 → ListBallot 3
  | 0 => ballot102
  | 1 => ballot201
  | 2 => ballot210

private noncomputable def vetoCondorcetLoserProfile : Profile (Fin 3) (Fin 3) :=
  profileOfListBallots vetoCondorcetLoserBallots

private lemma bottomRank_iff_prefersInList {m n : ℕ} (ballots : Fin m → ListBallot n)
    (v : Fin m) (c : Fin n) :
    BottomRank (profileOfListBallots ballots) v c ↔
      ∀ d : Fin n, d ≠ c → prefersInList (ballots v).ranking d c = true := by
  constructor
  · intro h d hd
    exact (prefers_iff_prefersInList ballots v d c).1 (h d hd)
  · intro h d hd
    exact (prefers_iff_prefersInList ballots v d c).2 (h d hd)

private lemma vetoCondorcetLoser_score (c : Fin 3) :
    scoreCandidate vetoCondorcetLoserProfile (fun r => vetoScore 3 r) c = (2 : Int) := by
  classical
  fin_cases c
  ·
    have hcard :
        (Finset.univ.filter (fun v => ¬ BottomRank vetoCondorcetLoserProfile v (0 : Fin 3))).card =
          2 := by
      have hset :
          (Finset.univ.filter (fun v => ¬ BottomRank vetoCondorcetLoserProfile v (0 : Fin 3))) =
            ({0, 1} : Finset (Fin 3)) := by
        ext v
        fin_cases v <;>
          simp [vetoCondorcetLoserProfile, vetoCondorcetLoserBallots, bottomRank_iff_prefersInList,
            prefersInList] <;>
          decide
      simp [hset]
    simpa [vetoScore, hcard] using
      (vetoScore_scoreCandidate_eq_notBottom_card (P := vetoCondorcetLoserProfile)
        (c := (0 : Fin 3)))
  ·
    have hcard :
        (Finset.univ.filter (fun v => ¬ BottomRank vetoCondorcetLoserProfile v (1 : Fin 3))).card =
          2 := by
      have hset :
          (Finset.univ.filter (fun v => ¬ BottomRank vetoCondorcetLoserProfile v (1 : Fin 3))) =
            ({0, 2} : Finset (Fin 3)) := by
        ext v
        fin_cases v <;>
          simp [vetoCondorcetLoserProfile, vetoCondorcetLoserBallots, bottomRank_iff_prefersInList,
            prefersInList] <;>
          decide
      simp [hset]
    simpa [vetoScore, hcard] using
      (vetoScore_scoreCandidate_eq_notBottom_card (P := vetoCondorcetLoserProfile)
        (c := (1 : Fin 3)))
  ·
    have hcard :
        (Finset.univ.filter (fun v => ¬ BottomRank vetoCondorcetLoserProfile v (2 : Fin 3))).card =
          2 := by
      have hset :
          (Finset.univ.filter (fun v => ¬ BottomRank vetoCondorcetLoserProfile v (2 : Fin 3))) =
            ({1, 2} : Finset (Fin 3)) := by
        ext v
        fin_cases v <;>
          simp [vetoCondorcetLoserProfile, vetoCondorcetLoserBallots, bottomRank_iff_prefersInList,
            prefersInList] <;>
          decide
      simp [hset]
    simpa [vetoScore, hcard] using
      (vetoScore_scoreCandidate_eq_notBottom_card (P := vetoCondorcetLoserProfile)
        (c := (2 : Fin 3)))

private lemma vetoCondorcetLoser_has_zero : (0 : Fin 3) ∈ veto vetoCondorcetLoserProfile := by
  classical
  have hA : (Finset.univ : Finset (Fin 3)).Nonempty := by
    simp
  have hmax :
      ∀ d : Fin 3,
        scoreCandidate vetoCondorcetLoserProfile (fun r => vetoScore 3 r) d ≤
          scoreCandidate vetoCondorcetLoserProfile (fun r => vetoScore 3 r) (0 : Fin 3) := by
    intro d
    fin_cases d <;> simp [vetoCondorcetLoser_score]
  have hmem :
      (0 : Fin 3) ∈ scoringWinners vetoCondorcetLoserProfile (fun r => vetoScore 3 r) := by
    exact
      (scoringWinners_iff_forall_le (P := vetoCondorcetLoserProfile)
        (score := fun r => vetoScore 3 r) (_hA := hA) (c := (0 : Fin 3))).2 hmax
  simpa [veto, scoringRule] using hmem

private lemma vetoCondorcetLoser_marginList_10 :
    marginList (fun v => (vetoCondorcetLoserBallots v).ranking) 1 0 > 0 := by
  decide

private lemma vetoCondorcetLoser_marginList_20 :
    marginList (fun v => (vetoCondorcetLoserBallots v).ranking) 2 0 > 0 := by
  decide

private lemma vetoCondorcetLoser_marginList (d : Fin 3) (hne : (0 : Fin 3) ≠ d) :
    marginList (fun v => (vetoCondorcetLoserBallots v).ranking) d 0 > 0 := by
  fin_cases d <;> try cases hne rfl
  · exact vetoCondorcetLoser_marginList_10
  · exact vetoCondorcetLoser_marginList_20

private lemma vetoCondorcetLoser_is_CondorcetLoser :
    CondorcetLoser vetoCondorcetLoserProfile (0 : Fin 3) := by
  refine (CondorcetLoser_iff_margin_pos (P := vetoCondorcetLoserProfile) (c := (0 : Fin 3))).2 ?_
  refine ⟨?_, ?_⟩
  · intro d hne
    have hlist :
        marginList (fun v => (vetoCondorcetLoserBallots v).ranking) d 0 > 0 :=
      vetoCondorcetLoser_marginList d hne
    have hpos :
        margin_pos (profileOfListBallots vetoCondorcetLoserBallots) d 0 := by
      exact
        (margin_pos_iff_marginList_pos (ballots := vetoCondorcetLoserBallots) (a := d) (b := 0)).2
          hlist
    simpa [vetoCondorcetLoserProfile] using hpos
  · exact ⟨1, by decide⟩

theorem veto_not_condorcetLoser_criterion : ¬ CondorcetLoserCriterion veto := by
  intro hcrit
  have hloser : CondorcetLoser vetoCondorcetLoserProfile (0 : Fin 3) :=
    vetoCondorcetLoser_is_CondorcetLoser
  have hwin : (0 : Fin 3) ∈ veto vetoCondorcetLoserProfile :=
    vetoCondorcetLoser_has_zero
  exact (hcrit (P := vetoCondorcetLoserProfile) (c := (0 : Fin 3)) hloser) hwin

end SocialChoice
