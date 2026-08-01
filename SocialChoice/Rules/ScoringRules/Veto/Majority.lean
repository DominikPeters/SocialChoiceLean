import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import SocialChoice.Axioms.Majority
import SocialChoice.Rules.ScoringRules.Veto.Common

namespace SocialChoice

open Finset
open scoped BigOperators

theorem veto_majority_loser_criterion : MajorityLoserCriterion veto := by
  intro V A _ _ P c hmaj hne
  classical
  rcases hne with ⟨d0, hd0c⟩
  haveI : Nonempty A := ⟨c⟩
  let scoreVec : Nat → Int := fun r => vetoScore (Fintype.card A) r
  have hnotbottom_c_eq :
      (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card =
        Fintype.card V - (votersBottom P c).card := by
    have hsum :
        (Finset.univ.filter (fun v => BottomRank P v c)).card +
          (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card =
          (Finset.univ : Finset V).card := by
      simpa using
        (Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset V)) (p := fun v => BottomRank P v c))
    have hsum' :
        (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card =
          (Finset.univ : Finset V).card -
            (Finset.univ.filter (fun v => BottomRank P v c)).card := by
      apply Nat.eq_sub_of_add_eq
      simpa [add_comm] using hsum
    simpa [votersBottom] using hsum'
  have hmaj' : 2 * (votersBottom P c).card > Fintype.card V := by
    simpa [StrictMajority] using hmaj
  have hlt_nat :
      (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card <
        (votersBottom P c).card := by
    have hlt_nat' : Fintype.card V - (votersBottom P c).card < (votersBottom P c).card := by
      omega
    simpa [hnotbottom_c_eq] using hlt_nat'
  have hscore_lt : ∀ d : A, d ≠ c →
      scoreCandidate P scoreVec c < scoreCandidate P scoreVec d := by
    intro d hdc
    have hnotbottom_d_ge :
        (votersBottom P c).card ≤
          (Finset.univ.filter (fun v => ¬ BottomRank P v d)).card := by
      have hsubset : ∀ v, BottomRank P v c → ¬ BottomRank P v d := by
        intro v hbc
        exact bottomRank_imp_not_bottomRank (P := P) (c := c) (d := d) hdc.symm v hbc
      have hcard :=
        cardinality_lemma (p := fun v => BottomRank P v c)
          (q := fun v => ¬ BottomRank P v d) hsubset
      simpa [votersBottom] using hcard
    have hscore_c :
        scoreCandidate P scoreVec c =
          ((Finset.univ.filter (fun v => ¬ BottomRank P v c)).card : Int) := by
      simpa [scoreVec, vetoScore] using
        (vetoScore_scoreCandidate_eq_notBottom_card (P := P) (c := c))
    have hscore_d :
        scoreCandidate P scoreVec d =
          ((Finset.univ.filter (fun v => ¬ BottomRank P v d)).card : Int) := by
      simpa [scoreVec, vetoScore] using
        (vetoScore_scoreCandidate_eq_notBottom_card (P := P) (c := d))
    have hlt_int :
        ((Finset.univ.filter (fun v => ¬ BottomRank P v c)).card : Int) <
          ((Finset.univ.filter (fun v => ¬ BottomRank P v d)).card : Int) := by
      have hlt_int' :
          ((Finset.univ.filter (fun v => ¬ BottomRank P v c)).card : Int) <
            ((votersBottom P c).card : Int) := by
        exact_mod_cast hlt_nat
      have hle_int :
          ((votersBottom P c).card : Int) ≤
            ((Finset.univ.filter (fun v => ¬ BottomRank P v d)).card : Int) := by
        exact_mod_cast hnotbottom_d_ge
      exact lt_of_lt_of_le hlt_int' hle_int
    simpa [hscore_c, hscore_d] using hlt_int
  have hA : (Finset.univ : Finset A).Nonempty := by
    simp
  have hnot : c ∉ scoringWinners P scoreVec := by
    intro hc
    have hforall :=
      (scoringWinners_iff_forall_le (P := P) (score := scoreVec) (_hA := hA) (c := c)).1 hc
    have hlt := hscore_lt d0 hd0c
    have hle := hforall d0
    exact (not_lt_of_ge hle) hlt
  simpa [veto, scoringRule, scoreVec] using hnot

end SocialChoice
