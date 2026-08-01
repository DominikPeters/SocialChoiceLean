import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Condorcet
import SocialChoice.ListBallot
import SocialChoice.Rules.ScoringRules.Defs

/-!
No scoring rule satisfies the Condorcet criterion.
Example taken from "Condorcet-Consistent Choice Among Three Candidates"
Felix Brandt, Chris Dong, and Dominik Peters.
-/

namespace SocialChoice

private abbrev Voters5 := Fin 5
private abbrev A3 := Fin 3

private def ballot012 : ListBallot 3 := ListBallot.identity 3
private def ballot102 : ListBallot 3 := ListBallot.mk' [1, 0, 2]
private def ballot120 : ListBallot 3 := ListBallot.mk' [1, 2, 0]
private def ballot201 : ListBallot 3 := ListBallot.mk' [2, 0, 1]

private lemma rank_ballot012_0 : rank ballot012.toLinearOrder (0 : Fin 3) = 0 := by decide
private lemma rank_ballot012_1 : rank ballot012.toLinearOrder (1 : Fin 3) = 1 := by decide
private lemma rank_ballot102_0 : rank ballot102.toLinearOrder (0 : Fin 3) = 1 := by decide
private lemma rank_ballot102_1 : rank ballot102.toLinearOrder (1 : Fin 3) = 0 := by decide
private lemma rank_ballot120_0 : rank ballot120.toLinearOrder (0 : Fin 3) = 2 := by decide
private lemma rank_ballot120_1 : rank ballot120.toLinearOrder (1 : Fin 3) = 0 := by decide
private lemma rank_ballot201_0 : rank ballot201.toLinearOrder (0 : Fin 3) = 1 := by decide
private lemma rank_ballot201_1 : rank ballot201.toLinearOrder (1 : Fin 3) = 2 := by decide

private def scoringCondorcetBallots : Voters5 → ListBallot 3
  | 0 => ballot012
  | 1 => ballot012
  | 2 => ballot102
  | 3 => ballot120
  | 4 => ballot201

private noncomputable def scoringCondorcetProfile : Profile Voters5 A3 :=
  profileOfListBallots scoringCondorcetBallots

private lemma scoringCondorcetProfile_eq :
    scoringCondorcetProfile = profileOfListBallots scoringCondorcetBallots := rfl

private lemma scoringCondorcet_winner_list :
    ∀ d : Fin 3, (0 : Fin 3) ≠ d →
      marginList (fun v => (scoringCondorcetBallots v).ranking) 0 d > 0 := by
  intro d hne
  fin_cases d
  · cases hne rfl
  · decide
  · decide

private theorem scoringCondorcet_winner :
    CondorcetWinner scoringCondorcetProfile (0 : Fin 3) := by
  rw [scoringCondorcetProfile_eq, CondorcetWinner_iff_marginList]
  exact scoringCondorcet_winner_list

private lemma scoreCandidate_scoringCondorcet_eq (score : Nat → Int) :
    scoreCandidate scoringCondorcetProfile score (0 : Fin 3) =
      scoreCandidate scoringCondorcetProfile score 1 := by
  calc
    scoreCandidate scoringCondorcetProfile score (0 : Fin 3) =
        score 0 + score 0 + score 1 + score 2 + score 1 := by
          unfold scoreCandidate scoringCondorcetProfile
          simp [scoringCondorcetBallots, profileOfListBallots, Fin.sum_univ_succ, rank_ballot012_0,
            rank_ballot102_0, rank_ballot120_0, rank_ballot201_0]
          ring
    _ = score 1 + score 1 + score 0 + score 0 + score 2 := by
          ring
    _ = scoreCandidate scoringCondorcetProfile score 1 := by
          unfold scoreCandidate scoringCondorcetProfile
          simp [scoringCondorcetBallots, profileOfListBallots, Fin.sum_univ_succ, rank_ballot012_1,
            rank_ballot102_1, rank_ballot120_1, rank_ballot201_1]
          ring

theorem scoringRule_not_condorcet (score : Nat → Nat → Int) :
    ¬ CondorcetConsistency (scoringRule score) := by
  intro hcriterion
  have hcond : CondorcetWinner scoringCondorcetProfile (0 : Fin 3) :=
    scoringCondorcet_winner
  have hres :
      scoringRule score scoringCondorcetProfile = ({0} : Finset (Fin 3)) :=
    hcriterion scoringCondorcetProfile 0 hcond
  have h0mem : (0 : Fin 3) ∈ scoringRule score scoringCondorcetProfile := by
    simp [hres]
  have hA : (Finset.univ : Finset (Fin 3)).Nonempty := by
    classical
    exact Finset.univ_nonempty
  have h0max :
      ∀ d : Fin 3,
        scoreCandidate scoringCondorcetProfile (fun r => score 3 r) d ≤
          scoreCandidate scoringCondorcetProfile (fun r => score 3 r) 0 := by
    have h0mem' :
        (0 : Fin 3) ∈ scoringWinners scoringCondorcetProfile (fun r => score 3 r) := by
      simpa [scoringRule] using h0mem
    exact
      (scoringWinners_iff_forall_le (P := scoringCondorcetProfile)
        (score := fun r => score 3 r) (_hA := hA) (c := (0 : Fin 3))).1 h0mem'
  have hscore_eq :
      scoreCandidate scoringCondorcetProfile (fun r => score 3 r) (0 : Fin 3) =
        scoreCandidate scoringCondorcetProfile (fun r => score 3 r) 1 := by
    simpa using (scoreCandidate_scoringCondorcet_eq (score := fun r => score 3 r))
  have h1mem :
      (1 : Fin 3) ∈ scoringWinners scoringCondorcetProfile (fun r => score 3 r) := by
    apply
      (scoringWinners_iff_forall_le (P := scoringCondorcetProfile)
        (score := fun r => score 3 r) (_hA := hA) (c := (1 : Fin 3))).2
    intro d
    have hle := h0max d
    simpa [hscore_eq] using hle
  have h1mem' : (1 : Fin 3) ∈ scoringRule score scoringCondorcetProfile := by
    simpa [scoringRule] using h1mem
  have h1not : (1 : Fin 3) ∉ ({0} : Finset (Fin 3)) := by
    simp
  have h1mem'' := h1mem'
  rw [hres] at h1mem''
  exact h1not h1mem''

end SocialChoice
