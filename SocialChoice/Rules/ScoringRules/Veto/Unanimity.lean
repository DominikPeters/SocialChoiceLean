import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Unanimity
import SocialChoice.ListBallot
import SocialChoice.Rules.ScoringRules.Veto.Defs

namespace SocialChoice

open Finset
open scoped BigOperators

private def vetoUnanimityBallot : ListBallot 3 := ListBallot.mk' [0, 1, 2]

private def vetoUnanimityBallots : Fin 1 → ListBallot 3
  | 0 => vetoUnanimityBallot

private noncomputable def vetoUnanimityProfile : Profile (Fin 1) (Fin 3) :=
  profileOfListBallots vetoUnanimityBallots

private lemma rank_vetoUnanimity_0 : rank vetoUnanimityBallot.toLinearOrder (0 : Fin 3) = 0 := by decide
private lemma rank_vetoUnanimity_1 : rank vetoUnanimityBallot.toLinearOrder (1 : Fin 3) = 1 := by decide
private lemma rank_vetoUnanimity_2 : rank vetoUnanimityBallot.toLinearOrder (2 : Fin 3) = 2 := by decide

private lemma vetoUnanimity_score (c : Fin 3) :
    scoreCandidate vetoUnanimityProfile (fun r => vetoScore 3 r) c =
      (if c = 2 then 0 else 1) := by
  fin_cases c <;>
    simp [scoreCandidate, vetoUnanimityProfile, vetoUnanimityBallots, profileOfListBallots,
      rank_vetoUnanimity_0, rank_vetoUnanimity_1, rank_vetoUnanimity_2, vetoScore]

private lemma vetoUnanimity_one_mem : (1 : Fin 3) ∈ veto vetoUnanimityProfile := by
  have hA : (Finset.univ : Finset (Fin 3)).Nonempty := by
    classical
    exact Finset.univ_nonempty
  have h1mem :
      (1 : Fin 3) ∈ scoringWinners vetoUnanimityProfile (fun r => vetoScore 3 r) := by
    apply
      (scoringWinners_iff_forall_le (P := vetoUnanimityProfile)
        (score := fun r => vetoScore 3 r) (_hA := hA) (c := (1 : Fin 3))).2
    intro d
    fin_cases d <;> simp [vetoUnanimity_score]
  simpa [veto, scoringRule] using h1mem

theorem veto_not_unanimity : ¬ Unanimity veto := by
  intro hunan
  have htop : ∀ v : Fin 1, TopRank vetoUnanimityProfile v (0 : Fin 3) := by
    intro v d hd
    fin_cases v
    fin_cases d
    · cases (hd rfl)
    · (simp [vetoUnanimityProfile, vetoUnanimityBallots, prefers_iff_prefersInList,
        prefersInList]; decide)
    · (simp [vetoUnanimityProfile, vetoUnanimityBallots, prefers_iff_prefersInList,
        prefersInList]; decide)
  have hmem : (1 : Fin 3) ∈ ({0} : Finset (Fin 3)) := by
    simpa [hunan vetoUnanimityProfile (0 : Fin 3) htop] using vetoUnanimity_one_mem
  simp at hmem

end SocialChoice
