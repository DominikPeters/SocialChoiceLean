import SocialChoice.Axioms.Reversal
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.Defs
import SocialChoice.Rules.PluralityWithRunoff.EqualsIRVForThreeCandidates
import SocialChoice.Rules.PluralityWithRunoff.Reversal

namespace SocialChoice

open PluralityWithRunoffReversalCounterexample

theorem instantRunoffVoting_not_singletonReversalSymmetry :
    ¬ SingletonReversalSymmetry instantRunoffVoting := by
  intro h
  have hIRV :
      instantRunoffVoting profile = pluralityWithRunoff profile := by
    simpa using
      (instantRunoffVoting_eq_pluralityWithRunoff_of_card_le_three
        (A := Fin 3) (hcard := by decide) (P := profile))
  have hsingle : instantRunoffVoting profile = ({0} : Finset (Fin 3)) := by
    have hpwr : pluralityWithRunoff profile = ({0} : Finset (Fin 3)) :=
      pluralityWithRunoff_profile_eq_singleton
    simpa [hIRV] using hpwr
  have hne : ∃ y : Fin 3, (0 : Fin 3) ≠ y := by
    exact ⟨1, by decide⟩
  have hnot :
      (0 : Fin 3) ∉ instantRunoffVoting (reverse_profile profile) :=
    h (P := profile) (x := (0 : Fin 3)) hne hsingle
  have hIRVrev :
      instantRunoffVoting (reverse_profile profile) =
        pluralityWithRunoff (reverse_profile profile) := by
    simpa using
      (instantRunoffVoting_eq_pluralityWithRunoff_of_card_le_three
        (A := Fin 3) (hcard := by decide) (P := reverse_profile profile))
  have hmem : (0 : Fin 3) ∈ instantRunoffVoting (reverse_profile profile) := by
    have hw :
        (0 : Fin 3) ∈ pluralityWithRunoff (reverse_profile profile) :=
      reverse_profile_has_0
    simpa [hIRVrev] using hw
  exact hnot hmem

end SocialChoice
