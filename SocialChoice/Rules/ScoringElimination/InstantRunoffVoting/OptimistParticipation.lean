import Mathlib.Tactic
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.Defs
import SocialChoice.Rules.PluralityWithRunoff.EqualsIRVForThreeCandidates
import SocialChoice.Rules.PluralityWithRunoff.OptimistParticipation

namespace SocialChoice

open PluralityWithRunoffOptimistParticipationCounterexample

theorem instantRunoffVoting_not_optimistParticipation :
    ¬ OptimistParticipation instantRunoffVoting := by
  intro hopt
  let r := profile5OP.pref (newVoter (u := (0 : Fin 5)) (V := voters4OP) voters4OP_not_mem)
  letI : LinearOrder (Fin 3) := r
  have hIRV5 :
      instantRunoffVoting profile5OP = pluralityWithRunoff profile5OP := by
    simpa using
      (instantRunoffVoting_eq_pluralityWithRunoff_of_card_le_three
        (A := Fin 3) (hcard := by decide) (P := profile5OP))
  have hIRV4 :
      instantRunoffVoting profile4OP = pluralityWithRunoff profile4OP := by
    simpa using
      (instantRunoffVoting_eq_pluralityWithRunoff_of_card_le_three
        (A := Fin 3) (hcard := by decide) (P := profile4OP))
  have hweak :
      @OptimistWeak (Fin 3) (fun a b => r.toDecidableEq a b) r
        (pluralityWithRunoff profile5OP) (pluralityWithRunoff profile4OP) := by
    have hweakIRV :
        @OptimistWeak (Fin 3) (fun a b => r.toDecidableEq a b) r
          (instantRunoffVoting profile5OP) (instantRunoffVoting profile4OP) := by
      simpa [OptimistParticipation, StrongParticipation, OptimistExtension, r] using
        hopt (V := voters4OP) (u := (0 : Fin 5)) (hu := voters4OP_not_mem)
          (P := profile4OP) (Q := profile5OP) profiles_agreeOP
    simpa [hIRV5, hIRV4] using hweakIRV
  rcases hweak with ⟨a, b, haTop, hbTop, hle⟩
  have ha2 : a = (2 : Fin 3) := by
    have haMem : a ∈ pluralityWithRunoff profile5OP := haTop.1
    fin_cases a
    · exact (pluralityWithRunoff_profile5OP_not_0 haMem).elim
    · exact (pluralityWithRunoff_profile5OP_not_1 haMem).elim
    · rfl
  have hb0 : b = (0 : Fin 3) := by
    have hbMem : b ∈ pluralityWithRunoff profile4OP := hbTop.1
    fin_cases b
    · rfl
    · exact (pluralityWithRunoff_profile4OP_not_1 hbMem).elim
    ·
      have h0mem : (0 : Fin 3) ∈ pluralityWithRunoff profile4OP :=
        pluralityWithRunoff_profile4OP_has_0
      have h0ne : (0 : Fin 3) ≠ (2 : Fin 3) := by decide
      have h20raw := hbTop.2 (0 : Fin 3) h0mem h0ne
      have h20 := h20raw
      simp at h20
  have hle' := hle
  simp [ha2, hb0, r] at hle'

end SocialChoice
