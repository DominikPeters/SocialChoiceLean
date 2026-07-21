import SocialChoice.Axioms.Anonymity
import SocialChoice.Axioms.Neutrality
import SocialChoice.Axioms.Resolute
import SocialChoice.Profile
import Mathlib.Tactic.FinCases

namespace SocialChoice

namespace AnonymousNeutralResolute

open Finset

noncomputable def swapCand : Equiv.Perm (Fin 2) := Equiv.swap 0 1

noncomputable def baseOrder : LinearOrder (Fin 2) := by
  infer_instance

noncomputable def swappedOrder : LinearOrder (Fin 2) :=
  relabelBallot baseOrder swapCand

noncomputable def twoVoterProfile : Profile (Fin 2) (Fin 2) :=
  { pref := fun v => if v = 0 then baseOrder else swappedOrder }

lemma relabelBallot_relabelBallot_symm {A : Type} (r : LinearOrder A) (σ : Equiv.Perm A) :
    relabelBallot (relabelBallot r σ) σ.symm = r := by
  classical
  apply LinearOrder.ext_lt
  intro a b
  change r.lt (σ (σ.symm a)) (σ (σ.symm b)) ↔ r.lt a b
  simp

lemma swapCand_symm : swapCand.symm = swapCand := by
  ext a
  fin_cases a <;> rfl

lemma relabelBallot_relabelBallot_swap :
    relabelBallot (relabelBallot baseOrder swapCand) swapCand = baseOrder := by
  simpa [swapCand_symm] using
    (relabelBallot_relabelBallot_symm (r := baseOrder) (σ := swapCand))

lemma permuteCandidates_twoVoterProfile :
    permuteCandidates twoVoterProfile swapCand =
      permuteVoters twoVoterProfile swapCand := by
  classical
  apply Profile.ext
  intro v
  fin_cases v
  · simp [twoVoterProfile, permuteCandidates, permuteVoters, swappedOrder, swapCand]
  · simp [twoVoterProfile, permuteCandidates, permuteVoters, swappedOrder, swapCand]
    exact relabelBallot_relabelBallot_swap

lemma swapCand_ne (c : Fin 2) : swapCand c ≠ c := by
  fin_cases c <;> decide

theorem no_anonymous_neutral_resolute
    (f : VotingRule) (hanon : Anonymity f) (hneu : Neutrality f) (hres : Resolute f) :
    False := by
  classical
  let P := twoVoterProfile
  have hcard := hres P
  rw [Finset.card_eq_one] at hcard
  obtain ⟨c, hc⟩ := hcard
  have hperm : f (permuteCandidates P swapCand) = {swapCand c} := by
    have hneu' := hneu P swapCand
    simpa [hc, permuteWinners] using hneu'.symm
  have hanon' : f (permuteCandidates P swapCand) = f P := by
    simpa [P, permuteCandidates_twoVoterProfile] using hanon P swapCand
  have hset : ({swapCand c} : Finset (Fin 2)) = {c} := by
    calc
      ({swapCand c} : Finset (Fin 2)) = f (permuteCandidates P swapCand) := by
        symm
        exact hperm
      _ = f P := hanon'
      _ = {c} := hc
  have hfix : swapCand c = c := by
    have hmem : swapCand c ∈ ({c} : Finset (Fin 2)) := by
      have hmem' : swapCand c ∈ ({swapCand c} : Finset (Fin 2)) := by simp
      simpa [hset] using hmem'
    simpa using hmem
  exact (swapCand_ne c) hfix

end AnonymousNeutralResolute

end SocialChoice
