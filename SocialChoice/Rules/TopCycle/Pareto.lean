import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Pareto
import SocialChoice.ListBallot
import SocialChoice.Rules.TopCycle.Defs

namespace SocialChoice

open Finset

namespace TopCycleParetoCounterexample

def ballot120 : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballot201 : ListBallot 3 := ListBallot.mk' [2, 0, 1]

def ballots : Fin 2 → ListBallot 3
  | 0 => ballot120
  | 1 => ballot201
  | _ => ballot201

noncomputable def profile : Profile (Fin 2) (Fin 3) :=
  profileOfListBallots ballots

private lemma not_margin_pos_profile_1_0 : ¬ margin_pos profile (1 : Fin 3) (0 : Fin 3) := by
  rw [profile, margin_pos_iff_marginList_pos]; decide

private lemma not_margin_pos_profile_2_1 : ¬ margin_pos profile (2 : Fin 3) (1 : Fin 3) := by
  rw [profile, margin_pos_iff_marginList_pos]; decide

private lemma zero_mem_topCycleSet : (0 : Fin 3) ∈ topCycleSet (P := profile) := by
  classical
  have hdom : dominatesSet profile (topCycleSet (P := profile)) :=
    topCycleSet_dominates (P := profile)
  have hne : (topCycleSet (P := profile)).Nonempty := hdom.1
  by_contra h0
  have hsubset : topCycleSet (P := profile) ⊆ ({2} : Finset (Fin 3)) := by
    intro a ha
    have hpos : margin_pos profile a (0 : Fin 3) := hdom.2 a ha (0 : Fin 3) h0
    fin_cases a
    · exact (False.elim (h0 (by simpa using ha)))
    · exact (False.elim (not_margin_pos_profile_1_0 hpos))
    · simp
  rcases hne with ⟨a, ha⟩
  have ha2 : a = (2 : Fin 3) := by
    have : a ∈ ({2} : Finset (Fin 3)) := hsubset ha
    simp at this
    exact this
  have h2mem : (2 : Fin 3) ∈ topCycleSet (P := profile) := by
    simp [ha2] at ha
    exact ha
  have h1not : (1 : Fin 3) ∉ topCycleSet (P := profile) := by
    intro h1mem
    have : (1 : Fin 3) ∈ ({2} : Finset (Fin 3)) := hsubset h1mem
    simp at this
  have hpos21 : margin_pos profile (2 : Fin 3) (1 : Fin 3) :=
    hdom.2 (2 : Fin 3) h2mem (1 : Fin 3) h1not
  exact (not_margin_pos_profile_2_1 hpos21)

lemma zero_mem_topCycle : (0 : Fin 3) ∈ topCycle profile := by
  classical
  have hA : Nonempty (Fin 3) := inferInstance
  have h0 : (0 : Fin 3) ∈ topCycleSet (P := profile) := zero_mem_topCycleSet
  simpa [topCycle, hA] using h0

lemma prefers_2_over_0 : ∀ v : Fin 2, Prefers profile v (2 : Fin 3) (0 : Fin 3) := by
  simp only [profile, prefers_iff_prefersInList]
  decide

end TopCycleParetoCounterexample

open TopCycleParetoCounterexample

theorem topCycle_not_pareto_efficiency : ¬ ParetoEfficiency topCycle := by
  intro hpareto
  have hmem : (0 : Fin 3) ∈ topCycle profile := zero_mem_topCycle
  have hpref : ∀ v : Fin 2, Prefers profile v (2 : Fin 3) (0 : Fin 3) :=
    prefers_2_over_0
  exact (hpareto profile (2 : Fin 3) (0 : Fin 3) hpref) hmem

end SocialChoice
