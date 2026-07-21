import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Clones
import SocialChoice.ListBallot
import SocialChoice.Rules.Minimax.Defs

namespace SocialChoice

open Classical
open Finset

attribute [instance] Classical.decEq Classical.decPred

/-!
## Minimax fails independence of clones

Counterexample profile (candidates 0,1,2,3; 3 voters):
v0: 1 > 3 > 0 > 2
v1: 2 > 0 > 1 > 3
v2: 3 > 0 > 1 > 2

Clone set: {0,1,3}. Minimax selects all candidates.
Removing clones except 3 leaves {2,3}, and only 3 wins.
-/

namespace MinimaxIndependenceCounterexample

def ballot1302 : ListBallot 4 := ListBallot.mk' [1, 3, 0, 2]
def ballot2013 : ListBallot 4 := ListBallot.mk' [2, 0, 1, 3]
def ballot3012 : ListBallot 4 := ListBallot.mk' [3, 0, 1, 2]

def ballots : Fin 3 → ListBallot 4
  | ⟨0, _⟩ => ballot1302
  | ⟨1, _⟩ => ballot2013
  | ⟨2, _⟩ => ballot3012

noncomputable def profile : Profile (Fin 3) (Fin 4) :=
  profileOfListBallots ballots

def cloneSet : Set (Fin 4) := {0, 1, 3}

lemma cloneSet_profile : CloneSet profile cloneSet := by
  refine ⟨?_, ?_⟩
  · refine ⟨(0 : Fin 4), by simp [cloneSet]⟩
  intro v c hc
  have hc' : c = (2 : Fin 4) := by
    fin_cases c
    · have hmem : (0 : Fin 4) ∈ cloneSet := by simp [cloneSet]
      exact (hc hmem).elim
    · have hmem : (1 : Fin 4) ∈ cloneSet := by simp [cloneSet]
      exact (hc hmem).elim
    · rfl
    · have hmem : (3 : Fin 4) ∈ cloneSet := by simp [cloneSet]
      exact (hc hmem).elim
  subst hc'
  fin_cases v <;>
    (first
      | left
        intro x hx
        have hx' : x = (0 : Fin 4) ∨ x = (1 : Fin 4) ∨ x = (3 : Fin 4) := by
          simpa [cloneSet] using hx
        cases hx' with
        | inl hx0 =>
            subst hx0
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
        | inr hx13 =>
            cases hx13 with
            | inl hx1 =>
                subst hx1
                simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
            | inr hx3 =>
                subst hx3
                simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
      | right
        intro x hx
        have hx' : x = (0 : Fin 4) ∨ x = (1 : Fin 4) ∨ x = (3 : Fin 4) := by
          simpa [cloneSet] using hx
        cases hx' with
        | inl hx0 =>
            subst hx0
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
        | inr hx13 =>
            cases hx13 with
            | inl hx1 =>
                subst hx1
                simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
            | inr hx3 =>
                subst hx3
                simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide)

def rep : Fin 4 := 3

lemma votersPreferring_profile_0_1 :
    votersPreferring profile (0 : Fin 4) (1 : Fin 4) = ({1, 2} : Finset (Fin 3)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_1_0 :
    votersPreferring profile (1 : Fin 4) (0 : Fin 4) = ({0} : Finset (Fin 3)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_0_2 :
    votersPreferring profile (0 : Fin 4) (2 : Fin 4) = ({0, 2} : Finset (Fin 3)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_2_0 :
    votersPreferring profile (2 : Fin 4) (0 : Fin 4) = ({1} : Finset (Fin 3)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_0_3 :
    votersPreferring profile (0 : Fin 4) (3 : Fin 4) = ({1} : Finset (Fin 3)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_3_0 :
    votersPreferring profile (3 : Fin 4) (0 : Fin 4) = ({0, 2} : Finset (Fin 3)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_1_2 :
    votersPreferring profile (1 : Fin 4) (2 : Fin 4) = ({0, 2} : Finset (Fin 3)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_2_1 :
    votersPreferring profile (2 : Fin 4) (1 : Fin 4) = ({1} : Finset (Fin 3)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_1_3 :
    votersPreferring profile (1 : Fin 4) (3 : Fin 4) = ({0, 1} : Finset (Fin 3)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_3_1 :
    votersPreferring profile (3 : Fin 4) (1 : Fin 4) = ({2} : Finset (Fin 3)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_2_3 :
    votersPreferring profile (2 : Fin 4) (3 : Fin 4) = ({1} : Finset (Fin 3)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_3_2 :
    votersPreferring profile (3 : Fin 4) (2 : Fin 4) = ({0, 2} : Finset (Fin 3)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma margin_profile_0_1 : margin profile (0 : Fin 4) (1 : Fin 4) = 1 := by
  have h1 :
      (Finset.univ.filter (fun v => Prefers profile v (0 : Fin 4) (1 : Fin 4))) =
        ({1, 2} : Finset (Fin 3)) := by
    simpa [votersPreferring] using votersPreferring_profile_0_1
  have h2 :
      (Finset.univ.filter (fun v => Prefers profile v (1 : Fin 4) (0 : Fin 4))) =
        ({0} : Finset (Fin 3)) := by
    simpa [votersPreferring] using votersPreferring_profile_1_0
  simp [margin, h1, h2]

lemma margin_profile_0_2 : margin profile (0 : Fin 4) (2 : Fin 4) = 1 := by
  have h1 :
      (Finset.univ.filter (fun v => Prefers profile v (0 : Fin 4) (2 : Fin 4))) =
        ({0, 2} : Finset (Fin 3)) := by
    simpa [votersPreferring] using votersPreferring_profile_0_2
  have h2 :
      (Finset.univ.filter (fun v => Prefers profile v (2 : Fin 4) (0 : Fin 4))) =
        ({1} : Finset (Fin 3)) := by
    simpa [votersPreferring] using votersPreferring_profile_2_0
  simp [margin, h1, h2]

lemma margin_profile_0_3 : margin profile (0 : Fin 4) (3 : Fin 4) = -1 := by
  have h1 :
      (Finset.univ.filter (fun v => Prefers profile v (0 : Fin 4) (3 : Fin 4))) =
        ({1} : Finset (Fin 3)) := by
    simpa [votersPreferring] using votersPreferring_profile_0_3
  have h2 :
      (Finset.univ.filter (fun v => Prefers profile v (3 : Fin 4) (0 : Fin 4))) =
        ({0, 2} : Finset (Fin 3)) := by
    simpa [votersPreferring] using votersPreferring_profile_3_0
  simp [margin, h1, h2]

lemma margin_profile_1_2 : margin profile (1 : Fin 4) (2 : Fin 4) = 1 := by
  have h1 :
      (Finset.univ.filter (fun v => Prefers profile v (1 : Fin 4) (2 : Fin 4))) =
        ({0, 2} : Finset (Fin 3)) := by
    simpa [votersPreferring] using votersPreferring_profile_1_2
  have h2 :
      (Finset.univ.filter (fun v => Prefers profile v (2 : Fin 4) (1 : Fin 4))) =
        ({1} : Finset (Fin 3)) := by
    simpa [votersPreferring] using votersPreferring_profile_2_1
  simp [margin, h1, h2]

lemma margin_profile_1_3 : margin profile (1 : Fin 4) (3 : Fin 4) = 1 := by
  have h1 :
      (Finset.univ.filter (fun v => Prefers profile v (1 : Fin 4) (3 : Fin 4))) =
        ({0, 1} : Finset (Fin 3)) := by
    simpa [votersPreferring] using votersPreferring_profile_1_3
  have h2 :
      (Finset.univ.filter (fun v => Prefers profile v (3 : Fin 4) (1 : Fin 4))) =
        ({2} : Finset (Fin 3)) := by
    simpa [votersPreferring] using votersPreferring_profile_3_1
  simp [margin, h1, h2]

lemma margin_profile_2_3 : margin profile (2 : Fin 4) (3 : Fin 4) = -1 := by
  have h1 :
      (Finset.univ.filter (fun v => Prefers profile v (2 : Fin 4) (3 : Fin 4))) =
        ({1} : Finset (Fin 3)) := by
    simpa [votersPreferring] using votersPreferring_profile_2_3
  have h2 :
      (Finset.univ.filter (fun v => Prefers profile v (3 : Fin 4) (2 : Fin 4))) =
        ({0, 2} : Finset (Fin 3)) := by
    simpa [votersPreferring] using votersPreferring_profile_3_2
  simp [margin, h1, h2]

lemma margin_profile_3_0 : margin profile (3 : Fin 4) (0 : Fin 4) = 1 := by
  have h := margin_antisymmetric (P := profile) (a := (3 : Fin 4)) (b := (0 : Fin 4))
  simpa [margin_profile_0_3] using h

lemma margin_profile_3_2 : margin profile (3 : Fin 4) (2 : Fin 4) = 1 := by
  have h := margin_antisymmetric (P := profile) (a := (3 : Fin 4)) (b := (2 : Fin 4))
  simpa [margin_profile_2_3] using h

lemma maxLoss_profile_2_le : maxLoss profile (2 : Fin 4) ≤ 1 := by
  refine maxLoss_le_of_forall_margin_le (P := profile) (a := (2 : Fin 4)) (k := 1) ?_
  intro b
  fin_cases b <;>
    simp [margin_profile_0_2, margin_profile_1_2, margin_profile_3_2, self_margin_zero]

lemma maxLoss_profile_2_ge : (1 : Int) ≤ maxLoss profile (2 : Fin 4) := by
  have hle := margin_le_maxLoss (P := profile) (a := (2 : Fin 4)) (b := (0 : Fin 4))
  simpa [margin_profile_0_2] using hle

lemma maxLoss_profile_2 : maxLoss profile (2 : Fin 4) = 1 :=
  le_antisymm maxLoss_profile_2_le maxLoss_profile_2_ge

lemma maxLoss_profile_ge_one : ∀ a : Fin 4, (1 : Int) ≤ maxLoss profile a := by
  intro a
  fin_cases a
  ·
    have hle := margin_le_maxLoss (P := profile) (a := (0 : Fin 4)) (b := (3 : Fin 4))
    simpa [margin_profile_3_0] using hle
  ·
    have hle := margin_le_maxLoss (P := profile) (a := (1 : Fin 4)) (b := (0 : Fin 4))
    simpa [margin_profile_0_1] using hle
  ·
    have hle := margin_le_maxLoss (P := profile) (a := (2 : Fin 4)) (b := (0 : Fin 4))
    simpa [margin_profile_0_2] using hle
  ·
    have hle := margin_le_maxLoss (P := profile) (a := (3 : Fin 4)) (b := (1 : Fin 4))
    simpa [margin_profile_1_3] using hle

lemma minimaxScore_profile : minimaxScore profile = 1 := by
  have hA : (Finset.univ : Finset (Fin 4)).Nonempty := by simp
  have hmin_ge :
      (1 : Int) ≤ minimaxScore profile :=
    le_minimaxScore_of_forall (P := profile) (k := 1) hA maxLoss_profile_ge_one
  have hmin_le :
      minimaxScore profile ≤ 1 := by
    have hle := minimaxScore_le_of_candidate (P := profile) (a := (2 : Fin 4))
    simpa [maxLoss_profile_2] using hle
  exact le_antisymm hmin_le hmin_ge

lemma minimax_profile_has_2 : (2 : Fin 4) ∈ minimax profile := by
  have hmem :
      (2 : Fin 4) ∈ Finset.univ.filter (fun a : Fin 4 => maxLoss profile a = minimaxScore profile) := by
    simp [maxLoss_profile_2, minimaxScore_profile]
  have hnonempty : Nonempty (Fin 4) := inferInstance
  simpa [minimax, hnonempty] using hmem

def cand2clone : {a : Fin 4 // clonePred cloneSet rep a} :=
  ⟨2, Or.inl (by simp [cloneSet])⟩

def cand3clone : {a : Fin 4 // clonePred cloneSet rep a} :=
  ⟨3, Or.inr rfl⟩

lemma clonePred_eq_23 (b : Fin 4) (hb : clonePred cloneSet rep b) : b = 2 ∨ b = 3 := by
  fin_cases b
  ·
    have hfalse : False := by
      have hb' := hb
      simp [cloneSet, clonePred, rep] at hb'
    exact hfalse.elim
  ·
    have hfalse : False := by
      have hb' := hb
      simp [cloneSet, clonePred, rep] at hb'
    exact hfalse.elim
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma margin_clone_3_2 :
    margin (removeClonesExcept profile cloneSet rep) cand3clone cand2clone = 1 := by
  change margin (restrictCandidates profile (clonePred cloneSet rep)) cand3clone cand2clone = 1
  calc
    _ = margin profile (3 : Fin 4) (2 : Fin 4) :=
      (margin_eq_margin_restrictCandidates (P := profile) (p := clonePred cloneSet rep)
        (a := cand3clone) (b := cand2clone)).symm
    _ = 1 := margin_profile_3_2

lemma margin_clone_2_3 :
    margin (removeClonesExcept profile cloneSet rep) cand2clone cand3clone = -1 := by
  change margin (restrictCandidates profile (clonePred cloneSet rep)) cand2clone cand3clone = -1
  calc
    _ = margin profile (2 : Fin 4) (3 : Fin 4) :=
      (margin_eq_margin_restrictCandidates (P := profile) (p := clonePred cloneSet rep)
        (a := cand2clone) (b := cand3clone)).symm
    _ = -1 := margin_profile_2_3

lemma maxLoss_clone_cand2_le :
    maxLoss (removeClonesExcept profile cloneSet rep) cand2clone ≤ 1 := by
  refine maxLoss_le_of_forall_margin_le
    (P := removeClonesExcept profile cloneSet rep) (a := cand2clone) (k := 1) ?_
  intro b
  rcases b with ⟨b, hb⟩
  have hb' : b = 2 ∨ b = 3 := clonePred_eq_23 b hb
  cases hb' with
  | inl hb2 =>
      subst hb2
      have hb_eq :
          (⟨2, hb⟩ : {a : Fin 4 // clonePred cloneSet rep a}) = cand2clone := by
        apply Subtype.ext
        rfl
      simp [hb_eq, self_margin_zero]
  | inr hb3 =>
      subst hb3
      have hb_eq :
          (⟨3, hb⟩ : {a : Fin 4 // clonePred cloneSet rep a}) = cand3clone := by
        apply Subtype.ext
        rfl
      simp [hb_eq, margin_clone_3_2]

lemma maxLoss_clone_cand2_ge :
    (1 : Int) ≤ maxLoss (removeClonesExcept profile cloneSet rep) cand2clone := by
  have hle := margin_le_maxLoss
    (P := removeClonesExcept profile cloneSet rep) (a := cand2clone) (b := cand3clone)
  simpa [margin_clone_3_2] using hle

lemma maxLoss_clone_cand2 :
    maxLoss (removeClonesExcept profile cloneSet rep) cand2clone = 1 :=
  le_antisymm maxLoss_clone_cand2_le maxLoss_clone_cand2_ge

lemma maxLoss_clone_cand3_le :
    maxLoss (removeClonesExcept profile cloneSet rep) cand3clone ≤ 0 := by
  refine maxLoss_le_of_forall_margin_le
    (P := removeClonesExcept profile cloneSet rep) (a := cand3clone) (k := 0) ?_
  intro b
  rcases b with ⟨b, hb⟩
  have hb' : b = 2 ∨ b = 3 := clonePred_eq_23 b hb
  cases hb' with
  | inl hb2 =>
      subst hb2
      have hb_eq :
          (⟨2, hb⟩ : {a : Fin 4 // clonePred cloneSet rep a}) = cand2clone := by
        apply Subtype.ext
        rfl
      simp [hb_eq, margin_clone_2_3]
  | inr hb3 =>
      subst hb3
      have hb_eq :
          (⟨3, hb⟩ : {a : Fin 4 // clonePred cloneSet rep a}) = cand3clone := by
        apply Subtype.ext
        rfl
      simp [hb_eq, self_margin_zero]

lemma maxLoss_clone_cand3_ge :
    (0 : Int) ≤ maxLoss (removeClonesExcept profile cloneSet rep) cand3clone := by
  have hle := margin_le_maxLoss
    (P := removeClonesExcept profile cloneSet rep) (a := cand3clone) (b := cand3clone)
  simpa [self_margin_zero] using hle

lemma maxLoss_clone_cand3 :
    maxLoss (removeClonesExcept profile cloneSet rep) cand3clone = 0 :=
  le_antisymm maxLoss_clone_cand3_le maxLoss_clone_cand3_ge

lemma minimaxScore_clone :
    minimaxScore (removeClonesExcept profile cloneSet rep) = 0 := by
  have hA :
      (Finset.univ :
        Finset {a : Fin 4 // clonePred cloneSet rep a}).Nonempty := by
    refine ⟨cand3clone, by simp⟩
  have hmin_ge :
      (0 : Int) ≤ minimaxScore (removeClonesExcept profile cloneSet rep) := by
    refine le_minimaxScore_of_forall
      (P := removeClonesExcept profile cloneSet rep) (k := 0) hA ?_
    intro a
    have hle := margin_le_maxLoss
      (P := removeClonesExcept profile cloneSet rep) (a := a) (b := a)
    simpa [self_margin_zero] using hle
  have hmin_le :
      minimaxScore (removeClonesExcept profile cloneSet rep) ≤ 0 := by
    have hle := minimaxScore_le_of_candidate
      (P := removeClonesExcept profile cloneSet rep) (a := cand3clone)
    simpa [maxLoss_clone_cand3] using hle
  exact le_antisymm hmin_le hmin_ge

lemma minimax_cloneProfile_not_2 :
    (⟨2, Or.inl (by simp [cloneSet])⟩ :
      {a : Fin 4 // clonePred cloneSet rep a}) ∉
      minimax (removeClonesExcept profile cloneSet rep) := by
  have hnotmem :
      cand2clone ∉
        Finset.univ.filter (fun a :
          {a : Fin 4 // clonePred cloneSet rep a} =>
            maxLoss (removeClonesExcept profile cloneSet rep) a =
              minimaxScore (removeClonesExcept profile cloneSet rep)) := by
    intro hmem
    have hEq := (Finset.mem_filter.mp hmem).2
    have hEq' := hEq
    simp [maxLoss_clone_cand2, minimaxScore_clone] at hEq'
  have hnonempty : Nonempty {a : Fin 4 // clonePred cloneSet rep a} := ⟨cand3clone⟩
  change cand2clone ∉ minimax (removeClonesExcept profile cloneSet rep)
  simpa [minimax, hnonempty] using hnotmem

end MinimaxIndependenceCounterexample

open MinimaxIndependenceCounterexample

theorem minimax_not_independenceOfClones : ¬ IndependenceOfClones minimax := by
  intro hind
  have hclone : CloneSet profile cloneSet := cloneSet_profile
  have hx : rep ∈ cloneSet := by
    simp [rep, cloneSet]
  have h := hind (P := profile) (X := cloneSet) (x := rep) hclone hx
  have hc : (2 : Fin 4) ∉ cloneSet := by
    simp [cloneSet]
  have hnonclone := h.1 (2 : Fin 4) hc
  have hleft :
      (⟨2, Or.inl hc⟩ :
        {a : Fin 4 // clonePred cloneSet rep a}) ∈
        minimax (removeClonesExcept profile cloneSet rep) := by
    exact (hnonclone).1 minimax_profile_has_2
  exact (minimax_cloneProfile_not_2 hleft).elim

end SocialChoice
