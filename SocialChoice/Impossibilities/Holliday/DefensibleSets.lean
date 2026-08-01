import Mathlib.Tactic
import SocialChoice.Impossibilities.Holliday.CondorcetLosers
import SocialChoice.Impossibilities.Holliday.DefensibleSlack
import SocialChoice.Rules.DefensibleSet.Defs

namespace SocialChoice

open Finset
open scoped BigOperators

namespace Holliday

lemma margin_P1Profile_d_c : margin P1Profile d c = (-41 : Int) := by
  have h := (margin_antisymmetric (P := P1Profile)) d c
  simp [margin_P1Profile_c_d] at h
  exact h

lemma margin_P1Profile_e_c : margin P1Profile e c = (-87 : Int) := by
  have h := (margin_antisymmetric (P := P1Profile)) e c
  simp [margin_P1Profile_c_e] at h
  exact h

lemma defensible_P1_a : a ∈ defensibleSetOf P1Profile := by
  classical
  refine (mem_defensibleSet_iff (P := P1Profile) (x := a)).2 ?_
  intro y
  fin_cases y
  · refine ⟨a, ?_⟩
    simp [self_margin_zero]
  · refine ⟨e, ?_⟩
    simp [margin_P1Profile_e_b, margin_P1Profile_b_a]
  · refine ⟨a, ?_⟩
    simp [margin_P1Profile_a_c, margin_P1Profile_c_a]
  · refine ⟨a, ?_⟩
    simp [margin_P1Profile_a_d, margin_P1Profile_d_a]
  · refine ⟨a, ?_⟩
    simp [margin_P1Profile_a_e, margin_P1Profile_e_a]

lemma defensible_P1_d : d ∈ defensibleSetOf P1Profile := by
  classical
  refine (mem_defensibleSet_iff (P := P1Profile) (x := d)).2 ?_
  intro y
  fin_cases y
  · refine ⟨b, ?_⟩
    simp [margin_P1Profile_b_a, margin_P1Profile_a_d]
  · refine ⟨e, ?_⟩
    simp [margin_P1Profile_e_b, margin_P1Profile_b_d]
  · refine ⟨a, ?_⟩
    simp [margin_P1Profile_a_c, margin_P1Profile_c_d]
  · refine ⟨a, ?_⟩
    simp [self_margin_zero, margin_P1Profile_a_d]
  · refine ⟨a, ?_⟩
    simp [margin_P1Profile_a_e, margin_P1Profile_e_d]

lemma not_defensible_P1_b : b ∉ defensibleSetOf P1Profile := by
  classical
  intro hb
  have hb' := (mem_defensibleSet_iff (P := P1Profile) (x := b)).1 hb
  rcases hb' e with ⟨z, hz⟩
  fin_cases z
  · have hz' : (47 : Int) ≥ 91 := by
      simp [margin_P1Profile_a_e, margin_P1Profile_e_b] at hz
    exact (by decide : ¬ (47 : Int) ≥ 91) hz'
  · have hz' : (-91 : Int) ≥ 91 := by
      simp [margin_P1Profile_b_e, margin_P1Profile_e_b] at hz
    exact (by decide : ¬ (-91 : Int) ≥ 91) hz'
  · have hz' : (87 : Int) ≥ 91 := by
      simp [margin_P1Profile_c_e, margin_P1Profile_e_b] at hz
    exact (by decide : ¬ (87 : Int) ≥ 91) hz'
  · have hz' : (-5 : Int) ≥ 91 := by
      simp [margin_P1Profile_d_e, margin_P1Profile_e_b] at hz
    exact (by decide : ¬ (-5 : Int) ≥ 91) hz'
  · have hz' : (0 : Int) ≥ 91 := by
      simp [self_margin_zero, margin_P1Profile_e_b] at hz
    exact (by decide : ¬ (0 : Int) ≥ 91) hz'

lemma not_defensible_P1_c : c ∉ defensibleSetOf P1Profile := by
  classical
  intro hc
  have hc' := (mem_defensibleSet_iff (P := P1Profile) (x := c)).1 hc
  rcases hc' a with ⟨z, hz⟩
  fin_cases z
  · have hz' : (0 : Int) ≥ 83 := by
      simp [self_margin_zero, margin_P1Profile_a_c] at hz
    exact (by decide : ¬ (0 : Int) ≥ 83) hz'
  · have hz' : (81 : Int) ≥ 83 := by
      simp [margin_P1Profile_b_a, margin_P1Profile_a_c] at hz
    exact (by decide : ¬ (81 : Int) ≥ 83) hz'
  · have hz' : (-83 : Int) ≥ 83 := by
      simp [margin_P1Profile_c_a, margin_P1Profile_a_c] at hz
    exact (by decide : ¬ (-83 : Int) ≥ 83) hz'
  · have hz' : (-1 : Int) ≥ 83 := by
      simp [margin_P1Profile_d_a, margin_P1Profile_a_c] at hz
    exact (by decide : ¬ (-1 : Int) ≥ 83) hz'
  · have hz' : (-47 : Int) ≥ 83 := by
      simp [margin_P1Profile_e_a, margin_P1Profile_a_c] at hz
    exact (by decide : ¬ (-47 : Int) ≥ 83) hz'

lemma not_defensible_P1_e : e ∉ defensibleSetOf P1Profile := by
  classical
  intro he
  have he' := (mem_defensibleSet_iff (P := P1Profile) (x := e)).1 he
  rcases he' c with ⟨z, hz⟩
  fin_cases z
  · have hz' : (83 : Int) ≥ 87 := by
      simp [margin_P1Profile_a_c, margin_P1Profile_c_e] at hz
    exact (by decide : ¬ (83 : Int) ≥ 87) hz'
  · have hz' : (37 : Int) ≥ 87 := by
      simp [margin_P1Profile_b_c, margin_P1Profile_c_e] at hz
    exact (by decide : ¬ (37 : Int) ≥ 87) hz'
  · have hz' : (0 : Int) ≥ 87 := by
      simp [self_margin_zero, margin_P1Profile_c_e] at hz
    exact (by decide : ¬ (0 : Int) ≥ 87) hz'
  · have hz' : (-41 : Int) ≥ 87 := by
      simp [margin_P1Profile_d_c, margin_P1Profile_c_e] at hz
    exact (by decide : ¬ (-41 : Int) ≥ 87) hz'
  · have hz' : (-87 : Int) ≥ 87 := by
      simp [margin_P1Profile_e_c, margin_P1Profile_c_e] at hz
    exact (by decide : ¬ (-87 : Int) ≥ 87) hz'

lemma defensibleSet_P1 : defensibleSetOf P1Profile = ({a, d} : Finset A5) := by
  classical
  ext x
  fin_cases x
  · simp [defensible_P1_a, a, d]
  · simp [not_defensible_P1_b, a, d]
  · simp [not_defensible_P1_c, a, d]
  · simp [defensible_P1_d, a, d]
  · simp [not_defensible_P1_e, a, d]

end Holliday

end SocialChoice
