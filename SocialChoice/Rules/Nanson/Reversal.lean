import Mathlib.Tactic
import SocialChoice.Axioms.Reversal
import SocialChoice.Rules.Nanson.Defs

namespace SocialChoice

open Finset
open Classical

lemma nanson_score_pos_of_mem {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (hall : ¬ ∀ a, c2BordaScore P a = 0)
    (hsurv : (Finset.univ.filter (fun a => c2BordaScore P a > 0)).Nonempty)
    {x : A} (hx : x ∈ nanson P) :
    0 < c2BordaScore P x := by
  classical
  let : DecidableEq A := Classical.decEq A
  cases hcardA : Fintype.card A with
  | zero =>
      have hpos : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨x⟩
      have : False := by
        linarith [hcardA, hpos]
      exact this.elim
  | succ n =>
      have hx' :=
        (by
          simpa [nanson, nansonAux, hcardA, hall, hsurv] using hx)
      rcases Finset.mem_image.mp hx' with ⟨y, _hy, rfl⟩
      exact y.property

theorem nanson_reversal_symmetry : ReversalSymmetry nanson := by
  intro V A _ _ _ P hnot
  classical
  have hnotall : ¬ ∀ a, c2BordaScore P a = 0 := by
    intro hall
    classical
    let : DecidableEq A := Classical.decEq A
    have haux : nansonAux (Fintype.card A) A P = (Finset.univ : Finset A) := by
      cases hcardA : Fintype.card A with
      | zero =>
          simp [nansonAux]
      | succ n =>
          simp [nansonAux, hall]
    have : nanson P = (Finset.univ : Finset A) := by
      simpa [nanson] using haux
    exact hnot this
  obtain ⟨x, hxne⟩ := not_forall.mp hnotall
  have hpos_ex : ∃ a, 0 < c2BordaScore P a := by
    have hlt_or_gt : c2BordaScore P x < 0 ∨ 0 < c2BordaScore P x := by
      exact lt_or_gt_of_ne hxne
    cases hlt_or_gt with
    | inl hneg =>
        exact exists_pos_c2BordaScore_of_neg (P := P) (c := x) hneg
    | inr hpos =>
        exact ⟨x, hpos⟩
  have hneg_ex : ∃ a, c2BordaScore P a < 0 := by
    have hlt_or_gt : c2BordaScore P x < 0 ∨ 0 < c2BordaScore P x := by
      exact lt_or_gt_of_ne hxne
    cases hlt_or_gt with
    | inl hneg =>
        exact ⟨x, hneg⟩
    | inr hpos =>
        exact exists_neg_c2BordaScore_of_pos (P := P) (c := x) hpos
  have hsurv : (Finset.univ.filter (fun a => c2BordaScore P a > 0)).Nonempty := by
    rcases hpos_ex with ⟨y, hy⟩
    exact ⟨y, by simp [hy]⟩
  have hpos_rev : ∃ y, 0 < c2BordaScore (reverse_profile P) y := by
    rcases hneg_ex with ⟨y, hyneg⟩
    refine ⟨y, ?_⟩
    have : 0 < - c2BordaScore P y := by
      linarith
    simpa [c2BordaScore_reverse (P := P) (x := y)] using this
  have hsurv_rev :
      (Finset.univ.filter (fun a => c2BordaScore (reverse_profile P) a > 0)).Nonempty := by
    rcases hpos_rev with ⟨y, hy⟩
    exact ⟨y, by simp [hy]⟩
  have hnotall_rev : ¬ ∀ a, c2BordaScore (reverse_profile P) a = 0 := by
    intro hall
    have hall' : ∀ a, c2BordaScore P a = 0 := by
      intro a
      have h := hall a
      simpa [c2BordaScore_reverse (P := P) (x := a)] using h
    exact hnotall hall'
  ext x
  constructor
  · intro hx
    rcases Finset.mem_inter.mp hx with ⟨hxP, hxR⟩
    have hxpos : 0 < c2BordaScore P x :=
      nanson_score_pos_of_mem (P := P) hnotall hsurv hxP
    have hxpos_rev : 0 < c2BordaScore (reverse_profile P) x :=
      nanson_score_pos_of_mem (P := reverse_profile P) hnotall_rev hsurv_rev hxR
    have hxneg : c2BordaScore P x < 0 := by
      have : 0 < - c2BordaScore P x := by
        simpa [c2BordaScore_reverse (P := P) (x := x)] using hxpos_rev
      linarith
    exact (lt_asymm hxpos hxneg).elim
  · intro hx
    cases hx

end SocialChoice
