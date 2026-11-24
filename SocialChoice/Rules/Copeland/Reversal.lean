import Mathlib.Data.Finset.Max
import Mathlib.Tactic
import SocialChoice.Axioms.Reversal
import SocialChoice.Margin
import SocialChoice.Rules.Copeland.Defs

namespace SocialChoice

open Finset

lemma copelandPairScore2_neg (m : Int) :
    copelandPairScore2 (-m) = 2 - copelandPairScore2 m := by
  by_cases hpos : m > 0
  · have hnot : ¬ m < 0 := by
      exact not_lt_of_ge (le_of_lt hpos)
    have hnegzero : -m ≠ 0 := by
      have hmzero : m ≠ 0 := ne_of_gt hpos
      simpa [neg_eq_zero] using hmzero
    have hleft : copelandPairScore2 (-m) = 0 := by
      simp [copelandPairScore2, hnot, hnegzero]
    have hright : copelandPairScore2 m = 2 := by
      simp [copelandPairScore2, hpos]
    simp [hleft, hright]
  · by_cases hzero : m = 0
    · simp [copelandPairScore2, hzero]
    · have hneg : m < 0 := by
        have hmle : m ≤ 0 := not_lt.mp hpos
        exact lt_of_le_of_ne hmle hzero
      have hleft : copelandPairScore2 (-m) = 2 := by
        simp [copelandPairScore2, hneg]
      have hright : copelandPairScore2 m = 0 := by
        simp [copelandPairScore2, hpos, hzero]
      simp [hleft, hright]

lemma copelandScore2_reverse {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a : A) :
    copelandScore2 (reverse_profile P) a =
      (Fintype.card A : Int) * 2 - copelandScore2 P a := by
  classical
  have hmargin : ∀ b : A, margin (reverse_profile P) a b = - margin P a b := by
    intro b
    have h1 : margin (reverse_profile P) a b = margin P b a := by
      simpa using (margin_reverse_eq (P := P) (a := b) (b := a))
    have h2 : margin P b a = - margin P a b := by
      have hskew := margin_antisymmetric (P := P)
      simpa using (hskew b a)
    simpa [h2] using h1
  dsimp [copelandScore2]
  calc
    (Finset.univ.sum (fun b => copelandPairScore2 (margin (reverse_profile P) a b))) =
        Finset.univ.sum (fun b => copelandPairScore2 (- margin P a b)) := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          simp [hmargin b]
    _ = Finset.univ.sum (fun b => (2 - copelandPairScore2 (margin P a b))) := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          simp [copelandPairScore2_neg]
    _ =
        (Finset.univ.sum (fun _ : A => (2 : Int))) -
          (Finset.univ.sum (fun b => copelandPairScore2 (margin P a b))) := by
          simp [Finset.sum_sub_distrib]
    _ = (Fintype.card A : Int) * 2 - copelandScore2 P a := by
          simp [copelandScore2, Finset.sum_const]

lemma copelandScore2_le_max {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a : A) :
    copelandScore2 P a ≤ copelandMaxScore2 P := by
  classical
  let : Nonempty A := ⟨a⟩
  have hAuniv : (Finset.univ : Finset A).Nonempty := Finset.univ_nonempty
  let scores : Finset Int := Finset.univ.image (fun x => copelandScore2 P x)
  have hScores : scores.Nonempty := hAuniv.image (fun x => copelandScore2 P x)
  have hmem : copelandScore2 P a ∈ scores := by
    exact Finset.mem_image.mpr ⟨a, by simp, rfl⟩
  have hle : copelandScore2 P a ≤ Finset.max' scores hScores :=
    Finset.le_max' scores _ hmem
  simpa [copelandMaxScore2, hAuniv, scores] using hle

theorem copeland_reversal_symmetry : ReversalSymmetry copeland := by
  intro V A _ _ _ P hnot
  classical
  by_cases hA : Nonempty A
  · let : Nonempty A := hA
    ext x
    constructor
    · intro hx
      rcases Finset.mem_inter.mp hx with ⟨hxP, hxR⟩
      have hxP' : copelandScore2 P x = copelandMaxScore2 P := by
        have hxP' :
            x ∈ Finset.univ.filter (fun a => copelandScore2 P a = copelandMaxScore2 P) := by
          simpa [copeland, hA] using hxP
        exact (Finset.mem_filter.mp hxP').2
      have hxR' :
          copelandScore2 (reverse_profile P) x = copelandMaxScore2 (reverse_profile P) := by
        have hxR' :
            x ∈
              Finset.univ.filter
                (fun a =>
                  copelandScore2 (reverse_profile P) a =
                    copelandMaxScore2 (reverse_profile P)) := by
          simpa [copeland, hA] using hxR
        exact (Finset.mem_filter.mp hxR').2
      have hle_max : ∀ y, copelandScore2 P y ≤ copelandScore2 P x := by
        intro y
        have hle : copelandScore2 P y ≤ copelandMaxScore2 P :=
          copelandScore2_le_max (P := P) (a := y)
        simpa [hxP'] using hle
      have hge_min : ∀ y, copelandScore2 P x ≤ copelandScore2 P y := by
        intro y
        have hle : copelandScore2 (reverse_profile P) y ≤
            copelandMaxScore2 (reverse_profile P) :=
          copelandScore2_le_max (P := reverse_profile P) (a := y)
        have hle' : copelandScore2 (reverse_profile P) y ≤
            copelandScore2 (reverse_profile P) x := by
          simpa [hxR'] using hle
        have hle'' :
            (Fintype.card A : Int) * 2 - copelandScore2 P y ≤
              (Fintype.card A : Int) * 2 - copelandScore2 P x := by
          simpa [copelandScore2_reverse (P := P) (a := y),
            copelandScore2_reverse (P := P) (a := x)] using hle'
        linarith
      have hEq_all : ∀ y, copelandScore2 P y = copelandScore2 P x := by
        intro y
        exact le_antisymm (hle_max y) (hge_min y)
      have hEq_all' : ∀ y, copelandScore2 P y = copelandMaxScore2 P := by
        intro y
        calc
          copelandScore2 P y = copelandScore2 P x := hEq_all y
          _ = copelandMaxScore2 P := hxP'
      have hcopeland_univ : copeland P = (Finset.univ : Finset A) := by
        simp [copeland, hA, hEq_all']
      exact (hnot hcopeland_univ).elim
    · intro hx
      cases hx
  · simp [copeland, hA]

end SocialChoice
