import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import SocialChoice.Axioms.Condorcet
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Baldwin.Defs
import SocialChoice.Rules.ScoringElimination.Baldwin.Condorcet
import SocialChoice.Rules.ScoringRules.Borda.C2Borda

namespace SocialChoice

open Finset
open scoped BigOperators

variable {V A : Type} [Fintype V] [Fintype A]

lemma univ_erase_eq_singleton_of_card_two {A : Type} [Fintype A] [DecidableEq A]
    (hcard : Fintype.card A = 2) {c d : A} (hcd : c ≠ d) :
    (Finset.univ.erase d : Finset A) = {c} := by
  classical
  refine Finset.eq_singleton_iff_unique_mem.mpr ?_
  refine ⟨?mem, ?unique⟩
  · simp [hcd]
  · intro x hx
    have hxne : x ≠ d := (Finset.mem_erase.mp hx).1
    have hx_or : x = c ∨ x = d := two_elems_eq_or_eq (A := A) hcard c d hcd x
    cases hx_or with
    | inl hxc => exact hxc
    | inr hxd => exact (hxne hxd).elim

lemma c2BordaScore_pos_of_two_of_neg
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (hcard : Fintype.card A = 2) {c d : A} (hcd : c ≠ d)
    (hneg : c2BordaScore P d < 0) : 0 < c2BordaScore P c := by
  have hsum := c2BordaScore_sum_zero (P := P)
  have hsum' :
      (Finset.univ.erase d).sum (fun x => c2BordaScore P x) + c2BordaScore P d = 0 := by
    have hsum' :=
      Finset.sum_erase_add (s := (Finset.univ : Finset A))
        (f := fun x => c2BordaScore P x) (a := d) (by simp)
    rw [hsum] at hsum'
    exact hsum'
  have herase : (Finset.univ.erase d : Finset A) = {c} :=
    univ_erase_eq_singleton_of_card_two (A := A) hcard (c := c) (d := d) hcd
  have hsum'' : c2BordaScore P c + c2BordaScore P d = 0 := by
    simpa [herase] using hsum'
  linarith

lemma CondorcetLoser_lower_borda_two
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (hcard : Fintype.card A = 2)
    (c d : A) (hcd : c ≠ d) (hloser : CondorcetLoser P d) :
    scoreCandidate P (fun r => bordaScore 2 r) d <
      scoreCandidate P (fun r => bordaScore 2 r) c := by
  have hneg : c2BordaScore P d < 0 :=
    c2BordaScore_neg_of_CondorcetLoser (P := P) (x := d) hloser
  have hpos : 0 < c2BordaScore P c :=
    c2BordaScore_pos_of_two_of_neg (P := P) (hcard := hcard) (c := c) (d := d) hcd hneg
  have hlt_c2 : c2BordaScore P d < c2BordaScore P c := lt_trans hneg hpos
  have hlt_borda :
      scoreCandidate P (fun r => bordaScore (Fintype.card A) r) d <
        scoreCandidate P (fun r => bordaScore (Fintype.card A) r) c :=
    (c2BordaScore_lt_iff_bordaScore_lt (P := P) (x := d) (y := c)).1 hlt_c2
  simpa [hcard] using hlt_borda

theorem baldwin_CondorcetLoser_criterion : CondorcetLoserCriterion baldwin := by
  intro V A _ _ P d hloser
  classical
  let : DecidableEq A := Classical.decEq A
  change d ∉ scoringEliminationAux bordaScore A P
  set n : Nat := Fintype.card A
  let Motive : Nat → Prop := fun k =>
    ∀ {A : Type} [Fintype A] [DecidableEq A],
      Fintype.card A = k →
        ∀ {V : Type} [Fintype V] (P : Profile V A) (d : A),
          CondorcetLoser P d → d ∉ scoringEliminationAux bordaScore A P
  have hStrong : Motive n := by
    classical
    refine Nat.strongRecOn (motive := Motive) n (fun k ih => ?_)
    intro A _ _ hcard V _ P d hloser
    classical
    have hnot_le_one : ¬ Fintype.card A ≤ 1 := by
      intro hle
      have hsubs : Subsingleton A := (Fintype.card_le_one_iff_subsingleton).1 hle
      rcases hloser.2 with ⟨y, hy⟩
      exact hy (Subsingleton.elim y d)
    by_cases htwo : Fintype.card A = 2
    · have haux :=
        scoringEliminationAux_eq_biUnion_of_not_card_le_one
          (score := bordaScore) (P := P) (hcard := hnot_le_one)
      intro hdmem
      have hdmem' := hdmem
      rw [haux] at hdmem'
      dsimp at hdmem'
      rcases (Finset.mem_biUnion.mp hdmem') with ⟨c, hcL, hd_in⟩
      have hcd : c ≠ d := by
        intro hEq
        subst hEq
        exact (not_mem_liftFinset_removed (c := c) _ hd_in)
      have hlt :
          scoreCandidate P (fun r => bordaScore (Fintype.card A) r) d <
            scoreCandidate P (fun r => bordaScore (Fintype.card A) r) c := by
        have hlt' :=
          CondorcetLoser_lower_borda_two (V := V) (A := A) (P := P) (hcard := htwo)
            (c := c) (d := d) hcd hloser
        simpa [htwo] using hlt'
      have hle :
          scoreCandidate P (fun r => bordaScore (Fintype.card A) r) c ≤
            scoreCandidate P (fun r => bordaScore (Fintype.card A) r) d :=
        scoreCandidate_le_of_mem_lowestScoring (P := P)
          (score := fun r => bordaScore (Fintype.card A) r) (c := c) (e := d) hcL
      exact (not_lt_of_ge hle) hlt
    · have hgt2 : 2 < Fintype.card A := by
        have hne2 : Fintype.card A ≠ 2 := htwo
        have hone : 1 < Fintype.card A := Nat.lt_of_not_ge hnot_le_one
        exact lt_of_le_of_ne (Nat.succ_le_of_lt hone) (Ne.symm hne2)
      have haux :=
        scoringEliminationAux_eq_biUnion_of_not_card_le_one
          (score := bordaScore) (P := P) (hcard := hnot_le_one)
      intro hdmem
      have hdmem' := hdmem
      rw [haux] at hdmem'
      dsimp at hdmem'
      rcases (Finset.mem_biUnion.mp hdmem') with ⟨c, hcL, hd_in⟩
      have hcd : c ≠ d := by
        intro hEq
        subst hEq
        exact (not_mem_liftFinset_removed (c := c) _ hd_in)
      have hdc : d ≠ c := by simpa [eq_comm] using hcd
      have hd_in' : (⟨d, hdc⟩ : {x : A // x ≠ c}) ∈
          scoringEliminationAux bordaScore {x : A // x ≠ c} (restrictProfile P c) := by
        rcases (mem_liftFinset_iff_subtype
          (s := scoringEliminationAux bordaScore {x : A // x ≠ c} (restrictProfile P c))
          (x := d)).1 hd_in with ⟨hdc', hd_in'⟩
        simpa using hd_in'
      have hltcard : Fintype.card {x : A // x ≠ c} < k := by
        simpa [hcard] using (card_restrict_lt (A := A) c)
      have hloser' :
          CondorcetLoser (restrictProfile P c) (⟨d, hdc⟩ : {x : A // x ≠ c}) :=
        CondorcetLoser_restrictProfile_of_two_lt_card (P := P) (hdc := hdc) (hcard := hgt2) hloser
      have hnot : (⟨d, hdc⟩ : {x : A // x ≠ c}) ∉
          scoringEliminationAux bordaScore {x : A // x ≠ c} (restrictProfile P c) := by
        have := ih (m := Fintype.card {x : A // x ≠ c}) hltcard
          (A := {x : A // x ≠ c}) (by rfl) (V := V) (P := restrictProfile P c)
          (d := (⟨d, hdc⟩ : {x : A // x ≠ c})) hloser'
        simpa using this
      exact hnot hd_in'
  exact hStrong (A := A) (by rfl) (V := V) (P := P) (d := d) hloser

end SocialChoice
