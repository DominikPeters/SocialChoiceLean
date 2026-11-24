import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import SocialChoice.Axioms.Condorcet
import SocialChoice.Rules.Nanson.Defs
import SocialChoice.Rules.ScoringRules.Borda.C2Borda

namespace SocialChoice

open Finset

lemma not_mem_liftWinners_of_not_pred {A : Type} {p : A → Prop} [DecidablePred p]
    {s : Finset {a : A // p a}} {c : A} (hc : ¬ p c) :
    c ∉ liftWinners s := by
  classical
  intro hc'
  rcases Finset.mem_image.mp hc' with ⟨x, hx, hxc⟩
  have : p c := by
    simpa [hxc] using x.property
  exact hc this

theorem nanson_CondorcetLoser_criterion : CondorcetLoserCriterion nanson := by
  intro V A _ _ P c hloser
  classical
  let : DecidableEq A := Classical.decEq A
  have hneg : c2BordaScore P c < 0 :=
    c2BordaScore_neg_of_CondorcetLoser (P := P) (x := c) hloser
  have hpos_ex : ∃ d, 0 < c2BordaScore P d :=
    exists_pos_c2BordaScore_of_neg (P := P) (c := c) hneg
  have hall : ¬ ∀ a : A, c2BordaScore P a = 0 := by
    intro hall
    have h0 := hall c
    exact (ne_of_lt hneg) h0
  let p : A → Prop := fun a => c2BordaScore P a > 0
  have hsurv : (Finset.univ.filter (fun a => p a)).Nonempty := by
    rcases hpos_ex with ⟨d, hdpos⟩
    exact ⟨d, by simp [p, hdpos]⟩
  have hcnotp : ¬ p c := by
    dsimp [p]
    exact not_lt_of_ge (le_of_lt hneg)
  have hcard_pos : 0 < Fintype.card A := by
    rcases hloser.2 with ⟨y, _hy⟩
    exact Fintype.card_pos_iff.mpr ⟨y⟩
  have hcard_ne_zero : Fintype.card A ≠ 0 := ne_of_gt hcard_pos
  simp [nanson]
  cases hcardA : Fintype.card A with
  | zero =>
      exact (hcard_ne_zero hcardA).elim
  | succ n =>
      change c ∉ nansonAux (Nat.succ n) A P
      have hnot :
          c ∉ liftWinners (nansonAux n {a : A // p a} (restrictCandidates P p)) :=
        not_mem_liftWinners_of_not_pred (p := p)
          (s := nansonAux n {a : A // p a} (restrictCandidates P p)) hcnotp
      simpa [nansonAux, hall, hsurv, p] using hnot

end SocialChoice
