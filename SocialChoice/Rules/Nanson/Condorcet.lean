import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import SocialChoice.Axioms.Condorcet
import SocialChoice.Rules.Nanson.Defs
import SocialChoice.Rules.ScoringRules.Borda.C2Borda

namespace SocialChoice

open Finset

lemma c2BordaScore_eq_zero_of_subsingleton {V A : Type} [Fintype V] [Fintype A]
    [Subsingleton A] (P : Profile V A) (a : A) :
    c2BordaScore P a = 0 := by
  classical
  have hsum := c2BordaScore_sum_zero (P := P)
  have huniv : (Finset.univ : Finset A) = {a} := by
    ext x
    constructor
    · intro _hx
      have hx' : x = a := Subsingleton.elim _ _
      simp [hx']
    · intro _hx
      simp
  simp [huniv] at hsum
  exact hsum

lemma CondorcetWinner_restrictCandidates {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (p : A → Prop) [DecidablePred p] {c : A} (hc : p c)
    (hwin : CondorcetWinner P c) :
    CondorcetWinner (restrictCandidates P p) (⟨c, hc⟩ : {x : A // p x}) := by
  intro y hy
  have hne : c ≠ (y : A) := by
    intro hEq
    apply hy
    apply Subtype.ext
    exact hEq.symm
  have hpos : margin_pos P c (y : A) :=
    (CondorcetWinner_iff_margin_pos P c).mp hwin (y : A) hne
  have hpos' : margin_pos (restrictCandidates P p) (⟨c, hc⟩ : {x : A // p x}) y := by
    dsimp [margin_pos] at hpos ⊢
    have heq := margin_eq_margin_restrictCandidates (P := P) (p := p)
      (a := (⟨c, hc⟩ : {x : A // p x})) (b := y)
    simpa [heq] using hpos
  exact (strictMajority_votersPreferring_iff_margin_pos
    (P := restrictCandidates P p) (c := (⟨c, hc⟩ : {x : A // p x})) (d := y)
      (hcd := Ne.symm hy)).2
    hpos'

theorem nanson_condorcet_consistency : CondorcetConsistency nanson := by
  intro V A _ _ P c hwin
  classical
  let : DecidableEq A := Classical.decEq A
  simp [nanson]
  set k : Nat := Fintype.card A
  let Motive : Nat → Prop := fun n =>
    ∀ {A : Type} [Fintype A] [DecidableEq A],
      Fintype.card A ≤ n →
        ∀ {V : Type} [Fintype V] (P : Profile V A) (c : A),
          CondorcetWinner P c → nansonAux n A P = {c}
  have hStrong : Motive k := by
    classical
    refine Nat.strongRecOn (motive := Motive) k ?_
    intro n ih A _ _ hcard_le V _ P c hwin
    classical
    by_cases hle : Fintype.card A ≤ 1
    · have hsub : Subsingleton A := (Fintype.card_le_one_iff_subsingleton).1 hle
      have huniv : (Finset.univ : Finset A) = {c} := by
        ext x
        constructor
        · intro _hx
          have hx' : x = c := Subsingleton.elim _ _
          simp [hx']
        · intro _hx
          simp
      have haux : nansonAux n A P = (Finset.univ : Finset A) := by
        cases n with
        | zero =>
            simp [nansonAux]
        | succ n =>
            have hall : ∀ a : A, c2BordaScore P a = 0 := by
              intro a
              exact c2BordaScore_eq_zero_of_subsingleton (P := P) (a := a)
            simp [nansonAux, hall]
      simp [haux, huniv]
    · have hcard_gt1 : 1 < Fintype.card A := Nat.lt_of_not_ge hle
      rcases Fintype.exists_ne_of_one_lt_card hcard_gt1 c with ⟨y, hy⟩
      have hpos : 0 < c2BordaScore P c :=
        c2BordaScore_pos_of_CondorcetWinner (P := P) (x := c) hwin ⟨y, hy⟩
      have hall : ¬ ∀ a : A, c2BordaScore P a = 0 := by
        intro hall
        have h0 := hall c
        exact (ne_of_gt hpos) h0
      let p : A → Prop := fun a => c2BordaScore P a > 0
      have hcpos : p c := hpos
      have hsurv : (Finset.univ.filter (fun a => p a)).Nonempty := by
        refine ⟨c, ?_⟩
        simp [p, hcpos]
      let P' : Profile V {a : A // p a} := restrictCandidates P p
      have hwin' :
          CondorcetWinner P' (⟨c, hcpos⟩ : {a : A // p a}) := by
        exact CondorcetWinner_restrictCandidates (P := P) (p := p) (hc := hcpos) hwin
      have hneg : ∃ d, c2BordaScore P d < 0 :=
        exists_neg_c2BordaScore_of_pos (P := P) (c := c) hpos
      rcases hneg with ⟨d, hdneg⟩
      have hnotp : ¬ p d := by
        dsimp [p]
        have hle : c2BordaScore P d ≤ 0 := le_of_lt hdneg
        exact not_lt_of_ge hle
      have hcard_lt : Fintype.card {a : A // p a} < Fintype.card A :=
        Fintype.card_subtype_lt (p := p) (x := d) hnotp
      cases n with
      | zero =>
          have hpos' : 0 < (Fintype.card A) := Fintype.card_pos_iff.mpr ⟨c⟩
          have hle0 : Fintype.card A ≤ 0 := hcard_le
          exact (False.elim ((not_lt_of_ge hle0) hpos'))
      | succ n =>
          have hcard_le' : Fintype.card {a : A // p a} ≤ n := by
            have hlt : Fintype.card {a : A // p a} < Nat.succ n :=
              lt_of_lt_of_le hcard_lt hcard_le
            exact Nat.lt_succ_iff.mp hlt
          have hrec :
              nansonAux n {a : A // p a} P' = {⟨c, hcpos⟩} := by
            have := ih (m := n) (Nat.lt_succ_self n)
              (A := {a : A // p a}) hcard_le' (V := V) (P := P')
              (c := (⟨c, hcpos⟩ : {a : A // p a})) hwin'
            exact this
          have haux :
              nansonAux (Nat.succ n) A P =
                liftWinners (nansonAux n {a : A // p a} P') := by
            simp [nansonAux, hall, hsurv, p, P']
          calc
            nansonAux (Nat.succ n) A P =
                liftWinners (nansonAux n {a : A // p a} P') := haux
            _ = liftWinners {⟨c, hcpos⟩} := by
                simp [hrec]
            _ = {c} := by
                simp [liftWinners]
  exact hStrong (A := A) (by simp [k]) (V := V) (P := P) (c := c) hwin

end SocialChoice
