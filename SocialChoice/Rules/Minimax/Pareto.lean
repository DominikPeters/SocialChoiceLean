import Mathlib.Tactic
import SocialChoice.Axioms.Pareto
import SocialChoice.Margin
import SocialChoice.Rank
import SocialChoice.Rules.Minimax.Defs

namespace SocialChoice

open Finset

private lemma margin_le_card_sub_one_of_topRank {V A : Type} [Fintype V] [Fintype A] [Nonempty V]
    (P : Profile V A) (v0 : V) (a b : A) (hb : b ≠ a) (htop : TopRank P v0 a) :
    margin P b a ≤ (Fintype.card V : Int) - 1 := by
  classical
  have hv0 : Prefers P v0 a b := htop b hb
  let SA : Finset V := Finset.univ.filter (fun v => Prefers P v a b)
  let SB : Finset V := Finset.univ.filter (fun v => Prefers P v b a)
  have hv0_mem : v0 ∈ SA := by
    simp [SA, hv0]
  have hSA_pos : 1 ≤ SA.card :=
    Finset.one_le_card.mpr ⟨v0, hv0_mem⟩
  have hv0_not : v0 ∉ SB := by
    intro hv
    have hv' : Prefers P v0 b a := (Finset.mem_filter.mp hv).2
    let _ := P.pref v0
    exact (lt_asymm hv' hv0)
  have hsubset : SB ⊆ (Finset.univ.erase v0) := by
    intro v hv
    have hv' : v ≠ v0 := by
      intro hEq
      subst hEq
      exact hv0_not hv
    exact Finset.mem_erase.mpr ⟨hv', by simp⟩
  have hSB_le_nat : SB.card ≤ (Finset.univ.erase v0).card :=
    Finset.card_le_card hsubset
  have hSB_le_nat' : SB.card ≤ Fintype.card V - 1 := by
    have hcard_erase :
        (Finset.univ.erase v0).card = Fintype.card V - 1 := by
      have hcard_erase' :
          (Finset.univ.erase v0).card = (Finset.univ : Finset V).card - 1 :=
        Finset.card_erase_of_mem (Finset.mem_univ v0)
      calc
        (Finset.univ.erase v0).card
            = (Finset.univ : Finset V).card - 1 := hcard_erase'
        _ = Fintype.card V - 1 := by simp
    simpa [hcard_erase] using hSB_le_nat
  have hpos : 1 ≤ Fintype.card V :=
    Nat.succ_le_iff.2 Fintype.card_pos
  have hSB_le : (Int.ofNat SB.card) ≤ (Fintype.card V : Int) - 1 := by
    have hSB_le' : (Int.ofNat SB.card) ≤ Int.ofNat (Fintype.card V - 1) :=
      Int.ofNat_le_ofNat_of_le hSB_le_nat'
    simpa [Int.ofNat_sub hpos] using hSB_le'
  have hSA_pos_int : (1 : Int) ≤ Int.ofNat SA.card :=
    Int.ofNat_le_ofNat_of_le hSA_pos
  have hmargin : margin P b a = Int.ofNat SB.card - Int.ofNat SA.card := by
    simp [margin, SA, SB]
  linarith [hmargin, hSB_le, hSA_pos_int]

/-- Minimax satisfies Pareto efficiency. -/
theorem minimax_pareto_efficiency : ParetoEfficiency minimax := by
  intro V A _ _ _ P c d hpref hd
  classical
  let : Nonempty A := ⟨c⟩
  have hcard_pos : 0 < Fintype.card V := Fintype.card_pos
  have hmargin_cd : margin P c d = (Fintype.card V : Int) :=
    unanimous_margin_eq_card (P := P) c d hpref
  have hmaxLoss_d_ge : (Fintype.card V : Int) ≤ maxLoss P d := by
    have hle := margin_le_maxLoss (P := P) (a := d) (b := c)
    simpa [hmargin_cd] using hle
  have hmaxLoss_d_le : maxLoss P d ≤ (Fintype.card V : Int) := by
    refine maxLoss_le_of_forall_margin_le (P := P) (a := d) (k := (Fintype.card V : Int)) ?_
    intro b
    exact margin_le_card (P := P) b d
  have hmaxLoss_d_eq : maxLoss P d = (Fintype.card V : Int) :=
    le_antisymm hmaxLoss_d_le hmaxLoss_d_ge
  rcases Classical.choice (inferInstance : Nonempty V) with v0
  let a : A := topChoice P v0
  have htop : TopRank P v0 a := topChoice_topRank (P := P) (v := v0)
  have hbound : ∀ b, margin P b a ≤ (Fintype.card V : Int) - 1 := by
    intro b
    by_cases hb : b = a
    · subst hb
      have hpos_int : (1 : Int) ≤ (Fintype.card V : Int) := by
        exact_mod_cast (Nat.succ_le_iff.2 hcard_pos)
      have hzero : (0 : Int) ≤ (Fintype.card V : Int) - 1 := by
        linarith
      simpa [self_margin_zero] using hzero
    · exact
        margin_le_card_sub_one_of_topRank (P := P) (v0 := v0) (a := a) (b := b) hb htop
  have hmaxLoss_a_le :
      maxLoss P a ≤ (Fintype.card V : Int) - 1 :=
    maxLoss_le_of_forall_margin_le (P := P) (a := a) (k := (Fintype.card V : Int) - 1)
      hbound
  have hmin_le : minimaxScore P ≤ maxLoss P a :=
    minimaxScore_le_of_candidate (P := P) a
  have hlt_card : (Fintype.card V : Int) - 1 < maxLoss P d := by
    have hpos_int : (1 : Int) ≤ (Fintype.card V : Int) := by
      exact_mod_cast (Nat.succ_le_iff.2 hcard_pos)
    linarith [hmaxLoss_d_eq]
  have hmin_lt : minimaxScore P < maxLoss P d :=
    lt_of_le_of_lt (le_trans hmin_le hmaxLoss_a_le) hlt_card
  have hd' :
      d ∈ Finset.univ.filter (fun a => maxLoss P a = minimaxScore P) := by
    simpa [minimax, (inferInstance : Nonempty A)] using hd
  have hdeq : maxLoss P d = minimaxScore P := (Finset.mem_filter.mp hd').2
  have hcontra : (minimaxScore P : Int) < minimaxScore P := by
    linarith [hmin_lt, hdeq]
  exact (lt_irrefl (minimaxScore P) hcontra)

end SocialChoice
