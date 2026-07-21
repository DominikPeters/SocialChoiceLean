import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic
import SocialChoice.Axioms.Majority
import SocialChoice.Margin
import SocialChoice.Rules.PluralityWithRunoff.Defs
import SocialChoice.Rules.ScoringRules.Plurality.Majority

namespace SocialChoice

open Finset

lemma margin_pos_of_majority_top {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {x y : A} (hxy : x ≠ y)
    (hmaj : StrictMajority (votersTop P x)) : margin_pos P x y := by
  classical
  have hsubset : votersTop P x ⊆ votersPreferring P x y := by
    intro v hv
    have hx : TopRank P v x := (Finset.mem_filter.mp hv).2
    have hxy' : Prefers P v x y := hx y (by simpa [eq_comm] using hxy)
    exact Finset.mem_filter.mpr ⟨mem_univ v, hxy'⟩
  have hcard : (votersTop P x).card ≤ (votersPreferring P x y).card :=
    Finset.card_le_card hsubset
  have hmaj' : Fintype.card V < 2 * (votersTop P x).card := by
    simpa [StrictMajority] using hmaj
  have hmajor_pref : Fintype.card V < 2 * (votersPreferring P x y).card :=
    lt_of_lt_of_le hmaj' (Nat.mul_le_mul_left 2 hcard)
  have hdisj : Disjoint (votersPreferring P x y) (votersPreferring P y x) := by
    refine disjoint_left.2 ?_
    intro v hv1 hv2
    have hx : Prefers P v x y := (Finset.mem_filter.mp hv1).2
    have hy : Prefers P v y x := (Finset.mem_filter.mp hv2).2
    let _ := P.pref v
    exact lt_asymm hx hy
  have hsubset' :
      (votersPreferring P x y ∪ votersPreferring P y x) ⊆ (Finset.univ : Finset V) := by
    intro v _
    exact mem_univ v
  have hsum :
      (votersPreferring P x y).card + (votersPreferring P y x).card ≤ Fintype.card V := by
    have hcard' :
        (votersPreferring P x y ∪ votersPreferring P y x).card ≤ (Finset.univ : Finset V).card :=
      Finset.card_le_card hsubset'
    have hcard'' :
        (votersPreferring P x y ∪ votersPreferring P y x).card =
          (votersPreferring P x y).card + (votersPreferring P y x).card := by
      simpa using
        (Finset.card_union_of_disjoint
          (s := votersPreferring P x y) (t := votersPreferring P y x) hdisj)
    have hcard''' :
        (votersPreferring P x y).card + (votersPreferring P y x).card ≤
          (Finset.univ : Finset V).card := by
      simpa [hcard''] using hcard'
    simpa [Finset.card_univ] using hcard'''
  have hlt' :
      (votersPreferring P x y).card + (votersPreferring P y x).card <
        (votersPreferring P x y).card + (votersPreferring P x y).card := by
    have hlt := lt_of_le_of_lt hsum hmajor_pref
    simpa [Nat.two_mul] using hlt
  have hlt : (votersPreferring P y x).card < (votersPreferring P x y).card :=
    Nat.lt_of_add_lt_add_left hlt'
  have hlt' :
      (Int.ofNat (votersPreferring P y x).card) <
        Int.ofNat (votersPreferring P x y).card :=
    Int.ofNat_lt_ofNat_of_lt hlt
  have hmargin :
      0 < Int.ofNat (votersPreferring P x y).card -
          Int.ofNat (votersPreferring P y x).card := sub_pos.mpr hlt'
  change 0 < Int.ofNat (votersPreferring P x y).card -
    Int.ofNat (votersPreferring P y x).card
  exact hmargin

theorem plurality_with_runoff_majority_criterion : MajorityCriterion pluralityWithRunoff := by
  intro V A _ _ P x hmaj
  classical
  by_cases hcard : Fintype.card A ≤ 1
  · have hforall : ∀ a b : A, a = b := (Fintype.card_le_one_iff).1 hcard
    apply Finset.ext
    intro y
    constructor
    · intro _hy
      have : y = x := hforall y x
      simp [this]
    · intro hy
      have hy' : y = x := by simpa using hy
      subst hy'
      simp [pluralityWithRunoff, hcard]
  · let S := plurality P
    have hplurality : S = {x} := by
      have hplurality' : plurality P = {x} :=
        plurality_majority_criterion (P := P) (c := x) hmaj
      simpa [S] using hplurality'
    have hS : ¬ S.card ≥ 2 := by
      have hScard : S.card = 1 := by
        simp [hplurality]
      simp [hScard]
    have hpair_mem : ∀ {z y : A},
        ({z, y} : Finset A) ∈ pluralityWithRunoffPairs P → x ∈ ({z, y} : Finset A) := by
      intro z y hpair
      have hpair' :
          ({z, y} : Finset A) ∈ (S.product (secondPluralitySet P S)).image
            (fun p => ({p.1, p.2} : Finset A)) := by
        simpa [pluralityWithRunoffPairs, hS, S] using hpair
      rcases Finset.mem_image.mp hpair' with ⟨p, hp, hpEq⟩
      rcases Finset.mem_product.mp hp with ⟨hp1, _hp2⟩
      have hp1' : p.1 = x := by
        simp [hplurality] at hp1
        exact hp1
      have hxmem : x ∈ ({p.1, p.2} : Finset A) := by
        simp [hp1']
      simpa [hpEq] using hxmem
    have hmargin : ∀ y : A, y ≠ x → margin_pos P x y := by
      intro y hy
      exact margin_pos_of_majority_top (P := P) (x := x) (y := y)
        (by simpa [eq_comm] using hy) hmaj
    have huniq : ∀ z : A, z ∈ pluralityWithRunoff P → z = x := by
      intro z hz
      have hz' :
          ∃ y : A, ({z, y} : Finset A) ∈ pluralityWithRunoffPairs P ∧ 0 ≤ margin P z y := by
        simpa [pluralityWithRunoff, hcard] using hz
      rcases hz' with ⟨y, hpair, hnonneg⟩
      have hxmem : x ∈ ({z, y} : Finset A) := hpair_mem hpair
      have hxmem' : x = z ∨ x = y := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hxmem
      cases hxmem' with
      | inl hxz =>
          simp [hxz]
      | inr hxy =>
          by_cases hzx : z = x
          · simp [hzx]
          · have hpos : margin_pos P x z := hmargin z (by simpa [eq_comm] using hzx)
            have hneg : margin P z x < 0 := by
              have hpos' : 0 < margin P x z := by
                simpa [margin_pos] using hpos
              have hskew : margin P z x = - margin P x z := by
                simpa [skew_symmetric] using (margin_antisymmetric (P := P)) z x
              linarith
            have hnonneg' : 0 ≤ margin P z x := by
              simpa [hxy] using hnonneg
            exact (False.elim ((not_lt_of_ge hnonneg') hneg))
    have hxmem : x ∈ pluralityWithRunoff P := by
      letI : Nonempty A := ⟨x⟩
      have hnonempty : (pluralityWithRunoff P).Nonempty :=
        plurality_with_runoff_nonempty (P := P)
      rcases hnonempty with ⟨w, hw⟩
      have hwx : w = x := huniq w hw
      simpa [hwx] using hw
    apply Finset.ext
    intro y
    constructor
    · intro hy
      have hy' : y = x := huniq y hy
      simp [hy']
    · intro hy
      have hy' : y = x := by simpa using hy
      subst hy'
      exact hxmem

end SocialChoice
