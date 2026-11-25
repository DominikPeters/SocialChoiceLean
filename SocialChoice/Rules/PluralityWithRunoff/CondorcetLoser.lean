import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic
import SocialChoice.Axioms.Condorcet
import SocialChoice.Rules.PluralityWithRunoff.Defs

namespace SocialChoice

open Finset

lemma mem_secondPluralitySet_not_mem {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (S : Finset A) {x : A} (hx : x ∈ secondPluralitySet P S) :
    x ∉ S := by
  classical
  by_cases hR : (Finset.univ.filter (fun c => c ∉ S)).Nonempty
  · have hx' :
      x ∈ (Finset.univ.filter (fun c => c ∉ S)).filter
        (fun c => topCount P c =
          ((Finset.univ.filter (fun c => c ∉ S)).image (fun c => topCount P c)).max' (by
            simpa [Finset.Nonempty] using hR.image (fun c => topCount P c))) := by
      have hx'' :
          x ∈ Finset.univ.filter (fun c => c ∉ S) ∧
            topCount P x =
              ((Finset.univ.filter (fun c => c ∉ S)).image (fun c => topCount P c)).max' (by
                simpa [Finset.Nonempty] using hR.image (fun c => topCount P c)) := by
        simpa [secondPluralitySet, hR] using hx
      exact Finset.mem_filter.mpr hx''
    have hxR : x ∈ Finset.univ.filter (fun c => c ∉ S) := (Finset.mem_filter.mp hx').1
    exact (Finset.mem_filter.mp hxR).2
  · have : secondPluralitySet P S = ∅ := by
      simp [secondPluralitySet, hR]
    simp [this] at hx

lemma mem_pluralityWithRunoffPairs_card {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) {s : Finset A} (hs : s ∈ pluralityWithRunoffPairs P) : s.card = 2 := by
  classical
  let S := plurality P
  by_cases hS : S.card ≥ 2
  · have hs' : s ∈ S.powersetCard 2 := by
      simpa [pluralityWithRunoffPairs, hS, S] using hs
    exact (Finset.mem_powersetCard.mp hs').2
  · have hs' :
        s ∈ (S.product (secondPluralitySet P S)).image
          (fun p => ({p.1, p.2} : Finset A)) := by
      simpa [pluralityWithRunoffPairs, hS, S] using hs
    rcases Finset.mem_image.mp hs' with ⟨p, hp, rfl⟩
    rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
    have hp2_notin : p.2 ∉ S := mem_secondPluralitySet_not_mem (P := P) (S := S) hp2
    have hp1_ne_hp2 : p.1 ≠ p.2 := by
      intro hEq
      apply hp2_notin
      simpa [hEq] using hp1
    exact Finset.card_eq_two.mpr ⟨p.1, p.2, hp1_ne_hp2, rfl⟩

lemma mem_secondPluralitySet_iff_forall_le
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (S : Finset A)
    (hR : (Finset.univ.filter (fun c => c ∉ S)).Nonempty) {d : A} :
    d ∈ secondPluralitySet P S ↔
      d ∈ (Finset.univ.filter (fun c => c ∉ S)) ∧
        ∀ e ∈ (Finset.univ.filter (fun c => c ∉ S)), topCount P e ≤ topCount P d := by
  classical
  let R := Finset.univ.filter (fun c => c ∉ S)
  have hRimage : (R.image (fun c => topCount P c)).Nonempty := by
    simpa [Finset.Nonempty, R] using hR.image (fun c => topCount P c)
  let maxScore : Nat := (R.image (fun c => topCount P c)).max' hRimage
  have hdef :
      secondPluralitySet P S = R.filter (fun c => topCount P c = maxScore) := by
    simp [secondPluralitySet, hR, R, maxScore]
  constructor
  · intro hd
    have hd' : d ∈ R ∧ topCount P d = maxScore := by
      simpa [hdef] using hd
    refine ⟨hd'.1, ?_⟩
    intro e he
    have hemem : topCount P e ∈ R.image (fun c => topCount P c) := by
      exact Finset.mem_image.mpr ⟨e, he, rfl⟩
    have hle : topCount P e ≤ maxScore := Finset.le_max' _ _ hemem
    simpa [hd'.2] using hle
  · intro hd
    rcases hd with ⟨hdR, hle⟩
    have hmem : topCount P d ∈ R.image (fun c => topCount P c) := by
      exact Finset.mem_image.mpr ⟨d, hdR, rfl⟩
    have hle_max : topCount P d ≤ maxScore := Finset.le_max' _ _ hmem
    have hmax_le : maxScore ≤ topCount P d := by
      apply Finset.max'_le
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨e, he, rfl⟩
      exact hle e he
    have hmax_eq : topCount P d = maxScore := le_antisymm hle_max hmax_le
    have hd' : d ∈ R.filter (fun c => topCount P c = maxScore) := by
      exact Finset.mem_filter.mpr ⟨hdR, hmax_eq⟩
    simpa [hdef] using hd'

lemma pair_mem_pluralityWithRunoffPairs_of_card_two
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (hcard : Fintype.card A = 2) {a b : A} (hab : a ≠ b) :
    ({a, b} : Finset A) ∈ pluralityWithRunoffPairs P := by
  classical
  let S := plurality P
  have : Nonempty A := by
    have hpos : 0 < Fintype.card A := by
      simp [hcard]
    exact Fintype.card_pos_iff.mp hpos
  by_cases hS : S.card ≥ 2
  · have hS_le : S.card ≤ 2 := by
      have hS_le' : S.card ≤ Fintype.card A := Finset.card_le_univ S
      simpa [hcard] using hS_le'
    have hS_card : S.card = 2 := le_antisymm hS_le hS
    have hS_eq : S = (Finset.univ : Finset A) := by
      apply Finset.eq_of_subset_of_card_le
      · intro z hz
        exact Finset.mem_univ z
      · simp [hS_card, Finset.card_univ, hcard]
    have hsubset : ({a, b} : Finset A) ⊆ S := by
      intro z hz
      simp [hS_eq]
    have hcardpair : ({a, b} : Finset A).card = 2 := Finset.card_pair hab
    have hmem :
        ({a, b} : Finset A) ∈ S.powersetCard 2 := by
      exact (Finset.mem_powersetCard.mpr ⟨hsubset, hcardpair⟩)
    simpa [pluralityWithRunoffPairs, hS, S] using hmem
  · have hS_le : S.card ≤ 1 := by
      have hS_lt : S.card < 2 := Nat.lt_of_not_ge hS
      exact Nat.lt_succ_iff.mp hS_lt
    have hS_nonempty : S.Nonempty := plurality_nonempty (P := P)
    have hS_ge : 1 ≤ S.card := Finset.one_le_card.mpr hS_nonempty
    have hS_card : S.card = 1 := Nat.le_antisymm hS_le hS_ge
    rcases Finset.card_eq_one.mp hS_card with ⟨t, htS⟩
    have hR : (Finset.univ.filter (fun c => c ∉ S)).Nonempty := by
      have hAcard : 1 < (Finset.univ : Finset A).card := by
        simp [Finset.card_univ, hcard]
      rcases Finset.exists_mem_ne (s := (Finset.univ : Finset A))
        hAcard t with
        ⟨u, hu, hut⟩
      refine ⟨u, ?_⟩
      have hu_not : u ∉ S := by
        simp [htS, hut]
      exact Finset.mem_filter.mpr ⟨hu, hu_not⟩
    rcases two_elems_eq_or_eq hcard a b hab t with hta | htb
    · have htS' : S = {a} := by
        simpa [hta] using htS
      have hbR : b ∈ (Finset.univ.filter (fun c => c ∉ S)) := by
        have hbmem_univ : b ∈ (Finset.univ : Finset A) := by simp
        have hb_not : b ∉ S := by
          intro hbS
          have hb_eq : b = a := by
            simpa [htS'] using hbS
          exact hab hb_eq.symm
        exact Finset.mem_filter.mpr ⟨hbmem_univ, hb_not⟩
      have hforall :
          ∀ e ∈ (Finset.univ.filter (fun c => c ∉ S)), topCount P e ≤ topCount P b := by
        intro e he
        have hnotS : e ∉ S := (Finset.mem_filter.mp he).2
        have he' : e ≠ a := by
          intro hEq
          apply hnotS
          simp [htS', hEq]
        rcases two_elems_eq_or_eq hcard a b hab e with rfl | rfl
        · exact (he' rfl).elim
        · exact le_rfl
      have hbmem : b ∈ secondPluralitySet P S :=
        (mem_secondPluralitySet_iff_forall_le (P := P) (S := S) hR).2 ⟨hbR, hforall⟩
      have haS : a ∈ S := by
        simp [htS']
      have hpair :
          ({a, b} : Finset A) ∈ (S.product (secondPluralitySet P S)).image
            (fun p => ({p.1, p.2} : Finset A)) := by
        refine Finset.mem_image.mpr ?_
        exact ⟨(a, b), Finset.mem_product.mpr ⟨haS, hbmem⟩, rfl⟩
      simpa [pluralityWithRunoffPairs, hS, S] using hpair
    · have htS' : S = {b} := by
        simpa [htb] using htS
      have haR : a ∈ (Finset.univ.filter (fun c => c ∉ S)) := by
        have hamem_univ : a ∈ (Finset.univ : Finset A) := by simp
        have ha_not : a ∉ S := by
          intro haS
          have ha_eq : a = b := by
            simpa [htS'] using haS
          exact hab ha_eq
        exact Finset.mem_filter.mpr ⟨hamem_univ, ha_not⟩
      have hforall :
          ∀ e ∈ (Finset.univ.filter (fun c => c ∉ S)), topCount P e ≤ topCount P a := by
        intro e he
        have hnotS : e ∉ S := (Finset.mem_filter.mp he).2
        have he' : e ≠ b := by
          intro hEq
          apply hnotS
          simp [htS', hEq]
        rcases two_elems_eq_or_eq hcard a b hab e with rfl | rfl
        · exact le_rfl
        · exact (he' rfl).elim
      have hamem : a ∈ secondPluralitySet P S :=
        (mem_secondPluralitySet_iff_forall_le (P := P) (S := S) hR).2 ⟨haR, hforall⟩
      have hbS : b ∈ S := by
        simp [htS']
      have hpair :
          ({a, b} : Finset A) ∈ (S.product (secondPluralitySet P S)).image
            (fun p => ({p.1, p.2} : Finset A)) := by
        refine Finset.mem_image.mpr ?_
        exact ⟨(b, a), Finset.mem_product.mpr ⟨hbS, hamem⟩, by
          simp [Finset.pair_comm]⟩
      simpa [pluralityWithRunoffPairs, hS, S, Finset.pair_comm] using hpair

lemma pluralityWithRunoff_of_card_two
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (hcard : Fintype.card A = 2) (a b : A) (hab : a ≠ b) :
    a ∈ pluralityWithRunoff P ↔ 0 ≤ margin P a b := by
  classical
  let : DecidableEq A := Classical.decEq A
  have hnot_le_one : ¬ Fintype.card A ≤ 1 := by
    omega
  constructor
  · intro ha
    have ha' :
        ∃ y : A, ({a, y} : Finset A) ∈ pluralityWithRunoffPairs P ∧ 0 ≤ margin P a y := by
      simpa [pluralityWithRunoff, hnot_le_one] using ha
    rcases ha' with ⟨y, hpair, hmargin⟩
    have hcardpair : ({a, y} : Finset A).card = 2 :=
      mem_pluralityWithRunoffPairs_card (P := P) hpair
    have hay : a ≠ y := by
      by_contra hEq
      subst hEq
      simp at hcardpair
    rcases two_elems_eq_or_eq hcard a b hab y with rfl | rfl
    · exact (hay rfl).elim
    · simpa using hmargin
  · intro hmargin
    have hpair : ({a, b} : Finset A) ∈ pluralityWithRunoffPairs P :=
      pair_mem_pluralityWithRunoffPairs_of_card_two (P := P) hcard hab
    have hx :
        ∃ y : A, ({a, y} : Finset A) ∈ pluralityWithRunoffPairs P ∧ 0 ≤ margin P a y := by
      exact ⟨b, hpair, hmargin⟩
    simpa [pluralityWithRunoff, hnot_le_one] using hx

theorem plurality_with_runoff_CondorcetLoser_criterion :
    CondorcetLoserCriterion pluralityWithRunoff := by
  intro V A _ _ P x hloser
  classical
  by_cases hcard : Fintype.card A ≤ 1
  · rcases hloser.2 with ⟨y, hxy⟩
    have hforall : ∀ a b : A, a = b := (Fintype.card_le_one_iff).1 hcard
    exfalso
    exact hxy (hforall y x)
  · by_contra hxmem
    have hxmem' :
        ∃ y : A, ({x, y} : Finset A) ∈ pluralityWithRunoffPairs P ∧ 0 ≤ margin P x y := by
      simpa [pluralityWithRunoff, hcard] using hxmem
    rcases hxmem' with ⟨y, hpair, hnonneg⟩
    have hcardpair : ({x, y} : Finset A).card = 2 :=
      mem_pluralityWithRunoffPairs_card (P := P) hpair
    have hxy : x ≠ y := by
      by_contra hxy
      simp [hxy] at hcardpair
    have hpos : margin_pos P y x :=
      (CondorcetLoser_iff_margin_pos P x).mp hloser |>.1 y (by simpa [eq_comm] using hxy)
    have hneg : margin P x y < 0 := by
      have hpos' : 0 < margin P y x := by
        simpa [margin_pos] using hpos
      have hskew : margin P x y = - margin P y x := by
        simpa [skew_symmetric] using (margin_antisymmetric (P := P)) x y
      linarith
    exact (not_lt_of_ge hnonneg) hneg

end SocialChoice
