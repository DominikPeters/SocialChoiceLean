import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic
import SocialChoice.Axioms.Pareto
import SocialChoice.Margin
import SocialChoice.Rules.PluralityWithRunoff.Defs

namespace SocialChoice

open Finset

theorem plurality_with_runoff_pareto_efficiency : ParetoEfficiency pluralityWithRunoff := by
  intro V A _ _ _ P c d hpref
  classical
  let : Nonempty A := ⟨c⟩
  let : DecidableEq A := Classical.decEq A
  by_cases hcard : Fintype.card A ≤ 1
  · have hforall : ∀ a b : A, a = b := (Fintype.card_le_one_iff).1 hcard
    have hcd : c ≠ d := by
      rcases Classical.choice (inferInstance : Nonempty V) with v0
      let _ := P.pref v0
      intro hEq
      subst hEq
      exact (lt_irrefl _ (hpref v0))
    exact (hcd (hforall c d)).elim
  · have htopcount_d : topCount P d = 0 :=
      topCount_eq_zero_of_dominated (P := P) (c := c) (d := d) hpref
    rcases Classical.choice (inferInstance : Nonempty V) with v0
    by_contra hdwin
    have hdwin' :
        ∃ y : A, ({d, y} : Finset A) ∈ pluralityWithRunoffPairs P ∧ 0 ≤ margin P d y := by
      simp [pluralityWithRunoff, hcard] at hdwin
      exact hdwin
    let _ := P.pref v0
    have hA : (Finset.univ : Finset A).Nonempty := ⟨c, by simp⟩
    let t : A := (Finset.univ.min' hA)
    have htopt : TopRank P v0 t := by
      intro a ha
      have hleast : IsLeast (↑(Finset.univ : Finset A)) t :=
        Finset.isLeast_min' (s := (Finset.univ : Finset A)) hA
      have hle : t ≤ a := hleast.2 (by simp)
      have hlt : t < a := lt_of_le_of_ne hle (by simpa [eq_comm] using ha)
      simpa [Prefers] using hlt
    have hv0 : v0 ∈ votersTop P t := by
      simp [votersTop, htopt]
    have hpos_t : 0 < topCount P t := by
      unfold topCount
      exact Finset.card_pos.mpr ⟨v0, hv0⟩
    rcases hdwin' with ⟨y, hpair, hnonneg⟩
    let S : Finset A := plurality P
    have hSnonempty : S.Nonempty := plurality_nonempty (P := P)
    by_cases hS : S.card ≥ 2
    · have hpair' : ({d, y} : Finset A) ∈ S.powersetCard 2 := by
        simpa [pluralityWithRunoffPairs, hS, S] using hpair
      have hsubset : ({d, y} : Finset A) ⊆ S := (Finset.mem_powersetCard.mp hpair').1
      have hdS : d ∈ S := hsubset (by simp)
      have hdS' :
          d ∈ (Finset.univ.filter (fun c => ∀ e : A, topCount P e ≤ topCount P c)) := by
        simpa [plurality, S] using hdS
      have hmax : ∀ e : A, topCount P e ≤ topCount P d :=
        (Finset.mem_filter.mp hdS').2
      have hlt : topCount P d < topCount P t := by
        simpa [htopcount_d] using hpos_t
      exact (not_lt_of_ge (hmax t)) hlt
    · have hSle : S.card ≤ 1 := by
        have hlt : S.card < 2 := lt_of_not_ge hS
        exact Nat.lt_succ_iff.mp hlt
      have hScard : S.card = 1 := Nat.le_antisymm hSle (Finset.one_le_card.mpr hSnonempty)
      rcases Finset.card_eq_one.mp hScard with ⟨x, hxS⟩
      have hxmem : x ∈ S := by
        simp [hxS]
      have hxmem' :
          x ∈ (Finset.univ.filter (fun c => ∀ e : A, topCount P e ≤ topCount P c)) := by
        simpa [plurality, S] using hxmem
      have hxmax : ∀ e : A, topCount P e ≤ topCount P x :=
        (Finset.mem_filter.mp hxmem').2
      have hpos_x : 0 < topCount P x := lt_of_lt_of_le hpos_t (hxmax t)
      have hdx : d ≠ x := by
        intro hEq
        subst hEq
        have hpos_d : 0 < topCount P d := hpos_x
        simp [htopcount_d] at hpos_d
      have hpair' :
          ({d, y} : Finset A) ∈ (S.product (secondPluralitySet P S)).image
            (fun p => ({p.1, p.2} : Finset A)) := by
        simpa [pluralityWithRunoffPairs, hS, S] using hpair
      rcases Finset.mem_image.mp hpair' with ⟨p, hp, hpEq⟩
      rcases Finset.mem_product.mp hp with ⟨hp1, hp2⟩
      have hp1' : p.1 = x := by
        simp [hxS] at hp1
        exact hp1
      have hdmem : d ∈ ({p.1, p.2} : Finset A) := by
        simp [hpEq]
      have hdmem' : d = p.1 ∨ d = p.2 := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hdmem
      have hdp2 : d = p.2 := by
        cases hdmem' with
        | inl hd1 =>
            have : d = x := by simpa [hp1'] using hd1
            exact (hdx this).elim
        | inr hd2 => exact hd2
      have hd2 : d ∈ secondPluralitySet P S := by
        simpa [hdp2] using hp2
      let R : Finset A := Finset.univ.filter (fun c => c ∉ S)
      have hcard' : 1 < Fintype.card A := Nat.lt_of_not_ge hcard
      have hAcard : 1 < (Finset.univ : Finset A).card := by
        simpa [Finset.card_univ] using hcard'
      have hR : R.Nonempty := by
        rcases Finset.exists_mem_ne (s := (Finset.univ : Finset A)) hAcard x with
          ⟨z, hz, hzx⟩
        have hzn : z ∉ S := by
          simp [hxS, hzx]
        exact ⟨z, Finset.mem_filter.mpr ⟨hz, hzn⟩⟩
      have hd2' :
          d ∈ R.filter (fun c => topCount P c =
            (R.image (fun c => topCount P c)).max' (by
              simpa [Finset.Nonempty] using hR.image (fun c => topCount P c))) := by
        simpa [secondPluralitySet, hR, R] using hd2
      have hmaxscore :
          topCount P d =
            (R.image (fun c => topCount P c)).max' (by
              simpa [Finset.Nonempty] using hR.image (fun c => topCount P c)) :=
        (Finset.mem_filter.mp hd2').2
      have hzero : ∀ z : A, z ≠ x → topCount P z = 0 := by
        intro z hzx
        have hzR : z ∈ R := by
          have hznot : z ∉ S := by
            simp [hxS, hzx]
          exact Finset.mem_filter.mpr ⟨mem_univ z, hznot⟩
        have hzmem : topCount P z ∈ R.image (fun c => topCount P c) := by
          exact Finset.mem_image.mpr ⟨z, hzR, rfl⟩
        have hzle :
            topCount P z ≤
              (R.image (fun c => topCount P c)).max' (by
                simpa [Finset.Nonempty] using hR.image (fun c => topCount P c)) :=
          Finset.le_max' _ _ hzmem
        have hzle' : topCount P z ≤ topCount P d := by
          simpa [hmaxscore] using hzle
        have hzle0 : topCount P z ≤ 0 := by
          simpa [htopcount_d] using hzle'
        exact Nat.eq_zero_of_le_zero hzle0
      have hall : ∀ v : V, TopRank P v x := by
        intro v
        let _ := P.pref v
        have hA' : (Finset.univ : Finset A).Nonempty := ⟨x, by simp⟩
        let t' : A := (Finset.univ.min' hA')
        have htopt' : TopRank P v t' := by
          intro a ha
          have hleast : IsLeast (↑(Finset.univ : Finset A)) t' :=
            Finset.isLeast_min' (s := (Finset.univ : Finset A)) hA'
          have hle : t' ≤ a := hleast.2 (by simp)
          have hlt : t' < a := lt_of_le_of_ne hle (by simpa [eq_comm] using ha)
          simpa [Prefers] using hlt
        have hv : v ∈ votersTop P t' := by
          simp [votersTop, htopt']
        have hpos' : 0 < topCount P t' := by
          unfold topCount
          exact Finset.card_pos.mpr ⟨v, hv⟩
        have htx : t' = x := by
          by_contra htx
          have htzero : topCount P t' = 0 := hzero t' htx
          have hpos'' : 0 < topCount P t' := hpos'
          simp [htzero] at hpos''
        simpa [htx] using htopt'
      have hxdpref : ∀ v : V, Prefers P v x d := by
        intro v
        have htop : TopRank P v x := hall v
        exact htop d (by simpa [eq_comm] using hdx)
      have hpos : margin_pos P x d := unanimous_margin P x d hxdpref
      have hneg : margin P d x < 0 := by
        have hpos' : 0 < margin P x d := by
          simpa [margin_pos] using hpos
        have hskew : margin P d x = - margin P x d := by
          simpa [skew_symmetric] using (margin_antisymmetric (P := P)) d x
        linarith
      have hyx : y = x := by
        have hxmem : x ∈ ({d, y} : Finset A) := by
          have hxmem' : x ∈ ({p.1, p.2} : Finset A) := by simp [hp1']
          simpa [hpEq] using hxmem'
        have hxmem' : x = d ∨ x = y := by
          simpa [Finset.mem_insert, Finset.mem_singleton] using hxmem
        cases hxmem' with
        | inl hxd' => exact (hdx hxd'.symm).elim
        | inr hxy => exact hxy.symm
      have hnonneg' : 0 ≤ margin P d x := by
        simpa [hyx] using hnonneg
      exact (not_lt_of_ge hnonneg') hneg

end SocialChoice
