import SocialChoice.Axioms.Pareto
import SocialChoice.Margin
import SocialChoice.Rules.UncoveredSet.Defs

namespace SocialChoice

open Finset

private lemma margin_le_of_unanimous_pref {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {x y z : A} (hxy : ∀ v : V, Prefers P v x y) :
    margin P y z ≤ margin P x z := by
  classical
  let Syz := Finset.univ.filter (fun v => Prefers P v y z)
  let Sxz := Finset.univ.filter (fun v => Prefers P v x z)
  let Szy := Finset.univ.filter (fun v => Prefers P v z y)
  let Szx := Finset.univ.filter (fun v => Prefers P v z x)
  have hsub1 : Syz ⊆ Sxz := by
    intro v hv
    have hv' : Prefers P v y z := (Finset.mem_filter.mp hv).2
    have hxyv : Prefers P v x y := hxy v
    let _ := P.pref v
    have hxz : Prefers P v x z := lt_trans hxyv hv'
    exact Finset.mem_filter.mpr ⟨by simp, hxz⟩
  have hsub2 : Szx ⊆ Szy := by
    intro v hv
    have hv' : Prefers P v z x := (Finset.mem_filter.mp hv).2
    have hxyv : Prefers P v x y := hxy v
    let _ := P.pref v
    have hzy : Prefers P v z y := lt_trans hv' hxyv
    exact Finset.mem_filter.mpr ⟨by simp, hzy⟩
  have h1 : Int.ofNat Syz.card ≤ Int.ofNat Sxz.card :=
    Int.ofNat_le_ofNat_of_le (Finset.card_le_card hsub1)
  have h2 : Int.ofNat Szx.card ≤ Int.ofNat Szy.card :=
    Int.ofNat_le_ofNat_of_le (Finset.card_le_card hsub2)
  have hle :
      Int.ofNat Syz.card + (- Int.ofNat Szy.card) ≤
        Int.ofNat Sxz.card + (- Int.ofNat Szx.card) := by
    exact add_le_add h1 (neg_le_neg h2)
  simpa [margin, Syz, Szy, Sxz, Szx, sub_eq_add_neg] using hle

private lemma covers_of_unanimous_pref {V A : Type} [Fintype V] [Fintype A] [Nonempty V]
    (P : Profile V A) {x y : A} (hxy : ∀ v : V, Prefers P v x y) :
    covers P x y := by
  refine ⟨unanimous_margin P x y hxy, ?_, ?_⟩
  · intro z hyz
    have hle : margin P y z ≤ margin P x z :=
      margin_le_of_unanimous_pref (P := P) (x := x) (y := y) (z := z) hxy
    have hyz' : 0 < margin P y z := by
      simpa [margin_pos] using hyz
    have hxz' : 0 < margin P x z := lt_of_lt_of_le hyz' hle
    simpa [margin_pos] using hxz'
  · intro z hzx
    have hle : margin P y z ≤ margin P x z :=
      margin_le_of_unanimous_pref (P := P) (x := x) (y := y) (z := z) hxy
    have hzx' : 0 < margin P z x := by
      simpa [margin_pos] using hzx
    have hskew : margin P z x = - margin P x z := by
      simpa [skew_symmetric] using (margin_antisymmetric (P := P)) z x
    have hxzneg : margin P x z < 0 := by
      have : 0 < - margin P x z := by
        simpa [hskew] using hzx'
      linarith
    have hyzneg : margin P y z < 0 := lt_of_le_of_lt hle hxzneg
    have hskew' : margin P z y = - margin P y z := by
      simpa [skew_symmetric] using (margin_antisymmetric (P := P)) z y
    have hpos : 0 < margin P z y := by
      have : 0 < - margin P y z := by linarith
      simpa [hskew'] using this
    simpa [margin_pos] using hpos

/-- uncoveredSet satisfies Pareto efficiency. -/
theorem uncoveredSet_pareto_efficiency : ParetoEfficiency uncoveredSet := by
  intro V A _ _ _ P c d hcd
  classical
  intro hd
  have hcov : covers P c d :=
    covers_of_unanimous_pref (P := P) (x := c) (y := d) hcd
  have huncov : uncovered P d := by
    simpa [uncoveredSet, uncoveredSetOf] using hd
  have hne : c ≠ d := ne_of_margin_pos (P := P) (a := c) (b := d) hcov.1
  exact (huncov c hne hcov)

end SocialChoice
