import Pivato.Neutrality.Proposition1
import Pivato.Theorem1.Defs

/-!
# Proposition 2 balance-side neutrality results

This file develops the balance-side analogue of Proposition 1:
- forward: neutral balance systems induce neutral balance rules;
- converse packaging: from a neutral balance rule represented by a perfect/skew
  balance system, construct an equivalent neutral perfect/skew representation.

This file proves explicit statements with assumptions written in each theorem.

Paper-correspondence note:
- these results are closest to the Appendix C Lemma C.3 layer;
- full Proposition 2 (`balance rule + weak additivity -> neutral perfect representation`)
  still depends on the paper-strength Lemma C.1 packaging.
-/

namespace Pivato

section Proposition2Forward

variable {G V X R : Type*} [Group G]
variable [AddCommMonoid R]
variable (mu : G →* Equiv.Perm X) (nu : G →* Equiv.Perm V)

/-- Transport of aggregate balances under `nu`-neutrality of the balance system. -/
lemma balanceAt_permute_of_balanceNeutral
    (B : BalanceSystem R X V)
    (hB : BalanceNeutral mu nu B)
    (g : G) (x y : X) (d : NProfile V) :
    balanceAt B ((mu g) x) ((mu g) y) (permuteNProfile (nu g) d) = balanceAt B x y d := by
  have hEval :
      evalNat (permuteWeight (nu g) (B.bal ((mu g) x) ((mu g) y))) d =
        evalNat (B.bal x y) d := by
    exact congrArg (fun w => evalNat w d) (hB g x y)
  calc
    balanceAt B ((mu g) x) ((mu g) y) (permuteNProfile (nu g) d)
        = evalNat (B.bal ((mu g) x) ((mu g) y)) (permuteNProfile (nu g) d) := rfl
    _ = evalNat (permuteWeight (nu g) (B.bal ((mu g) x) ((mu g) y))) d := by
      symm
      exact lemmaC2a_evalNat_permuteWeight
        (b := B.bal ((mu g) x) ((mu g) y)) (n := d) (π := nu g)
    _ = evalNat (B.bal x y) d := hEval
    _ = balanceAt B x y d := rfl

/-- Proposition 2 forward direction: neutral balance systems induce neutral
balance rules (assuming domain invariance). -/
theorem balanceRule_ruleNeutral_of_balanceNeutral
    [Preorder R] [Zero R] {D : Domain V}
    (B : BalanceSystem R X V)
    (hInv : DomainInvariant nu D)
    (hB : BalanceNeutral mu nu B) :
    RuleNeutral mu nu D (balanceRule (D := D) B) := by
  refine ⟨hInv, ?_⟩
  intro g d hd
  ext x
  constructor
  · intro hx
    refine (mem_permuteSet_iff (π := mu g) (S := balanceRule (D := D) B ⟨d, hd⟩) (x := x)).2 ?_
    intro z
    have hx' :
        (0 : R) ≤
          balanceAt B x ((mu g) z) (permuteNProfile (nu g) d) := hx ((mu g) z)
    have htransport :
        balanceAt B x ((mu g) z) (permuteNProfile (nu g) d) =
          balanceAt B ((mu g).symm x) z d := by
      simpa using
        (balanceAt_permute_of_balanceNeutral (mu := mu) (nu := nu) (B := B)
          hB g ((mu g).symm x) z d)
    simpa [htransport] using hx'
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    intro z
    have hy' :
        (0 : R) ≤ balanceAt B y ((mu g).symm z) d := hy ((mu g).symm z)
    have htransport :
        balanceAt B ((mu g) y) z (permuteNProfile (nu g) d) =
          balanceAt B y ((mu g).symm z) d := by
      simpa using
        (balanceAt_permute_of_balanceNeutral (mu := mu) (nu := nu) (B := B)
          hB g y ((mu g).symm z) d)
    simpa [htransport] using hy'

/-- Lemma C.3 (`←`) wrapper:
`BalanceNeutral -> RuleNeutral` for the induced balance rule. -/
theorem lemmaC3_left_of_balanceNeutral
    [Preorder R] [Zero R] {D : Domain V}
    (B : BalanceSystem R X V)
    (hInv : DomainInvariant nu D)
    (hB : BalanceNeutral mu nu B) :
    RuleNeutral mu nu D (balanceRule (D := D) B) :=
  balanceRule_ruleNeutral_of_balanceNeutral
    (mu := mu) (nu := nu) (B := B) hInv hB

end Proposition2Forward

section Proposition2ConverseCore

variable {G V X R : Type*} [Group G] [Fintype G]
variable [AddCommGroup R] [LinearOrder R]
variable [CovariantClass R R (fun a b => a + b) (· ≤ ·)]
variable [CovariantClass R R (fun a b => a + b) (· < ·)]
variable (mu : G →* Equiv.Perm X) (nu : G →* Equiv.Perm V)

/-- Group-average balance system used in the converse direction. -/
noncomputable def averagedBalanceSystem (B : BalanceSystem R X V) : BalanceSystem R X V where
  bal x y v := ∑ g : G, B.bal ((mu g) x) ((mu g) y) ((nu g) v)

omit [LinearOrder R]
    [CovariantClass R R (fun a b => a + b) (· ≤ ·)]
    [CovariantClass R R (fun a b => a + b) (· < ·)] in
lemma balanceAt_averaged_eq_sum (B : BalanceSystem R X V) (x y : X) (d : NProfile V) :
    balanceAt (averagedBalanceSystem (mu := mu) (nu := nu) B) x y d
      = ∑ g : G, balanceAt B ((mu g) x) ((mu g) y) (permuteNProfile (nu g) d) := by
  calc
    balanceAt (averagedBalanceSystem (mu := mu) (nu := nu) B) x y d
        = evalNat (fun v => ∑ g : G, B.bal ((mu g) x) ((mu g) y) ((nu g) v)) d := rfl
    _ = ∑ g : G, evalNat (fun v => B.bal ((mu g) x) ((mu g) y) ((nu g) v)) d :=
      evalNat_weight_sum (w := fun g v => B.bal ((mu g) x) ((mu g) y) ((nu g) v)) d
    _ = ∑ g : G, balanceAt B ((mu g) x) ((mu g) y) (permuteNProfile (nu g) d) := by
      apply Finset.sum_congr rfl
      intro g _
      exact lemmaC2a_evalNat_permuteWeight (b := B.bal ((mu g) x) ((mu g) y)) (n := d) (π := nu g)

omit [LinearOrder R]
    [CovariantClass R R (fun a b => a + b) (· ≤ ·)]
    [CovariantClass R R (fun a b => a + b) (· < ·)] in
lemma averagedBalanceSystem_balanceNeutral (B : BalanceSystem R X V) :
    BalanceNeutral mu nu (averagedBalanceSystem (mu := mu) (nu := nu) B) := by
  intro g x y
  funext v
  calc
    permuteWeight (nu g)
        ((averagedBalanceSystem (mu := mu) (nu := nu) B).bal ((mu g) x) ((mu g) y)) v
        = ∑ h : G, B.bal ((mu h) ((mu g) x)) ((mu h) ((mu g) y)) ((nu h) ((nu g) v)) := by
            simp [averagedBalanceSystem, permuteWeight]
    _ = ∑ h : G, B.bal ((mu (h * g)) x) ((mu (h * g)) y) ((nu (h * g)) v) := by
            refine Finset.sum_congr rfl ?_
            intro h hh
            simp [map_mul]
    _ = ∑ k : G, B.bal ((mu k) x) ((mu k) y) ((nu k) v) := by
            refine (Fintype.sum_equiv (Equiv.mulRight g)
              (fun h : G => B.bal ((mu (h * g)) x) ((mu (h * g)) y) ((nu (h * g)) v))
              (fun k : G => B.bal ((mu k) x) ((mu k) y) ((nu k) v)) ?_)
            intro h
            rfl
    _ = (averagedBalanceSystem (mu := mu) (nu := nu) B).bal x y v := by
            simp [averagedBalanceSystem]

omit [LinearOrder R]
    [CovariantClass R R (fun a b => a + b) (· ≤ ·)]
    [CovariantClass R R (fun a b => a + b) (· < ·)] in
lemma averagedBalanceSystem_skew (B : BalanceSystem R X V)
    (hskew : BalanceSkew (B := B)) :
    BalanceSkew (B := averagedBalanceSystem (mu := mu) (nu := nu) B) := by
  intro x y d
  calc
    balanceAt (averagedBalanceSystem (mu := mu) (nu := nu) B) x y d
        = ∑ g : G, balanceAt B ((mu g) x) ((mu g) y) (permuteNProfile (nu g) d) :=
            balanceAt_averaged_eq_sum (mu := mu) (nu := nu) B x y d
    _ = ∑ g : G, -balanceAt B ((mu g) y) ((mu g) x) (permuteNProfile (nu g) d) := by
          apply Finset.sum_congr rfl
          intro g hg
          simpa using
            (hskew ((mu g) x) ((mu g) y) (permuteNProfile (nu g) d))
    _ = -∑ g : G, balanceAt B ((mu g) y) ((mu g) x) (permuteNProfile (nu g) d) := by
          simp [Finset.sum_neg_distrib]
    _ = -balanceAt (averagedBalanceSystem (mu := mu) (nu := nu) B) y x d := by
          have hsum :
              balanceAt (averagedBalanceSystem (mu := mu) (nu := nu) B) y x d
                = ∑ g : G, balanceAt B ((mu g) y) ((mu g) x) (permuteNProfile (nu g) d) :=
            balanceAt_averaged_eq_sum (mu := mu) (nu := nu) B y x d
          simp [hsum]

/-- Equality of the original balance rule and the averaged one, assuming
rule-neutrality and nonemptiness on the domain. -/
lemma balanceRule_eq_averaged_of_ruleNeutral
    {D : Domain V} (B : BalanceSystem R X V)
    (hN : RuleNeutral mu nu D (balanceRule (D := D) B))
    (hskew : BalanceSkew (B := B))
    (hperfect : PerfectOn (D := D) (B := B))
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B)) :
    balanceRule (D := D) B =
      balanceRule (D := D) (averagedBalanceSystem (mu := mu) (nu := nu) B) := by
  classical
  funext d
  ext x
  constructor
  · intro hx z
    have hle_g :
        ∀ g : G,
          (0 : R) ≤
            balanceAt B ((mu g) x) ((mu g) z) (permuteNProfile (nu g) d.1) := by
      intro g
      have hEqg := hN.equivariant g d.2
      have hximg : (mu g) x ∈ permuteSet (mu g) (balanceRule (D := D) B d) :=
        ⟨x, hx, rfl⟩
      have hxg :
          (mu g) x ∈ balanceRule (D := D) B
            ⟨permuteNProfile (nu g) d.1, hN.domainInvariant g d.2⟩ := by
        exact hEqg.symm ▸ hximg
      exact hxg ((mu g) z)
    have hsum_nonneg :
        (0 : R) ≤ ∑ g : G, balanceAt B ((mu g) x) ((mu g) z) (permuteNProfile (nu g) d.1) := by
      have hsum :
          (∑ g : G, (0 : R))
            ≤ ∑ g : G, balanceAt B ((mu g) x) ((mu g) z) (permuteNProfile (nu g) d.1) := by
        exact Finset.sum_le_sum (s := (Finset.univ : Finset G)) (fun g hg => hle_g g)
      simpa using hsum
    calc
      (0 : R) ≤ ∑ g : G, balanceAt B ((mu g) x) ((mu g) z) (permuteNProfile (nu g) d.1) :=
          hsum_nonneg
      _ = balanceAt (averagedBalanceSystem (mu := mu) (nu := nu) B) x z d.1 := by
          symm
          exact balanceAt_averaged_eq_sum (mu := mu) (nu := nu) B x z d.1
  · intro hx
    by_contra hxnot
    rcases hNE d with ⟨y, hy⟩
    have hlt_g :
        ∀ g : G,
          balanceAt B ((mu g) x) ((mu g) y) (permuteNProfile (nu g) d.1) < 0 := by
      intro g
      have hEqg := hN.equivariant g d.2
      have hyimg : (mu g) y ∈ permuteSet (mu g) (balanceRule (D := D) B d) :=
        ⟨y, hy, rfl⟩
      have hyg :
          (mu g) y ∈ balanceRule (D := D) B
            ⟨permuteNProfile (nu g) d.1, hN.domainInvariant g d.2⟩ := by
        exact hEqg.symm ▸ hyimg
      have hxnotg :
          (mu g) x ∉ balanceRule (D := D) B
            ⟨permuteNProfile (nu g) d.1, hN.domainInvariant g d.2⟩ := by
        intro hxg
        have hximg : (mu g) x ∈ permuteSet (mu g) (balanceRule (D := D) B d) := by
          exact hEqg ▸ hxg
        have hxorig : x ∈ balanceRule (D := D) B d := by
          simpa using
            (mem_permuteSet_iff (π := mu g) (S := balanceRule (D := D) B d)
              (x := (mu g) x)).1 hximg
        exact hxnot hxorig
      have hpos :
          0 < balanceAt B ((mu g) y) ((mu g) x) (permuteNProfile (nu g) d.1) :=
        hperfect (hN.domainInvariant g d.2) hyg hxnotg
      calc
        balanceAt B ((mu g) x) ((mu g) y) (permuteNProfile (nu g) d.1)
            = -balanceAt B ((mu g) y) ((mu g) x) (permuteNProfile (nu g) d.1) := by
                simpa using
                  (hskew ((mu g) x) ((mu g) y) (permuteNProfile (nu g) d.1))
        _ < 0 := (neg_neg_iff_pos).2 hpos
    let f : G → R := fun g =>
      balanceAt B ((mu g) x) ((mu g) y) (permuteNProfile (nu g) d.1)
    have hone_neg : f 1 < 0 := hlt_g 1
    have hrest_nonpos : (Finset.univ.erase (1 : G)).sum f ≤ 0 := by
      exact Finset.sum_nonpos (s := (Finset.univ.erase (1 : G)))
        (fun g hg => (hlt_g g).le)
    have hsum_eq : (∑ g : G, f g) = f 1 + (Finset.univ.erase (1 : G)).sum f := by
      have hsumErase :
          (Finset.univ.erase (1 : G)).sum f + f 1 = ∑ g : G, f g := by
        exact Finset.sum_erase_add (s := (Finset.univ : Finset G)) (f := f) (a := (1 : G))
          (by exact Finset.mem_univ (1 : G))
      calc
        (∑ g : G, f g) = (Finset.univ.erase (1 : G)).sum f + f 1 := by
          exact hsumErase.symm
        _ = f 1 + (Finset.univ.erase (1 : G)).sum f := by
          simp [add_comm]
    have hlt_sum : ∑ g : G, f g < 0 := by
      have hsum_le_one : ∑ g : G, f g ≤ f 1 := by
        calc
          ∑ g : G, f g = f 1 + (Finset.univ.erase (1 : G)).sum f := hsum_eq
          _ ≤ f 1 + 0 := add_le_add_right hrest_nonpos (f 1)
          _ = f 1 := by simp
      exact lt_of_le_of_lt hsum_le_one hone_neg
    have hlt_avg :
        balanceAt (averagedBalanceSystem (mu := mu) (nu := nu) B) x y d.1 < 0 := by
      calc
        balanceAt (averagedBalanceSystem (mu := mu) (nu := nu) B) x y d.1
            = ∑ g : G, balanceAt B ((mu g) x) ((mu g) y) (permuteNProfile (nu g) d.1) :=
                balanceAt_averaged_eq_sum (mu := mu) (nu := nu) B x y d.1
        _ = ∑ g : G, f g := by
            rfl
        _ < 0 := hlt_sum
    exact (not_lt_of_ge (hx y)) hlt_avg

omit [CovariantClass R R (fun a b => a + b) (· < ·)] in
lemma averagedBalanceSystem_perfect_of_ruleNeutral
    {D : Domain V} (B : BalanceSystem R X V)
    (hN : RuleNeutral mu nu D (balanceRule (D := D) B))
    (hEq :
      balanceRule (D := D) B =
        balanceRule (D := D) (averagedBalanceSystem (mu := mu) (nu := nu) B))
    (hperfect : PerfectOn (D := D) (B := B)) :
    PerfectOn (D := D) (B := averagedBalanceSystem (mu := mu) (nu := nu) B) := by
  classical
  intro d hd x y hx hy
  have hxB : x ∈ balanceRule (D := D) B ⟨d, hd⟩ := by
    simpa [hEq] using hx
  have hyB : y ∉ balanceRule (D := D) B ⟨d, hd⟩ := by
    simpa [hEq] using hy
  have hpos_g :
      ∀ g : G,
        0 < balanceAt B ((mu g) x) ((mu g) y) (permuteNProfile (nu g) d) := by
    intro g
    have hEqg := hN.equivariant g hd
    have hximg : (mu g) x ∈ permuteSet (mu g) (balanceRule (D := D) B ⟨d, hd⟩) :=
      ⟨x, hxB, rfl⟩
    have hxg :
        (mu g) x ∈ balanceRule (D := D) B
          ⟨permuteNProfile (nu g) d, hN.domainInvariant g hd⟩ := by
      exact hEqg.symm ▸ hximg
    have hynotg :
        (mu g) y ∉ balanceRule (D := D) B
          ⟨permuteNProfile (nu g) d, hN.domainInvariant g hd⟩ := by
      intro hyg
      have hyimg : (mu g) y ∈ permuteSet (mu g) (balanceRule (D := D) B ⟨d, hd⟩) := by
        exact hEqg ▸ hyg
      have hyorig : y ∈ balanceRule (D := D) B ⟨d, hd⟩ := by
        simpa using
          (mem_permuteSet_iff (π := mu g) (S := balanceRule (D := D) B ⟨d, hd⟩)
            (x := (mu g) y)).1 hyimg
      exact hyB hyorig
    exact hperfect (hN.domainInvariant g hd) hxg hynotg
  let f : G → R := fun g =>
    balanceAt B ((mu g) x) ((mu g) y) (permuteNProfile (nu g) d)
  have hone_pos : 0 < f 1 := hpos_g 1
  have hrest_nonneg : 0 ≤ (Finset.univ.erase (1 : G)).sum f := by
    exact Finset.sum_nonneg (s := (Finset.univ.erase (1 : G)))
      (fun g hg => (hpos_g g).le)
  have hsum_eq : (∑ g : G, f g) = f 1 + (Finset.univ.erase (1 : G)).sum f := by
    have hsumErase :
        (Finset.univ.erase (1 : G)).sum f + f 1 = ∑ g : G, f g := by
      exact Finset.sum_erase_add (s := (Finset.univ : Finset G)) (f := f) (a := (1 : G))
        (by exact Finset.mem_univ (1 : G))
    calc
      (∑ g : G, f g) = (Finset.univ.erase (1 : G)).sum f + f 1 := by
        exact hsumErase.symm
      _ = f 1 + (Finset.univ.erase (1 : G)).sum f := by
        simp [add_comm]
  have hpos_sum : (0 : R) < ∑ g : G, f g := by
    have hpos_add : 0 < f 1 + (Finset.univ.erase (1 : G)).sum f :=
      add_pos_of_pos_of_nonneg hone_pos hrest_nonneg
    exact hsum_eq.symm ▸ hpos_add
  calc
    (0 : R) < ∑ g : G, f g := hpos_sum
    _ = ∑ g : G, balanceAt B ((mu g) x) ((mu g) y) (permuteNProfile (nu g) d) := by
        rfl
    _ = balanceAt (averagedBalanceSystem (mu := mu) (nu := nu) B) x y d := by
        symm
        exact balanceAt_averaged_eq_sum (mu := mu) (nu := nu) B x y d

/-- Proposition 2 converse (core form) on an explicitly represented perfect/skew
balance rule, with nonemptiness on the represented rule. -/
theorem exists_balanceNeutralPerfectSkew_of_ruleNeutral_balanceRule_with_nonempty
    {D : Domain V} (B : BalanceSystem R X V)
    (hN : RuleNeutral mu nu D (balanceRule (D := D) B))
    (hskew : BalanceSkew (B := B))
    (hperfect : PerfectOn (D := D) (B := B))
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B)) :
    ∃ Bbar : BalanceSystem R X V,
      BalanceNeutral mu nu Bbar ∧
      BalanceSkew (B := Bbar) ∧
      PerfectOn (D := D) (B := Bbar) ∧
      balanceRule (D := D) B = balanceRule (D := D) Bbar := by
  let Bbar := averagedBalanceSystem (mu := mu) (nu := nu) B
  have hNeutralBar : BalanceNeutral mu nu Bbar :=
    averagedBalanceSystem_balanceNeutral (mu := mu) (nu := nu) B
  have hSkewBar : BalanceSkew (B := Bbar) :=
    averagedBalanceSystem_skew (mu := mu) (nu := nu) B hskew
  have hEq :
      balanceRule (D := D) B = balanceRule (D := D) Bbar :=
    balanceRule_eq_averaged_of_ruleNeutral (mu := mu) (nu := nu) B hN hskew hperfect hNE
  have hPerfectBar : PerfectOn (D := D) (B := Bbar) :=
    averagedBalanceSystem_perfect_of_ruleNeutral (mu := mu) (nu := nu) B hN hEq hperfect
  exact ⟨Bbar, hNeutralBar, hSkewBar, hPerfectBar, hEq⟩

/-- Lemma C.3 (`→`) wrapper:
from rule-neutrality of a represented perfect/skew balance rule (plus
nonemptiness), produce an equivalent neutral perfect/skew representation. -/
theorem lemmaC3_right_of_ruleNeutral_balanceRule_with_nonempty
    {D : Domain V} (B : BalanceSystem R X V)
    (hN : RuleNeutral mu nu D (balanceRule (D := D) B))
    (hskew : BalanceSkew (B := B))
    (hperfect : PerfectOn (D := D) (B := B))
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B)) :
    ∃ Bbar : BalanceSystem R X V,
      BalanceNeutral mu nu Bbar ∧
      BalanceSkew (B := Bbar) ∧
      PerfectOn (D := D) (B := Bbar) ∧
      balanceRule (D := D) B = balanceRule (D := D) Bbar :=
  exists_balanceNeutralPerfectSkew_of_ruleNeutral_balanceRule_with_nonempty
    (mu := mu) (nu := nu) (D := D) B hN hskew hperfect hNE

end Proposition2ConverseCore

section Proposition2ConversePackaging

variable {G V X R : Type*} [Group G] [Fintype G]
variable [AddCommGroup R] [LinearOrder R]
variable [CovariantClass R R (fun a b => a + b) (· ≤ ·)]
variable [CovariantClass R R (fun a b => a + b) (· < ·)]
variable (mu : G →* Equiv.Perm X) (nu : G →* Equiv.Perm V)

/-- Converse packaging over an explicit perfect/skew representation of `F`. -/
theorem exists_balanceNeutralPerfectSkew_of_ruleNeutral_representation_with_nonempty
    {D : Domain V} {F : RuleOn D X}
    (hN : RuleNeutral mu nu D F)
    (hRep : ∃ B : BalanceSystem R X V,
      BalanceSkew (B := B) ∧ PerfectOn (D := D) (B := B) ∧
        F = balanceRule (D := D) B)
    (hNE : NonemptyOnDomain D F) :
    ∃ Bbar : BalanceSystem R X V,
      BalanceNeutral mu nu Bbar ∧
      BalanceSkew (B := Bbar) ∧
      PerfectOn (D := D) (B := Bbar) ∧
      F = balanceRule (D := D) Bbar := by
  rcases hRep with ⟨B, hskew, hperfect, hFB⟩
  have hN_B : RuleNeutral mu nu D (balanceRule (D := D) B) := by
    simpa [hFB] using hN
  have hNE_B : NonemptyOnDomain D (balanceRule (D := D) B) := by
    simpa [hFB] using hNE
  rcases exists_balanceNeutralPerfectSkew_of_ruleNeutral_balanceRule_with_nonempty
      (mu := mu) (nu := nu) (D := D) B hN_B hskew hperfect hNE_B with
      ⟨Bbar, hNeutral, hSkewBar, hPerfectBar, hEq⟩
  refine ⟨Bbar, hNeutral, hSkewBar, hPerfectBar, ?_⟩
  calc
    F = balanceRule (D := D) B := hFB
    _ = balanceRule (D := D) Bbar := hEq

end Proposition2ConversePackaging

section Proposition2ConverseStageDWrapper

universe uG uV uX uR

variable {G : Type uG} {V : Type uV} {X : Type uX} [Group G] [Fintype G]
variable (mu : G →* Equiv.Perm X) (nu : G →* Equiv.Perm V)

/-- Direct Stage-D-predicate wrapper for Proposition 2 converse:
from `IsPerfectBalanceRuleRepresentable` plus rule-neutrality, obtain a
neutral perfect/skew balance representation. -/
theorem exists_balanceNeutralPerfectSkewRepresentation_of_ruleNeutral
    [DecidableEq V] {D : Domain V} {F : RuleOn D X}
    (hN : RuleNeutral mu nu D F)
    (hRep : IsPerfectBalanceRuleRepresentable.{uV, uX, uR} (D := D) (F := F))
    (hNE : NonemptyOnDomain D F) :
    ∃ (R : Type uR),
      ∃ (instAdd : AddCommGroup R),
      ∃ (instLin : LinearOrder R),
      ∃ (instCovLe : CovariantClass R R (fun a b => a + b) (· ≤ ·)),
      ∃ (instCovLt : CovariantClass R R (fun a b => a + b) (· < ·)),
      ∃ B : BalanceSystem R X V,
        letI : AddCommGroup R := instAdd
        letI : LinearOrder R := instLin
        letI : CovariantClass R R (fun a b => a + b) (· ≤ ·) := instCovLe
        letI : CovariantClass R R (fun a b => a + b) (· < ·) := instCovLt
        BalanceNeutral mu nu B ∧
        BalanceSkew (B := B) ∧
        PerfectOn (D := D) (B := B) ∧
        F = balanceRule (D := D) B := by
  rcases hRep with ⟨R, instAdd, instLin, instCovLe, instCovLt, B, hRepB⟩
  let : AddCommGroup R := instAdd
  let : LinearOrder R := instLin
  let : CovariantClass R R (fun a b => a + b) (· ≤ ·) := instCovLe
  let : CovariantClass R R (fun a b => a + b) (· < ·) := instCovLt
  rcases hRepB with ⟨hskew, hperfect, hFB⟩
  have hN_B : RuleNeutral mu nu D (balanceRule (D := D) B) := by
    simpa [hFB] using hN
  have hNE_B : NonemptyOnDomain D (balanceRule (D := D) B) := by
    simpa [hFB] using hNE
  rcases exists_balanceNeutralPerfectSkew_of_ruleNeutral_balanceRule_with_nonempty
      (mu := mu) (nu := nu) (D := D) B hN_B hskew hperfect hNE_B with
      ⟨Bbar, hNeutral, hSkewBar, hPerfectBar, hEq⟩
  refine ⟨R, instAdd, instLin, instCovLe, instCovLt, Bbar, ?_⟩
  refine ⟨hNeutral, hSkewBar, hPerfectBar, ?_⟩
  exact hFB.trans hEq

/-- Paper-facing alias for the Stage-D Proposition 2 converse wrapper. -/
theorem exists_balanceNeutralPerfectRepresentation_of_ruleNeutral
    [DecidableEq V] {D : Domain V} {F : RuleOn D X}
    (hN : RuleNeutral mu nu D F)
    (hRep : IsPerfectBalanceRuleRepresentable.{uV, uX, uR} (D := D) (F := F))
    (hNE : NonemptyOnDomain D F) :
    ∃ (R : Type uR),
      ∃ (instAdd : AddCommGroup R),
      ∃ (instLin : LinearOrder R),
      ∃ (instCovLe : CovariantClass R R (fun a b => a + b) (· ≤ ·)),
      ∃ (instCovLt : CovariantClass R R (fun a b => a + b) (· < ·)),
      ∃ B : BalanceSystem R X V,
        letI : AddCommGroup R := instAdd
        letI : LinearOrder R := instLin
        letI : CovariantClass R R (fun a b => a + b) (· ≤ ·) := instCovLe
        letI : CovariantClass R R (fun a b => a + b) (· < ·) := instCovLt
        BalanceNeutral mu nu B ∧
        BalanceSkew (B := B) ∧
        PerfectOn (D := D) (B := B) ∧
        F = balanceRule (D := D) B :=
  exists_balanceNeutralPerfectSkewRepresentation_of_ruleNeutral
    (mu := mu) (nu := nu) hN hRep hNE

end Proposition2ConverseStageDWrapper

section Proposition2FinalPackaging

universe uG uV uX uR

variable {G : Type uG} {V : Type uV} {X : Type uX} [Group G] [Fintype G]
variable (mu : G →* Equiv.Perm X) (nu : G →* Equiv.Perm V)

/-- Proposition 2 packaged as an `iff` under the explicit Stage-D predicate:
rule-neutrality is equivalent to existence of a neutral perfect/skew
representation of the same rule. -/
theorem proposition2_of_perfectSkewRepresentation
    [DecidableEq V] {D : Domain V} {F : RuleOn D X}
    (hInv : DomainInvariant nu D)
    (hRep : IsPerfectBalanceRuleRepresentable.{uV, uX, uR} (D := D) (F := F))
    (hNE : NonemptyOnDomain D F) :
    RuleNeutral mu nu D F ↔
      ∃ (R : Type uR),
      ∃ (instAdd : AddCommGroup R),
      ∃ (instLin : LinearOrder R),
      ∃ (instCovLe : CovariantClass R R (fun a b => a + b) (· ≤ ·)),
      ∃ (instCovLt : CovariantClass R R (fun a b => a + b) (· < ·)),
      ∃ B : BalanceSystem R X V,
        letI : AddCommGroup R := instAdd
        letI : LinearOrder R := instLin
        letI : CovariantClass R R (fun a b => a + b) (· ≤ ·) := instCovLe
        letI : CovariantClass R R (fun a b => a + b) (· < ·) := instCovLt
        BalanceNeutral mu nu B ∧
        BalanceSkew (B := B) ∧
        PerfectOn (D := D) (B := B) ∧
        F = balanceRule (D := D) B := by
  constructor
  · intro hN
    exact exists_balanceNeutralPerfectSkewRepresentation_of_ruleNeutral
      (mu := mu) (nu := nu) hN hRep hNE
  · intro hNeutralRep
    rcases hNeutralRep with ⟨R, instAdd, instLin, instCovLe, instCovLt, B, hB⟩
    let : AddCommGroup R := instAdd
    let : LinearOrder R := instLin
    let : CovariantClass R R (fun a b => a + b) (· ≤ ·) := instCovLe
    let : CovariantClass R R (fun a b => a + b) (· < ·) := instCovLt
    rcases hB with ⟨hNeutral, _hSkew, _hPerfect, hFB⟩
    have hRuleNeutralB : RuleNeutral mu nu D (balanceRule (D := D) B) :=
      balanceRule_ruleNeutral_of_balanceNeutral
        (mu := mu) (nu := nu) (B := B) hInv hNeutral
    simpa [hFB] using hRuleNeutralB

/-- Paper-facing Proposition 2 packaging name. -/
theorem proposition2_of_perfectRepresentation
    [DecidableEq V] {D : Domain V} {F : RuleOn D X}
    (hInv : DomainInvariant nu D)
    (hRep : IsPerfectBalanceRuleRepresentable.{uV, uX, uR} (D := D) (F := F))
    (hNE : NonemptyOnDomain D F) :
    RuleNeutral mu nu D F ↔
      ∃ (R : Type uR),
      ∃ (instAdd : AddCommGroup R),
      ∃ (instLin : LinearOrder R),
      ∃ (instCovLe : CovariantClass R R (fun a b => a + b) (· ≤ ·)),
      ∃ (instCovLt : CovariantClass R R (fun a b => a + b) (· < ·)),
      ∃ B : BalanceSystem R X V,
        letI : AddCommGroup R := instAdd
        letI : LinearOrder R := instLin
        letI : CovariantClass R R (fun a b => a + b) (· ≤ ·) := instCovLe
        letI : CovariantClass R R (fun a b => a + b) (· < ·) := instCovLt
        BalanceNeutral mu nu B ∧
        BalanceSkew (B := B) ∧
        PerfectOn (D := D) (B := B) ∧
        F = balanceRule (D := D) B :=
  proposition2_of_perfectSkewRepresentation
    (mu := mu) (nu := nu) hInv hRep hNE

end Proposition2FinalPackaging

section Proposition2ConverseFiniteGroup

variable {G V X R : Type*} [Group G] [Finite G]
variable [AddCommGroup R] [LinearOrder R]
variable [CovariantClass R R (fun a b => a + b) (· ≤ ·)]
variable [CovariantClass R R (fun a b => a + b) (· < ·)]
variable (mu : G →* Equiv.Perm X) (nu : G →* Equiv.Perm V)

/-- Finite-group wrapper for the explicit-representation converse theorem. -/
theorem exists_balanceNeutralPerfectSkew_of_ruleNeutral_representation_with_nonempty_of_finiteGroup
    {D : Domain V} {F : RuleOn D X}
    (hN : RuleNeutral mu nu D F)
    (hRep : ∃ B : BalanceSystem R X V,
      BalanceSkew (B := B) ∧ PerfectOn (D := D) (B := B) ∧
        F = balanceRule (D := D) B)
    (hNE : NonemptyOnDomain D F) :
    ∃ Bbar : BalanceSystem R X V,
      BalanceNeutral mu nu Bbar ∧
      BalanceSkew (B := Bbar) ∧
      PerfectOn (D := D) (B := Bbar) ∧
      F = balanceRule (D := D) Bbar := by
  classical
  let : Fintype G := Fintype.ofFinite G
  exact exists_balanceNeutralPerfectSkew_of_ruleNeutral_representation_with_nonempty
    (mu := mu) (nu := nu) (D := D) (F := F) hN hRep hNE

end Proposition2ConverseFiniteGroup

end Pivato
