import Pivato.Theorem1.LemmaC1
import Pivato.Theorem1.OrderedAdditiveExtension
import Pivato.Theorem1.Skewification

/-!
# Ordered-additive package for the Lemma C.1 raw codomain

This file packages the C.1 raw codomain with an ordered-additive linear
extension (when the raw codomain is torsion-free), and provides helper lemmas
to build that torsion-freeness from the saturated pairwise-kernel construction.
-/

namespace Pivato

universe uV uX

section C1OrderedCodomain

variable {V : Type uV} {X : Type uX} {D : Domain V} (F : RuleOn D X)

/-- The coordinatewise partial order relation used in the C.1 raw codomain. -/
abbrev c1RawRel
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F) :
    C1RawCodomain (F := F) hD hA hR → C1RawCodomain (F := F) hD hA hR → Prop :=
  fun f g => ∀ p : X × X,
    pairwiseQuotientRel (F := F) hD hA hR p.1 p.2 (f p) (g p)

noncomputable instance c1RawRel_isPartialOrder
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F) :
    IsPartialOrder (C1RawCodomain (F := F) hD hA hR) (c1RawRel (F := F) hD hA hR) where
  refl := by
    intro f p
    exact (pairwiseQuotientRel_isPartialOrderRel (F := F) hD hA hR p.1 p.2).1.1 (f p)
  trans := by
    intro f g h hfg hgh p
    exact (pairwiseQuotientRel_isPartialOrderRel (F := F) hD hA hR p.1 p.2).1.2
      (hfg p) (hgh p)
  antisymm := by
    intro f g hfg hgf
    funext p
    exact
      (pairwiseQuotientRel_isPartialOrderRel (F := F) hD hA hR p.1 p.2).2.antisymm
        (f p) (g p) (hfg p) (hgf p)

lemma c1RawRel_homogeneous
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F) :
    Homogeneous (c1RawRel (F := F) hD hA hR) := by
  intro f g
  constructor
  · intro hfg p
    exact (pairwiseQuotientRel_homogeneous (F := F) hD hA hR p.1 p.2 (f p) (g p)).1 (hfg p)
  · intro h0 p
    exact (pairwiseQuotientRel_homogeneous (F := F) hD hA hR p.1 p.2 (f p) (g p)).2 (h0 p)

lemma pairwiseQuotientRel_zero_left_iff
    {hD : IsDomain D} {hA : GeneralAbstention D F} {hR : Reinforcement D F} {x y : X}
    {q : PairwiseQuotient (F := F) hD hA hR x y} :
    pairwiseQuotientRel (F := F) hD hA hR x y 0 q ↔
      q ∈ pairwiseQuotientCone (F := F) hD hA hR x y := by
  simp [pairwiseQuotientRel, relOfConoid]

lemma c1RawRel_nonneg_of_winner
    [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    {d : NProfile V} {hd : d ∈ D} {x y : X}
    (hxd : x ∈ F ⟨d, hd⟩) :
    c1RawRel (F := F) hD hA hR
      (0 : C1RawCodomain (F := F) hD hA hR)
      (balanceAt (B := c1RawBalanceSystem (F := F) hD hA hR) x y d) := by
  intro p
  by_cases hp : p = (x, y)
  · subst hp
    let : PartialOrder (PairwiseQuotient (F := F) hD hA hR x y) :=
      pairwiseQuotientPartialOrder (F := F) hD hA hR x y
    change
      pairwiseQuotientRel (F := F) hD hA hR x y 0
        ((balanceAt (B := c1RawBalanceSystem (F := F) hD hA hR) x y d) (x, y))
    have hmem :
        toZProfile d ∈ pairwiseDifferenceCone F x y :=
      toZProfile_mem_pairwiseDifferenceCone_of_winner (F := F) hD hA
        (wins_mk (d := d) (hd := hd) hxd)
    have hcone :
        balanceAt (B := c1RawBalanceSystem (F := F) hD hA hR) x y d (x, y) ∈
          pairwiseQuotientCone (F := F) hD hA hR x y := by
      have hcoord :
          balanceAt (B := c1RawBalanceSystem (F := F) hD hA hR) x y d (x, y) =
            pairwiseLinearMap (F := F) hD hA hR x y (toZProfile d) := by
        simp [c1_balanceAt_apply (F := F) hD hA hR x y d (x, y)]
      have hmap :
          (QuotientAddGroup.mk'
            (pairwiseKernelSubgroup (F := F) hD hA hR x y) (toZProfile d) :
              PairwiseQuotient (F := F) hD hA hR x y) =
            pairwiseLinearMap (F := F) hD hA hR x y (toZProfile d) := by
        change
          (QuotientAddGroup.mk'
            (pairwiseKernelSubgroup (F := F) hD hA hR x y) (toZProfile d) :
              PairwiseQuotient (F := F) hD hA hR x y) =
            toLinearExtension
              (α := PairwiseQuotient (F := F) hD hA hR x y)
              (QuotientAddGroup.mk'
                (pairwiseKernelSubgroup (F := F) hD hA hR x y) (toZProfile d))
        rfl
      exact ⟨toZProfile d, hmem, hmap.trans hcoord.symm⟩
    exact (pairwiseQuotientRel_zero_left_iff F).2 hcone
  · have hrefl :
      pairwiseQuotientRel (F := F) hD hA hR p.1 p.2
        (0 : C1PairCoord (F := F) hD hA hR p) 0 :=
      (pairwiseQuotientRel_isPartialOrderRel (F := F) hD hA hR p.1 p.2).1.1 0
    rw [c1_balanceAt_apply (F := F) hD hA hR x y d p, ite_eq_right hp]
    exact hrefl

lemma c1RawRel_nonpos_of_winner_loser_swapped
    [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    {d : NProfile V} {hd : d ∈ D} {x y : X}
    (hyd : y ∈ F ⟨d, hd⟩)
    (_hxnotd : x ∉ F ⟨d, hd⟩) :
    c1RawRel (F := F) hD hA hR
      (balanceAt (B := c1RawBalanceSystem (F := F) hD hA hR) x y d)
      (0 : C1RawCodomain (F := F) hD hA hR) := by
  intro p
  by_cases hp : p = (x, y)
  · subst hp
    let : PartialOrder (PairwiseQuotient (F := F) hD hA hR x y) :=
      pairwiseQuotientPartialOrder (F := F) hD hA hR x y
    change
      pairwiseQuotientRel (F := F) hD hA hR x y
        ((balanceAt (B := c1RawBalanceSystem (F := F) hD hA hR) x y d) (x, y))
        0
    change
      (0 - balanceAt (B := c1RawBalanceSystem (F := F) hD hA hR) x y d (x, y)) ∈
        pairwiseQuotientCone (F := F) hD hA hR x y
    have hnegMem :
        -toZProfile d ∈ pairwiseDifferenceCone F x y := by
      simpa [pairwiseRel, relOfConoid, sub_eq_add_neg] using
        (pairwiseRel_toZProfile_zero_of_winner_swapped (F := F) hD hA
          (x := x) (y := y) (d := d) (wins_mk (d := d) (hd := hd) hyd))
    have hcoord :
        balanceAt (B := c1RawBalanceSystem (F := F) hD hA hR) x y d (x, y) =
          pairwiseLinearMap (F := F) hD hA hR x y (toZProfile d) := by
      simp [c1_balanceAt_apply (F := F) hD hA hR x y d (x, y)]
    have hmap :
        (QuotientAddGroup.mk'
          (pairwiseKernelSubgroup (F := F) hD hA hR x y) (toZProfile d) :
            PairwiseQuotient (F := F) hD hA hR x y) =
          pairwiseLinearMap (F := F) hD hA hR x y (toZProfile d) := by
      change
        (QuotientAddGroup.mk'
          (pairwiseKernelSubgroup (F := F) hD hA hR x y) (toZProfile d) :
            PairwiseQuotient (F := F) hD hA hR x y) =
          toLinearExtension
            (α := PairwiseQuotient (F := F) hD hA hR x y)
            (QuotientAddGroup.mk'
              (pairwiseKernelSubgroup (F := F) hD hA hR x y) (toZProfile d))
      rfl
    have hneg :
        (0 : C1PairCoord (F := F) hD hA hR (x, y)) -
            balanceAt (B := c1RawBalanceSystem (F := F) hD hA hR) x y d (x, y) =
          pairwiseLinearMap (F := F) hD hA hR x y (-toZProfile d) := by
      rw [hcoord, zero_sub, map_neg]
    exact ⟨-toZProfile d, hnegMem, hneg.symm⟩
  · have hrefl :
      pairwiseQuotientRel (F := F) hD hA hR p.1 p.2
        (0 : C1PairCoord (F := F) hD hA hR p) 0 :=
      (pairwiseQuotientRel_isPartialOrderRel (F := F) hD hA hR p.1 p.2).1.1 0
    rw [c1_balanceAt_apply (F := F) hD hA hR x y d p, ite_eq_right hp]
    exact hrefl

/-- Torsion-freeness of each pairwise linear quotient. -/
theorem c1PairCoord_isAddTorsionFree
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    :
    ∀ p : X × X, IsAddTorsionFree (C1PairCoord (F := F) hD hA hR p) := by
  intro p
  simpa [C1PairCoord, PairwiseLinearQuotient] using
    (pairwiseLinearQuotient_isAddTorsionFree
      (F := F) hD hA hR p.1 p.2)

/-- Build torsion-freeness of the C.1 raw codomain from coordinatewise
pairwise torsion-freeness. -/
theorem c1RawCodomain_isAddTorsionFree_of_pairwise
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    (hTF :
      ∀ p : X × X, IsAddTorsionFree (C1PairCoord (F := F) hD hA hR p)) :
    IsAddTorsionFree (C1RawCodomain (F := F) hD hA hR) := by
  let : ∀ p : X × X, IsAddTorsionFree (C1PairCoord (F := F) hD hA hR p) := hTF
  infer_instance

/-- Unconditional torsion-freeness of the C.1 raw codomain. -/
theorem c1RawCodomain_isAddTorsionFree
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F) :
    IsAddTorsionFree (C1RawCodomain (F := F) hD hA hR) := by
  exact
    c1RawCodomain_isAddTorsionFree_of_pairwise (F := F) hD hA hR
      (c1PairCoord_isAddTorsionFree (F := F) hD hA hR)

/-- Ordered-additive package for the C.1 raw codomain relation. -/
theorem c1RawCodomain_orderedAdditive
    [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    [IsAddTorsionFree (C1RawCodomain (F := F) hD hA hR)] :
    ∃ (instLin : LinearOrder (C1RawCodomain (F := F) hD hA hR)),
      ∃ (instOrd :
          @IsOrderedAddMonoid (C1RawCodomain (F := F) hD hA hR)
            (by infer_instance) instLin.toPreorder),
      ∃ (instCovLe :
          CovariantClass (C1RawCodomain (F := F) hD hA hR)
            (C1RawCodomain (F := F) hD hA hR)
            (fun a b => a + b) (leOfLinearOrder instLin)),
      ∃ (instCovLt :
          CovariantClass (C1RawCodomain (F := F) hD hA hR)
            (C1RawCodomain (F := F) hD hA hR)
            (fun a b => a + b) (ltOfLinearOrder instLin)),
        letI : LinearOrder (C1RawCodomain (F := F) hD hA hR) := instLin
        letI : @IsOrderedAddMonoid (C1RawCodomain (F := F) hD hA hR)
          (by infer_instance) instLin.toPreorder := instOrd
        letI : CovariantClass (C1RawCodomain (F := F) hD hA hR)
          (C1RawCodomain (F := F) hD hA hR)
          (fun a b => a + b) (leOfLinearOrder instLin) := instCovLe
        letI : CovariantClass (C1RawCodomain (F := F) hD hA hR)
          (C1RawCodomain (F := F) hD hA hR)
          (fun a b => a + b) (ltOfLinearOrder instLin) := instCovLt
        c1RawRel (F := F) hD hA hR ≤ leOfLinearOrder instLin := by
  obtain ⟨instLin, instOrd, instCovLe, instCovLt, hExt, _hHom⟩ :=
    homogeneous_szpilrajn_orderedAdditive
      (G := C1RawCodomain (F := F) hD hA hR)
      (r := c1RawRel (F := F) hD hA hR)
      (c1RawRel_homogeneous (F := F) hD hA hR)
  exact ⟨instLin, instOrd, instCovLe, instCovLt, hExt⟩

/-- Ordered-codomain C.1 bridge to the Stage-D skew predicate.

This removes the explicit covariance argument from the caller-facing API:
covariance is obtained from the ordered-additive package on the raw C.1
codomain (under torsion-freeness of that codomain), in the corrected
domain-purity setting. -/
theorem lemmaC1_reinforcement_to_isPerfectSkewBalanceRepresentable
    [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    (hNE : NonemptyOnDomain D F) :
    IsPerfectSkewBalanceRepresentable.{uV, uX, max uV uX} (F := F) := by
  let : IsAddTorsionFree (C1RawCodomain (F := F) hD hA hR) :=
    c1RawCodomain_isAddTorsionFree (F := F) hD hA hR
  rcases c1RawCodomain_orderedAdditive (F := F) hD hA hR with
      ⟨instLin, _instOrd, instCovLe, instCovLt, hExt⟩
  let : LE (C1RawCodomain (F := F) hD hA hR) := instLin.toLE
  let : LT (C1RawCodomain (F := F) hD hA hR) := instLin.toLT
  let : LinearOrder (C1RawCodomain (F := F) hD hA hR) := instLin
  let : Preorder (C1RawCodomain (F := F) hD hA hR) := instLin.toPreorder
  let : PartialOrder (C1RawCodomain (F := F) hD hA hR) := instLin.toPartialOrder
  have instCovLe' :
      CovariantClass
        (C1RawCodomain (F := F) hD hA hR)
        (C1RawCodomain (F := F) hD hA hR)
        (fun a b => a + b) (· ≤ ·) := instCovLe
  have instCovLt' :
      CovariantClass
        (C1RawCodomain (F := F) hD hA hR)
        (C1RawCodomain (F := F) hD hA hR)
        (fun a b => a + b) (· < ·) := instCovLt
  have hExt' :
      c1RawRel (F := F) hD hA hR ≤ (· ≤ ·) := by
    exact hExt
  let B0 : BalanceSystem (C1RawCodomain (F := F) hD hA hR) X V :=
    c1RawBalanceSystem (F := F) hD hA hR
  let B : BalanceSystem (C1RawCodomain (F := F) hD hA hR) X V :=
    skewifyBalanceSystem B0
  have hEqRule : F = balanceRule (D := D) B := by
    funext d
    ext x
    constructor
    · intro hxd y
      by_cases hyd : y ∈ F ⟨d.1, d.2⟩
      · have hxy0 :
          balanceAt (B := B0) x y d.1 = (0 : C1RawCodomain (F := F) hD hA hR) :=
          c1_balanceAt_eq_zero_raw_of_winner_winner (F := F) hD hA hR
            (hd := d.2) (x := x) (y := y) hxd hyd
        have hyx0 :
            balanceAt (B := B0) y x d.1 = (0 : C1RawCodomain (F := F) hD hA hR) :=
          c1_balanceAt_eq_zero_raw_of_winner_winner (F := F) hD hA hR
            (hd := d.2) (x := y) (y := x) hyd hxd
        simp [B, balanceAt_skewify (B := B0), hxy0, hyx0]
      · have hxyNonnegRaw :
          c1RawRel (F := F) hD hA hR
            (0 : C1RawCodomain (F := F) hD hA hR)
            (balanceAt (B := B0) x y d.1) :=
          c1RawRel_nonneg_of_winner (F := F) hD hA hR
            (hd := d.2) (x := x) (y := y) hxd
        have hxyNonneg :
          (0 : C1RawCodomain (F := F) hD hA hR) ≤ balanceAt (B := B0) x y d.1 :=
          hExt' _ _ hxyNonnegRaw
        have hyxNonposRaw :
            c1RawRel (F := F) hD hA hR
              (balanceAt (B := B0) y x d.1)
              (0 : C1RawCodomain (F := F) hD hA hR) :=
          c1RawRel_nonpos_of_winner_loser_swapped (F := F) hD hA hR
            (hd := d.2) (x := y) (y := x) hxd hyd
        have hyxNonpos :
            balanceAt (B := B0) y x d.1 ≤ (0 : C1RawCodomain (F := F) hD hA hR) :=
          hExt' _ _ hyxNonposRaw
        have hnegHyxNonneg :
            (0 : C1RawCodomain (F := F) hD hA hR) ≤ -balanceAt (B := B0) y x d.1 :=
          neg_nonneg.mpr hyxNonpos
        have hsumNonneg :
            (0 : C1RawCodomain (F := F) hD hA hR) ≤
              balanceAt (B := B0) x y d.1 + (-balanceAt (B := B0) y x d.1) :=
          add_nonneg hxyNonneg hnegHyxNonneg
        simpa [B, balanceAt_skewify (B := B0), sub_eq_add_neg] using hsumNonneg
    · intro hxB
      by_contra hxnot
      rcases hNE d with ⟨y, hyd⟩
      have hxyNonposRaw :
          c1RawRel (F := F) hD hA hR
            (balanceAt (B := B0) x y d.1)
            (0 : C1RawCodomain (F := F) hD hA hR) :=
        c1RawRel_nonpos_of_winner_loser_swapped (F := F) hD hA hR
          (hd := d.2) (x := x) (y := y) hyd hxnot
      have hxyNonpos :
          balanceAt (B := B0) x y d.1 ≤ (0 : C1RawCodomain (F := F) hD hA hR) :=
        hExt' _ _ hxyNonposRaw
      have hxyNe :
          balanceAt (B := B0) x y d.1 ≠ (0 : C1RawCodomain (F := F) hD hA hR) :=
        c1_balanceAt_ne_zero_raw_of_winner_loser_swapped (F := F) hD hA hR
          (hd := d.2) (x := x) (y := y) hyd hxnot
      have hxyNeg :
          balanceAt (B := B0) x y d.1 < (0 : C1RawCodomain (F := F) hD hA hR) := by
        have h0ne : (0 : C1RawCodomain (F := F) hD hA hR) ≠ balanceAt (B := B0) x y d.1 := by
          intro hEq
          exact hxyNe hEq.symm
        exact lt_of_le_of_ne hxyNonpos h0ne.symm
      have hyxNonnegRaw :
          c1RawRel (F := F) hD hA hR
            (0 : C1RawCodomain (F := F) hD hA hR)
            (balanceAt (B := B0) y x d.1) :=
        c1RawRel_nonneg_of_winner (F := F) hD hA hR
          (hd := d.2) (x := y) (y := x) hyd
      have hyxNonneg :
          (0 : C1RawCodomain (F := F) hD hA hR) ≤ balanceAt (B := B0) y x d.1 :=
        hExt' _ _ hyxNonnegRaw
      have hnegHyxNonpos :
          -balanceAt (B := B0) y x d.1 ≤ (0 : C1RawCodomain (F := F) hD hA hR) :=
        neg_nonpos.mpr hyxNonneg
      have hsumNeg :
          balanceAt (B := B0) x y d.1 + (-balanceAt (B := B0) y x d.1) <
            (0 : C1RawCodomain (F := F) hD hA hR) :=
        add_neg_of_neg_of_nonpos hxyNeg hnegHyxNonpos
      have hbalNeg : balanceAt (B := B) x y d.1 < (0 : C1RawCodomain (F := F) hD hA hR) := by
        simpa [B, balanceAt_skewify (B := B0), sub_eq_add_neg] using hsumNeg
      exact (not_lt_of_ge (hxB y)) hbalNeg
  have hPerfect : PerfectOn (D := D) (B := B) := by
    intro d hd x y hxdB hynotB
    have hxdF : x ∈ F ⟨d, hd⟩ := by simpa [hEqRule] using hxdB
    have hynotF : y ∉ F ⟨d, hd⟩ := by simpa [hEqRule] using hynotB
    have hxyNonnegRaw :
        c1RawRel (F := F) hD hA hR
          (0 : C1RawCodomain (F := F) hD hA hR)
          (balanceAt (B := B0) x y d) :=
      c1RawRel_nonneg_of_winner (F := F) hD hA hR
        (hd := hd) (x := x) (y := y) hxdF
    have hxyNonneg :
        (0 : C1RawCodomain (F := F) hD hA hR) ≤ balanceAt (B := B0) x y d :=
      hExt' _ _ hxyNonnegRaw
    have hxyNe :
        balanceAt (B := B0) x y d ≠ (0 : C1RawCodomain (F := F) hD hA hR) :=
      c1_balanceAt_ne_zero_raw_of_winner_loser (F := F) hD hA hR
        (hd := hd) (x := x) (y := y) hxdF hynotF
    have hxyPos :
        (0 : C1RawCodomain (F := F) hD hA hR) < balanceAt (B := B0) x y d := by
      have h0ne : (0 : C1RawCodomain (F := F) hD hA hR) ≠ balanceAt (B := B0) x y d := by
        intro hEq
        exact hxyNe hEq.symm
      exact lt_of_le_of_ne hxyNonneg h0ne
    have hyxNonposRaw :
        c1RawRel (F := F) hD hA hR
          (balanceAt (B := B0) y x d)
          (0 : C1RawCodomain (F := F) hD hA hR) :=
      c1RawRel_nonpos_of_winner_loser_swapped (F := F) hD hA hR
        (hd := hd) (x := y) (y := x) hxdF hynotF
    have hyxNonpos :
        balanceAt (B := B0) y x d ≤ (0 : C1RawCodomain (F := F) hD hA hR) :=
      hExt' _ _ hyxNonposRaw
    have hnegHyxNonneg :
        (0 : C1RawCodomain (F := F) hD hA hR) ≤ -balanceAt (B := B0) y x d :=
      neg_nonneg.mpr hyxNonpos
    have hsumPos :
        (0 : C1RawCodomain (F := F) hD hA hR) <
          balanceAt (B := B0) x y d + (-balanceAt (B := B0) y x d) :=
      add_pos_of_pos_of_nonneg hxyPos hnegHyxNonneg
    simpa [B, balanceAt_skewify (B := B0), sub_eq_add_neg] using hsumPos
  have hSkew : BalanceSkew (B := B) :=
    skewifyBalanceSystem_skew (B := B0)
  exact
    ⟨C1RawCodomain (F := F) hD hA hR, inferInstance, instLin,
      instCovLe', instCovLt', B, hSkew, hPerfect, hEqRule⟩

end C1OrderedCodomain

end Pivato
