import Pivato.Theorem1.Defs
import Pivato.Theorem1.PairwiseOrders
import Mathlib.Order.Extension.Linear

/-!
# Lemma C.1 consolidated theorem file

This file contains:
- forward/Claim C.1.1 wrappers, and
- the full Appendix C constructive statement.

Full statement formalized here:
from reinforcement (plus explicit rule nonemptiness on the domain), construct
a linearly ordered-codomain balance representation that is perfect.
-/

namespace Pivato

universe uV uX

section LemmaC1

variable {V : Type uV} {X : Type uX} {D : Domain V} (F : RuleOn D X)

/-- Forward fragment of Lemma C.1:
`reinforcement -> isBalanceRepresentable`. -/
theorem lemmaC1_reinforcement_to_isBalanceRepresentable
    [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F) :
    IsBalanceRepresentable (F := F) :=
  isBalanceRepresentable_of_reinforcement (F := F) hD hA hR

/-- Descriptive alias for the forward representability statement. -/
theorem lemmaC1_forward
    [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F) :
    IsBalanceRepresentable (F := F) :=
  lemmaC1_reinforcement_to_isBalanceRepresentable (F := F) hD hA hR

/-- Paper Claim C.1.1(a), in pairwise-relation form:
if `x` wins at `d`, then `0 ≼ b^{x,y}(d)`. -/
theorem lemmaC1_claimC11a_pairwiseRel
    (hD : IsDomain D) (hA : GeneralAbstention D F)
    {d : NProfile V} {hd : d ∈ D} {x y : X}
    (hxd : x ∈ F ⟨d, hd⟩) :
    pairwiseRel F x y 0 (toZProfile d) := by
  exact pairwiseRel_zero_toZProfile_of_winner (F := F) hD hA
    (wins_mk (d := d) (hd := hd) hxd)

/-- Paper Claim C.1.1(b), in pairwise-relation form:
if `x` wins at `d` and `y` does not, then `b^{x,y}(d)` is strictly above `0`
for the pairwise preorder (`0 ≼ b` and not `b ≼ 0`). -/
theorem lemmaC1_claimC11b_pairwiseRel
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    {d : NProfile V} {hd : d ∈ D} {x y : X}
    (hxd : x ∈ F ⟨d, hd⟩)
    (hynotd : y ∉ F ⟨d, hd⟩) :
    pairwiseRel F x y 0 (toZProfile d) ∧
      ¬ pairwiseRel F x y (toZProfile d) 0 := by
  refine ⟨lemmaC1_claimC11a_pairwiseRel (F := F) hD hA hxd, ?_⟩
  exact not_pairwiseRel_toZProfile_zero_of_winner_loser (F := F) hR hxd hynotd

lemma evalNat_apply_dep {ι : Type*} (β : ι → Type*) [∀ i, AddCommMonoid (β i)]
    (w : V → (∀ i, β i)) (d : NProfile V) (i : ι) :
    evalNat (w := w) d i = evalNat (w := fun v => w v i) d := by
  unfold evalNat
  simp [Finsupp.sum]

lemma evalNat_map_hom {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (φ : A →+ B) (w : V → A) (d : NProfile V) :
    evalNat (w := fun v => φ (w v)) d = φ (evalNat (w := w) d) := by
  unfold evalNat
  simp [Finsupp.sum, φ.map_nsmul]

lemma evalNat_single_one_int [DecidableEq V] (d : NProfile V) :
    evalNat (w := fun v => (Finsupp.single v (1 : ℤ) : ZProfile V)) d = toZProfile d := by
  ext u
  simp [evalNat, toZProfile, Finsupp.sum]
  by_cases hu : u ∈ d.support
  · rw [Finset.sum_eq_single u]
    · simp
    · intro a _ha hau
      simp [Finsupp.single_eq_of_ne (M := ℤ) (a := a) (a' := u) (b := 1) hau.symm]
    · intro hnot
      exact (hnot hu).elim
  · rw [Finset.sum_eq_zero]
    · have hdu : d u = 0 := by
        simpa [Finsupp.mem_support_iff] using hu
      simp [hdu]
    · intro a ha
      have hau : u ≠ a := by
        intro hEq
        apply hu
        simpa [hEq] using ha
      simp [Finsupp.single_eq_of_ne (M := ℤ) (a := a) (a' := u) (b := 1) hau]

noncomputable instance pairwiseQuotientPartialOrderInst
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    (p : X × X) :
    PartialOrder (PairwiseQuotient (F := F) hD hA hR p.1 p.2) :=
  pairwiseQuotientPartialOrder (F := F) hD hA hR p.1 p.2

abbrev C1PairCoord
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    (p : X × X) :=
  PairwiseLinearQuotient (F := F) hD hA hR p.1 p.2

abbrev C1RawCodomain
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F) :=
  (p : X × X) → C1PairCoord (F := F) hD hA hR p

abbrev C1Codomain
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F) :=
  LinearExtension (C1RawCodomain (F := F) hD hA hR)

noncomputable def c1RawBalanceSystem [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F) :
    BalanceSystem (C1RawCodomain (F := F) hD hA hR) X V where
  bal x y v p :=
    if p = (x, y) then
      pairwiseLinearMap (F := F) hD hA hR p.1 p.2 (Finsupp.single v (1 : ℤ))
    else 0

noncomputable def c1LinearBalanceSystem [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F) :
    BalanceSystem (C1Codomain (F := F) hD hA hR) X V where
  bal := (c1RawBalanceSystem (F := F) hD hA hR).bal

lemma c1_balanceAt_apply [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    (x y : X) (d : NProfile V) (p : X × X) :
    balanceAt (B := c1RawBalanceSystem (F := F) hD hA hR) x y d p =
      if p = (x, y) then
        pairwiseLinearMap (F := F) hD hA hR p.1 p.2 (toZProfile d)
      else 0 := by
  unfold balanceAt
  rw [evalNat_apply_dep (β := C1PairCoord (F := F) hD hA hR)]
  by_cases hp : p = (x, y)
  · subst hp
    have hEval :
        evalNat (w := fun v =>
            pairwiseLinearMap (F := F) hD hA hR x y (Finsupp.single v (1 : ℤ))) d =
          pairwiseLinearMap (F := F) hD hA hR x y (toZProfile d) := by
      calc
        evalNat (w := fun v =>
            pairwiseLinearMap (F := F) hD hA hR x y (Finsupp.single v (1 : ℤ))) d
            = pairwiseLinearMap (F := F) hD hA hR x y
                (evalNat (w := fun v =>
                  (Finsupp.single v (1 : ℤ) : ZProfile V)) d) :=
              (evalNat_map_hom (φ := pairwiseLinearMap (F := F) hD hA hR x y)
                (w := fun v => (Finsupp.single v (1 : ℤ) : ZProfile V)) d)
        _ = pairwiseLinearMap (F := F) hD hA hR x y (toZProfile d) := by
            simp [evalNat_single_one_int (V := V) d]
    simp [c1RawBalanceSystem, hEval]
  · have hZeroEval :
        evalNat (w := fun _ : V =>
            (0 : C1PairCoord (F := F) hD hA hR p)) d = 0 :=
      by
        unfold evalNat
        simp [Finsupp.sum]
    simpa [c1RawBalanceSystem, hp] using hZeroEval

lemma c1_balanceAt_nonneg_raw_of_winner [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    {d : NProfile V} {hd : d ∈ D} {x y : X}
    (hxd : x ∈ F ⟨d, hd⟩) :
    (0 : C1RawCodomain (F := F) hD hA hR) ≤
      balanceAt (B := c1RawBalanceSystem (F := F) hD hA hR) x y d := by
  intro p
  by_cases hp : p = (x, y)
  · subst hp
    simpa [c1_balanceAt_apply (F := F) hD hA hR x y d (x, y)] using
      pairwiseLinearMap_nonneg_of_winner (F := F) hD hA hR
        (x := x) (y := y) (d := d) (wins_mk (d := d) (hd := hd) hxd)
  · simp [c1_balanceAt_apply (F := F) hD hA hR x y d p, hp]

lemma c1_balanceAt_nonpos_raw_of_winner_loser_swapped [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    {d : NProfile V} {hd : d ∈ D} {x y : X}
    (hyd : y ∈ F ⟨d, hd⟩)
    (_hxnotd : x ∉ F ⟨d, hd⟩) :
    balanceAt (B := c1RawBalanceSystem (F := F) hD hA hR) x y d ≤
      (0 : C1RawCodomain (F := F) hD hA hR) := by
  intro p
  by_cases hp : p = (x, y)
  · subst hp
    simpa [c1_balanceAt_apply (F := F) hD hA hR x y d (x, y)] using
      pairwiseLinearMap_nonpos_of_winner_swapped (F := F) hD hA hR
        (x := x) (y := y) (d := d) (wins_mk (d := d) (hd := hd) hyd)
  · simp [c1_balanceAt_apply (F := F) hD hA hR x y d p, hp]

lemma c1_balanceAt_ne_zero_raw_of_winner_loser [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    {d : NProfile V} {hd : d ∈ D} {x y : X}
    (hxd : x ∈ F ⟨d, hd⟩)
    (hynotd : y ∉ F ⟨d, hd⟩) :
    balanceAt (B := c1RawBalanceSystem (F := F) hD hA hR) x y d ≠
      (0 : C1RawCodomain (F := F) hD hA hR) := by
  intro hzero
  have hcoord :
      pairwiseLinearMap (F := F) hD hA hR x y (toZProfile d) = 0 := by
    have hcoord0 := congrArg (fun f => f (x, y)) hzero
    simpa [c1_balanceAt_apply (F := F) hD hA hR x y d (x, y)] using hcoord0
  have hEqQ :
      (QuotientAddGroup.mk'
        (pairwiseKernelSubgroup (F := F) hD hA hR x y) (toZProfile d) :
          PairwiseQuotient (F := F) hD hA hR x y) = 0 := by
    exact hcoord
  exact
    (pairwiseQuotientMap_ne_zero_of_winner_loser (F := F) hD hA hR
      (x := x) (y := y) (d := d) (hd := hd) hxd hynotd)
    hEqQ

lemma c1_balanceAt_ne_zero_raw_of_winner_loser_swapped [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    {d : NProfile V} {hd : d ∈ D} {x y : X}
    (hyd : y ∈ F ⟨d, hd⟩)
    (hxnotd : x ∉ F ⟨d, hd⟩) :
    balanceAt (B := c1RawBalanceSystem (F := F) hD hA hR) x y d ≠
      (0 : C1RawCodomain (F := F) hD hA hR) := by
  intro hzero
  have hcoord :
      pairwiseLinearMap (F := F) hD hA hR x y (toZProfile d) = 0 := by
    have hcoord0 := congrArg (fun f => f (x, y)) hzero
    simpa [c1_balanceAt_apply (F := F) hD hA hR x y d (x, y)] using hcoord0
  have hEqQ :
      (QuotientAddGroup.mk'
        (pairwiseKernelSubgroup (F := F) hD hA hR x y) (toZProfile d) :
          PairwiseQuotient (F := F) hD hA hR x y) = 0 := by
    exact hcoord
  exact
    (pairwiseQuotientMap_ne_zero_of_not_pairwiseRel_zero (F := F) hD hA hR
      (x := x) (y := y) (d := d)
      (not_pairwiseRel_zero_toZProfile_of_winner_loser_swapped (F := F) hR
        (x := x) (y := y) (d := d) (hd := hd) hyd hxnotd))
    hEqQ

lemma c1_balanceAt_eq_zero_raw_of_winner_winner [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    {d : NProfile V} {hd : d ∈ D} {x y : X}
    (hxd : x ∈ F ⟨d, hd⟩)
    (hyd : y ∈ F ⟨d, hd⟩) :
    balanceAt (B := c1RawBalanceSystem (F := F) hD hA hR) x y d =
      (0 : C1RawCodomain (F := F) hD hA hR) := by
  funext p
  by_cases hp : p = (x, y)
  · subst hp
    have hxy0 : pairwiseRel F x y 0 (toZProfile d) :=
      pairwiseRel_zero_toZProfile_of_winner (F := F) hD hA
        (wins_mk (d := d) (hd := hd) hxd)
    have hxyBack : pairwiseRel F x y (toZProfile d) 0 :=
      pairwiseRel_toZProfile_zero_of_winner_swapped (F := F) hD hA
        (x := x) (y := y) (d := d)
        (wins_mk (d := d) (hd := hd) hyd)
    have hker :
        toZProfile d ∈ pairwiseKernelSubgroup (F := F) hD hA hR x y := by
      exact (mem_pairwiseKernelSubgroup_iff (F := F) hD hA hR
        (x := x) (y := y) (z := toZProfile d)).2 ⟨hxyBack, hxy0⟩
    have hEqQ :
        (QuotientAddGroup.mk'
          (pairwiseKernelSubgroup (F := F) hD hA hR x y) (toZProfile d) :
            PairwiseQuotient (F := F) hD hA hR x y) = 0 := by
      exact (QuotientAddGroup.eq_zero_iff
        (N := pairwiseKernelSubgroup (F := F) hD hA hR x y)
        (x := toZProfile d)).2 hker
    have hcoord :
        pairwiseLinearMap (F := F) hD hA hR x y (toZProfile d) = 0 := by
      exact hEqQ
    simpa [c1_balanceAt_apply (F := F) hD hA hR x y d (x, y)] using hcoord
  · simp [c1_balanceAt_apply (F := F) hD hA hR x y d p, hp]

lemma c1_balanceAt_nonneg_of_winner [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    {d : NProfile V} {hd : d ∈ D} {x y : X}
    (hxd : x ∈ F ⟨d, hd⟩) :
    (0 : C1Codomain (F := F) hD hA hR) ≤
      balanceAt (B := c1LinearBalanceSystem (F := F) hD hA hR) x y d := by
  have hraw :
      (0 : C1RawCodomain (F := F) hD hA hR) ≤
        balanceAt (B := c1RawBalanceSystem (F := F) hD hA hR) x y d :=
    c1_balanceAt_nonneg_raw_of_winner (F := F) hD hA hR
      (hd := hd) (x := x) (y := y) hxd
  exact
    (toLinearExtension (α := C1RawCodomain (F := F) hD hA hR)).monotone hraw

lemma c1_balanceAt_nonpos_of_winner_loser_swapped [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    {d : NProfile V} {hd : d ∈ D} {x y : X}
    (hyd : y ∈ F ⟨d, hd⟩)
    (hxnotd : x ∉ F ⟨d, hd⟩) :
    balanceAt (B := c1LinearBalanceSystem (F := F) hD hA hR) x y d ≤
      (0 : C1Codomain (F := F) hD hA hR) := by
  have hraw :
      balanceAt (B := c1RawBalanceSystem (F := F) hD hA hR) x y d ≤
        (0 : C1RawCodomain (F := F) hD hA hR) :=
    c1_balanceAt_nonpos_raw_of_winner_loser_swapped (F := F) hD hA hR
      (hd := hd) (x := x) (y := y) hyd hxnotd
  exact
    (toLinearExtension (α := C1RawCodomain (F := F) hD hA hR)).monotone hraw

lemma c1_balanceAt_ne_zero_of_winner_loser [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    {d : NProfile V} {hd : d ∈ D} {x y : X}
    (hxd : x ∈ F ⟨d, hd⟩)
    (hynotd : y ∉ F ⟨d, hd⟩) :
    balanceAt (B := c1LinearBalanceSystem (F := F) hD hA hR) x y d ≠
      (0 : C1Codomain (F := F) hD hA hR) := by
  have hraw :
      balanceAt (B := c1RawBalanceSystem (F := F) hD hA hR) x y d ≠
        (0 : C1RawCodomain (F := F) hD hA hR) :=
    c1_balanceAt_ne_zero_raw_of_winner_loser (F := F) hD hA hR
      (hd := hd) (x := x) (y := y) hxd hynotd
  intro hEq
  exact hraw hEq

lemma c1_balanceAt_ne_zero_of_winner_loser_swapped [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    {d : NProfile V} {hd : d ∈ D} {x y : X}
    (hyd : y ∈ F ⟨d, hd⟩)
    (hxnotd : x ∉ F ⟨d, hd⟩) :
    balanceAt (B := c1LinearBalanceSystem (F := F) hD hA hR) x y d ≠
      (0 : C1Codomain (F := F) hD hA hR) := by
  have hraw :
      balanceAt (B := c1RawBalanceSystem (F := F) hD hA hR) x y d ≠
        (0 : C1RawCodomain (F := F) hD hA hR) :=
    c1_balanceAt_ne_zero_raw_of_winner_loser_swapped (F := F) hD hA hR
      (hd := hd) (x := x) (y := y) hyd hxnotd
  intro hEq
  exact hraw hEq

lemma c1_balanceAt_eq_zero_of_winner_winner [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    {d : NProfile V} {hd : d ∈ D} {x y : X}
    (hxd : x ∈ F ⟨d, hd⟩)
    (hyd : y ∈ F ⟨d, hd⟩) :
    balanceAt (B := c1LinearBalanceSystem (F := F) hD hA hR) x y d =
      (0 : C1Codomain (F := F) hD hA hR) := by
  have hraw :
      balanceAt (B := c1RawBalanceSystem (F := F) hD hA hR) x y d =
        (0 : C1RawCodomain (F := F) hD hA hR) :=
    c1_balanceAt_eq_zero_raw_of_winner_winner (F := F) hD hA hR
      (hd := hd) (x := x) (y := y) hxd hyd
  exact hraw

/-- Full Lemma C.1 constructive theorem. -/
theorem lemmaC1
    [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    (hNE : NonemptyOnDomain D F) :
    ∃ B : BalanceSystem (C1Codomain (F := F) hD hA hR) X V,
      PerfectOn (D := D) (B := B) ∧
        F = balanceRule (D := D) B := by
  let : AddCommGroup (C1RawCodomain (F := F) hD hA hR) := inferInstance
  let : PartialOrder (C1RawCodomain (F := F) hD hA hR) := inferInstance
  let : AddCommGroup (C1Codomain (F := F) hD hA hR) := inferInstance
  let : LinearOrder (C1Codomain (F := F) hD hA hR) := inferInstance
  let Braw : BalanceSystem (C1RawCodomain (F := F) hD hA hR) X V :=
    c1RawBalanceSystem (F := F) hD hA hR
  let B : BalanceSystem (C1Codomain (F := F) hD hA hR) X V :=
    c1LinearBalanceSystem (F := F) hD hA hR
  have hEqRule : F = balanceRule (D := D) B := by
    funext d
    ext x
    constructor
    · intro hxd y
      have hraw :
          (0 : C1RawCodomain (F := F) hD hA hR) ≤ balanceAt (B := Braw) x y d.1 :=
        c1_balanceAt_nonneg_raw_of_winner (F := F) hD hA hR
          (hd := d.2) (x := x) (y := y) hxd
      exact
        (toLinearExtension (α := C1RawCodomain (F := F) hD hA hR)).monotone hraw
    · intro hxB
      by_contra hxnot
      rcases hNE d with ⟨y, hyd⟩
      have hlinNonneg :
          (0 : C1Codomain (F := F) hD hA hR) ≤ balanceAt (B := B) x y d.1 := hxB y
      have hrawNonpos :
          balanceAt (B := Braw) x y d.1 ≤ (0 : C1RawCodomain (F := F) hD hA hR) :=
        c1_balanceAt_nonpos_raw_of_winner_loser_swapped (F := F) hD hA hR
          (hd := d.2) (x := x) (y := y) hyd hxnot
      have hlinNonpos :
          balanceAt (B := B) x y d.1 ≤ (0 : C1Codomain (F := F) hD hA hR) := by
        exact
          (toLinearExtension (α := C1RawCodomain (F := F) hD hA hR)).monotone hrawNonpos
      have hneqRaw :
          balanceAt (B := Braw) x y d.1 ≠ (0 : C1RawCodomain (F := F) hD hA hR) :=
        c1_balanceAt_ne_zero_raw_of_winner_loser_swapped (F := F) hD hA hR
          (hd := d.2) (x := x) (y := y) hyd hxnot
      have hneqLin :
          balanceAt (B := B) x y d.1 ≠ (0 : C1Codomain (F := F) hD hA hR) := by
        intro hEq
        exact hneqRaw hEq
      have hzero :
          balanceAt (B := B) x y d.1 = (0 : C1Codomain (F := F) hD hA hR) :=
        le_antisymm hlinNonpos hlinNonneg
      exact hneqLin hzero
  have hPerfect : PerfectOn (D := D) (B := B) := by
    intro d hd x y hxdB hynotB
    have hxdF : x ∈ F ⟨d, hd⟩ := by simpa [hEqRule] using hxdB
    have hynotF : y ∉ F ⟨d, hd⟩ := by simpa [hEqRule] using hynotB
    have hrawNonneg :
        (0 : C1RawCodomain (F := F) hD hA hR) ≤ balanceAt (B := Braw) x y d :=
      c1_balanceAt_nonneg_raw_of_winner (F := F) hD hA hR
        (hd := hd) (x := x) (y := y) hxdF
    have hlinNonneg :
        (0 : C1Codomain (F := F) hD hA hR) ≤ balanceAt (B := B) x y d := by
      exact
        (toLinearExtension (α := C1RawCodomain (F := F) hD hA hR)).monotone hrawNonneg
    have hneqRaw :
        balanceAt (B := Braw) x y d ≠ (0 : C1RawCodomain (F := F) hD hA hR) :=
      c1_balanceAt_ne_zero_raw_of_winner_loser (F := F) hD hA hR
        (hd := hd) (x := x) (y := y) hxdF hynotF
    have hneqLin :
        balanceAt (B := B) x y d ≠ (0 : C1Codomain (F := F) hD hA hR) := by
      intro hEq
      exact hneqRaw hEq
    have h0ne : (0 : C1Codomain (F := F) hD hA hR) ≠ balanceAt (B := B) x y d := by
      intro hEq
      exact hneqLin hEq.symm
    exact lt_of_le_of_ne hlinNonneg h0ne
  refine ⟨B, ?_⟩
  exact ⟨hPerfect, hEqRule⟩

/-- Bridge packaging of Lemma C.1:
an explicit existential representation bundle suitable for downstream APIs. -/
theorem lemmaC1_representationBundle
    [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    (hNE : NonemptyOnDomain D F) :
    ∃ (R : Type (max uV uX)),
      ∃ (instAdd : AddCommGroup R),
      ∃ (instLin : LinearOrder R),
      ∃ B : BalanceSystem R X V,
        letI : AddCommGroup R := instAdd
        letI : LinearOrder R := instLin
        PerfectOn (D := D) (B := B) ∧
          F = balanceRule (D := D) B := by
  rcases lemmaC1 (F := F) hD hA hR hNE with ⟨B, hPerfect, hEqRule⟩
  refine ⟨C1Codomain (F := F) hD hA hR, inferInstance, inferInstance, B, ?_⟩
  exact ⟨hPerfect, hEqRule⟩

/-- Paper-facing Lemma C.1 wrapper:
reinforcement plus nonemptiness yields a perfect balance representation. -/
theorem lemmaC1_reinforcement_to_isPerfectBalanceRepresentable
    [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    (hNE : NonemptyOnDomain D F) :
    IsPerfectBalanceRepresentable (F := F) := by
  rcases lemmaC1_representationBundle (F := F) hD hA hR hNE with
      ⟨R, instAdd, instLin, B, hPerfect, hEqRule⟩
  exact ⟨R, instAdd, instLin, B, hPerfect, hEqRule⟩

end LemmaC1

end Pivato
