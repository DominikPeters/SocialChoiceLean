import Pivato.Balance
import Pivato.Theorem1.Cones

/-!
# Theorem 1 representation layer (Stage D)

This file gives a constructive reinforcement-to-balance representation in the
current abstract framework.
-/

namespace Pivato

section StageD

variable {V X : Type*} {D : Domain V} (F : RuleOn D X)

/-- Ambient codomain used by the canonical Stage-D representation. -/
abbrev PairCode (X V : Type*) := (X × X) → NProfile V

section EvalLemmas

/-- Pointwise evaluation commutes with `evalNat` when the codomain is a function type. -/
lemma evalNat_apply {S R : Type*} [AddCommMonoid R]
    (w : V → S → R) (d : NProfile V) (s : S) :
    evalNat (V := V) (R := S → R) w d s =
      evalNat (V := V) (R := R) (fun v => w v s) d := by
  unfold evalNat
  simp [Finsupp.sum, Finset.sum_apply, Pi.smul_apply]

/-- Evaluating basis profile weights recovers the original profile. -/
lemma evalNat_single_one [DecidableEq V] (d : NProfile V) :
    evalNat (V := V) (R := NProfile V) (fun v => Finsupp.single v (1 : ℕ)) d = d := by
  classical
  ext u
  unfold evalNat
  simp [Finsupp.sum]
  change (∑ x ∈ d.support, d x * (Finsupp.single x (1 : ℕ)) u) = d u
  by_cases hu : u ∈ d.support
  · rw [Finset.sum_eq_single u]
    · simp
    · intro a _hau1 hau
      exact (Nat.mul_eq_zero).2 <|
        Or.inr (by
          simpa using
            (Finsupp.single_eq_of_ne (M := ℕ) (a := a) (a' := u) (b := 1) hau.symm))
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
      exact (Nat.mul_eq_zero).2 <|
        Or.inr (by
          simpa using
            (Finsupp.single_eq_of_ne (M := ℕ) (a := a) (a' := u) (b := 1) hau))

end EvalLemmas

/-- `s` is above `r` if each coordinate is obtained by adding an element from the
corresponding winner cone. -/
def winnerConeLe (r s : PairCode X V) : Prop :=
  ∀ p : X × X, ∃ c : NProfile V, c ∈ winnerCone F p.1 ∧ s p = r p + c

lemma winnerConeLe_refl
    (hD : IsDomain D) (hA : GeneralAbstention D F) :
    ∀ r, winnerConeLe F r r := by
  intro r p
  refine ⟨0, ?_, by simp⟩
  exact winnerCone_zero_of_generalAbstention (F := F) hD hA p.1

lemma winnerConeLe_trans
    (hR : Reinforcement D F) :
    ∀ ⦃r s t⦄, winnerConeLe F r s → winnerConeLe F s t → winnerConeLe F r t := by
  intro r s t hrs hst p
  rcases hrs p with ⟨c₁, hc₁, hs⟩
  rcases hst p with ⟨c₂, hc₂, ht⟩
  refine ⟨c₁ + c₂, ?_, ?_⟩
  · exact (winnerCone_add_closed_of_reinforcement (F := F) hR p.1) hc₁ hc₂
  · calc
      t p = s p + c₂ := ht
      _ = (r p + c₁) + c₂ := by simp [hs]
      _ = r p + (c₁ + c₂) := by simp [add_assoc]

/-- Canonical preorder from winner cones. -/
@[instance_reducible]
def winnerConePreorder
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F) :
    Preorder (PairCode X V) where
  le := winnerConeLe F
  le_refl := winnerConeLe_refl (F := F) hD hA
  le_trans := winnerConeLe_trans (F := F) hR

/-- Canonical balance system used for the Stage-D representation. -/
noncomputable def canonicalBalanceSystem [DecidableEq X] : BalanceSystem (PairCode X V) X V where
  bal x y v p := if p = (x, y) then Finsupp.single v 1 else 0

section CanonicalLemmas

variable [DecidableEq X] [DecidableEq V]

/-- Evaluating the pair-basis weight family at profile `d`. -/
lemma evalNat_pair_basis (x y : X) (d : NProfile V) :
    evalNat (V := V) (R := PairCode X V)
        (fun v p => if p = (x, y) then Finsupp.single v 1 else 0) d
      = (fun p => if p = (x, y) then d else 0) := by
  funext p
  rw [evalNat_apply]
  by_cases hp : p = (x, y)
  · subst hp
    simpa using (evalNat_single_one (V := V) (d := d))
  · simp [hp, evalNat]

lemma balanceAt_canonical_apply (x y : X) (d : NProfile V) (p : X × X) :
    balanceAt (B := canonicalBalanceSystem (X := X) (V := V)) x y d p =
      if p = (x, y) then d else 0 := by
  simpa [canonicalBalanceSystem, balanceAt] using
    congrArg (fun r => r p) (evalNat_pair_basis (x := x) (y := y) (d := d))

end CanonicalLemmas

section MembershipEquivalence

variable [DecidableEq X] [DecidableEq V]

lemma mem_balanceRule_canonical_iff
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F)
    {d : NProfile V} (hd : d ∈ D) (x : X) :
    letI : Preorder (PairCode X V) := winnerConePreorder (F := F) hD hA hR
    x ∈ balanceRule (D := D) (canonicalBalanceSystem (X := X) (V := V)) ⟨d, hd⟩ ↔
      x ∈ F ⟨d, hd⟩ := by
  classical
  let : Preorder (PairCode X V) := winnerConePreorder (F := F) hD hA hR
  constructor
  · intro hx
    have hxx : 0 ≤ balanceAt (B := canonicalBalanceSystem (X := X) (V := V)) x x d := hx x
    change winnerConeLe F 0 (balanceAt (B := canonicalBalanceSystem (X := X) (V := V)) x x d) at hxx
    rcases hxx (x, x) with ⟨c, hc, hcEq⟩
    have hcVal : balanceAt (B := canonicalBalanceSystem (X := X) (V := V)) x x d (x, x) = c := by
      simpa using hcEq
    have hdc : d = c := by
      simpa [balanceAt_canonical_apply (x := x) (y := x) (d := d) (p := (x, x))] using hcVal
    have hmemC : d ∈ winnerCone F x := hdc ▸ hc
    rcases hmemC with ⟨hd', hxd'⟩
    exact (wins_proof_irrel (F := F) (x := x) (d := d) (hd₁ := hd') (hd₂ := hd)).1 hxd'
  · intro hxd y
    change winnerConeLe F 0 (balanceAt (B := canonicalBalanceSystem (X := X) (V := V)) x y d)
    intro p
    by_cases hp : p = (x, y)
    · subst hp
      refine ⟨d, ?_, ?_⟩
      · exact wins_mk (d := d) (hd := hd) hxd
      · simp [balanceAt_canonical_apply (x := x) (y := y) (d := d) (p := (x, y))]
    · refine ⟨0, ?_, ?_⟩
      · exact winnerCone_zero_of_generalAbstention (F := F) hD hA p.1
      · simp [balanceAt_canonical_apply (x := x) (y := y) (d := d) (p := p), hp]

end MembershipEquivalence

/-- Stage-D constructive representation:
`Reinforcement D F` + `GeneralAbstention D F` yields
`∃ B : BalanceSystem (PairCode X V) X V, F = balanceRule B`. -/
theorem reinforcement_has_balance_representation
    [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hA : GeneralAbstention D F) (hR : Reinforcement D F) :
    let R := PairCode X V
    letI : Preorder R := winnerConePreorder (F := F) hD hA hR
    ∃ B : BalanceSystem R X V, F = balanceRule (D := D) B := by
  let : Preorder (PairCode X V) := winnerConePreorder (F := F) hD hA hR
  refine ⟨canonicalBalanceSystem (X := X) (V := V), ?_⟩
  funext d
  ext x
  exact (mem_balanceRule_canonical_iff (F := F) hD hA hR (hd := d.2) x).symm

section ConverseDefs

variable {R : Type*}

/-- Pairwise skew-symmetry at the aggregated balance level. -/
def BalanceSkew [AddCommGroup R] (B : BalanceSystem R X V) : Prop :=
  ∀ x y d, balanceAt B x y d = - balanceAt B y x d

/-- Perfection on a domain: every non-winner is strictly defeated by every winner. -/
def PerfectOn [AddCommMonoid R] [Preorder R] [Zero R] (B : BalanceSystem R X V) : Prop :=
  ∀ ⦃d : NProfile V⦄ (hd : d ∈ D) ⦃x y : X⦄,
    x ∈ balanceRule (D := D) B ⟨d, hd⟩ →
    y ∉ balanceRule (D := D) B ⟨d, hd⟩ →
    0 < balanceAt B x y d

end ConverseDefs

section Converse

variable {R : Type*}
variable [DecidableEq V]
variable [AddCommGroup R] [LinearOrder R]
variable [CovariantClass R R (fun a b => a + b) (· ≤ ·)]
variable [CovariantClass R R (fun a b => a + b) (· < ·)]

omit [CovariantClass R R (fun a b => a + b) (· < ·)] in
lemma mem_add_of_mem_inter
    (B : BalanceSystem R X V)
    {d e : NProfile V} {hd : d ∈ D} {he : e ∈ D} {hsum : d + e ∈ D}
    {z : X}
    (hzd : z ∈ balanceRule (D := D) B ⟨d, hd⟩)
    (hze : z ∈ balanceRule (D := D) B ⟨e, he⟩) :
    z ∈ balanceRule (D := D) B ⟨d + e, hsum⟩ := by
  intro y
  have hdy : (0 : R) ≤ balanceAt B z y d := hzd y
  have hey : (0 : R) ≤ balanceAt B z y e := hze y
  calc
    (0 : R) ≤ balanceAt B z y d + balanceAt B z y e := add_nonneg hdy hey
    _ = balanceAt B z y (d + e) := by
      symm
      simpa using (balanceAt_add (B := B) (x := z) (y := y) d e)

lemma not_mem_add_of_not_mem_left
    (B : BalanceSystem R X V)
    (hskew : BalanceSkew B)
    (hperfect : PerfectOn (D := D) B)
    {d e : NProfile V} {hd : d ∈ D} {he : e ∈ D} {hsum : d + e ∈ D}
    {x z : X}
    (hxd : x ∈ balanceRule (D := D) B ⟨d, hd⟩)
    (hxe : x ∈ balanceRule (D := D) B ⟨e, he⟩)
    (hznotd : z ∉ balanceRule (D := D) B ⟨d, hd⟩) :
    z ∉ balanceRule (D := D) B ⟨d + e, hsum⟩ := by
  intro hzsum
  have hxzPos : 0 < balanceAt B x z d := hperfect hd hxd hznotd
  have hzxNegD : balanceAt B z x d < 0 := by
    calc
      balanceAt B z x d = -balanceAt B x z d := hskew z x d
      _ < 0 := (neg_neg_iff_pos).2 hxzPos
  have hzxNonposE : balanceAt B z x e ≤ 0 := by
    calc
      balanceAt B z x e = -balanceAt B x z e := hskew z x e
      _ ≤ 0 := (neg_nonpos).2 (hxe z)
  have hzxNegSum : balanceAt B z x (d + e) < 0 := by
    calc
      balanceAt B z x (d + e) = balanceAt B z x d + balanceAt B z x e := by
        simpa using (balanceAt_add (B := B) (x := z) (y := x) d e)
      _ < 0 := add_neg_of_neg_of_nonpos hzxNegD hzxNonposE
  exact (not_lt_of_ge (hzsum x)) hzxNegSum

lemma not_mem_add_of_not_mem_right
    (B : BalanceSystem R X V)
    (hskew : BalanceSkew B)
    (hperfect : PerfectOn (D := D) B)
    {d e : NProfile V} {hd : d ∈ D} {he : e ∈ D} {hsum : d + e ∈ D}
    {x z : X}
    (hxd : x ∈ balanceRule (D := D) B ⟨d, hd⟩)
    (hxe : x ∈ balanceRule (D := D) B ⟨e, he⟩)
    (hznote : z ∉ balanceRule (D := D) B ⟨e, he⟩) :
    z ∉ balanceRule (D := D) B ⟨d + e, hsum⟩ := by
  intro hzsum
  have hxzPos : 0 < balanceAt B x z e := hperfect he hxe hznote
  have hzxNegE : balanceAt B z x e < 0 := by
    calc
      balanceAt B z x e = -balanceAt B x z e := hskew z x e
      _ < 0 := (neg_neg_iff_pos).2 hxzPos
  have hzxNonposD : balanceAt B z x d ≤ 0 := by
    calc
      balanceAt B z x d = -balanceAt B x z d := hskew z x d
      _ ≤ 0 := (neg_nonpos).2 (hxd z)
  have hzxNegSum : balanceAt B z x (d + e) < 0 := by
    calc
      balanceAt B z x (d + e) = balanceAt B z x d + balanceAt B z x e := by
        simpa using (balanceAt_add (B := B) (x := z) (y := x) d e)
      _ < 0 := add_neg_of_nonpos_of_neg hzxNonposD hzxNegE
  exact (not_lt_of_ge (hzsum x)) hzxNegSum

/-- Converse direction under explicit structure assumptions on the balance system. -/
theorem balanceRule_reinforcement_of_perfect
    (B : BalanceSystem R X V)
    (hWA : WeaklyAdditive D (balanceRule (D := D) B))
    (hskew : BalanceSkew B)
    (hperfect : PerfectOn (D := D) B) :
    Reinforcement D (balanceRule (D := D) B) := by
  refine ⟨?_, ?_⟩
  · intro d e hd he hinter
    exact hWA hd he hinter
  · intro d e hd he hsum hinter
    apply Set.Subset.antisymm
    · intro z hzsum
      rcases hinter with ⟨x, hxd, hxe⟩
      constructor
      · by_contra hznotd
        exact (not_mem_add_of_not_mem_left (D := D) B hskew hperfect
          (hd := hd) (he := he) (hsum := hsum) hxd hxe hznotd) hzsum
      · by_contra hznote
        exact (not_mem_add_of_not_mem_right (D := D) B hskew hperfect
          (hd := hd) (he := he) (hsum := hsum) hxd hxe hznote) hzsum
    · intro z hz
      exact mem_add_of_mem_inter (D := D) B (hd := hd) (he := he) (hsum := hsum) hz.1 hz.2

end Converse

end StageD

end Pivato
