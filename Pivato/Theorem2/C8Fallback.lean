import Pivato.Theorem2.C8OrbitCases
import Mathlib.Tactic.Abel

/-!
# Lemma C.8.4 fallback development

This module formalizes the Case 1/2 branch of Appendix C.8:
- paper-form equation packages `(C.9)--(C.14)` and `(C.15)--(C.20)`;
- designated reductions to Eq. (C.21);
- branch-split assembly (`C.8.3` vs `C.8.4`) via orbit-partition witnesses.
-/

namespace Pivato

section C8Fallback

universe uV uX uR

variable {V : Type uV} {X : Type uX} {R : Type uR}
variable (nu : Equiv.Perm X →* Equiv.Perm V)

/-- C.8.4 fallback package: 4-cycle equations (C.9--C.14 style). -/
structure C8FallbackEquationPack4
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (D : Domain V) (B : BalanceSystem R X V) where
  x : X
  y : X
  z : X
  w : X
  hxy : x ≠ y
  hyz : y ≠ z
  hzx : z ≠ x
  hzw : z ≠ w
  hwx : w ≠ x
  eqC9 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B x y d + balanceAt B y z d +
        balanceAt B z w d + balanceAt B w x d = 0
  eqC10 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B x y d + balanceAt B y w d +
        balanceAt B w z d + balanceAt B z x d = 0
  eqC11 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B y z d + balanceAt B z x d +
        balanceAt B x w d + balanceAt B w y d = 0
  eqC12 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B y z d + balanceAt B z w d +
        balanceAt B w x d + balanceAt B x y d = 0
  eqC13 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B z x d + balanceAt B x y d +
        balanceAt B y w d + balanceAt B w z d = 0
  eqC14 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B z x d + balanceAt B x w d +
        balanceAt B w y d + balanceAt B y z d = 0

/-- C.8.4 fallback package: 5-cycle equations (C.15--C.20 style). -/
structure C8FallbackEquationPack5
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (D : Domain V) (B : BalanceSystem R X V) where
  x : X
  y : X
  z : X
  u : X
  v : X
  hxy : x ≠ y
  hyz : y ≠ z
  hzx : z ≠ x
  hzu : z ≠ u
  huv : u ≠ v
  hvx : v ≠ x
  eqC15 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B x y d + balanceAt B y z d + balanceAt B z u d +
        balanceAt B u v d + balanceAt B v x d = 0
  eqC16 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B x y d + balanceAt B y z d + balanceAt B z v d +
        balanceAt B v u d + balanceAt B u x d = 0
  eqC17 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B y z d + balanceAt B z x d + balanceAt B x u d +
        balanceAt B u v d + balanceAt B v y d = 0
  eqC18 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B y z d + balanceAt B z x d + balanceAt B x v d +
        balanceAt B v u d + balanceAt B u y d = 0
  eqC19 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B z x d + balanceAt B x y d + balanceAt B y u d +
        balanceAt B u v d + balanceAt B v z d = 0
  eqC20 :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B z x d + balanceAt B x y d + balanceAt B y v d +
        balanceAt B v u d + balanceAt B u z d = 0

/-- C.8.4 fallback equation package: either the 4-cycle or 5-cycle package. -/
def C8FallbackEquationPack
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (D : Domain V) (B : BalanceSystem R X V) : Prop :=
  Nonempty (C8FallbackEquationPack4 (D := D) (B := B)) ∨
    Nonempty (C8FallbackEquationPack5 (D := D) (B := B))

/-- Paper-faithful Case-1 reduction:
from (C.9)--(C.14), derive Eq. (C.21) on the designated triple `(x,y,z)`. -/
theorem c8EqC21_designated_of_equationPack4
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    (hPack4 : C8FallbackEquationPack4 (D := D) (B := B)) :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B hPack4.x hPack4.y d + balanceAt B hPack4.y hPack4.z d +
        balanceAt B hPack4.z hPack4.x d = 0 := by
  intro d hd
  let S : R :=
      balanceAt B hPack4.x hPack4.y d +
      balanceAt B hPack4.y hPack4.z d +
      balanceAt B hPack4.z hPack4.x d
  have h9 := hPack4.eqC9 hd
  have h10 := hPack4.eqC10 hd
  have h11 := hPack4.eqC11 hd
  have hxw : balanceAt B hPack4.x hPack4.w d = -balanceAt B hPack4.w hPack4.x d := by
    simpa using hSkew hPack4.x hPack4.w d
  have hwy : balanceAt B hPack4.w hPack4.y d = -balanceAt B hPack4.y hPack4.w d := by
    simpa using hSkew hPack4.w hPack4.y d
  have hwz : balanceAt B hPack4.w hPack4.z d = -balanceAt B hPack4.z hPack4.w d := by
    simpa using hSkew hPack4.w hPack4.z d
  have hsum0 :
      (balanceAt B hPack4.x hPack4.y d + balanceAt B hPack4.y hPack4.z d +
          balanceAt B hPack4.z hPack4.w d + balanceAt B hPack4.w hPack4.x d) +
        (balanceAt B hPack4.x hPack4.y d + balanceAt B hPack4.y hPack4.w d +
          balanceAt B hPack4.w hPack4.z d + balanceAt B hPack4.z hPack4.x d) +
        (balanceAt B hPack4.y hPack4.z d + balanceAt B hPack4.z hPack4.x d +
          balanceAt B hPack4.x hPack4.w d + balanceAt B hPack4.w hPack4.y d) = 0 := by
    calc
      (balanceAt B hPack4.x hPack4.y d + balanceAt B hPack4.y hPack4.z d +
          balanceAt B hPack4.z hPack4.w d + balanceAt B hPack4.w hPack4.x d) +
        (balanceAt B hPack4.x hPack4.y d + balanceAt B hPack4.y hPack4.w d +
          balanceAt B hPack4.w hPack4.z d + balanceAt B hPack4.z hPack4.x d) +
        (balanceAt B hPack4.y hPack4.z d + balanceAt B hPack4.z hPack4.x d +
          balanceAt B hPack4.x hPack4.w d + balanceAt B hPack4.w hPack4.y d)
          = (0 : R) + 0 + 0 := by simp [h9, h10, h11]
      _ = 0 := by simp
  have hdouble : S + S = 0 := by
    unfold S
    calc
      (balanceAt B hPack4.x hPack4.y d + balanceAt B hPack4.y hPack4.z d +
          balanceAt B hPack4.z hPack4.x d) +
        (balanceAt B hPack4.x hPack4.y d + balanceAt B hPack4.y hPack4.z d +
          balanceAt B hPack4.z hPack4.x d)
      =
          (balanceAt B hPack4.x hPack4.y d + balanceAt B hPack4.y hPack4.z d +
            balanceAt B hPack4.z hPack4.w d + balanceAt B hPack4.w hPack4.x d) +
            (balanceAt B hPack4.x hPack4.y d + balanceAt B hPack4.y hPack4.w d +
              balanceAt B hPack4.w hPack4.z d + balanceAt B hPack4.z hPack4.x d) +
              (balanceAt B hPack4.y hPack4.z d + balanceAt B hPack4.z hPack4.x d +
                balanceAt B hPack4.x hPack4.w d + balanceAt B hPack4.w hPack4.y d) := by
              simp [hxw, hwy, hwz]
              abel_nf
      _ = 0 := by simpa [add_assoc] using hsum0
  have hle : S ≤ 0 := by
    by_contra hnot
    have hpos : 0 < S := lt_of_not_ge hnot
    have hpos2 : 0 < S + S := add_pos hpos hpos
    have hnotPos : ¬ 0 < S + S := by simp [hdouble]
    exact hnotPos hpos2
  have hge : 0 ≤ S := by
    by_contra hnot
    have hneg : S < 0 := lt_of_not_ge hnot
    have hneg2 : S + S < 0 := add_neg hneg hneg
    have hnotNeg : ¬ S + S < 0 := by simp [hdouble]
    exact hnotNeg hneg2
  have hS0 : S = 0 := le_antisymm hle hge
  simpa [S] using hS0

/-- Paper-faithful Case-2 reduction:
from (C.15)--(C.20), derive Eq. (C.21) on the designated triple `(x,y,z)`. -/
theorem c8EqC21_designated_of_equationPack5
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    (hPack5 : C8FallbackEquationPack5 (D := D) (B := B)) :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B hPack5.x hPack5.y d + balanceAt B hPack5.y hPack5.z d +
        balanceAt B hPack5.z hPack5.x d = 0 := by
  intro d hd
  let S : R :=
      balanceAt B hPack5.x hPack5.y d +
      balanceAt B hPack5.y hPack5.z d +
      balanceAt B hPack5.z hPack5.x d
  have h15 := hPack5.eqC15 hd
  have h16 := hPack5.eqC16 hd
  have h17 := hPack5.eqC17 hd
  have h18 := hPack5.eqC18 hd
  have h19 := hPack5.eqC19 hd
  have h20 := hPack5.eqC20 hd
  have hux : balanceAt B hPack5.u hPack5.x d = -balanceAt B hPack5.x hPack5.u d := by
    simpa using hSkew hPack5.u hPack5.x d
  have hvu : balanceAt B hPack5.v hPack5.u d = -balanceAt B hPack5.u hPack5.v d := by
    simpa using hSkew hPack5.v hPack5.u d
  have hbxv : balanceAt B hPack5.x hPack5.v d = -balanceAt B hPack5.v hPack5.x d := by
    simpa using hSkew hPack5.x hPack5.v d
  have hbvy : balanceAt B hPack5.v hPack5.y d = -balanceAt B hPack5.y hPack5.v d := by
    simpa using hSkew hPack5.v hPack5.y d
  have hbuy : balanceAt B hPack5.u hPack5.y d = -balanceAt B hPack5.y hPack5.u d := by
    simpa using hSkew hPack5.u hPack5.y d
  have hbzv : balanceAt B hPack5.z hPack5.v d = -balanceAt B hPack5.v hPack5.z d := by
    simpa using hSkew hPack5.z hPack5.v d
  have hbuz : balanceAt B hPack5.u hPack5.z d = -balanceAt B hPack5.z hPack5.u d := by
    simpa using hSkew hPack5.u hPack5.z d
  have hsum0 :
      (balanceAt B hPack5.x hPack5.y d + balanceAt B hPack5.y hPack5.z d +
          balanceAt B hPack5.z hPack5.u d + balanceAt B hPack5.u hPack5.v d +
          balanceAt B hPack5.v hPack5.x d) +
        (balanceAt B hPack5.x hPack5.y d + balanceAt B hPack5.y hPack5.z d +
          balanceAt B hPack5.z hPack5.v d + balanceAt B hPack5.v hPack5.u d +
          balanceAt B hPack5.u hPack5.x d) +
        (balanceAt B hPack5.y hPack5.z d + balanceAt B hPack5.z hPack5.x d +
          balanceAt B hPack5.x hPack5.u d + balanceAt B hPack5.u hPack5.v d +
          balanceAt B hPack5.v hPack5.y d) +
        (balanceAt B hPack5.y hPack5.z d + balanceAt B hPack5.z hPack5.x d +
          balanceAt B hPack5.x hPack5.v d + balanceAt B hPack5.v hPack5.u d +
          balanceAt B hPack5.u hPack5.y d) +
        (balanceAt B hPack5.z hPack5.x d + balanceAt B hPack5.x hPack5.y d +
          balanceAt B hPack5.y hPack5.u d + balanceAt B hPack5.u hPack5.v d +
          balanceAt B hPack5.v hPack5.z d) +
        (balanceAt B hPack5.z hPack5.x d + balanceAt B hPack5.x hPack5.y d +
          balanceAt B hPack5.y hPack5.v d + balanceAt B hPack5.v hPack5.u d +
          balanceAt B hPack5.u hPack5.z d) = 0 := by
    calc
      (balanceAt B hPack5.x hPack5.y d + balanceAt B hPack5.y hPack5.z d +
          balanceAt B hPack5.z hPack5.u d + balanceAt B hPack5.u hPack5.v d +
          balanceAt B hPack5.v hPack5.x d) +
        (balanceAt B hPack5.x hPack5.y d + balanceAt B hPack5.y hPack5.z d +
          balanceAt B hPack5.z hPack5.v d + balanceAt B hPack5.v hPack5.u d +
          balanceAt B hPack5.u hPack5.x d) +
        (balanceAt B hPack5.y hPack5.z d + balanceAt B hPack5.z hPack5.x d +
          balanceAt B hPack5.x hPack5.u d + balanceAt B hPack5.u hPack5.v d +
          balanceAt B hPack5.v hPack5.y d) +
        (balanceAt B hPack5.y hPack5.z d + balanceAt B hPack5.z hPack5.x d +
          balanceAt B hPack5.x hPack5.v d + balanceAt B hPack5.v hPack5.u d +
          balanceAt B hPack5.u hPack5.y d) +
        (balanceAt B hPack5.z hPack5.x d + balanceAt B hPack5.x hPack5.y d +
          balanceAt B hPack5.y hPack5.u d + balanceAt B hPack5.u hPack5.v d +
          balanceAt B hPack5.v hPack5.z d) +
        (balanceAt B hPack5.z hPack5.x d + balanceAt B hPack5.x hPack5.y d +
          balanceAt B hPack5.y hPack5.v d + balanceAt B hPack5.v hPack5.u d +
          balanceAt B hPack5.u hPack5.z d)
          = (0 : R) + 0 + 0 + 0 + 0 + 0 := by
              simp [h15, h16, h17, h18, h19, h20]
      _ = 0 := by simp
  have hquadruple : S + S + S + S = 0 := by
    unfold S
    calc
      (balanceAt B hPack5.x hPack5.y d + balanceAt B hPack5.y hPack5.z d +
          balanceAt B hPack5.z hPack5.x d) +
        (balanceAt B hPack5.x hPack5.y d + balanceAt B hPack5.y hPack5.z d +
          balanceAt B hPack5.z hPack5.x d) +
        (balanceAt B hPack5.x hPack5.y d + balanceAt B hPack5.y hPack5.z d +
          balanceAt B hPack5.z hPack5.x d) +
        (balanceAt B hPack5.x hPack5.y d + balanceAt B hPack5.y hPack5.z d +
          balanceAt B hPack5.z hPack5.x d)
      =
          (balanceAt B hPack5.x hPack5.y d + balanceAt B hPack5.y hPack5.z d +
            balanceAt B hPack5.z hPack5.u d + balanceAt B hPack5.u hPack5.v d +
            balanceAt B hPack5.v hPack5.x d) +
            (balanceAt B hPack5.x hPack5.y d + balanceAt B hPack5.y hPack5.z d +
              balanceAt B hPack5.z hPack5.v d + balanceAt B hPack5.v hPack5.u d +
              balanceAt B hPack5.u hPack5.x d) +
              (balanceAt B hPack5.y hPack5.z d + balanceAt B hPack5.z hPack5.x d +
                balanceAt B hPack5.x hPack5.u d + balanceAt B hPack5.u hPack5.v d +
                balanceAt B hPack5.v hPack5.y d) +
                (balanceAt B hPack5.y hPack5.z d + balanceAt B hPack5.z hPack5.x d +
                  balanceAt B hPack5.x hPack5.v d + balanceAt B hPack5.v hPack5.u d +
                  balanceAt B hPack5.u hPack5.y d) +
                  (balanceAt B hPack5.z hPack5.x d + balanceAt B hPack5.x hPack5.y d +
                    balanceAt B hPack5.y hPack5.u d + balanceAt B hPack5.u hPack5.v d +
                    balanceAt B hPack5.v hPack5.z d) +
                    (balanceAt B hPack5.z hPack5.x d + balanceAt B hPack5.x hPack5.y d +
                      balanceAt B hPack5.y hPack5.v d + balanceAt B hPack5.v hPack5.u d +
                      balanceAt B hPack5.u hPack5.z d) := by
                simp [hux, hvu, hbxv, hbvy, hbuy, hbzv, hbuz]
                abel_nf
      _ = 0 := by simpa [add_assoc] using hsum0
  have hle : S ≤ 0 := by
    by_contra hnot
    have hpos : 0 < S := lt_of_not_ge hnot
    have hpos4 : 0 < S + S + S + S := by
      have h2 : 0 < S + S := add_pos hpos hpos
      have h4 : 0 < (S + S) + (S + S) := add_pos h2 h2
      simpa [add_assoc] using h4
    have hnotPos : ¬ 0 < S + S + S + S := by simp [hquadruple]
    exact hnotPos hpos4
  have hge : 0 ≤ S := by
    by_contra hnot
    have hneg : S < 0 := lt_of_not_ge hnot
    have hneg4 : S + S + S + S < 0 := by
      have h2 : S + S < 0 := add_neg hneg hneg
      have h4 : (S + S) + (S + S) < 0 := add_neg h2 h2
      simpa [add_assoc] using h4
    have hnotNeg : ¬ S + S + S + S < 0 := by simp [hquadruple]
    exact hnotNeg hneg4
  have hS0 : S = 0 := le_antisymm hle hge
  simpa [S] using hS0

/-- Package Case-1 equation data as a C.8.4 branch witness. -/
theorem c8Fallback_fourFiveCycleBranch_of_equationPack4
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    (hPack4 : C8FallbackEquationPack4 (D := D) (B := B)) :
    C8FourFiveCycleBranchHypothesis (D := D) (B := B) := by
  exact C8FourFiveCycleBranchHypothesis.ofFourCycle
    hPack4.x hPack4.y hPack4.z hPack4.w
    hPack4.hxy hPack4.hyz hPack4.hzx hPack4.hzw hPack4.hwx
    (c8EqC21_designated_of_equationPack4 (D := D) (B := B) hSkew hPack4)

/-- Package Case-2 equation data as a C.8.4 branch witness. -/
theorem c8Fallback_fourFiveCycleBranch_of_equationPack5
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    (hPack5 : C8FallbackEquationPack5 (D := D) (B := B)) :
    C8FourFiveCycleBranchHypothesis (D := D) (B := B) := by
  exact C8FourFiveCycleBranchHypothesis.ofFiveCycle
    hPack5.x hPack5.y hPack5.z hPack5.u hPack5.v
    hPack5.hxy hPack5.hyz hPack5.hzx hPack5.hzu hPack5.huv hPack5.hvx
    (c8EqC21_designated_of_equationPack5 (D := D) (B := B) hSkew hPack5)

theorem c8CycleSumHypothesis_of_equationPack4
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    (hPack4 : C8FallbackEquationPack4 (D := D) (B := B)) :
    C8CycleSumHypothesis (D := D) (B := B) := by
  refine ⟨hPack4.x, hPack4.y, hPack4.z, hPack4.hxy, hPack4.hyz, hPack4.hzx, ?_⟩
  exact c8EqC21_designated_of_equationPack4 (D := D) (B := B) hSkew hPack4

theorem c8CycleSumHypothesis_of_equationPack5
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    (hPack5 : C8FallbackEquationPack5 (D := D) (B := B)) :
    C8CycleSumHypothesis (D := D) (B := B) := by
  refine ⟨hPack5.x, hPack5.y, hPack5.z, hPack5.hxy, hPack5.hyz, hPack5.hzx, ?_⟩
  exact c8EqC21_designated_of_equationPack5 (D := D) (B := B) hSkew hPack5

theorem c8CycleSumHypothesis_of_equationPack
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    (hPack : C8FallbackEquationPack (D := D) (B := B)) :
    C8CycleSumHypothesis (D := D) (B := B) := by
  rcases hPack with hPack4 | hPack5
  · rcases hPack4 with ⟨hPack4⟩
    exact c8CycleSumHypothesis_of_equationPack4 (D := D) (B := B) hSkew hPack4
  · rcases hPack5 with ⟨hPack5⟩
    exact c8CycleSumHypothesis_of_equationPack5 (D := D) (B := B) hSkew hPack5

theorem c8Fallback_fourFiveCycleBranch_of_equationPack
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    (hSkew : BalanceSkew (B := B))
    (hPack : C8FallbackEquationPack (D := D) (B := B)) :
    C8FourFiveCycleBranchHypothesis (D := D) (B := B) := by
  rcases hPack with hPack4 | hPack5
  · rcases hPack4 with ⟨p4⟩
    exact c8Fallback_fourFiveCycleBranch_of_equationPack4 (D := D) (B := B) hSkew p4
  · rcases hPack5 with ⟨p5⟩
    exact c8Fallback_fourFiveCycleBranch_of_equationPack5 (D := D) (B := B) hSkew p5

noncomputable def c8Fallback_case1_orbitMap
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (d1 : C8Case1OrbitPartitionData X) :
    NProfile V → NProfile V :=
  orbitProfileSum (nu d1.φ) (d1.period - 1)

noncomputable def c8Fallback_case2_orbitMap
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (d2 : C8Case2OrbitPartitionData X) :
    NProfile V → NProfile V :=
  orbitProfileSum (nu d2.φ) (d2.period - 1)

theorem c8Fallback_case1_orbitMap_mem
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (hInv : DomainInvariant nu D)
    (d1 : C8Case1OrbitPartitionData X)
    {d : NProfile V} (hd : d ∈ D) :
    c8Fallback_case1_orbitMap (nu := nu) (R := R) d1 d ∈ D := by
  exact orbitProfileSum_mem_of_domainInvariant
    (D := D) hCone nu hInv d1.φ hd (d1.period - 1)

theorem c8Fallback_case2_orbitMap_mem
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (hInv : DomainInvariant nu D)
    (d2 : C8Case2OrbitPartitionData X)
    {d : NProfile V} (hd : d ∈ D) :
    c8Fallback_case2_orbitMap (nu := nu) (R := R) d2 d ∈ D := by
  exact orbitProfileSum_mem_of_domainInvariant
    (D := D) hCone nu hInv d2.φ hd (d2.period - 1)

noncomputable def c8Fallback_case1_blockDomainAt
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hInv : DomainInvariant nu D)
    (d1 : C8Case1OrbitPartitionData X)
    (x0 : X) :
    Domain V :=
  orbitBlockDomain D (balanceRule (D := D) B)
    (c8Fallback_case1_orbitMap (nu := nu) (R := R) d1)
    (by
      intro d hd
      exact c8Fallback_case1_orbitMap_mem
        (nu := nu) (R := R) (D := D) hCone hInv d1 hd)
    (orbitSet d1.φ x0)

noncomputable def c8Fallback_case2_blockDomainAt
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hInv : DomainInvariant nu D)
    (d2 : C8Case2OrbitPartitionData X)
    (x0 : X) :
    Domain V :=
  orbitBlockDomain D (balanceRule (D := D) B)
    (c8Fallback_case2_orbitMap (nu := nu) (R := R) d2)
    (by
      intro d hd
      exact c8Fallback_case2_orbitMap_mem
        (nu := nu) (R := R) (D := D) hCone hInv d2 hd)
    (orbitSet d2.φ x0)

structure C8Case1HullWitnessData
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hInv : DomainInvariant nu D)
    (d1 : C8Case1OrbitPartitionData X) where
  x0 : X
  K : AddSubgroup (ZProfile V)
  Kx0 : AddSubgroup (ZProfile V)
  hHullD : IsDivisibleHull (domainImageZ D) K
  hHullBlock0 :
    IsDivisibleHull
      (domainImageZ
        (c8Fallback_case1_blockDomainAt
          (nu := nu) (R := R) (D := D) hCone B hInv d1 x0))
      Kx0
  hHullEq0 : K = Kx0

structure C8Case2HullWitnessData
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hInv : DomainInvariant nu D)
    (d2 : C8Case2OrbitPartitionData X) where
  x0 : X
  K : AddSubgroup (ZProfile V)
  Kx0 : AddSubgroup (ZProfile V)
  hHullD : IsDivisibleHull (domainImageZ D) K
  hHullBlock0 :
    IsDivisibleHull
      (domainImageZ
        (c8Fallback_case2_blockDomainAt
          (nu := nu) (R := R) (D := D) hCone B hInv d2 x0))
      Kx0
  hHullEq0 : K = Kx0

inductive C8Case1WitnessOrbitType (d1 : C8Case1OrbitPartitionData X) (x0 : X) : Prop where
  | threeOrbit : (d1.φ ^ 3) x0 = x0 → C8Case1WitnessOrbitType d1 x0
  | bigOrbit : x0 ∈ orbitSet d1.φ d1.x → C8Case1WitnessOrbitType d1 x0

inductive C8Case2WitnessOrbitType (d2 : C8Case2OrbitPartitionData X) (x0 : X) : Prop where
  | threeOrbit : (d2.φ ^ 3) x0 = x0 → C8Case2WitnessOrbitType d2 x0
  | bigOrbit : x0 ∈ orbitSet d2.φ d2.x → C8Case2WitnessOrbitType d2 x0

theorem c8Fallback_case1_exists_hullWitness
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (_hSkew : BalanceSkew (B := B))
    (_hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (d1 : C8Case1OrbitPartitionData X) :
    Nonempty
      (C8Case1HullWitnessData
        (nu := nu) (R := R) (D := D) hCone B hInv d1) := by
  obtain ⟨K, hHullD⟩ :
      ∃ K : AddSubgroup (ZProfile V), IsDivisibleHull (domainImageZ D) K :=
    exists_divisibleHull (A := ZProfile V) (S := domainImageZ D)
  choose Kx hHullBlocks using
    (fun x0 : X =>
      exists_divisibleHull
        (A := ZProfile V)
        (S :=
          domainImageZ
            (c8Fallback_case1_blockDomainAt
              (nu := nu) (R := R) (D := D) hCone B hInv d1 x0)))
  have hPeriodPos : 0 < d1.period := by
    rcases d1.hPeriod with h4 | h12
    · simp [h4]
    · simp [h12]
  have hPow : d1.φ ^ ((d1.period - 1) + 1) = 1 := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hPeriodPos)] using d1.hPow
  have hHullBlocksOrbit :
      ∀ x : X,
        IsDivisibleHull
          (domainImageZ
            (orbitBlockDomain D (balanceRule (D := D) B)
              (orbitProfileSum (nu d1.φ) (d1.period - 1))
              (by
                intro d hd
                exact orbitProfileSum_mem_of_domainInvariant
                  (D := D) hCone nu hInv d1.φ hd (d1.period - 1))
              (orbitSet d1.φ x)))
          (Kx x) := by
    intro x
    simpa [c8Fallback_case1_blockDomainAt, c8Fallback_case1_orbitMap] using hHullBlocks x
  rcases exists_orbitSet_hull_eq_of_neutral_balance
      (D := D) (R := R) hCone B hR nu hInv hNeutralB hNE
      d1.φ (d1.period - 1) hPow
      K Kx hHullD hHullBlocksOrbit with
      ⟨x0, hHullEq0⟩
  exact ⟨x0, K, Kx x0, hHullD, hHullBlocks x0, hHullEq0⟩

theorem c8Fallback_case2_exists_hullWitness
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (_hSkew : BalanceSkew (B := B))
    (_hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (d2 : C8Case2OrbitPartitionData X) :
    Nonempty
      (C8Case2HullWitnessData
        (nu := nu) (R := R) (D := D) hCone B hInv d2) := by
  obtain ⟨K, hHullD⟩ :
      ∃ K : AddSubgroup (ZProfile V), IsDivisibleHull (domainImageZ D) K :=
    exists_divisibleHull (A := ZProfile V) (S := domainImageZ D)
  choose Kx hHullBlocks using
    (fun x0 : X =>
      exists_divisibleHull
        (A := ZProfile V)
        (S :=
          domainImageZ
            (c8Fallback_case2_blockDomainAt
              (nu := nu) (R := R) (D := D) hCone B hInv d2 x0)))
  have hPeriodPos : 0 < d2.period := by
    rcases d2.hPeriod with h5 | h15
    · simp [h5]
    · simp [h15]
  have hPow : d2.φ ^ ((d2.period - 1) + 1) = 1 := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hPeriodPos)] using d2.hPow
  have hHullBlocksOrbit :
      ∀ x : X,
        IsDivisibleHull
          (domainImageZ
            (orbitBlockDomain D (balanceRule (D := D) B)
              (orbitProfileSum (nu d2.φ) (d2.period - 1))
              (by
                intro d hd
                exact orbitProfileSum_mem_of_domainInvariant
                  (D := D) hCone nu hInv d2.φ hd (d2.period - 1))
              (orbitSet d2.φ x)))
          (Kx x) := by
    intro x
    simpa [c8Fallback_case2_blockDomainAt, c8Fallback_case2_orbitMap] using hHullBlocks x
  rcases exists_orbitSet_hull_eq_of_neutral_balance
      (D := D) (R := R) hCone B hR nu hInv hNeutralB hNE
      d2.φ (d2.period - 1) hPow
      K Kx hHullD hHullBlocksOrbit with
      ⟨x0, hHullEq0⟩
  exact ⟨x0, K, Kx x0, hHullD, hHullBlocks x0, hHullEq0⟩

theorem c8Fallback_case1_classify_witnessOrbit
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hInv : DomainInvariant nu D)
    (d1 : C8Case1OrbitPartitionData X)
    (w : C8Case1HullWitnessData
      (nu := nu) (R := R) (D := D) hCone B hInv d1) :
    C8Case1WitnessOrbitType d1 w.x0 := by
  rcases d1.hClassify w.x0 with hthree | hbig
  · exact C8Case1WitnessOrbitType.threeOrbit hthree
  · exact C8Case1WitnessOrbitType.bigOrbit hbig

theorem c8Fallback_case2_classify_witnessOrbit
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hInv : DomainInvariant nu D)
    (d2 : C8Case2OrbitPartitionData X)
    (w : C8Case2HullWitnessData
      (nu := nu) (R := R) (D := D) hCone B hInv d2) :
    C8Case2WitnessOrbitType d2 w.x0 := by
  rcases d2.hClassify w.x0 with hthree | hbig
  · exact C8Case2WitnessOrbitType.threeOrbit hthree
  · exact C8Case2WitnessOrbitType.bigOrbit hbig

theorem c8Fallback_case1_cycleSum_of_threeOrbitWitness
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (_hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (_hR : Reinforcement D (balanceRule (D := D) B))
    (_hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (d1 : C8Case1OrbitPartitionData X)
    (w : C8Case1HullWitnessData
      (nu := nu) (R := R) (D := D) hCone B hInv d1)
    (hthree : (d1.φ ^ 3) w.x0 = w.x0) :
    C8CycleSumHypothesis (D := D) (B := B) := by
  let x : X := w.x0
  let z : X := d1.φ x
  let y : X := (d1.φ ^ 2) x
  have hzx : z ≠ x := by
    dsimp [z, x]
    simpa using d1.hNoFix w.x0
  have hxy : x ≠ y := by
    intro hxy'
    have hfix : d1.φ x = x := by
      calc
        d1.φ x = d1.φ ((d1.φ ^ 2) x) := by simpa [x, y] using congrArg d1.φ hxy'
        _ = (d1.φ ^ 3) x := by simp [pow_succ']
        _ = x := by simpa [x] using hthree
    exact d1.hNoFix x hfix
  have hyz : y ≠ z := by
    intro hyz'
    have hfix : d1.φ x = x := by
      have hEq2 : (d1.φ ^ 2) x = d1.φ x := by simpa [x, y, z] using hyz'
      have hEq3 : d1.φ (d1.φ x) = d1.φ x := by simpa [pow_succ'] using hEq2
      exact d1.φ.injective hEq3
    exact d1.hNoFix x hfix
  have hφx : d1.φ x = z := by
    rfl
  have hφz : d1.φ z = y := by
    simp [z, y, pow_succ']
  have hφy : d1.φ y = x := by
    simpa [x, y, pow_succ'] using hthree
  have hPeriodPos : 0 < d1.period := by
    rcases d1.hPeriod with h4 | h12
    · simp [h4]
    · simp [h12]
  have hThreeDivPeriod : 3 ∣ d1.period := by
    rcases d1.hPeriod with h4 | h12
    · exfalso
      have hpow4 : d1.φ ^ 4 = 1 := by
        simpa [h4] using d1.hPow
      have hpow4x : (d1.φ ^ 4) x = x := by
        simpa [x] using congrArg (fun q : Equiv.Perm X => q x) hpow4
      have hpow4_from_three : (d1.φ ^ 4) x = d1.φ x := by
        simpa [x, pow_succ'] using congrArg d1.φ hthree
      have hfix : d1.φ x = x := by
        calc
          d1.φ x = (d1.φ ^ 4) x := by simpa using hpow4_from_three.symm
          _ = x := hpow4x
      exact d1.hNoFix x hfix
    · simp [h12]
  have hThreeDiv : 3 ∣ (d1.period - 1) + 1 := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hPeriodPos)] using hThreeDivPeriod
  have horbit :
      ∀ {d : NProfile V}, d ∈ D → orbitProfileSum (nu d1.φ) (d1.period - 1) d ∈ D := by
    intro d hd
    exact orbitProfileSum_mem_of_domainInvariant
      (D := D) hCone nu hInv d1.φ hd (d1.period - 1)
  have hHullBlock :
      IsDivisibleHull
        (domainImageZ
          (orbitBlockDomain D (balanceRule (D := D) B)
            (orbitProfileSum (nu d1.φ) (d1.period - 1)) horbit (orbitSet d1.φ x)))
        w.Kx0 := by
    simpa [x, c8Fallback_case1_blockDomainAt, c8Fallback_case1_orbitMap, horbit] using
      w.hHullBlock0
  exact cycleSumHypothesis_of_threeCycle_orbitBlock_hullEq
    (D := D) (B := B) hSkew nu hNeutralB d1.φ
    (M := d1.period - 1) hThreeDiv horbit
    hxy hyz hzx hφx hφy hφz
    w.K w.Kx0 w.hHullD hHullBlock w.hHullEq0

theorem c8Fallback_case2_cycleSum_of_threeOrbitWitness
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (_hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (_hR : Reinforcement D (balanceRule (D := D) B))
    (_hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (d2 : C8Case2OrbitPartitionData X)
    (w : C8Case2HullWitnessData
      (nu := nu) (R := R) (D := D) hCone B hInv d2)
    (hthree : (d2.φ ^ 3) w.x0 = w.x0) :
    C8CycleSumHypothesis (D := D) (B := B) := by
  let x : X := w.x0
  let z : X := d2.φ x
  let y : X := (d2.φ ^ 2) x
  have hzx : z ≠ x := by
    dsimp [z, x]
    simpa using d2.hNoFix w.x0
  have hxy : x ≠ y := by
    intro hxy'
    have hfix : d2.φ x = x := by
      calc
        d2.φ x = d2.φ ((d2.φ ^ 2) x) := by simpa [x, y] using congrArg d2.φ hxy'
        _ = (d2.φ ^ 3) x := by simp [pow_succ']
        _ = x := by simpa [x] using hthree
    exact d2.hNoFix x hfix
  have hyz : y ≠ z := by
    intro hyz'
    have hfix : d2.φ x = x := by
      have hEq2 : (d2.φ ^ 2) x = d2.φ x := by simpa [x, y, z] using hyz'
      have hEq3 : d2.φ (d2.φ x) = d2.φ x := by simpa [pow_succ'] using hEq2
      exact d2.φ.injective hEq3
    exact d2.hNoFix x hfix
  have hφx : d2.φ x = z := by
    rfl
  have hφz : d2.φ z = y := by
    simp [z, y, pow_succ']
  have hφy : d2.φ y = x := by
    simpa [x, y, pow_succ'] using hthree
  have hPeriodPos : 0 < d2.period := by
    rcases d2.hPeriod with h5 | h15
    · simp [h5]
    · simp [h15]
  have hThreeDivPeriod : 3 ∣ d2.period := by
    rcases d2.hPeriod with h5 | h15
    · exfalso
      have hpow5 : d2.φ ^ 5 = 1 := by
        simpa [h5] using d2.hPow
      have hpow5x : (d2.φ ^ 5) x = x := by
        simpa [x] using congrArg (fun q : Equiv.Perm X => q x) hpow5
      have hpow4_from_three : (d2.φ ^ 4) x = d2.φ x := by
        simpa [x, pow_succ'] using congrArg d2.φ hthree
      have hpow5_from_three : (d2.φ ^ 5) x = (d2.φ ^ 2) x := by
        simpa [pow_succ'] using congrArg d2.φ hpow4_from_three
      have hxy' : x = (d2.φ ^ 2) x := by
        calc
          x = (d2.φ ^ 5) x := hpow5x.symm
          _ = (d2.φ ^ 2) x := hpow5_from_three
      have hfix : d2.φ x = x := by
        calc
          d2.φ x = d2.φ ((d2.φ ^ 2) x) := by simpa [x] using congrArg d2.φ hxy'
          _ = (d2.φ ^ 3) x := by simp [pow_succ']
          _ = x := by simpa [x] using hthree
      exact d2.hNoFix x hfix
    · simp [h15]
  have hThreeDiv : 3 ∣ (d2.period - 1) + 1 := by
    simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hPeriodPos)] using hThreeDivPeriod
  have horbit :
      ∀ {d : NProfile V}, d ∈ D → orbitProfileSum (nu d2.φ) (d2.period - 1) d ∈ D := by
    intro d hd
    exact orbitProfileSum_mem_of_domainInvariant
      (D := D) hCone nu hInv d2.φ hd (d2.period - 1)
  have hHullBlock :
      IsDivisibleHull
        (domainImageZ
          (orbitBlockDomain D (balanceRule (D := D) B)
            (orbitProfileSum (nu d2.φ) (d2.period - 1)) horbit (orbitSet d2.φ x)))
        w.Kx0 := by
    simpa [x, c8Fallback_case2_blockDomainAt, c8Fallback_case2_orbitMap, horbit] using
      w.hHullBlock0
  exact cycleSumHypothesis_of_threeCycle_orbitBlock_hullEq
    (D := D) (B := B) hSkew nu hNeutralB d2.φ
    (M := d2.period - 1) hThreeDiv horbit
    hxy hyz hzx hφx hφy hφz
    w.K w.Kx0 w.hHullD hHullBlock w.hHullEq0

lemma c8Fallback_eq_zero_of_triple_sum_eq_zero
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {a : R}
    (h : a + a + a = 0) :
    a = 0 := by
  have hle : a ≤ 0 := by
    by_contra hnot
    have hpos : 0 < a := lt_of_not_ge hnot
    have hpos3 : 0 < a + a + a := add_pos (add_pos hpos hpos) hpos
    have hnotPos : ¬ 0 < a + a + a := by simp [h]
    exact hnotPos hpos3
  have hge : 0 ≤ a := by
    by_contra hnot
    have hneg : a < 0 := lt_of_not_ge hnot
    have hneg3 : a + a + a < 0 := add_neg (add_neg hneg hneg) hneg
    have hnotNeg : ¬ a + a + a < 0 := by simp [h]
    exact hnotNeg hneg3
  exact le_antisymm hle hge

lemma c8Fallback_pow8_fix_of_pow4_fix
    (φ : Equiv.Perm X) {x : X}
    (hpow4 : (φ ^ 4) x = x) :
    (φ ^ 8) x = x := by
  have h8 : (8 : ℕ) = 4 * 2 := by decide
  have hpowMul : φ ^ (4 * 2) = (φ ^ 4) ^ 2 :=
    pow_mul φ 4 2
  calc
    (φ ^ 8) x = (φ ^ (4 * 2)) x := by simp [h8]
    _ = ((φ ^ 4) ^ 2) x := by simp [hpowMul]
    _ = (φ ^ 4) ((φ ^ 4) x) := rfl
    _ = (φ ^ 4) x := by simp [hpow4]
    _ = x := hpow4

lemma c8Fallback_pow10_fix_of_pow5_fix
    (φ : Equiv.Perm X) {x : X}
    (hpow5 : (φ ^ 5) x = x) :
    (φ ^ 10) x = x := by
  have h10 : (10 : ℕ) = 5 * 2 := by decide
  have hpowMul : φ ^ (5 * 2) = (φ ^ 5) ^ 2 :=
    pow_mul φ 5 2
  calc
    (φ ^ 10) x = (φ ^ (5 * 2)) x := by simp [h10]
    _ = ((φ ^ 5) ^ 2) x := by simp [hpowMul]
    _ = (φ ^ 5) ((φ ^ 5) x) := rfl
    _ = (φ ^ 5) x := by simp [hpow5]
    _ = x := hpow5

lemma c8Fallback_balanceAt_fixed_of_pow_fix
    [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (B : BalanceSystem R X V)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (φ : Equiv.Perm X) (n : ℕ) (a b : X) (d : NProfile V)
    (hpa : (φ ^ n) a = a) (hpb : (φ ^ n) b = b) :
    balanceAt B a b (permuteNProfile ((nu φ) ^ n) d) = balanceAt B a b d := by
  simpa [MonoidHom.map_pow, hpa, hpb] using
    (balanceAt_permute_of_balanceNeutral
      (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B)
      hNeutralB (φ ^ n) a b d)

lemma c8Fallback_evalNat_weight_sum4
    [AddCommMonoid R] [DecidableEq V]
    (w1 w2 w3 w4 : V → R) (d : NProfile V) :
    evalNat (fun v => w1 v + w2 v + w3 v + w4 v) d =
      evalNat w1 d + evalNat w2 d + evalNat w3 d + evalNat w4 d := by
  unfold evalNat
  simp [Finsupp.sum, Finset.sum_add_distrib, add_assoc, add_comm, add_left_comm]

lemma c8Fallback_evalNat_weight_sum5
    [AddCommMonoid R] [DecidableEq V]
    (w1 w2 w3 w4 w5 : V → R) (d : NProfile V) :
    evalNat (fun v => w1 v + w2 v + w3 v + w4 v + w5 v) d =
      evalNat w1 d + evalNat w2 d + evalNat w3 d + evalNat w4 d + evalNat w5 d := by
  unfold evalNat
  simp [Finsupp.sum, Finset.sum_add_distrib, add_assoc, add_comm, add_left_comm]

lemma c8Fallback_evalIntHom_toZProfile_eq4
    [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (B : BalanceSystem R X V)
    (x y z w : X) (d : NProfile V) :
    evalIntHom (fun v => B.bal x y v + B.bal y z v + B.bal z w v + B.bal w x v)
        (toZProfile d) =
      balanceAt B x y d + balanceAt B y z d + balanceAt B z w d + balanceAt B w x d := by
  calc
    evalIntHom (fun v => B.bal x y v + B.bal y z v + B.bal z w v + B.bal w x v)
        (toZProfile d)
        = evalNat (fun v => B.bal x y v + B.bal y z v + B.bal z w v + B.bal w x v) d := by
            simpa using
              (evalIntHom_toZProfile
                (w := fun v =>
                  B.bal x y v + B.bal y z v + B.bal z w v + B.bal w x v)
                d)
    _ = evalNat (B.bal x y) d + evalNat (B.bal y z) d +
          evalNat (B.bal z w) d + evalNat (B.bal w x) d := by
          simpa [add_assoc, add_comm, add_left_comm] using
            (c8Fallback_evalNat_weight_sum4
              (w1 := B.bal x y) (w2 := B.bal y z) (w3 := B.bal z w) (w4 := B.bal w x) d)
    _ = balanceAt B x y d + balanceAt B y z d + balanceAt B z w d + balanceAt B w x d := by
          rfl

lemma c8Fallback_evalIntHom_toZProfile_eq5
    [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (B : BalanceSystem R X V)
    (x y z u v : X) (d : NProfile V) :
    evalIntHom (fun t => B.bal x y t + B.bal y z t + B.bal z u t + B.bal u v t + B.bal v x t)
        (toZProfile d) =
      balanceAt B x y d + balanceAt B y z d + balanceAt B z u d +
        balanceAt B u v d + balanceAt B v x d := by
  calc
    evalIntHom (fun t => B.bal x y t + B.bal y z t + B.bal z u t + B.bal u v t + B.bal v x t)
        (toZProfile d)
        = evalNat (fun t => B.bal x y t + B.bal y z t + B.bal z u t + B.bal u v t + B.bal v x t) d := by
            simpa using
              (evalIntHom_toZProfile
                (w := fun t =>
                  B.bal x y t + B.bal y z t + B.bal z u t + B.bal u v t + B.bal v x t)
                d)
    _ = evalNat (B.bal x y) d + evalNat (B.bal y z) d + evalNat (B.bal z u) d +
          evalNat (B.bal u v) d + evalNat (B.bal v x) d := by
          simpa [add_assoc, add_comm, add_left_comm] using
            (c8Fallback_evalNat_weight_sum5
              (w1 := B.bal x y) (w2 := B.bal y z) (w3 := B.bal z u) (w4 := B.bal u v)
              (w5 := B.bal v x) d)
    _ = balanceAt B x y d + balanceAt B y z d + balanceAt B z u d +
          balanceAt B u v d + balanceAt B v x d := by
          rfl

lemma c8Fallback_permute_pow_comm
    (π : Equiv.Perm V) (n m : ℕ) (d : NProfile V) :
    permuteNProfile (π ^ n) (permuteNProfile (π ^ m) d) =
      permuteNProfile (π ^ m) (permuteNProfile (π ^ n) d) := by
  calc
    permuteNProfile (π ^ n) (permuteNProfile (π ^ m) d)
        = permuteNProfile ((π ^ n) * (π ^ m)) d := by
            simp [permuteNProfile_mul]
    _ = permuteNProfile (π ^ (n + m)) d := by
          simp [pow_add]
    _ = permuteNProfile (π ^ (m + n)) d := by
          simp [Nat.add_comm]
    _ = permuteNProfile ((π ^ m) * (π ^ n)) d := by
          simp [pow_add]
    _ = permuteNProfile (π ^ m) (permuteNProfile (π ^ n) d) := by
          simp [permuteNProfile_mul]

lemma c8Fallback_orbitProfileSum11_split
    (π : Equiv.Perm V) (d : NProfile V) :
    orbitProfileSum π 11 d =
      orbitProfileSum π 3 d +
      orbitProfileSum π 3 (permuteNProfile (π ^ 4) d) +
      orbitProfileSum π 3 (permuteNProfile (π ^ 8) d) := by
  unfold orbitProfileSum
  let f : ℕ → NProfile V := fun k => permuteNProfile (π ^ k) d
  have h12eq : (12 : ℕ) = 4 + 8 := by decide
  have h12 :
      Finset.sum (Finset.range 12) f =
        Finset.sum (Finset.range 4) f +
          Finset.sum (Finset.range 4) (fun k => f (4 + k)) +
            Finset.sum (Finset.range 4) (fun k => f (8 + k)) := by
    calc
      Finset.sum (Finset.range 12) f
          = Finset.sum (Finset.range (4 + 8)) f := by simp [h12eq]
      _ = Finset.sum (Finset.range 4) f + Finset.sum (Finset.range 8) (fun k => f (4 + k)) := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (Finset.sum_range_add f 4 8)
      _ = Finset.sum (Finset.range 4) f +
            (Finset.sum (Finset.range 4) (fun k => f (4 + k)) +
              Finset.sum (Finset.range 4) (fun k => f (8 + k))) := by
            congr 1
            simpa [← Nat.add_assoc] using
              (Finset.sum_range_add (fun k => f (4 + k)) 4 4)
      _ = Finset.sum (Finset.range 4) f +
            Finset.sum (Finset.range 4) (fun k => f (4 + k)) +
              Finset.sum (Finset.range 4) (fun k => f (8 + k)) := by
            abel_nf
  have h4 : Finset.sum (Finset.range 4) f = orbitProfileSum π 3 d := by
    simp [f, orbitProfileSum]
  have h4shift :
      Finset.sum (Finset.range 4) (fun k => f (4 + k)) =
        orbitProfileSum π 3 (permuteNProfile (π ^ 4) d) := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [f]
    calc
      permuteNProfile (π ^ (4 + k)) d
          = permuteNProfile (π ^ 4) (permuteNProfile (π ^ k) d) := by
              simp [pow_add, permuteNProfile_mul]
      _ = permuteNProfile (π ^ k) (permuteNProfile (π ^ 4) d) :=
            c8Fallback_permute_pow_comm (π := π) 4 k d
  have h8shift :
      Finset.sum (Finset.range 4) (fun k => f (8 + k)) =
        orbitProfileSum π 3 (permuteNProfile (π ^ 8) d) := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [f]
    calc
      permuteNProfile (π ^ (8 + k)) d
          = permuteNProfile (π ^ 8) (permuteNProfile (π ^ k) d) := by
              simp [pow_add, permuteNProfile_mul]
      _ = permuteNProfile (π ^ k) (permuteNProfile (π ^ 8) d) :=
            c8Fallback_permute_pow_comm (π := π) 8 k d
  calc
    Finset.sum (Finset.range 12) f
        = Finset.sum (Finset.range 4) f +
            Finset.sum (Finset.range 4) (fun k => f (4 + k)) +
              Finset.sum (Finset.range 4) (fun k => f (8 + k)) := h12
    _ = orbitProfileSum π 3 d +
          orbitProfileSum π 3 (permuteNProfile (π ^ 4) d) +
            orbitProfileSum π 3 (permuteNProfile (π ^ 8) d) := by
          simp [h4, h4shift, h8shift]

lemma c8Fallback_orbitProfileSum14_split
    (π : Equiv.Perm V) (d : NProfile V) :
    orbitProfileSum π 14 d =
      orbitProfileSum π 4 d +
      orbitProfileSum π 4 (permuteNProfile (π ^ 5) d) +
      orbitProfileSum π 4 (permuteNProfile (π ^ 10) d) := by
  unfold orbitProfileSum
  let f : ℕ → NProfile V := fun k => permuteNProfile (π ^ k) d
  have h15eq : (15 : ℕ) = 5 + 10 := by decide
  have h15 :
      Finset.sum (Finset.range 15) f =
        Finset.sum (Finset.range 5) f +
          Finset.sum (Finset.range 5) (fun k => f (5 + k)) +
            Finset.sum (Finset.range 5) (fun k => f (10 + k)) := by
    calc
      Finset.sum (Finset.range 15) f
          = Finset.sum (Finset.range (5 + 10)) f := by simp [h15eq]
      _ = Finset.sum (Finset.range 5) f + Finset.sum (Finset.range 10) (fun k => f (5 + k)) := by
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
              (Finset.sum_range_add f 5 10)
      _ = Finset.sum (Finset.range 5) f +
            (Finset.sum (Finset.range 5) (fun k => f (5 + k)) +
              Finset.sum (Finset.range 5) (fun k => f (10 + k))) := by
            congr 1
            simpa [← Nat.add_assoc] using
              (Finset.sum_range_add (fun k => f (5 + k)) 5 5)
      _ = Finset.sum (Finset.range 5) f +
            Finset.sum (Finset.range 5) (fun k => f (5 + k)) +
              Finset.sum (Finset.range 5) (fun k => f (10 + k)) := by
            abel_nf
  have h5 : Finset.sum (Finset.range 5) f = orbitProfileSum π 4 d := by
    simp [f, orbitProfileSum]
  have h5shift :
      Finset.sum (Finset.range 5) (fun k => f (5 + k)) =
        orbitProfileSum π 4 (permuteNProfile (π ^ 5) d) := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [f]
    calc
      permuteNProfile (π ^ (5 + k)) d
          = permuteNProfile (π ^ 5) (permuteNProfile (π ^ k) d) := by
              simp [pow_add, permuteNProfile_mul]
      _ = permuteNProfile (π ^ k) (permuteNProfile (π ^ 5) d) :=
            c8Fallback_permute_pow_comm (π := π) 5 k d
  have h10shift :
      Finset.sum (Finset.range 5) (fun k => f (10 + k)) =
        orbitProfileSum π 4 (permuteNProfile (π ^ 10) d) := by
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [f]
    calc
      permuteNProfile (π ^ (10 + k)) d
          = permuteNProfile (π ^ 10) (permuteNProfile (π ^ k) d) := by
              simp [pow_add, permuteNProfile_mul]
      _ = permuteNProfile (π ^ k) (permuteNProfile (π ^ 10) d) :=
            c8Fallback_permute_pow_comm (π := π) 10 k d
  calc
    Finset.sum (Finset.range 15) f
        = Finset.sum (Finset.range 5) f +
            Finset.sum (Finset.range 5) (fun k => f (5 + k)) +
              Finset.sum (Finset.range 5) (fun k => f (10 + k)) := h15
    _ = orbitProfileSum π 4 d +
          orbitProfileSum π 4 (permuteNProfile (π ^ 5) d) +
            orbitProfileSum π 4 (permuteNProfile (π ^ 10) d) := by
          simp [h5, h5shift, h10shift]

lemma c8Fallback_eq4_transport
    [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hInv : DomainInvariant nu D)
    (B : BalanceSystem R X V)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    {x y z w : X}
    (hEq :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y z d +
          balanceAt B z w d + balanceAt B w x d = 0)
    (g : Equiv.Perm X) :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B (g x) (g y) d + balanceAt B (g y) (g z) d +
        balanceAt B (g z) (g w) d + balanceAt B (g w) (g x) d = 0 := by
  intro d hd
  have hd' : permuteNProfile (nu g.symm) d ∈ D := hInv g.symm hd
  have h0 := hEq hd'
  have hxy :
      balanceAt B x y (permuteNProfile (nu g.symm) d) =
        balanceAt B (g x) (g y) d := by
    simpa [MonoidHom.id_apply] using
      (balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B)
        hNeutralB g.symm (g x) (g y) d)
  have hyz :
      balanceAt B y z (permuteNProfile (nu g.symm) d) =
        balanceAt B (g y) (g z) d := by
    simpa [MonoidHom.id_apply] using
      (balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B)
        hNeutralB g.symm (g y) (g z) d)
  have hzw :
      balanceAt B z w (permuteNProfile (nu g.symm) d) =
        balanceAt B (g z) (g w) d := by
    simpa [MonoidHom.id_apply] using
      (balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B)
        hNeutralB g.symm (g z) (g w) d)
  have hwx :
      balanceAt B w x (permuteNProfile (nu g.symm) d) =
        balanceAt B (g w) (g x) d := by
    simpa [MonoidHom.id_apply] using
      (balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B)
        hNeutralB g.symm (g w) (g x) d)
  simpa [hxy, hyz, hzw, hwx, add_assoc, add_comm, add_left_comm] using h0

lemma c8Fallback_eq5_transport
    [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hInv : DomainInvariant nu D)
    (B : BalanceSystem R X V)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    {x y z u v : X}
    (hEq :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y z d + balanceAt B z u d +
          balanceAt B u v d + balanceAt B v x d = 0)
    (g : Equiv.Perm X) :
    ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B (g x) (g y) d + balanceAt B (g y) (g z) d +
        balanceAt B (g z) (g u) d + balanceAt B (g u) (g v) d +
          balanceAt B (g v) (g x) d = 0 := by
  intro d hd
  have hd' : permuteNProfile (nu g.symm) d ∈ D := hInv g.symm hd
  have h0 := hEq hd'
  have hxy :
      balanceAt B x y (permuteNProfile (nu g.symm) d) =
        balanceAt B (g x) (g y) d := by
    simpa [MonoidHom.id_apply] using
      (balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B)
        hNeutralB g.symm (g x) (g y) d)
  have hyz :
      balanceAt B y z (permuteNProfile (nu g.symm) d) =
        balanceAt B (g y) (g z) d := by
    simpa [MonoidHom.id_apply] using
      (balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B)
        hNeutralB g.symm (g y) (g z) d)
  have hzu :
      balanceAt B z u (permuteNProfile (nu g.symm) d) =
        balanceAt B (g z) (g u) d := by
    simpa [MonoidHom.id_apply] using
      (balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B)
        hNeutralB g.symm (g z) (g u) d)
  have huv :
      balanceAt B u v (permuteNProfile (nu g.symm) d) =
        balanceAt B (g u) (g v) d := by
    simpa [MonoidHom.id_apply] using
      (balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B)
        hNeutralB g.symm (g u) (g v) d)
  have hvx :
      balanceAt B v x (permuteNProfile (nu g.symm) d) =
        balanceAt B (g v) (g x) d := by
    simpa [MonoidHom.id_apply] using
      (balanceAt_permute_of_balanceNeutral
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B)
        hNeutralB g.symm (g v) (g x) d)
  simpa [hxy, hyz, hzu, huv, hvx, add_assoc, add_comm, add_left_comm] using h0

lemma c8Fallback_cycle4_pair_average
    [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (B : BalanceSystem R X V)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (φ : Equiv.Perm X)
    (x y z w : X)
    (hφx : φ x = y) (hφy : φ y = z) (hφz : φ z = w) (hφw : φ w = x)
    (d : NProfile V) :
    balanceAt B x y (orbitProfileSum (nu φ) 3 d) =
      balanceAt B x y d + balanceAt B y z d +
        balanceAt B z w d + balanceAt B w x d := by
  have h1raw :=
    balanceAt_permute_of_balanceNeutral
      (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B)
      hNeutralB φ w x d
  have h1 :
      balanceAt B x y (permuteNProfile (nu φ) d) = balanceAt B w x d := by
    simpa [hφx, hφw] using h1raw
  have hpow2z : (φ ^ 2) z = x := by
    calc
      (φ ^ 2) z = φ (φ z) := by simp [pow_succ']
      _ = φ w := by simp [hφz]
      _ = x := hφw
  have hpow2w : (φ ^ 2) w = y := by
    calc
      (φ ^ 2) w = φ (φ w) := by simp [pow_succ']
      _ = φ x := by simp [hφw]
      _ = y := hφx
  have h2raw :=
    balanceAt_permute_of_balanceNeutral
      (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B)
      hNeutralB (φ ^ 2) z w d
  have h2 :
      balanceAt B x y (permuteNProfile ((nu φ) ^ 2) d) = balanceAt B z w d := by
    simpa [hpow2z, hpow2w, MonoidHom.map_pow] using h2raw
  have hpow3y : (φ ^ 3) y = x := by
    calc
      (φ ^ 3) y = φ ((φ ^ 2) y) := by simp [pow_succ']
      _ = φ (φ (φ y)) := by simp [pow_succ']
      _ = φ (φ z) := by simp [hφy]
      _ = φ w := by simp [hφz]
      _ = x := hφw
  have hpow3z : (φ ^ 3) z = y := by
    calc
      (φ ^ 3) z = φ ((φ ^ 2) z) := by simp [pow_succ']
      _ = φ x := by simp [hpow2z]
      _ = y := hφx
  have h3raw :=
    balanceAt_permute_of_balanceNeutral
      (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B)
      hNeutralB (φ ^ 3) y z d
  have h3 :
      balanceAt B x y (permuteNProfile ((nu φ) ^ 3) d) = balanceAt B y z d := by
    simpa [hpow3y, hpow3z, MonoidHom.map_pow] using h3raw
  unfold orbitProfileSum
  simp [Finset.sum_range_succ, balanceAt_add, h1, h2, h3, add_assoc, add_comm, add_left_comm]

lemma c8Fallback_cycle5_pair_average
    [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (B : BalanceSystem R X V)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (φ : Equiv.Perm X)
    (x y z u v : X)
    (hφx : φ x = y) (hφy : φ y = z) (hφz : φ z = u)
    (hφu : φ u = v) (hφv : φ v = x)
    (d : NProfile V) :
    balanceAt B x y (orbitProfileSum (nu φ) 4 d) =
      balanceAt B x y d + balanceAt B y z d + balanceAt B z u d +
        balanceAt B u v d + balanceAt B v x d := by
  have h1raw :=
    balanceAt_permute_of_balanceNeutral
      (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B)
      hNeutralB φ v x d
  have h1 :
      balanceAt B x y (permuteNProfile (nu φ) d) = balanceAt B v x d := by
    simpa [hφx, hφv] using h1raw
  have hpow2u : (φ ^ 2) u = x := by
    simp [pow_succ', hφu, hφv]
  have hpow2v : (φ ^ 2) v = y := by
    simp [pow_succ', hφv, hφx]
  have h2raw :=
    balanceAt_permute_of_balanceNeutral
      (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B)
      hNeutralB (φ ^ 2) u v d
  have h2 :
      balanceAt B x y (permuteNProfile ((nu φ) ^ 2) d) = balanceAt B u v d := by
    simpa [hpow2u, hpow2v, MonoidHom.map_pow] using h2raw
  have hpow3z : (φ ^ 3) z = x := by
    simp [pow_succ', hφz, hφu, hφv]
  have hpow3u : (φ ^ 3) u = y := by
    simp [pow_succ', hφu, hφv, hφx]
  have h3raw :=
    balanceAt_permute_of_balanceNeutral
      (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B)
      hNeutralB (φ ^ 3) z u d
  have h3 :
      balanceAt B x y (permuteNProfile ((nu φ) ^ 3) d) = balanceAt B z u d := by
    simpa [hpow3z, hpow3u, MonoidHom.map_pow] using h3raw
  have hpow4y : (φ ^ 4) y = x := by
    simp [pow_succ', hφy, hφz, hφu, hφv]
  have hpow4z : (φ ^ 4) z = y := by
    simp [pow_succ', hφz, hφu, hφv, hφx]
  have h4raw :=
    balanceAt_permute_of_balanceNeutral
      (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (B := B)
      hNeutralB (φ ^ 4) y z d
  have h4 :
      balanceAt B x y (permuteNProfile ((nu φ) ^ 4) d) = balanceAt B y z d := by
    simpa [hpow4y, hpow4z, MonoidHom.map_pow] using h4raw
  unfold orbitProfileSum
  simp [Finset.sum_range_succ, balanceAt_add, h1, h2, h3, h4, add_assoc, add_comm, add_left_comm]

theorem c8Fallback_case1_equationPack4_of_bigOrbitWitness
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (_hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (_hR : Reinforcement D (balanceRule (D := D) B))
    (_hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (d1 : C8Case1OrbitPartitionData X)
    (w : C8Case1HullWitnessData
      (nu := nu) (R := R) (D := D) hCone B hInv d1)
    (hbig : w.x0 ∈ orbitSet d1.φ d1.x) :
    Nonempty (C8FallbackEquationPack4 (D := D) (B := B)) := by
  rcases hbig with ⟨k, hk⟩
  let x : X := w.x0
  let y : X := d1.φ x
  let z : X := d1.φ y
  let s : X := d1.φ z
  have hxk : x = (d1.φ ^ k) d1.x := by
    simpa [x] using hk.symm
  have hyk : y = (d1.φ ^ k) d1.y := by
    calc
      y = d1.φ x := rfl
      _ = d1.φ ((d1.φ ^ k) d1.x) := by simpa [x] using congrArg d1.φ hk.symm
      _ = (d1.φ ^ (k + 1)) d1.x := by simp [pow_succ']
      _ = (d1.φ ^ k) (d1.φ d1.x) := by simp [pow_succ]
      _ = (d1.φ ^ k) d1.y := by simp [d1.hφx]
  have hzk : z = (d1.φ ^ k) d1.z := by
    calc
      z = d1.φ y := rfl
      _ = d1.φ ((d1.φ ^ k) d1.y) := by simpa [y] using congrArg d1.φ hyk
      _ = (d1.φ ^ (k + 1)) d1.y := by simp [pow_succ']
      _ = (d1.φ ^ k) (d1.φ d1.y) := by simp [pow_succ]
      _ = (d1.φ ^ k) d1.z := by simp [d1.hφy]
  have hsk : s = (d1.φ ^ k) d1.w := by
    calc
      s = d1.φ z := rfl
      _ = d1.φ ((d1.φ ^ k) d1.z) := by simpa [z] using congrArg d1.φ hzk
      _ = (d1.φ ^ (k + 1)) d1.z := by simp [pow_succ']
      _ = (d1.φ ^ k) (d1.φ d1.z) := by simp [pow_succ]
      _ = (d1.φ ^ k) d1.w := by simp [d1.hφz]
  have hφx : d1.φ x = y := by rfl
  have hφy : d1.φ y = z := by rfl
  have hφz : d1.φ z = s := by rfl
  have hφs : d1.φ s = x := by
    calc
      d1.φ s = d1.φ ((d1.φ ^ k) d1.w) := by simpa [s] using congrArg d1.φ hsk
      _ = (d1.φ ^ (k + 1)) d1.w := by simp [pow_succ']
      _ = (d1.φ ^ k) (d1.φ d1.w) := by simp [pow_succ]
      _ = (d1.φ ^ k) d1.x := by simp [d1.hφw]
      _ = x := by simpa [x] using hk
  have hxy : x ≠ y := by
    intro hxy'
    have hxyk : (d1.φ ^ k) d1.x = (d1.φ ^ k) d1.y := by
      simpa [hxk, hyk] using hxy'
    exact d1.hxy ((d1.φ ^ k).injective hxyk)
  have hyz : y ≠ z := by
    intro hyz'
    have hyzk : (d1.φ ^ k) d1.y = (d1.φ ^ k) d1.z := by
      simpa [hyk, hzk] using hyz'
    exact d1.hyz ((d1.φ ^ k).injective hyzk)
  have hzx : z ≠ x := by
    intro hzx'
    have hzxk : (d1.φ ^ k) d1.z = (d1.φ ^ k) d1.x := by
      simpa [hzk, hxk] using hzx'
    exact d1.hzx ((d1.φ ^ k).injective hzxk)
  have hzw : z ≠ s := by
    intro hzw'
    have hzwk : (d1.φ ^ k) d1.z = (d1.φ ^ k) d1.w := by
      simpa [hzk, hsk] using hzw'
    exact d1.hzw ((d1.φ ^ k).injective hzwk)
  have hsx : s ≠ x := by
    intro hsx'
    have hsxk : (d1.φ ^ k) d1.w = (d1.φ ^ k) d1.x := by
      simpa [hsk, hxk] using hsx'
    exact d1.hwx ((d1.φ ^ k).injective hsxk)
  have hyw0 : d1.y ≠ d1.w := by
    intro hyw0
    have hxz0 : d1.x = d1.z := by
      apply d1.φ.injective
      calc
        d1.φ d1.x = d1.y := d1.hφx
        _ = d1.w := hyw0
        _ = d1.φ d1.z := d1.hφz.symm
    exact d1.hzx hxz0.symm
  have hys : y ≠ s := by
    intro hys'
    have hysk : (d1.φ ^ k) d1.y = (d1.φ ^ k) d1.w := by
      simpa [hyk, hsk] using hys'
    exact hyw0 ((d1.φ ^ k).injective hysk)
  let orbitMap : NProfile V → NProfile V := orbitProfileSum (nu d1.φ) (d1.period - 1)
  have horbit : ∀ {d : NProfile V}, d ∈ D → orbitMap d ∈ D := by
    intro d hd
    exact orbitProfileSum_mem_of_domainInvariant
      (D := D) hCone nu hInv d1.φ hd (d1.period - 1)
  let Dblock : Domain V :=
    orbitBlockDomain D (balanceRule (D := D) B) orbitMap horbit (orbitSet d1.φ x)
  let ψ : ZProfile V →+ R :=
    evalIntHom (fun v => B.bal x y v + B.bal y z v + B.bal z s v + B.bal s x v)
  let E9 : NProfile V → R := fun d =>
    balanceAt B x y d + balanceAt B y z d + balanceAt B z s d + balanceAt B s x d
  have hyOrbit : y ∈ orbitSet d1.φ x := by
    refine ⟨1, ?_⟩
    simp [x, y]
  have hzOrbit : z ∈ orbitSet d1.φ x := by
    refine ⟨2, ?_⟩
    simp [x, y, z, pow_succ']
  have hsOrbit : s ∈ orbitSet d1.φ x := by
    refine ⟨3, ?_⟩
    simp [x, y, z, s, pow_succ']
  have hHullBlock :
      IsDivisibleHull (domainImageZ Dblock) w.Kx0 := by
    simpa [Dblock, orbitMap, x, c8Fallback_case1_blockDomainAt, c8Fallback_case1_orbitMap, horbit] using
      w.hHullBlock0
  have eqC9 : ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B x y d + balanceAt B y z d +
        balanceAt B z s d + balanceAt B s x d = 0 := by
    intro d hd
    have hZeroOnD :
        ∀ z0, z0 ∈ domainImageZ D → ψ z0 = 0 := by
      refine zero_on_domainImageZ_of_hullEq
        (D := D) (Dblock := Dblock) (ψ := ψ)
        (K := w.K) (Kblock := w.Kx0)
        w.hHullD hHullBlock w.hHullEq0 ?_
      intro z0 hz0
      rcases hz0 with ⟨d0, hd0, rfl⟩
      rcases hd0 with ⟨hd0D, hblock⟩
      have hd0Orbit : orbitMap d0 ∈ D := horbit hd0D
      have hxWin :
          x ∈ balanceRule (D := D) B ⟨orbitMap d0, hd0Orbit⟩ :=
        hblock (self_mem_orbitSet d1.φ x)
      have hyWin :
          y ∈ balanceRule (D := D) B ⟨orbitMap d0, hd0Orbit⟩ :=
        hblock hyOrbit
      have hxy0 :
          balanceAt B x y (orbitMap d0) = 0 :=
        balanceAt_eq_zero_of_two_winners
          (D := D) (B := B) hSkew hd0Orbit hxWin hyWin
      have hE0 : E9 d0 = 0 := by
        rcases d1.hPeriod with h4 | h12
        · have havg :
            balanceAt B x y (orbitMap d0) = E9 d0 := by
            simpa [orbitMap, h4, E9] using
              (c8Fallback_cycle4_pair_average
                (nu := nu) (B := B) hNeutralB d1.φ x y z s
                hφx hφy hφz hφs d0)
          simpa [havg] using hxy0
        · have hpow4x : (d1.φ ^ 4) x = x := by
            simp [pow_succ', hφx, hφy, hφz, hφs]
          have hpow4y : (d1.φ ^ 4) y = y := by
            simp [pow_succ', hφy, hφz, hφs, hφx]
          have hpow4z : (d1.φ ^ 4) z = z := by
            simp [pow_succ', hφz, hφs, hφx, hφy]
          have hpow4s : (d1.φ ^ 4) s = s := by
            simp [pow_succ', hφs, hφx, hφy, hφz]
          have hpow8x : (d1.φ ^ 8) x = x := by
            exact c8Fallback_pow8_fix_of_pow4_fix (φ := d1.φ) (x := x) hpow4x
          have hpow8y : (d1.φ ^ 8) y = y := by
            exact c8Fallback_pow8_fix_of_pow4_fix (φ := d1.φ) (x := y) hpow4y
          have hpow8z : (d1.φ ^ 8) z = z := by
            exact c8Fallback_pow8_fix_of_pow4_fix (φ := d1.φ) (x := z) hpow4z
          have hpow8s : (d1.φ ^ 8) s = s := by
            exact c8Fallback_pow8_fix_of_pow4_fix (φ := d1.φ) (x := s) hpow4s
          have hfix4xy :
              balanceAt B x y (permuteNProfile ((nu d1.φ) ^ 4) d0) =
                balanceAt B x y d0 := by
            exact c8Fallback_balanceAt_fixed_of_pow_fix
              (nu := nu) (B := B) hNeutralB d1.φ 4 x y d0 hpow4x hpow4y
          have hfix4yz :
              balanceAt B y z (permuteNProfile ((nu d1.φ) ^ 4) d0) =
                balanceAt B y z d0 := by
            exact c8Fallback_balanceAt_fixed_of_pow_fix
              (nu := nu) (B := B) hNeutralB d1.φ 4 y z d0 hpow4y hpow4z
          have hfix4zs :
              balanceAt B z s (permuteNProfile ((nu d1.φ) ^ 4) d0) =
                balanceAt B z s d0 := by
            exact c8Fallback_balanceAt_fixed_of_pow_fix
              (nu := nu) (B := B) hNeutralB d1.φ 4 z s d0 hpow4z hpow4s
          have hfix4sx :
              balanceAt B s x (permuteNProfile ((nu d1.φ) ^ 4) d0) =
                balanceAt B s x d0 := by
            exact c8Fallback_balanceAt_fixed_of_pow_fix
              (nu := nu) (B := B) hNeutralB d1.φ 4 s x d0 hpow4s hpow4x
          have hfix8xy :
              balanceAt B x y (permuteNProfile ((nu d1.φ) ^ 8) d0) =
                balanceAt B x y d0 := by
            exact c8Fallback_balanceAt_fixed_of_pow_fix
              (nu := nu) (B := B) hNeutralB d1.φ 8 x y d0 hpow8x hpow8y
          have hfix8yz :
              balanceAt B y z (permuteNProfile ((nu d1.φ) ^ 8) d0) =
                balanceAt B y z d0 := by
            exact c8Fallback_balanceAt_fixed_of_pow_fix
              (nu := nu) (B := B) hNeutralB d1.φ 8 y z d0 hpow8y hpow8z
          have hfix8zs :
              balanceAt B z s (permuteNProfile ((nu d1.φ) ^ 8) d0) =
                balanceAt B z s d0 := by
            exact c8Fallback_balanceAt_fixed_of_pow_fix
              (nu := nu) (B := B) hNeutralB d1.φ 8 z s d0 hpow8z hpow8s
          have hfix8sx :
              balanceAt B s x (permuteNProfile ((nu d1.φ) ^ 8) d0) =
                balanceAt B s x d0 := by
            exact c8Fallback_balanceAt_fixed_of_pow_fix
              (nu := nu) (B := B) hNeutralB d1.φ 8 s x d0 hpow8s hpow8x
          have hEfix4 :
              E9 (permuteNProfile ((nu d1.φ) ^ 4) d0) = E9 d0 := by
            simp [E9, hfix4xy, hfix4yz, hfix4zs, hfix4sx]
          have hEfix8 :
              E9 (permuteNProfile ((nu d1.φ) ^ 8) d0) = E9 d0 := by
            simp [E9, hfix8xy, hfix8yz, hfix8zs, hfix8sx]
          have havg3 :
              ∀ e : NProfile V,
                balanceAt B x y (orbitProfileSum (nu d1.φ) 3 e) = E9 e := by
            intro e
            simpa [E9] using
              (c8Fallback_cycle4_pair_average
                (nu := nu) (B := B) hNeutralB d1.φ x y z s
                hφx hφy hφz hφs e)
          have havg11 :
              balanceAt B x y (orbitProfileSum (nu d1.φ) 11 d0) =
                E9 d0 + E9 d0 + E9 d0 := by
            calc
              balanceAt B x y (orbitProfileSum (nu d1.φ) 11 d0)
                  = balanceAt B x y
                      (orbitProfileSum (nu d1.φ) 3 d0 +
                        orbitProfileSum (nu d1.φ) 3
                          (permuteNProfile ((nu d1.φ) ^ 4) d0) +
                        orbitProfileSum (nu d1.φ) 3
                          (permuteNProfile ((nu d1.φ) ^ 8) d0)) := by
                        rw [c8Fallback_orbitProfileSum11_split (π := nu d1.φ) d0]
              _ = balanceAt B x y (orbitProfileSum (nu d1.φ) 3 d0) +
                    balanceAt B x y (orbitProfileSum (nu d1.φ) 3
                      (permuteNProfile ((nu d1.φ) ^ 4) d0)) +
                    balanceAt B x y (orbitProfileSum (nu d1.φ) 3
                      (permuteNProfile ((nu d1.φ) ^ 8) d0)) := by
                      simp [balanceAt_add, add_assoc]
              _ = E9 d0 + E9 d0 + E9 d0 := by
                    simp [havg3, hEfix4, hEfix8, add_assoc]
          have htriple :
              E9 d0 + E9 d0 + E9 d0 = 0 := by
            calc
              E9 d0 + E9 d0 + E9 d0
                  = balanceAt B x y (orbitProfileSum (nu d1.φ) 11 d0) := havg11.symm
              _ = balanceAt B x y (orbitMap d0) := by simp [orbitMap, h12]
              _ = 0 := hxy0
          exact c8Fallback_eq_zero_of_triple_sum_eq_zero htriple
      have hψ :
          ψ (toZProfile d0) = E9 d0 := by
        simpa [ψ, E9] using
          (c8Fallback_evalIntHom_toZProfile_eq4 (B := B) x y z s d0)
      exact hψ.trans hE0
    have hdz : toZProfile d ∈ domainImageZ D := ⟨d, hd, rfl⟩
    have hψ0 := hZeroOnD (toZProfile d) hdz
    have hψ :
        ψ (toZProfile d) = E9 d := by
      simpa [ψ, E9] using
        (c8Fallback_evalIntHom_toZProfile_eq4 (B := B) x y z s d)
    simpa [hψ] using hψ0
  let g10 : Equiv.Perm X := Equiv.swap z s
  have hg10x : g10 x = x := by
    simp [g10, Equiv.swap_apply_of_ne_of_ne, hzx.symm, hsx.symm]
  have hg10y : g10 y = y := by
    simp [g10, Equiv.swap_apply_of_ne_of_ne, hyz, hys]
  have eqC10 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y s d +
          balanceAt B s z d + balanceAt B z x d = 0 := by
    intro d hd
    have h := c8Fallback_eq4_transport
      (nu := nu) (D := D) hInv B hNeutralB eqC9 g10 hd
    simpa [g10, hg10x, hg10y, Equiv.swap_apply_left, Equiv.swap_apply_right] using h
  let g11 : Equiv.Perm X := c8Cycle3Perm x y z
  have hg11x : g11 x = y := c8Cycle3Perm_apply_x (x := x) (y := y) (z := z) hxy hzx
  have hg11y : g11 y = z := c8Cycle3Perm_apply_y (x := x) (y := y) (z := z) hyz hzx
  have hg11z : g11 z = x := c8Cycle3Perm_apply_z (x := x) (y := y) (z := z)
  have hg11s : g11 s = s :=
    c8Cycle3Perm_apply_of_ne (x := x) (y := y) (z := z) (t := s)
      hsx hys.symm hzw.symm
  have eqC11 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B y z d + balanceAt B z x d +
          balanceAt B x s d + balanceAt B s y d = 0 := by
    intro d hd
    have h := c8Fallback_eq4_transport
      (nu := nu) (D := D) hInv B hNeutralB eqC9 g11 hd
    simpa [g11, hg11x, hg11y, hg11z, hg11s, add_assoc, add_comm, add_left_comm] using h
  have eqC12 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B y z d + balanceAt B z s d +
          balanceAt B s x d + balanceAt B x y d = 0 := by
    intro d hd
    simpa [add_assoc, add_comm, add_left_comm] using eqC9 (d := d) hd
  let g13 : Equiv.Perm X := c8Cycle3Perm x z y
  have hg13x : g13 x = z := by
    simpa [g13] using
      (c8Cycle3Perm_apply_x (x := x) (y := z) (z := y) hzx.symm hxy.symm)
  have hg13z : g13 z = y := by
    simpa [g13] using
      (c8Cycle3Perm_apply_y (x := x) (y := z) (z := y) hyz.symm hxy.symm)
  have hg13y : g13 y = x := by
    simpa [g13] using (c8Cycle3Perm_apply_z (x := x) (y := z) (z := y))
  have hg13s : g13 s = s :=
    c8Cycle3Perm_apply_of_ne (x := x) (y := z) (z := y) (t := s)
      hsx hzw.symm hys.symm
  have eqC13 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B z x d + balanceAt B x y d +
          balanceAt B y s d + balanceAt B s z d = 0 := by
    intro d hd
    have h := c8Fallback_eq4_transport
      (nu := nu) (D := D) hInv B hNeutralB eqC9 g13 hd
    simpa [g13, hg13x, hg13z, hg13y, hg13s, add_assoc, add_comm, add_left_comm] using h
  let g14 : Equiv.Perm X := Equiv.swap y s * c8Cycle3Perm x z y
  have hg14x : g14 x = z := by
    calc
      g14 x = Equiv.swap y s ((c8Cycle3Perm x z y) x) := rfl
      _ = Equiv.swap y s z := by simp [g13, hg13x]
      _ = z := by
        exact Equiv.swap_apply_of_ne_of_ne hyz.symm hzw
  have hg14y : g14 y = x := by
    calc
      g14 y = Equiv.swap y s ((c8Cycle3Perm x z y) y) := rfl
      _ = Equiv.swap y s x := by simp [g13, hg13y]
      _ = x := by
        exact Equiv.swap_apply_of_ne_of_ne hxy hsx.symm
  have hg14z : g14 z = s := by
    calc
      g14 z = Equiv.swap y s ((c8Cycle3Perm x z y) z) := rfl
      _ = Equiv.swap y s y := by simp [g13, hg13z]
      _ = s := by simp [Equiv.swap_apply_left]
  have hg14s : g14 s = y := by
    calc
      g14 s = Equiv.swap y s ((c8Cycle3Perm x z y) s) := rfl
      _ = Equiv.swap y s s := by simp [g13, hg13s]
      _ = y := by simp [Equiv.swap_apply_right]
  have eqC14 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B z x d + balanceAt B x s d +
          balanceAt B s y d + balanceAt B y z d = 0 := by
    intro d hd
    have h := c8Fallback_eq4_transport
      (nu := nu) (D := D) hInv B hNeutralB eqC9 g14 hd
    simpa [g14, hg14x, hg14y, hg14z, hg14s, add_assoc, add_comm, add_left_comm] using h
  refine ⟨{
    x := x
    y := y
    z := z
    w := s
    hxy := hxy
    hyz := hyz
    hzx := hzx
    hzw := hzw
    hwx := hsx
    eqC9 := eqC9
    eqC10 := eqC10
    eqC11 := eqC11
    eqC12 := eqC12
    eqC13 := eqC13
    eqC14 := eqC14
  }⟩

theorem c8Fallback_case2_equationPack5_of_bigOrbitWitness
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (_hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (_hR : Reinforcement D (balanceRule (D := D) B))
    (_hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (d2 : C8Case2OrbitPartitionData X)
    (w : C8Case2HullWitnessData
      (nu := nu) (R := R) (D := D) hCone B hInv d2)
    (hbig : w.x0 ∈ orbitSet d2.φ d2.x) :
    Nonempty (C8FallbackEquationPack5 (D := D) (B := B)) := by
  rcases hbig with ⟨k, hk⟩
  let x : X := w.x0
  let y : X := d2.φ x
  let z : X := d2.φ y
  let u : X := d2.φ z
  let v : X := d2.φ u
  have hxk : x = (d2.φ ^ k) d2.x := by
    simpa [x] using hk.symm
  have hyk : y = (d2.φ ^ k) d2.y := by
    calc
      y = d2.φ x := rfl
      _ = d2.φ ((d2.φ ^ k) d2.x) := by simpa [x] using congrArg d2.φ hk.symm
      _ = (d2.φ ^ (k + 1)) d2.x := by simp [pow_succ']
      _ = (d2.φ ^ k) (d2.φ d2.x) := by simp [pow_succ]
      _ = (d2.φ ^ k) d2.y := by simp [d2.hφx]
  have hzk : z = (d2.φ ^ k) d2.z := by
    calc
      z = d2.φ y := rfl
      _ = d2.φ ((d2.φ ^ k) d2.y) := by simpa [y] using congrArg d2.φ hyk
      _ = (d2.φ ^ (k + 1)) d2.y := by simp [pow_succ']
      _ = (d2.φ ^ k) (d2.φ d2.y) := by simp [pow_succ]
      _ = (d2.φ ^ k) d2.z := by simp [d2.hφy]
  have huk : u = (d2.φ ^ k) d2.u := by
    calc
      u = d2.φ z := rfl
      _ = d2.φ ((d2.φ ^ k) d2.z) := by simpa [z] using congrArg d2.φ hzk
      _ = (d2.φ ^ (k + 1)) d2.z := by simp [pow_succ']
      _ = (d2.φ ^ k) (d2.φ d2.z) := by simp [pow_succ]
      _ = (d2.φ ^ k) d2.u := by simp [d2.hφz]
  have hvk : v = (d2.φ ^ k) d2.v := by
    calc
      v = d2.φ u := rfl
      _ = d2.φ ((d2.φ ^ k) d2.u) := by simpa [u] using congrArg d2.φ huk
      _ = (d2.φ ^ (k + 1)) d2.u := by simp [pow_succ']
      _ = (d2.φ ^ k) (d2.φ d2.u) := by simp [pow_succ]
      _ = (d2.φ ^ k) d2.v := by simp [d2.hφu]
  have hφx : d2.φ x = y := by rfl
  have hφy : d2.φ y = z := by rfl
  have hφz : d2.φ z = u := by rfl
  have hφu : d2.φ u = v := by rfl
  have hφv : d2.φ v = x := by
    calc
      d2.φ v = d2.φ ((d2.φ ^ k) d2.v) := by simpa [v] using congrArg d2.φ hvk
      _ = (d2.φ ^ (k + 1)) d2.v := by simp [pow_succ']
      _ = (d2.φ ^ k) (d2.φ d2.v) := by simp [pow_succ]
      _ = (d2.φ ^ k) d2.x := by simp [d2.hφv]
      _ = x := by simpa [x] using hk
  have hxy : x ≠ y := by
    intro hxy'
    have hxyk : (d2.φ ^ k) d2.x = (d2.φ ^ k) d2.y := by
      simpa [hxk, hyk] using hxy'
    exact d2.hxy ((d2.φ ^ k).injective hxyk)
  have hyz : y ≠ z := by
    intro hyz'
    have hyzk : (d2.φ ^ k) d2.y = (d2.φ ^ k) d2.z := by
      simpa [hyk, hzk] using hyz'
    exact d2.hyz ((d2.φ ^ k).injective hyzk)
  have hzx : z ≠ x := by
    intro hzx'
    have hzxk : (d2.φ ^ k) d2.z = (d2.φ ^ k) d2.x := by
      simpa [hzk, hxk] using hzx'
    exact d2.hzx ((d2.φ ^ k).injective hzxk)
  have hzu : z ≠ u := by
    intro hzu'
    have hzuk : (d2.φ ^ k) d2.z = (d2.φ ^ k) d2.u := by
      simpa [hzk, huk] using hzu'
    exact d2.hzu ((d2.φ ^ k).injective hzuk)
  have huv : u ≠ v := by
    intro huv'
    have huvk : (d2.φ ^ k) d2.u = (d2.φ ^ k) d2.v := by
      simpa [huk, hvk] using huv'
    exact d2.huv ((d2.φ ^ k).injective huvk)
  have hvx : v ≠ x := by
    intro hvx'
    have hvxk : (d2.φ ^ k) d2.v = (d2.φ ^ k) d2.x := by
      simpa [hvk, hxk] using hvx'
    exact d2.hvx ((d2.φ ^ k).injective hvxk)
  have hxu0 : d2.x ≠ d2.u := by
    intro hxu0
    have hvy0 : d2.v = d2.y := by
      calc
        d2.v = d2.φ d2.u := d2.hφu.symm
        _ = d2.φ d2.x := by simp [hxu0]
        _ = d2.y := d2.hφx
    have hzx0 : d2.z = d2.x := by
      calc
        d2.z = d2.φ d2.y := d2.hφy.symm
        _ = d2.φ d2.v := by simp [hvy0]
        _ = d2.x := d2.hφv
    exact d2.hzx hzx0
  have hzv0 : d2.z ≠ d2.v := by
    intro hzv0
    have hux0 : d2.u = d2.x := by
      apply d2.φ.injective
      simpa [d2.hφz, d2.hφv] using congrArg d2.φ hzv0
    exact hxu0 hux0.symm
  have hyu0 : d2.y ≠ d2.u := by
    intro hyu0
    have hzv0' : d2.z = d2.v := by
      apply d2.φ.injective
      simpa [d2.hφy, d2.hφu] using congrArg d2.φ hyu0
    exact hzv0 hzv0'
  have hyv0 : d2.y ≠ d2.v := by
    intro hyv0
    have hzx0 : d2.z = d2.x := by
      apply d2.φ.injective
      simpa [d2.hφy, d2.hφv] using congrArg d2.φ hyv0
    exact d2.hzx hzx0
  have hxu : x ≠ u := by
    intro hxu'
    have hxuk : (d2.φ ^ k) d2.x = (d2.φ ^ k) d2.u := by
      simpa [hxk, huk] using hxu'
    exact hxu0 ((d2.φ ^ k).injective hxuk)
  have hzv : z ≠ v := by
    intro hzv'
    have hzvk : (d2.φ ^ k) d2.z = (d2.φ ^ k) d2.v := by
      simpa [hzk, hvk] using hzv'
    exact hzv0 ((d2.φ ^ k).injective hzvk)
  have hyu : y ≠ u := by
    intro hyu'
    have hyuk : (d2.φ ^ k) d2.y = (d2.φ ^ k) d2.u := by
      simpa [hyk, huk] using hyu'
    exact hyu0 ((d2.φ ^ k).injective hyuk)
  have hyv : y ≠ v := by
    intro hyv'
    have hyvk : (d2.φ ^ k) d2.y = (d2.φ ^ k) d2.v := by
      simpa [hyk, hvk] using hyv'
    exact hyv0 ((d2.φ ^ k).injective hyvk)
  have hxv : x ≠ v := hvx.symm
  let orbitMap : NProfile V → NProfile V := orbitProfileSum (nu d2.φ) (d2.period - 1)
  have horbit : ∀ {d : NProfile V}, d ∈ D → orbitMap d ∈ D := by
    intro d hd
    exact orbitProfileSum_mem_of_domainInvariant
      (D := D) hCone nu hInv d2.φ hd (d2.period - 1)
  let Dblock : Domain V :=
    orbitBlockDomain D (balanceRule (D := D) B) orbitMap horbit (orbitSet d2.φ x)
  let ψ : ZProfile V →+ R :=
    evalIntHom (fun t => B.bal x y t + B.bal y z t + B.bal z u t + B.bal u v t + B.bal v x t)
  let E15 : NProfile V → R := fun d =>
    balanceAt B x y d + balanceAt B y z d + balanceAt B z u d +
      balanceAt B u v d + balanceAt B v x d
  have hyOrbit : y ∈ orbitSet d2.φ x := by
    refine ⟨1, ?_⟩
    simp [x, y]
  have hzOrbit : z ∈ orbitSet d2.φ x := by
    refine ⟨2, ?_⟩
    simp [x, y, z, pow_succ']
  have huOrbit : u ∈ orbitSet d2.φ x := by
    refine ⟨3, ?_⟩
    simp [x, y, z, u, pow_succ']
  have hvOrbit : v ∈ orbitSet d2.φ x := by
    refine ⟨4, ?_⟩
    simp [x, y, z, u, v, pow_succ']
  have hHullBlock :
      IsDivisibleHull (domainImageZ Dblock) w.Kx0 := by
    simpa [Dblock, orbitMap, x, c8Fallback_case2_blockDomainAt, c8Fallback_case2_orbitMap, horbit] using
      w.hHullBlock0
  have eqC15 : ∀ ⦃d : NProfile V⦄, d ∈ D →
      balanceAt B x y d + balanceAt B y z d + balanceAt B z u d +
        balanceAt B u v d + balanceAt B v x d = 0 := by
    intro d hd
    have hZeroOnD :
        ∀ z0, z0 ∈ domainImageZ D → ψ z0 = 0 := by
      refine zero_on_domainImageZ_of_hullEq
        (D := D) (Dblock := Dblock) (ψ := ψ)
        (K := w.K) (Kblock := w.Kx0)
        w.hHullD hHullBlock w.hHullEq0 ?_
      intro z0 hz0
      rcases hz0 with ⟨d0, hd0, rfl⟩
      rcases hd0 with ⟨hd0D, hblock⟩
      have hd0Orbit : orbitMap d0 ∈ D := horbit hd0D
      have hxWin :
          x ∈ balanceRule (D := D) B ⟨orbitMap d0, hd0Orbit⟩ :=
        hblock (self_mem_orbitSet d2.φ x)
      have hyWin :
          y ∈ balanceRule (D := D) B ⟨orbitMap d0, hd0Orbit⟩ :=
        hblock hyOrbit
      have hxy0 :
          balanceAt B x y (orbitMap d0) = 0 :=
        balanceAt_eq_zero_of_two_winners
          (D := D) (B := B) hSkew hd0Orbit hxWin hyWin
      have hE0 : E15 d0 = 0 := by
        rcases d2.hPeriod with h5 | h15
        · have havg :
            balanceAt B x y (orbitMap d0) = E15 d0 := by
            simpa [orbitMap, h5, E15] using
              (c8Fallback_cycle5_pair_average
                (nu := nu) (B := B) hNeutralB d2.φ x y z u v
                hφx hφy hφz hφu hφv d0)
          simpa [havg] using hxy0
        · have hpow5x : (d2.φ ^ 5) x = x := by
            simp [pow_succ', hφx, hφy, hφz, hφu, hφv]
          have hpow5y : (d2.φ ^ 5) y = y := by
            simp [pow_succ', hφy, hφz, hφu, hφv, hφx]
          have hpow5z : (d2.φ ^ 5) z = z := by
            simp [pow_succ', hφz, hφu, hφv, hφx, hφy]
          have hpow5u : (d2.φ ^ 5) u = u := by
            simp [pow_succ', hφu, hφv, hφx, hφy, hφz]
          have hpow5v : (d2.φ ^ 5) v = v := by
            simp [pow_succ', hφv, hφx, hφy, hφz, hφu]
          have hpow10x : (d2.φ ^ 10) x = x := by
            exact c8Fallback_pow10_fix_of_pow5_fix (φ := d2.φ) (x := x) hpow5x
          have hpow10y : (d2.φ ^ 10) y = y := by
            exact c8Fallback_pow10_fix_of_pow5_fix (φ := d2.φ) (x := y) hpow5y
          have hpow10z : (d2.φ ^ 10) z = z := by
            exact c8Fallback_pow10_fix_of_pow5_fix (φ := d2.φ) (x := z) hpow5z
          have hpow10u : (d2.φ ^ 10) u = u := by
            exact c8Fallback_pow10_fix_of_pow5_fix (φ := d2.φ) (x := u) hpow5u
          have hpow10v : (d2.φ ^ 10) v = v := by
            exact c8Fallback_pow10_fix_of_pow5_fix (φ := d2.φ) (x := v) hpow5v
          have hfix5xy :
              balanceAt B x y (permuteNProfile ((nu d2.φ) ^ 5) d0) =
                balanceAt B x y d0 := by
            exact c8Fallback_balanceAt_fixed_of_pow_fix
              (nu := nu) (B := B) hNeutralB d2.φ 5 x y d0 hpow5x hpow5y
          have hfix5yz :
              balanceAt B y z (permuteNProfile ((nu d2.φ) ^ 5) d0) =
                balanceAt B y z d0 := by
            exact c8Fallback_balanceAt_fixed_of_pow_fix
              (nu := nu) (B := B) hNeutralB d2.φ 5 y z d0 hpow5y hpow5z
          have hfix5zu :
              balanceAt B z u (permuteNProfile ((nu d2.φ) ^ 5) d0) =
                balanceAt B z u d0 := by
            exact c8Fallback_balanceAt_fixed_of_pow_fix
              (nu := nu) (B := B) hNeutralB d2.φ 5 z u d0 hpow5z hpow5u
          have hfix5uv :
              balanceAt B u v (permuteNProfile ((nu d2.φ) ^ 5) d0) =
                balanceAt B u v d0 := by
            exact c8Fallback_balanceAt_fixed_of_pow_fix
              (nu := nu) (B := B) hNeutralB d2.φ 5 u v d0 hpow5u hpow5v
          have hfix5vx :
              balanceAt B v x (permuteNProfile ((nu d2.φ) ^ 5) d0) =
                balanceAt B v x d0 := by
            exact c8Fallback_balanceAt_fixed_of_pow_fix
              (nu := nu) (B := B) hNeutralB d2.φ 5 v x d0 hpow5v hpow5x
          have hfix10xy :
              balanceAt B x y (permuteNProfile ((nu d2.φ) ^ 10) d0) =
                balanceAt B x y d0 := by
            exact c8Fallback_balanceAt_fixed_of_pow_fix
              (nu := nu) (B := B) hNeutralB d2.φ 10 x y d0 hpow10x hpow10y
          have hfix10yz :
              balanceAt B y z (permuteNProfile ((nu d2.φ) ^ 10) d0) =
                balanceAt B y z d0 := by
            exact c8Fallback_balanceAt_fixed_of_pow_fix
              (nu := nu) (B := B) hNeutralB d2.φ 10 y z d0 hpow10y hpow10z
          have hfix10zu :
              balanceAt B z u (permuteNProfile ((nu d2.φ) ^ 10) d0) =
                balanceAt B z u d0 := by
            exact c8Fallback_balanceAt_fixed_of_pow_fix
              (nu := nu) (B := B) hNeutralB d2.φ 10 z u d0 hpow10z hpow10u
          have hfix10uv :
              balanceAt B u v (permuteNProfile ((nu d2.φ) ^ 10) d0) =
                balanceAt B u v d0 := by
            exact c8Fallback_balanceAt_fixed_of_pow_fix
              (nu := nu) (B := B) hNeutralB d2.φ 10 u v d0 hpow10u hpow10v
          have hfix10vx :
              balanceAt B v x (permuteNProfile ((nu d2.φ) ^ 10) d0) =
                balanceAt B v x d0 := by
            exact c8Fallback_balanceAt_fixed_of_pow_fix
              (nu := nu) (B := B) hNeutralB d2.φ 10 v x d0 hpow10v hpow10x
          have hEfix5 :
              E15 (permuteNProfile ((nu d2.φ) ^ 5) d0) = E15 d0 := by
            simp [E15, hfix5xy, hfix5yz, hfix5zu, hfix5uv, hfix5vx]
          have hEfix10 :
              E15 (permuteNProfile ((nu d2.φ) ^ 10) d0) = E15 d0 := by
            simp [E15, hfix10xy, hfix10yz, hfix10zu, hfix10uv, hfix10vx]
          have havg4 :
              ∀ e : NProfile V,
                balanceAt B x y (orbitProfileSum (nu d2.φ) 4 e) = E15 e := by
            intro e
            simpa [E15] using
              (c8Fallback_cycle5_pair_average
                (nu := nu) (B := B) hNeutralB d2.φ x y z u v
                hφx hφy hφz hφu hφv e)
          have havg14 :
              balanceAt B x y (orbitProfileSum (nu d2.φ) 14 d0) =
                E15 d0 + E15 d0 + E15 d0 := by
            calc
              balanceAt B x y (orbitProfileSum (nu d2.φ) 14 d0)
                  = balanceAt B x y
                      (orbitProfileSum (nu d2.φ) 4 d0 +
                        orbitProfileSum (nu d2.φ) 4
                          (permuteNProfile ((nu d2.φ) ^ 5) d0) +
                        orbitProfileSum (nu d2.φ) 4
                          (permuteNProfile ((nu d2.φ) ^ 10) d0)) := by
                        rw [c8Fallback_orbitProfileSum14_split (π := nu d2.φ) d0]
              _ = balanceAt B x y (orbitProfileSum (nu d2.φ) 4 d0) +
                    balanceAt B x y (orbitProfileSum (nu d2.φ) 4
                      (permuteNProfile ((nu d2.φ) ^ 5) d0)) +
                    balanceAt B x y (orbitProfileSum (nu d2.φ) 4
                      (permuteNProfile ((nu d2.φ) ^ 10) d0)) := by
                      simp [balanceAt_add, add_assoc]
              _ = E15 d0 + E15 d0 + E15 d0 := by
                    simp [havg4, hEfix5, hEfix10, add_assoc]
          have htriple :
              E15 d0 + E15 d0 + E15 d0 = 0 := by
            calc
              E15 d0 + E15 d0 + E15 d0
                  = balanceAt B x y (orbitProfileSum (nu d2.φ) 14 d0) := havg14.symm
              _ = balanceAt B x y (orbitMap d0) := by simp [orbitMap, h15]
              _ = 0 := hxy0
          exact c8Fallback_eq_zero_of_triple_sum_eq_zero htriple
      have hψ :
          ψ (toZProfile d0) = E15 d0 := by
        simpa [ψ, E15] using
          (c8Fallback_evalIntHom_toZProfile_eq5 (B := B) x y z u v d0)
      exact hψ.trans hE0
    have hdz : toZProfile d ∈ domainImageZ D := ⟨d, hd, rfl⟩
    have hψ0 := hZeroOnD (toZProfile d) hdz
    have hψ :
        ψ (toZProfile d) = E15 d := by
      simpa [ψ, E15] using
        (c8Fallback_evalIntHom_toZProfile_eq5 (B := B) x y z u v d)
    simpa [hψ] using hψ0
  have hux : u ≠ x := hxu.symm
  have huy : u ≠ y := hyu.symm
  have huz : u ≠ z := hzu.symm
  have hvy : v ≠ y := hyv.symm
  have hvz : v ≠ z := hzv.symm
  let g16 : Equiv.Perm X := Equiv.swap u v
  have hg16x : g16 x = x := by
    simp [g16, Equiv.swap_apply_of_ne_of_ne, hxu, hxv]
  have hg16y : g16 y = y := by
    simp [g16, Equiv.swap_apply_of_ne_of_ne, hyu, hyv]
  have hg16z : g16 z = z := by
    simp [g16, Equiv.swap_apply_of_ne_of_ne, hzu, hzv]
  have hg16u : g16 u = v := by
    simp [g16, Equiv.swap_apply_left]
  have hg16v : g16 v = u := by
    simp [g16, Equiv.swap_apply_right]
  have eqC16 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B x y d + balanceAt B y z d + balanceAt B z v d +
          balanceAt B v u d + balanceAt B u x d = 0 := by
    intro d hd
    have h := c8Fallback_eq5_transport
      (nu := nu) (D := D) hInv B hNeutralB eqC15 g16 hd
    simpa [g16, hg16x, hg16y, hg16z, hg16u, hg16v] using h
  let g17 : Equiv.Perm X := c8Cycle3Perm x y z
  have hg17x : g17 x = y := c8Cycle3Perm_apply_x (x := x) (y := y) (z := z) hxy hzx
  have hg17y : g17 y = z := c8Cycle3Perm_apply_y (x := x) (y := y) (z := z) hyz hzx
  have hg17z : g17 z = x := c8Cycle3Perm_apply_z (x := x) (y := y) (z := z)
  have hg17u : g17 u = u :=
    c8Cycle3Perm_apply_of_ne (x := x) (y := y) (z := z) (t := u)
      hux huy huz
  have hg17v : g17 v = v :=
    c8Cycle3Perm_apply_of_ne (x := x) (y := y) (z := z) (t := v)
      hvx hvy hvz
  have eqC17 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B y z d + balanceAt B z x d + balanceAt B x u d +
          balanceAt B u v d + balanceAt B v y d = 0 := by
    intro d hd
    have h := c8Fallback_eq5_transport
      (nu := nu) (D := D) hInv B hNeutralB eqC15 g17 hd
    simpa [g17, hg17x, hg17y, hg17z, hg17u, hg17v] using h
  let g18 : Equiv.Perm X := Equiv.swap u v * c8Cycle3Perm x y z
  have hg18x : g18 x = y := by
    calc
      g18 x = Equiv.swap u v ((c8Cycle3Perm x y z) x) := rfl
      _ = Equiv.swap u v y := by simp [g17, hg17x]
      _ = y := by
        exact Equiv.swap_apply_of_ne_of_ne hyu hyv
  have hg18y : g18 y = z := by
    calc
      g18 y = Equiv.swap u v ((c8Cycle3Perm x y z) y) := rfl
      _ = Equiv.swap u v z := by simp [g17, hg17y]
      _ = z := by
        exact Equiv.swap_apply_of_ne_of_ne hzu hzv
  have hg18z : g18 z = x := by
    calc
      g18 z = Equiv.swap u v ((c8Cycle3Perm x y z) z) := rfl
      _ = Equiv.swap u v x := by simp [g17, hg17z]
      _ = x := by
        exact Equiv.swap_apply_of_ne_of_ne hxu hxv
  have hg18u : g18 u = v := by
    calc
      g18 u = Equiv.swap u v ((c8Cycle3Perm x y z) u) := rfl
      _ = Equiv.swap u v u := by simp [g17, hg17u]
      _ = v := by simp [Equiv.swap_apply_left]
  have hg18v : g18 v = u := by
    calc
      g18 v = Equiv.swap u v ((c8Cycle3Perm x y z) v) := rfl
      _ = Equiv.swap u v v := by simp [g17, hg17v]
      _ = u := by simp [Equiv.swap_apply_right]
  have eqC18 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B y z d + balanceAt B z x d + balanceAt B x v d +
          balanceAt B v u d + balanceAt B u y d = 0 := by
    intro d hd
    have h := c8Fallback_eq5_transport
      (nu := nu) (D := D) hInv B hNeutralB eqC15 g18 hd
    simpa [g18, hg18x, hg18y, hg18z, hg18u, hg18v] using h
  let g19 : Equiv.Perm X := c8Cycle3Perm x z y
  have hg19x : g19 x = z := by
    simpa [g19] using
      (c8Cycle3Perm_apply_x (x := x) (y := z) (z := y) hzx.symm hxy.symm)
  have hg19z : g19 z = y := by
    simpa [g19] using
      (c8Cycle3Perm_apply_y (x := x) (y := z) (z := y) hyz.symm hxy.symm)
  have hg19y : g19 y = x := by
    simpa [g19] using (c8Cycle3Perm_apply_z (x := x) (y := z) (z := y))
  have hg19u : g19 u = u :=
    c8Cycle3Perm_apply_of_ne (x := x) (y := z) (z := y) (t := u)
      hux huz huy
  have hg19v : g19 v = v :=
    c8Cycle3Perm_apply_of_ne (x := x) (y := z) (z := y) (t := v)
      hvx hvz hvy
  have eqC19 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B z x d + balanceAt B x y d + balanceAt B y u d +
          balanceAt B u v d + balanceAt B v z d = 0 := by
    intro d hd
    have h := c8Fallback_eq5_transport
      (nu := nu) (D := D) hInv B hNeutralB eqC15 g19 hd
    simpa [g19, hg19x, hg19z, hg19y, hg19u, hg19v] using h
  let g20 : Equiv.Perm X := Equiv.swap u v * c8Cycle3Perm x z y
  have hg20x : g20 x = z := by
    calc
      g20 x = Equiv.swap u v ((c8Cycle3Perm x z y) x) := rfl
      _ = Equiv.swap u v z := by simp [g19, hg19x]
      _ = z := by
        exact Equiv.swap_apply_of_ne_of_ne hzu hzv
  have hg20y : g20 y = x := by
    calc
      g20 y = Equiv.swap u v ((c8Cycle3Perm x z y) y) := rfl
      _ = Equiv.swap u v x := by simp [g19, hg19y]
      _ = x := by
        exact Equiv.swap_apply_of_ne_of_ne hxu hxv
  have hg20z : g20 z = y := by
    calc
      g20 z = Equiv.swap u v ((c8Cycle3Perm x z y) z) := rfl
      _ = Equiv.swap u v y := by simp [g19, hg19z]
      _ = y := by
        exact Equiv.swap_apply_of_ne_of_ne hyu hyv
  have hg20u : g20 u = v := by
    calc
      g20 u = Equiv.swap u v ((c8Cycle3Perm x z y) u) := rfl
      _ = Equiv.swap u v u := by simp [g19, hg19u]
      _ = v := by simp [Equiv.swap_apply_left]
  have hg20v : g20 v = u := by
    calc
      g20 v = Equiv.swap u v ((c8Cycle3Perm x z y) v) := rfl
      _ = Equiv.swap u v v := by simp [g19, hg19v]
      _ = u := by simp [Equiv.swap_apply_right]
  have eqC20 :
      ∀ ⦃d : NProfile V⦄, d ∈ D →
        balanceAt B z x d + balanceAt B x y d + balanceAt B y v d +
          balanceAt B v u d + balanceAt B u z d = 0 := by
    intro d hd
    have h := c8Fallback_eq5_transport
      (nu := nu) (D := D) hInv B hNeutralB eqC15 g20 hd
    simpa [g20, hg20x, hg20y, hg20z, hg20u, hg20v] using h
  refine ⟨{
    x := x
    y := y
    z := z
    u := u
    v := v
    hxy := hxy
    hyz := hyz
    hzx := hzx
    hzu := hzu
    huv := huv
    hvx := hvx
    eqC15 := eqC15
    eqC16 := eqC16
    eqC17 := eqC17
    eqC18 := eqC18
    eqC19 := eqC19
    eqC20 := eqC20
  }⟩

theorem c8Fallback_case1_branchSplit_of_hullWitness
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (d1 : C8Case1OrbitPartitionData X)
    (w : C8Case1HullWitnessData
      (nu := nu) (R := R) (D := D) hCone B hInv d1) :
    C8BranchSplitHypothesis (D := D) (B := B) := by
  rcases c8Fallback_case1_classify_witnessOrbit
      (nu := nu) (R := R) (D := D) hCone B hInv d1 w with hType
  cases hType with
  | threeOrbit hthree =>
      have hCycle : C8CycleSumHypothesis (D := D) (B := B) :=
        c8Fallback_case1_cycleSum_of_threeOrbitWitness
          (nu := nu) (R := R) (D := D)
          hCone B hSkew hPerfect hInv hNeutralB hR hNE d1 w hthree
      exact Or.inl (threeCycleBranch_of_cycleSumHypothesis (D := D) (B := B) hCycle)
  | bigOrbit hbig =>
      rcases c8Fallback_case1_equationPack4_of_bigOrbitWitness
          (nu := nu) (R := R) (D := D)
          hCone B hSkew hPerfect hInv hNeutralB hR hNE d1 w hbig with ⟨p4⟩
      exact Or.inr
        (c8Fallback_fourFiveCycleBranch_of_equationPack
          (D := D) (B := B) hSkew (Or.inl ⟨p4⟩))

theorem c8Fallback_case2_branchSplit_of_hullWitness
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (d2 : C8Case2OrbitPartitionData X)
    (w : C8Case2HullWitnessData
      (nu := nu) (R := R) (D := D) hCone B hInv d2) :
    C8BranchSplitHypothesis (D := D) (B := B) := by
  rcases c8Fallback_case2_classify_witnessOrbit
      (nu := nu) (R := R) (D := D) hCone B hInv d2 w with hType
  cases hType with
  | threeOrbit hthree =>
      have hCycle : C8CycleSumHypothesis (D := D) (B := B) :=
        c8Fallback_case2_cycleSum_of_threeOrbitWitness
          (nu := nu) (R := R) (D := D)
          hCone B hSkew hPerfect hInv hNeutralB hR hNE d2 w hthree
      exact Or.inl (threeCycleBranch_of_cycleSumHypothesis (D := D) (B := B) hCycle)
  | bigOrbit hbig =>
      rcases c8Fallback_case2_equationPack5_of_bigOrbitWitness
          (nu := nu) (R := R) (D := D)
          hCone B hSkew hPerfect hInv hNeutralB hR hNE d2 w hbig with ⟨p5⟩
      exact Or.inr
        (c8Fallback_fourFiveCycleBranch_of_equationPack
          (D := D) (B := B) hSkew (Or.inr ⟨p5⟩))

/-- Case-1 partition entrypoint:
construct a hull witness then branch to C.8.3 or C.8.4. -/
theorem c8Fallback_branchSplit_of_case1_partition
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (_hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (d1 : C8Case1OrbitPartitionData X) :
    C8BranchSplitHypothesis (D := D) (B := B) := by
  rcases c8Fallback_case1_exists_hullWitness
      (nu := nu) (R := R) (D := D)
      hCone B hSkew _hPerfect hInv hNeutralB hR hNE d1 with ⟨w⟩
  exact c8Fallback_case1_branchSplit_of_hullWitness
    (nu := nu) (R := R) (D := D)
    hCone B hSkew _hPerfect hInv hNeutralB hR hNE d1 w

/-- Case-2 partition entrypoint:
construct a hull witness then branch to C.8.3 or C.8.4. -/
theorem c8Fallback_branchSplit_of_case2_partition
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (_hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (d2 : C8Case2OrbitPartitionData X) :
    C8BranchSplitHypothesis (D := D) (B := B) := by
  rcases c8Fallback_case2_exists_hullWitness
      (nu := nu) (R := R) (D := D)
      hCone B hSkew _hPerfect hInv hNeutralB hR hNE d2 with ⟨w⟩
  exact c8Fallback_case2_branchSplit_of_hullWitness
    (nu := nu) (R := R) (D := D)
    hCone B hSkew _hPerfect hInv hNeutralB hR hNE d2 w

theorem c8Fallback_branchSplit_of_case1
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase1 : Fintype.card X % 3 = 1) :
    C8BranchSplitHypothesis (D := D) (B := B) := by
  rcases c8Case1OrbitPartitionData_of_case1 (X := X) hCardGtTwo hCase1 with ⟨d1⟩
  exact c8Fallback_branchSplit_of_case1_partition
    (nu := nu) (R := R) (D := D)
    hCone B hSkew hPerfect hInv hNeutralB hR hNE d1

theorem c8Fallback_branchSplit_of_case2
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hR : Reinforcement D (balanceRule (D := D) B))
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (hCardGtTwo : 2 < Fintype.card X)
    (hCase2 : Fintype.card X % 3 = 2) :
    C8BranchSplitHypothesis (D := D) (B := B) := by
  rcases c8Case2OrbitPartitionData_of_case2 (X := X) hCardGtTwo hCase2 with ⟨d2⟩
  exact c8Fallback_branchSplit_of_case2_partition
    (nu := nu) (R := R) (D := D)
    hCone B hSkew hPerfect hInv hNeutralB hR hNE d2

end C8Fallback

end Pivato
