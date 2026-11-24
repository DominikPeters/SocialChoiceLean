import Pivato.Scoring

/-!
# Balance semantics on count-profile domains
-/

namespace Pivato

section Balance

variable {V X R : Type*}

/-- A balance system records pairwise signal weights between alternatives. -/
structure BalanceSystem (R X V : Type*) where
  bal : X → X → V → R

section AddGroup

variable [AddCommGroup R]

/-- Canonical conversion from scores to pairwise balances (`s^x - s^y`). -/
def scoreToBalance (S : ScoreSystem R X V) : BalanceSystem R X V where
  bal x y v := S.score x v - S.score y v

lemma scoreToBalance_skew (S : ScoreSystem R X V) (x y : X) :
    (scoreToBalance S).bal x y = fun v => -((scoreToBalance S).bal y x v) := by
  funext v
  simp [scoreToBalance, sub_eq_add_neg]

end AddGroup

variable [AddCommMonoid R]

/-- Total pairwise balance value for profile `d`. -/
def balanceAt (B : BalanceSystem R X V) (x y : X) (d : NProfile V) : R :=
  evalNat (B.bal x y) d

variable [Preorder R] [Zero R] {D : Domain V}

/-- The balance correspondence: pairwise nonnegative against all opponents. -/
def balanceRule (B : BalanceSystem R X V) : RuleOn D X :=
  fun d => {x | ∀ y, (0 : R) ≤ balanceAt B x y d.1}

lemma mem_balanceRule_iff {B : BalanceSystem R X V}
    {d : {d : NProfile V // d ∈ D}} {x : X} :
    x ∈ balanceRule (D := D) B d ↔ ∀ y, (0 : R) ≤ balanceAt B x y d.1 :=
  Iff.rfl

omit [Preorder R] [Zero R] in
lemma balanceAt_add [DecidableEq V] (B : BalanceSystem R X V) (x y : X)
    (d e : NProfile V) :
    balanceAt B x y (d + e) = balanceAt B x y d + balanceAt B x y e :=
  evalNat_add (w := B.bal x y) d e

end Balance

end Pivato
