import Pivato.AppendixB
import Pivato.Balance
import Mathlib.Algebra.Order.Group.Unbundled.Basic

/-!
# Appendix C.4 and C.5 core lemmas

This file formalizes the balance/scoring cocycle bridge used downstream in the
Lemma C.8 pipeline:
- C.4-style equivalence between scoring and cocycle-balanced representations;
- C.5-style divisible-hull propagation for additive homomorphisms.
-/

namespace Pivato

section C4_C5

universe uA uR uV uX

variable {V : Type uV} {X : Type uX} {R : Type uR}

/-- Appendix C.8 additivity condition for a balance system on a domain:
`b^{x,y}(d) + b^{y,z}(d) = b^{x,z}(d)` for all `x,y,z` and `d ∈ D`. -/
def BalanceCocycleOn [AddCommMonoid R]
    (D : Domain V) (B : BalanceSystem R X V) : Prop :=
  ∀ ⦃d : NProfile V⦄, d ∈ D →
    ∀ x y z : X,
      balanceAt B x y d + balanceAt B y z d = balanceAt B x z d

lemma balanceAt_scoreToBalance
    [AddCommGroup R]
    (S : ScoreSystem R X V) (x y : X) (d : NProfile V) :
    balanceAt (scoreToBalance S) x y d = scoreAt S x d - scoreAt S y d := by
  unfold balanceAt scoreAt scoreToBalance evalNat
  calc
    (Finsupp.sum d fun v n => n • (S.score x v - S.score y v))
        = (Finsupp.sum d fun v n => (n • S.score x v) - (n • S.score y v)) := by
          apply Finsupp.sum_congr
          intro a _ha
          exact nsmul_sub (S.score x a) (S.score y a) (d a)
    _ = (Finsupp.sum d fun v n => n • S.score x v) -
          (Finsupp.sum d fun v n => n • S.score y v) := by
          simp

lemma scoringRule_eq_balanceRule_scoreToBalance
    [AddCommGroup R] [Preorder R] [AddRightMono R]
    {D : Domain V} (S : ScoreSystem R X V) :
    scoringRule (D := D) S = balanceRule (D := D) (scoreToBalance S) := by
  funext d
  ext x
  constructor
  · intro hx y
    have hyx : scoreAt S y d.1 ≤ scoreAt S x d.1 := hx y
    have hnonneg : 0 ≤ scoreAt S x d.1 - scoreAt S y d.1 := (sub_nonneg).2 hyx
    simpa [balanceAt_scoreToBalance (S := S) (x := x) (y := y) (d := d.1)] using hnonneg
  · intro hx y
    have hnonneg : 0 ≤ balanceAt (scoreToBalance S) x y d.1 := hx y
    exact (sub_nonneg).1 (by
      simpa [balanceAt_scoreToBalance (S := S) (x := x) (y := y) (d := d.1)] using hnonneg)

/-- C.4 forward direction:
a scoring rule induces a balance rule satisfying the cocycle condition. -/
theorem lemmaC4_forward
    [AddCommGroup R] [Preorder R] [AddRightMono R]
    {D : Domain V} (S : ScoreSystem R X V) :
    ∃ B : BalanceSystem R X V,
      BalanceCocycleOn D B ∧
        scoringRule (D := D) S = balanceRule (D := D) B := by
  refine ⟨scoreToBalance S, ?_, ?_⟩
  · intro d hd x y z
    calc
      balanceAt (scoreToBalance S) x y d + balanceAt (scoreToBalance S) y z d
          = (scoreAt S x d - scoreAt S y d) + (scoreAt S y d - scoreAt S z d) := by
              simp [balanceAt_scoreToBalance]
      _ = scoreAt S x d - scoreAt S z d := by
              exact sub_add_sub_cancel (scoreAt S x d) (scoreAt S y d) (scoreAt S z d)
      _ = balanceAt (scoreToBalance S) x z d := by
              simp [balanceAt_scoreToBalance]
  · exact scoringRule_eq_balanceRule_scoreToBalance (S := S)

/-- C.4 backward direction:
a balance rule satisfying the cocycle condition admits a scoring
representation (fixing one reference alternative). -/
theorem lemmaC4_backward
    [AddCommGroup R] [Preorder R] [AddRightMono R] [Nonempty X]
    {D : Domain V} (B : BalanceSystem R X V)
    (hC8 : BalanceCocycleOn D B) :
    ∃ S : ScoreSystem R X V,
      balanceRule (D := D) B = scoringRule (D := D) S := by
  classical
  let o : X := Classical.choice ‹Nonempty X›
  let S : ScoreSystem R X V := {
    score := fun x v => B.bal x o v
  }
  refine ⟨S, ?_⟩
  funext d
  ext x
  constructor
  · intro hx y
    have hxy_nonneg : 0 ≤ balanceAt B x y d.1 := hx y
    have hxy_eq : balanceAt B x y d.1 = balanceAt B x o d.1 - balanceAt B y o d.1 :=
      (eq_sub_iff_add_eq).2 (hC8 d.2 x y o)
    have hnonneg' : 0 ≤ balanceAt B x o d.1 - balanceAt B y o d.1 := by
      simpa [hxy_eq] using hxy_nonneg
    have hyx_le : balanceAt B y o d.1 ≤ balanceAt B x o d.1 := (sub_nonneg).1 hnonneg'
    simpa [S, scoreAt, balanceAt] using hyx_le
  · intro hx y
    have hyx_le : scoreAt S y d.1 ≤ scoreAt S x d.1 := hx y
    have hnonneg' : 0 ≤ balanceAt B x o d.1 - balanceAt B y o d.1 := by
      exact (sub_nonneg).2 (by simpa [S, scoreAt, balanceAt] using hyx_le)
    have hdiff_eq : balanceAt B x o d.1 - balanceAt B y o d.1 = balanceAt B x y d.1 :=
      ((eq_sub_iff_add_eq).2 (hC8 d.2 x y o)).symm
    simpa [hdiff_eq] using hnonneg'

/-- Lemma C.4 (packaged):
`F` is scoring iff `F` is balance-representable by a system satisfying C.8. -/
theorem lemmaC4
    [AddCommGroup R] [Preorder R] [AddRightMono R] [Nonempty X]
    {D : Domain V} {F : RuleOn D X} :
    (∃ S : ScoreSystem R X V, F = scoringRule (D := D) S) ↔
      ∃ B : BalanceSystem R X V,
        BalanceCocycleOn D B ∧ F = balanceRule (D := D) B := by
  constructor
  · intro hScore
    rcases hScore with ⟨S, hFS⟩
    rcases lemmaC4_forward (D := D) S with ⟨B, hC8, hEq⟩
    refine ⟨B, hC8, ?_⟩
    calc
      F = scoringRule (D := D) S := hFS
      _ = balanceRule (D := D) B := hEq
  · intro hBal
    rcases hBal with ⟨B, hC8, hFB⟩
    rcases lemmaC4_backward (D := D) B hC8 with ⟨S, hEq⟩
    refine ⟨S, ?_⟩
    calc
      F = balanceRule (D := D) B := hFB
      _ = scoringRule (D := D) S := hEq

variable {A : Type uA} {R' : Type uR}

/-- `K` is the divisible hull of `S` when it is divisible, contains `S`, and is
minimal among divisible subgroups containing `S`. -/
def IsDivisibleHull [AddCommGroup A] (S : Set A) (K : AddSubgroup A) : Prop :=
  IsDivisibleSubgroup K ∧
    S ⊆ K ∧
      ∀ L : AddSubgroup A, IsDivisibleSubgroup L → S ⊆ L → K ≤ L

lemma IsDivisibleHull.eq
    [AddCommGroup A] {S : Set A} {K L : AddSubgroup A}
    (hK : IsDivisibleHull S K) (hL : IsDivisibleHull S L) :
    K = L := by
  rcases hK with ⟨hKDiv, hSsubK, hKmin⟩
  rcases hL with ⟨hLDiv, hSsubL, hLmin⟩
  exact le_antisymm (hKmin L hLDiv hSsubL) (hLmin K hKDiv hSsubK)

/-- Existence of a divisible hull for any subset of an additive commutative
group, as the infimum of all divisible subgroups containing the subset. -/
theorem exists_divisibleHull
    [AddCommGroup A] (S : Set A) :
    ∃ K : AddSubgroup A, IsDivisibleHull S K := by
  let C : Set (AddSubgroup A) := {L | IsDivisibleSubgroup L ∧ S ⊆ (L : Set A)}
  let K : AddSubgroup A := sInf C
  have hKDiv : IsDivisibleSubgroup K := by
    intro a n hn hna
    rw [AddSubgroup.mem_sInf] at hna ⊢
    intro L hLC
    exact hLC.1 hn (hna L hLC)
  have hSsubK : S ⊆ (K : Set A) := by
    intro s hs
    change s ∈ (sInf C : AddSubgroup A)
    rw [AddSubgroup.mem_sInf]
    intro L hLC
    exact hLC.2 hs
  have hKmin : ∀ L : AddSubgroup A, IsDivisibleSubgroup L → S ⊆ (L : Set A) → K ≤ L := by
    intro L hLDiv hSsubL
    exact sInf_le ⟨hLDiv, hSsubL⟩
  exact ⟨K, hKDiv, hSsubK, hKmin⟩

/-- Lemma C.5 (hull form):
if a homomorphism into a torsion-free codomain vanishes on `S`, then it
vanishes on the divisible hull of `S`. -/
theorem lemmaC5
    [AddCommGroup A] [AddCommGroup R'] [IsAddTorsionFree R']
    (φ : A →+ R') (S : Set A) (K : AddSubgroup A)
    (hHull : IsDivisibleHull S K)
    (hZero : ∀ s, s ∈ S → φ s = 0) :
    ∀ a, a ∈ K → φ a = 0 := by
  rcases hHull with ⟨_hKDiv, _hSsubK, hKmin⟩
  let L : AddSubgroup A := φ.ker
  have hLDiv : IsDivisibleSubgroup L := by
    intro b n hn hnb
    have hnb0 : φ (n • b) = 0 :=
      (AddMonoidHom.mem_ker (f := φ) (x := n • b)).1 hnb
    have hphi0 : n • φ b = 0 := by
      simpa [map_nsmul] using hnb0
    have hb0 : φ b = 0 := (nsmul_eq_zero_iff_right hn).1 hphi0
    exact (AddMonoidHom.mem_ker (f := φ) (x := b)).2 hb0
  have hSsubL : S ⊆ L := by
    intro s hs
    exact (AddMonoidHom.mem_ker (f := φ) (x := s)).2 (hZero s hs)
  have hKleL : K ≤ L := hKmin L hLDiv hSsubL
  intro a haK
  exact (AddMonoidHom.mem_ker (f := φ) (x := a)).1 (hKleL haK)

end C4_C5

end Pivato
