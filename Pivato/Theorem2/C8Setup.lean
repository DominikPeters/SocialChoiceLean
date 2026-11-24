import Pivato.Theorem2.C6_C7
import Pivato.Neutrality.Main

/-!
# Lemma C.8 setup layer

This file contains shared definitions/interfaces for the long C.8 proof:
- orbit-summed profiles `d^φ`,
- block-filtered profile domains `D_n^φ`,
- local/global cocycle predicates.
-/

namespace Pivato

section C8Setup

universe uV uX uR

variable {V : Type uV} {X : Type uX} {R : Type uR}

/-- Orbit-summed profile
`d + φ(d) + ⋯ + φ^M(d)` over signal permutations. -/
noncomputable def orbitProfileSum (φ : Equiv.Perm V) (M : ℕ) (d : NProfile V) : NProfile V :=
  Finset.sum (Finset.range (M + 1)) (fun k => permuteNProfile (φ ^ k) d)

/-- Additivity of orbit-profile summation (setup lemma for Claim C.8.1). -/
theorem orbitProfileSum_add
    (φ : Equiv.Perm V) (M : ℕ) (d e : NProfile V) :
    orbitProfileSum φ M (d + e) = orbitProfileSum φ M d + orbitProfileSum φ M e := by
  simp [orbitProfileSum, Finset.sum_add_distrib]

/-- Compatibility of orbit-profile summation with scalar multiplication
(setup lemma for Claim C.8.1). -/
theorem orbitProfileSum_nsmul
    (φ : Equiv.Perm V) (M : ℕ) (n : ℕ) (d : NProfile V) :
    orbitProfileSum φ M (n • d) = n • orbitProfileSum φ M d := by
  induction n with
  | zero =>
      simp [orbitProfileSum]
  | succ n ih =>
      simp [add_nsmul, ih, orbitProfileSum_add, one_nsmul]

/-- Block-filtered orbit domain:
profiles whose orbit-sum winners contain a designated block. -/
def orbitBlockDomain
    (D : Domain V) (F : RuleOn D X)
    (orbitMap : NProfile V → NProfile V)
    (horbit : ∀ {d : NProfile V}, d ∈ D → orbitMap d ∈ D)
    (block : Set X) : Domain V :=
  {d | ∃ hd : d ∈ D, block ⊆ F ⟨orbitMap d, horbit hd⟩}

@[simp] theorem mem_orbitBlockDomain_iff
    {D : Domain V} {F : RuleOn D X}
    (orbitMap : NProfile V → NProfile V)
    (horbit : ∀ {d : NProfile V}, d ∈ D → orbitMap d ∈ D)
    (block : Set X) (d : NProfile V) :
    d ∈ orbitBlockDomain D F orbitMap horbit block ↔
      ∃ hd : d ∈ D, block ⊆ F ⟨orbitMap d, horbit hd⟩ := by
  rfl

/-- Triple-local cocycle form used in Claims C.8.3/C.8.4. -/
def BalanceCocycleAtTriple [AddCommMonoid R]
    (D : Domain V) (B : BalanceSystem R X V) (x y z : X) : Prop :=
  ∀ ⦃d : NProfile V⦄, d ∈ D →
    balanceAt B x y d + balanceAt B y z d = balanceAt B x z d

/-- Local cocycle follows from global cocycle. -/
theorem balanceCocycleAtTriple_of_balanceCocycleOn
    [AddCommMonoid R]
    {D : Domain V} {B : BalanceSystem R X V}
    {x y z : X}
    (hCocycle : BalanceCocycleOn D B) :
    BalanceCocycleAtTriple D B x y z := by
  intro d hd
  exact hCocycle hd x y z

end C8Setup

end Pivato
