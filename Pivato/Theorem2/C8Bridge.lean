import Pivato.Theorem2.C8Fallback
import Pivato.Theorem1.Representation
import Mathlib.Tactic.IntervalCases

/-!
# Lemma C.8 bridge assembly

This file centralizes the paper-facing C.8 bridge ingredients:
- a small-card cocycle shortcut (`|X| ≤ 2`);
- the large-card bridge target producing Eq. (C.21)-style cycle-sum data.
-/

namespace Pivato

section C8Bridge

universe uV uX

variable {V : Type uV} {X : Type uX} {R : Type*}
variable (nu : Equiv.Perm X →* Equiv.Perm V)

lemma no_three_distinct_of_card_le_two
    [Fintype X]
    (hCard : Fintype.card X ≤ 2) :
    ¬ ∃ x y z : X, x ≠ y ∧ x ≠ z ∧ y ≠ z := by
  intro hThree
  have hgt : 2 < Fintype.card X := (Fintype.two_lt_card_iff).2 hThree
  exact not_lt_of_ge hCard hgt

lemma balanceAt_diag_eq_zero_of_skew
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (a : X) (d : NProfile V) :
    balanceAt B a a d = (0 : R) := by
  let t : R := balanceAt B a a d
  have hsk : t = -t := by
    simpa [t] using (hSkew a a d)
  have hsum : t + t = 0 := by
    calc
      t + t = t + (-t) := by
        nth_rewrite 2 [hsk]
        rfl
      _ = 0 := by simp
  have ht0 : t = 0 :=
    (nsmul_eq_zero_iff_right two_ne_zero).1 (by simpa [two_nsmul] using hsum)
  simpa [t] using ht0

lemma balanceCocycleOn_of_skew_card_le_two
    [Fintype X]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hCard : Fintype.card X ≤ 2) :
    BalanceCocycleOn D B := by
  have hNoThree : ¬ ∃ x y z : X, x ≠ y ∧ x ≠ z ∧ y ≠ z :=
    no_three_distinct_of_card_le_two (X := X) hCard
  intro d hd x y z
  by_cases hxy : x = y
  · subst y
    simp [balanceAt_diag_eq_zero_of_skew (B := B) hSkew x d]
  · by_cases hyz : y = z
    · subst z
      simp [balanceAt_diag_eq_zero_of_skew (B := B) hSkew y d]
    · by_cases hzx : z = x
      · subst z
        calc
          balanceAt B x y d + balanceAt B y x d
              = balanceAt B x y d + (-balanceAt B x y d) := by
                  simp [hSkew y x d]
          _ = 0 := by simp
          _ = balanceAt B x x d := by
              simp [balanceAt_diag_eq_zero_of_skew (B := B) hSkew x d]
      · exfalso
        apply hNoThree
        refine ⟨x, y, z, hxy, ?_, hyz⟩
        intro hxz
        exact hzx hxz.symm

/-- Step 1 (C.8 bridge):
derive reinforcement for `balanceRule B` from cone + skew + perfectness. -/
theorem c8Bridge_step1_reinforcement_of_neutral_perfect_balance
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B)) :
    Reinforcement D (balanceRule (D := D) B) := by
  have hWA : WeaklyAdditive D (balanceRule (D := D) B) := by
    intro d e hd he _hinter
    exact hCone.1 hd he
  exact balanceRule_reinforcement_of_perfect
    (D := D) (B := B) hWA hSkew hPerfect

/-- Step 2 TODO (C.8 bridge, case 0):
build the three-cycle branch hypothesis in the `card % 3 = 0` regime. -/
theorem c8Bridge_step2_threeCycleBranch_of_case0
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
    (_hCardGtTwo : 2 < Fintype.card X)
    (hCase0 : Fintype.card X % 3 = 0) :
    C8ThreeCycleBranchHypothesis (D := D) (B := B) := by
  classical
  obtain ⟨φ, hPow, hNoFix⟩ :
      ∃ φ : Equiv.Perm X, φ ^ 3 = 1 ∧ ∀ x : X, φ x ≠ x :=
    c8ExistsPerm_pow_three_no_fixed_of_card_mod_three_eq_zero
      (X := X) hCase0
  let orbitMap : NProfile V → NProfile V := orbitProfileSum (nu φ) 2
  have horbit : ∀ {d : NProfile V}, d ∈ D → orbitMap d ∈ D := by
    intro d hd
    exact orbitProfileSum_mem_of_domainInvariant
      (D := D) hCone nu hInv φ hd 2
  obtain ⟨K, hHullD⟩ :
      ∃ K : AddSubgroup (ZProfile V), IsDivisibleHull (domainImageZ D) K :=
    exists_divisibleHull (A := ZProfile V) (S := domainImageZ D)
  choose Kx hHullBlocks using
    (fun x : X =>
      exists_divisibleHull
        (A := ZProfile V)
        (S :=
          domainImageZ
            (orbitBlockDomain D (balanceRule (D := D) B)
              orbitMap horbit (orbitSet φ x))))
  rcases exists_orbitSet_hull_eq_of_neutral_balance
      (D := D) (R := R) hCone B hR nu hInv hNeutralB hNE
      φ 2 (by simpa using hPow)
      K Kx hHullD hHullBlocks with
      ⟨x0, hHullEq⟩
  let c3 : C8Cycle3OrbitData X :=
    c8Cycle3OrbitData_of_powThree_noFixed
      (X := X) φ hPow hNoFix x0
  rcases cycleSumHypothesis_of_threeCycle_orbitBlock_hullEq
      (D := D) (B := B) hSkew nu hNeutralB φ
      (M := 2) (hThreeDiv := by decide) horbit
      c3.hxy c3.hyz c3.hzx c3.hφx c3.hφy c3.hφz
      K (Kx x0) hHullD (hHullBlocks x0) hHullEq with
      ⟨x, y, z, hxy, hyz, hzx, hsum⟩
  exact ⟨x, y, z, hxy, hyz, hzx, hsum⟩

/-- Step 3 (C.8 bridge, cases 1/2):
build branch-split hypothesis in the `card % 3 = 1` or `2` regimes via
the C.8.4 fallback module. -/
theorem c8Bridge_step3_case1_branchSplit
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
  exact c8Fallback_branchSplit_of_case1
    (nu := nu) (R := R) (D := D)
    hCone B hSkew hPerfect hInv hNeutralB hR hNE hCardGtTwo hCase1

theorem c8Bridge_step3_case2_branchSplit
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
  exact c8Fallback_branchSplit_of_case2
    (nu := nu) (R := R) (D := D)
    hCone B hSkew hPerfect hInv hNeutralB hR hNE hCardGtTwo hCase2

theorem c8Bridge_step3_branchSplit_of_cases12
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
    (hCase12 : Fintype.card X % 3 = 1 ∨ Fintype.card X % 3 = 2) :
    C8BranchSplitHypothesis (D := D) (B := B) := by
  rcases hCase12 with hCase1 | hCase2
  · exact c8Bridge_step3_case1_branchSplit
      (nu := nu) (R := R) (D := D)
      hCone B hSkew hPerfect hInv hNeutralB hR hNE hCardGtTwo hCase1
  · exact c8Bridge_step3_case2_branchSplit
      (nu := nu) (R := R) (D := D)
      hCone B hSkew hPerfect hInv hNeutralB hR hNE hCardGtTwo hCase2

/-- Step 4 (C.8 bridge):
assemble the global branch split from the cardinal-case partition and steps 2/3. -/
theorem c8Bridge_step4_branchSplit_of_neutral_perfect_balance
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (hCardGtTwo : 2 < Fintype.card X) :
    C8BranchSplitHypothesis (D := D) (B := B) := by
  have hR : Reinforcement D (balanceRule (D := D) B) :=
    c8Bridge_step1_reinforcement_of_neutral_perfect_balance
      (R := R) (D := D) hCone B hSkew hPerfect
  have hCases :
      Fintype.card X % 3 = 0 ∨
        Fintype.card X % 3 = 1 ∨ Fintype.card X % 3 = 2 := by
    have hlt : Fintype.card X % 3 < 3 := Nat.mod_lt _ (by decide : 0 < 3)
    interval_cases hmod : Fintype.card X % 3 <;> simp
  rcases hCases with hCase0 | hCase12
  · exact Or.inl
      (c8Bridge_step2_threeCycleBranch_of_case0
        (nu := nu) (R := R) (D := D)
        hCone B hSkew hPerfect hInv hNeutralB hR hNE hCardGtTwo hCase0)
  · exact c8Bridge_step3_branchSplit_of_cases12
      (nu := nu) (R := R) (D := D)
      hCone B hSkew hPerfect hInv hNeutralB hR hNE hCardGtTwo hCase12

/-- Core C.8 bridge target in the large-card regime `|X| > 2`. -/
theorem c8CycleSumHypothesis_of_neutral_perfect_balance
    [Finite X] [Fintype X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V}
    (hCone : IsCone D)
    (B : BalanceSystem R X V)
    (hSkew : BalanceSkew (B := B))
    (hPerfect : PerfectOn (D := D) (B := B))
    (hInv : DomainInvariant nu D)
    (hNeutralB : BalanceNeutral (MonoidHom.id (Equiv.Perm X)) nu B)
    (hNE : NonemptyOnDomain D (balanceRule (D := D) B))
    (hCardGtTwo : 2 < Fintype.card X) :
    C8CycleSumHypothesis (D := D) (B := B) := by
  exact cycleSumHypothesis_of_branchSplit (D := D) (B := B)
    (c8Bridge_step4_branchSplit_of_neutral_perfect_balance
      (nu := nu) (R := R) (D := D)
      hCone B hSkew hPerfect hInv hNeutralB hNE hCardGtTwo)

end C8Bridge

end Pivato
