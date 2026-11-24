import Pivato.Theorem2.C8Claims34

/-!
# Lemma C.8 claim C.8.5

This file isolates the transport step from one seed triple to global cocycle.
-/

namespace Pivato

section C8Claim5

universe uG uV uX uR

variable {G : Type uG} [Group G]
variable {V : Type uV} {X : Type uX} {R : Type uR}

/-- Distinct-triple transport property used in Claim C.8.5:
any distinct triple can be sent to a fixed seed triple by the `mu` action. -/
def TripleTransportTo
    (mu : G →* Equiv.Perm X) (x y z : X) : Prop :=
  ∀ x' y' z' : X, x' ≠ y' → y' ≠ z' → z' ≠ x' →
    ∃ g : G, (mu g) x' = x ∧ (mu g) y' = y ∧ (mu g) z' = z

/-- Claim C.8.5:
if one seed triple satisfies the cocycle identity, neutrality transports it to
all triples. -/
theorem claimC85_globalCocycle_of_seedTriple
    [Finite X] [Nonempty X]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (mu : G →* Equiv.Perm X) (nu : G →* Equiv.Perm V)
    {D : Domain V} (B : BalanceSystem R X V)
    (hInv : DomainInvariant nu D)
    (hSkew : BalanceSkew (B := B))
    (hNeutral : BalanceNeutral mu nu B)
    (hSeed :
      ∃ x y z : X,
        x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
          BalanceCocycleAtTriple D B x y z)
    (hTransport :
      ∀ x y z : X, x ≠ y → y ≠ z → z ≠ x →
        TripleTransportTo (mu := mu) x y z) :
    BalanceCocycleOn D B := by
  rcases hSeed with ⟨x, y, z, hxy, hyz, hzx, hSeedXYZ⟩
  have hDiag : ∀ a : X, ∀ d : NProfile V, balanceAt B a a d = (0 : R) := by
    intro a d
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
  have hToSeed : TripleTransportTo (mu := mu) x y z :=
    hTransport x y z hxy hyz hzx
  intro d hd x' y' z'
  by_cases hxy' : x' = y'
  · subst y'
    simp [hDiag x' d]
  · by_cases hyz' : y' = z'
    · subst z'
      simp [hDiag y' d]
    · by_cases hzx' : z' = x'
      · subst z'
        calc
          balanceAt B x' y' d + balanceAt B y' x' d
              = balanceAt B x' y' d + (-balanceAt B x' y' d) := by
                  simp [hSkew y' x' d]
          _ = 0 := by simp
          _ = balanceAt B x' x' d := by simp [hDiag x' d]
      · rcases hToSeed x' y' z' hxy' hyz' hzx' with ⟨g, hgx, hgy, hgz⟩
        have hperm :
            balanceAt B x y (permuteNProfile (nu g) d) +
              balanceAt B y z (permuteNProfile (nu g) d) =
              balanceAt B x z (permuteNProfile (nu g) d) := by
          exact hSeedXYZ (d := permuteNProfile (nu g) d) (hInv g hd)
        have hxy_perm :
            balanceAt B x' y' d = balanceAt B x y (permuteNProfile (nu g) d) := by
          have hxy_base :
              balanceAt B ((mu g) x') ((mu g) y') (permuteNProfile (nu g) d) =
                balanceAt B x' y' d :=
            balanceAt_permute_of_balanceNeutral
              (mu := mu) (nu := nu) (B := B) hNeutral g x' y' d
          simpa [hgx, hgy] using hxy_base.symm
        have hyz_perm :
            balanceAt B y' z' d = balanceAt B y z (permuteNProfile (nu g) d) := by
          have hyz_base :
              balanceAt B ((mu g) y') ((mu g) z') (permuteNProfile (nu g) d) =
                balanceAt B y' z' d :=
            balanceAt_permute_of_balanceNeutral
              (mu := mu) (nu := nu) (B := B) hNeutral g y' z' d
          simpa [hgy, hgz] using hyz_base.symm
        have hxz_perm :
            balanceAt B x' z' d = balanceAt B x z (permuteNProfile (nu g) d) := by
          have hxz_base :
              balanceAt B ((mu g) x') ((mu g) z') (permuteNProfile (nu g) d) =
                balanceAt B x' z' d :=
            balanceAt_permute_of_balanceNeutral
              (mu := mu) (nu := nu) (B := B) hNeutral g x' z' d
          simpa [hgx, hgz] using hxz_base.symm
        calc
          balanceAt B x' y' d + balanceAt B y' z' d
              = balanceAt B x y (permuteNProfile (nu g) d) +
                  balanceAt B y z (permuteNProfile (nu g) d) := by
                    simp [hxy_perm, hyz_perm]
          _ = balanceAt B x z (permuteNProfile (nu g) d) := hperm
          _ = balanceAt B x' z' d := hxz_perm.symm

/-- Pipeline wrapper: combine Claims C.8.3/C.8.4 branch outputs into the seed
triple form expected by Claim C.8.5. -/
theorem claimC85_globalCocycle_of_branchSplit
    [Finite X] [Nonempty X]
    [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    (mu : G →* Equiv.Perm X) (nu : G →* Equiv.Perm V)
    {D : Domain V} (B : BalanceSystem R X V)
    (hInv : DomainInvariant nu D)
    (hSkew : BalanceSkew (B := B))
    (hNeutral : BalanceNeutral mu nu B)
    (hSeedFromC83orC84 :
      ∃ x y z : X,
        x ≠ y ∧ y ≠ z ∧ z ≠ x ∧
          BalanceCocycleAtTriple D B x y z)
    (hTransport :
      ∀ x y z : X, x ≠ y → y ≠ z → z ≠ x →
        TripleTransportTo (mu := mu) x y z) :
    BalanceCocycleOn D B := by
  exact claimC85_globalCocycle_of_seedTriple
    (mu := mu) (nu := nu) (B := B) hInv hSkew hNeutral
    hSeedFromC83orC84 hTransport

end C8Claim5

end Pivato
