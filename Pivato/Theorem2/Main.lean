import Pivato.Theorem2.C8Orbit
import Pivato.Theorem1.Main

/-!
# Theorem 2

This file assembles the proof pipeline into a final biconditional Theorem 2:
a voting rule on a cone domain satisfies neutrality and reinforcement if and
only if it is representable as a neutral scoring rule.
-/

namespace Pivato

universe uV uX

section Theorem2

variable {G : Type*} [Group G]
variable {V : Type uV} {X : Type uX}
variable (mu : G →* Equiv.Perm X) (nu : G →* Equiv.Perm V)
variable {D : Domain V} (F : RuleOn D X)

/-- Theorem-2 target predicate: `F` is representable by some linearly ordered
additive codomain with a `mu`/`nu`-neutral score system. -/
def IsNeutralScoringRepresentable : Prop :=
  ∃ (R : Type (max uV uX)),
    ∃ (instAdd : AddCommGroup R),
    ∃ (instLin : LinearOrder R),
    ∃ (instOrdCancel : IsOrderedCancelAddMonoid R),
    ∃ S : ScoreSystem R X V,
      letI : AddCommGroup R := instAdd
      letI : LinearOrder R := instLin
      letI : IsOrderedCancelAddMonoid R := instOrdCancel
      ScoreNeutral mu nu S ∧ F = scoringRule (D := D) S

private theorem scoringRule_reinforcement_of_isCone
    [DecidableEq V]
    {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
    {D : Domain V} (hCone : IsCone D) (S : ScoreSystem R X V) :
    Reinforcement D (scoringRule (D := D) S) := by
  refine ⟨?_, ?_⟩
  · intro d e hd he _hinter
    exact hCone.1 hd he
  · intro d e hd he hsum hinter
    apply Set.Subset.antisymm
    · intro x hx
      rcases hinter with ⟨z, hzD, hzE⟩
      constructor
      · intro y
        have hyzD : scoreAt S y d ≤ scoreAt S z d := hzD y
        have hzxSum :
            scoreAt S z (d + e) ≤ scoreAt S x (d + e) := hx z
        have hzxSum' :
            scoreAt S z d + scoreAt S z e ≤
              scoreAt S x d + scoreAt S x e := by
          simpa [scoreAt_add (S := S)] using hzxSum
        have hxeLeZe : scoreAt S x e ≤ scoreAt S z e := hzE x
        have hzdLeXd : scoreAt S z d ≤ scoreAt S x d := by
          have hFirst :
              scoreAt S z d + scoreAt S x e ≤
                scoreAt S z d + scoreAt S z e := by
            simpa [add_assoc, add_left_comm, add_comm] using
              (add_le_add_left hxeLeZe (scoreAt S z d))
          have hAux :
              scoreAt S z d + scoreAt S x e ≤
                scoreAt S x d + scoreAt S x e := by
            exact
              le_trans
                hFirst
                hzxSum'
          exact (add_le_add_iff_right (scoreAt S x e)).1 hAux
        exact le_trans hyzD hzdLeXd
      · intro y
        have hyzE : scoreAt S y e ≤ scoreAt S z e := hzE y
        have hzxSum :
            scoreAt S z (d + e) ≤ scoreAt S x (d + e) := hx z
        have hzxSum' :
            scoreAt S z d + scoreAt S z e ≤
              scoreAt S x d + scoreAt S x e := by
          simpa [scoreAt_add (S := S)] using hzxSum
        have hxdLeZd : scoreAt S x d ≤ scoreAt S z d := hzD x
        have hzeLeXe : scoreAt S z e ≤ scoreAt S x e := by
          have hFirst :
              scoreAt S x d + scoreAt S z e ≤
                scoreAt S z d + scoreAt S z e := by
            simpa [add_assoc, add_left_comm, add_comm] using
              (add_le_add_right hxdLeZd (scoreAt S z e))
          have hAux :
              scoreAt S x d + scoreAt S z e ≤
                scoreAt S x d + scoreAt S x e := by
            exact
              le_trans
                hFirst
                hzxSum'
          exact (add_le_add_iff_left (scoreAt S x d)).1 hAux
        exact le_trans hyzE hzeLeXe
    · intro x hx y
      have hyd : scoreAt S y d ≤ scoreAt S x d := hx.1 y
      have hye : scoreAt S y e ≤ scoreAt S x e := hx.2 y
      have hsumLe :
          scoreAt S y d + scoreAt S y e ≤
            scoreAt S x d + scoreAt S x e :=
        add_le_add hyd hye
      simpa [scoreAt_add (S := S)] using hsumLe

/-- Theorem 2 backward direction:
neutral scoring representability implies neutrality and reinforcement under
domain invariance and cone-domain closure. -/
theorem theorem2_backward
    [Finite X] [Nonempty X] [DecidableEq V]
    (hCone : IsCone D)
    (hInv : DomainInvariant nu D)
    (hScore :
      IsNeutralScoringRepresentable (mu := mu) (nu := nu) (D := D) (F := F)) :
    RuleNeutral mu nu D F ∧ Reinforcement D F := by
  rcases hScore with ⟨R, instAdd, instLin, instOrdCancel, S, hSNeutral, hFS⟩
  let : AddCommGroup R := instAdd
  let : LinearOrder R := instLin
  let : IsOrderedCancelAddMonoid R := instOrdCancel
  have hNeutralS : RuleNeutral mu nu D (scoringRule (D := D) S) :=
    scoringRule_ruleNeutral_of_scoreNeutral
      (mu := mu) (nu := nu) (S := S) hInv hSNeutral
  have hRS : Reinforcement D (scoringRule (D := D) S) :=
    scoringRule_reinforcement_of_isCone (X := X) (hCone := hCone) S
  refine ⟨?_, ?_⟩
  · simpa [hFS] using hNeutralS
  · simpa [hFS] using hRS

end Theorem2

section Theorem2

variable {V : Type uV} {X : Type uX}
variable (nu : Equiv.Perm X →* Equiv.Perm V)
variable {D : Domain V} (F : RuleOn D X)

/-- Theorem 2 forward direction:
neutrality + reinforcement imply neutral scoring representability. -/
theorem theorem2_forward
    [Finite X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hCone : IsCone D) (hA : GeneralAbstention D F)
    (hNE : NonemptyOnDomain D F)
    (hNeutral : RuleNeutral (MonoidHom.id (Equiv.Perm X)) nu D F)
    (hR : Reinforcement D F) :
    IsNeutralScoringRepresentable
      (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (D := D) (F := F) := by
  rcases lemmaC1_reinforcement_to_isPerfectSkewBalanceRepresentable
      (F := F) hD hA hR hNE with
      ⟨R, instAdd, instLin, instCovLe, instCovLt, B, hSkew, hPerfect, hFB⟩
  let : AddCommGroup R := instAdd
  let : LinearOrder R := instLin
  let : CovariantClass R R (fun a b => a + b) (· ≤ ·) := instCovLe
  let : CovariantClass R R (fun a b => a + b) (· < ·) := instCovLt
  let instOrdCancel : IsOrderedCancelAddMonoid R :=
    IsOrderedCancelAddMonoid.of_add_lt_add_left
      (fun a b c hbc => by
        simpa [add_assoc, add_left_comm, add_comm] using add_lt_add_left hbc a)
  let : IsOrderedCancelAddMonoid R := instOrdCancel
  have hRep :
      ∃ B0 : BalanceSystem R X V,
        BalanceSkew (B := B0) ∧
          PerfectOn (D := D) (B := B0) ∧
          F = balanceRule (D := D) B0 :=
    ⟨B, hSkew, hPerfect, hFB⟩
  rcases lemmaC8_of_representation
      (nu := nu) (R := R) (D := D) (F := F)
      hCone hRep hNeutral hNE with
      ⟨S, hSNeutral, hFS⟩
  exact ⟨R, instAdd, instLin, instOrdCancel, S, hSNeutral, hFS⟩

/-- Theorem 2: a voting rule satisfies neutrality and reinforcement on a cone
domain if and only if it is a neutral scoring rule. -/
theorem theorem2
    [Finite X] [Nonempty X] [DecidableEq X] [DecidableEq V]
    (hD : IsDomain D) (hCone : IsCone D) (hA : GeneralAbstention D F)
    (hInv : DomainInvariant nu D)
    (hNE : NonemptyOnDomain D F) :
    (RuleNeutral (MonoidHom.id (Equiv.Perm X)) nu D F ∧ Reinforcement D F) ↔
      IsNeutralScoringRepresentable
        (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (D := D) (F := F) := by
  constructor
  · intro h
    exact theorem2_forward (nu := nu) (F := F)
      hD hCone hA hNE h.1 h.2
  · intro hScore
    exact theorem2_backward
      (mu := MonoidHom.id (Equiv.Perm X)) (nu := nu) (F := F)
      hCone hInv hScore

end Theorem2

end Pivato
