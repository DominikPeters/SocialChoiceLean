import Pivato.Neutrality.LemmaC2
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Proposition 1 (forward direction) for scoring rules

This file proves the direction:
`nu`-neutral score system `=>` `nu`-neutral induced scoring rule.
-/

namespace Pivato

section Proposition1

variable {G V X R : Type*} [Group G]
variable [AddCommMonoid R]
variable (mu : G →* Equiv.Perm X) (nu : G →* Equiv.Perm V)
variable (S : ScoreSystem R X V)

/-- Score transport under neutralizer actions (derived from Lemma C.2(a)). -/
lemma scoreAt_permute_of_scoreNeutral
    (hS : ScoreNeutral mu nu S) (g : G) (x : X) (d : NProfile V) :
    scoreAt S ((mu g) x) (permuteNProfile (nu g) d) = scoreAt S x d := by
  have hEval :
      evalNat (permuteWeight (nu g) (S.score ((mu g) x))) d = evalNat (S.score x) d := by
    exact congrArg (fun w => evalNat w d) (hS g x)
  calc
    scoreAt S ((mu g) x) (permuteNProfile (nu g) d)
        = evalNat (S.score ((mu g) x)) (permuteNProfile (nu g) d) := rfl
    _ = evalNat (permuteWeight (nu g) (S.score ((mu g) x))) d := by
      symm
      exact lemmaC2a_evalNat_permuteWeight (b := S.score ((mu g) x)) (n := d) (π := nu g)
    _ = evalNat (S.score x) d := hEval
    _ = scoreAt S x d := rfl

/-- Proposition 1 (`←` direction in the paper): neutral score systems induce neutral
scoring rules, assuming domain invariance under the signal action. -/
theorem scoringRule_ruleNeutral_of_scoreNeutral
    [Preorder R] {D : Domain V}
    (hInv : DomainInvariant nu D) (hS : ScoreNeutral mu nu S) :
    RuleNeutral mu nu D (scoringRule (D := D) S) := by
  refine ⟨hInv, ?_⟩
  intro g d hd
  ext x
  constructor
  · intro hx
    refine (mem_permuteSet_iff (π := mu g) (S := scoringRule (D := D) S ⟨d, hd⟩) (x := x)).2 ?_
    intro z
    have hx' :
        scoreAt S ((mu g) z) (permuteNProfile (nu g) d) ≤
          scoreAt S x (permuteNProfile (nu g) d) := hx ((mu g) z)
    calc
      scoreAt S z d = scoreAt S ((mu g) z) (permuteNProfile (nu g) d) := by
        symm
        exact scoreAt_permute_of_scoreNeutral (mu := mu) (nu := nu) (S := S) hS g z d
      _ ≤ scoreAt S x (permuteNProfile (nu g) d) := hx'
      _ = scoreAt S ((mu g).symm x) d := by
        simpa using
          (scoreAt_permute_of_scoreNeutral (mu := mu) (nu := nu) (S := S)
            hS g ((mu g).symm x) d)
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    intro z
    have hy' : scoreAt S ((mu g).symm z) d ≤ scoreAt S y d := hy ((mu g).symm z)
    calc
      scoreAt S z (permuteNProfile (nu g) d) = scoreAt S ((mu g).symm z) d := by
        simpa using
          (scoreAt_permute_of_scoreNeutral (mu := mu) (nu := nu) (S := S)
            hS g ((mu g).symm z) d)
      _ ≤ scoreAt S y d := hy'
      _ = scoreAt S ((mu g) y) (permuteNProfile (nu g) d) := by
        symm
        exact scoreAt_permute_of_scoreNeutral (mu := mu) (nu := nu) (S := S) hS g y d

end Proposition1

section Proposition1Converse

variable {G V X R : Type*} [Group G] [Fintype G]
variable [AddCommMonoid R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
variable (mu : G →* Equiv.Perm X) (nu : G →* Equiv.Perm V)

/-- Group-average score system used in the converse direction of Proposition 1. -/
noncomputable def averagedScoreSystem (S : ScoreSystem R X V) : ScoreSystem R X V where
  score x v := ∑ g : G, S.score ((mu g) x) ((nu g) v)

lemma nsmul_sum' {G R : Type*} [Fintype G] [AddCommMonoid R]
    (n : ℕ) (f : G → R) :
    n • (∑ g : G, f g) = ∑ g : G, n • f g :=
  (Finset.sum_nsmul _ _ _).symm

omit [Group G] [LinearOrder R] [IsOrderedCancelAddMonoid R] in
lemma evalNat_weight_sum (w : G → V → R) (d : NProfile V) :
    evalNat (fun v => ∑ g : G, w g v) d = ∑ g : G, evalNat (w g) d := by
  classical
  unfold evalNat
  simp only [Finsupp.sum]
  have hswap :
      (∑ x ∈ d.support, d x • ∑ g : G, w g x)
        = ∑ g : G, ∑ x ∈ d.support, d x • w g x := by
    calc
      (∑ x ∈ d.support, d x • ∑ g : G, w g x)
          = (∑ x ∈ d.support, ∑ g : G, d x • w g x) := by
              apply Finset.sum_congr rfl
              intro x hx
              exact nsmul_sum' (n := d x) (f := fun g => w g x)
      _ = ∑ g : G, ∑ x ∈ d.support, d x • w g x := by
              exact Finset.sum_comm
  simpa [Finsupp.sum] using hswap

omit [LinearOrder R] [IsOrderedCancelAddMonoid R] in
lemma scoreAt_averaged_eq_sum (S : ScoreSystem R X V) (x : X) (d : NProfile V) :
    scoreAt (averagedScoreSystem (mu := mu) (nu := nu) S) x d
      = ∑ g : G, scoreAt S ((mu g) x) (permuteNProfile (nu g) d) := by
  calc
    scoreAt (averagedScoreSystem (mu := mu) (nu := nu) S) x d
        = evalNat (fun v => ∑ g : G, S.score ((mu g) x) ((nu g) v)) d := rfl
    _ = ∑ g : G, evalNat (fun v => S.score ((mu g) x) ((nu g) v)) d :=
      evalNat_weight_sum (w := fun g v => S.score ((mu g) x) ((nu g) v)) d
    _ = ∑ g : G, scoreAt S ((mu g) x) (permuteNProfile (nu g) d) := by
      apply Finset.sum_congr rfl
      intro g _
      exact lemmaC2a_evalNat_permuteWeight (b := S.score ((mu g) x)) (n := d) (π := nu g)

omit [LinearOrder R] [IsOrderedCancelAddMonoid R] in
lemma averagedScoreSystem_scoreNeutral (S : ScoreSystem R X V) :
    ScoreNeutral mu nu (averagedScoreSystem (mu := mu) (nu := nu) S) := by
  intro g x
  funext v
  calc
    permuteWeight (nu g) ((averagedScoreSystem (mu := mu) (nu := nu) S).score ((mu g) x)) v
        = ∑ h : G, S.score ((mu h) ((mu g) x)) ((nu h) ((nu g) v)) := by
            simp [averagedScoreSystem, permuteWeight]
    _ = ∑ h : G, S.score ((mu (h * g)) x) ((nu (h * g)) v) := by
            refine Finset.sum_congr rfl ?_
            intro h hh
            simp [map_mul]
    _ = ∑ k : G, S.score ((mu k) x) ((nu k) v) := by
            refine (Fintype.sum_equiv (Equiv.mulRight g)
              (fun h : G => S.score ((mu (h * g)) x) ((nu (h * g)) v))
              (fun k : G => S.score ((mu k) x) ((nu k) v)) ?_)
            intro h
            rfl
    _ = (averagedScoreSystem (mu := mu) (nu := nu) S).score x v := by
            simp [averagedScoreSystem]

omit [IsOrderedCancelAddMonoid R] in
lemma scoreAt_lt_of_mem_not_mem_scoringRule
    {D : Domain V} (S : ScoreSystem R X V) {d : {d : NProfile V // d ∈ D}} {x y : X}
    (hy : y ∈ scoringRule (D := D) S d)
    (hx : x ∉ scoringRule (D := D) S d) :
    scoreAt S x d.1 < scoreAt S y d.1 := by
  have hyx_not : ¬ scoreAt S y d.1 ≤ scoreAt S x d.1 := by
    intro hyx
    apply hx
    intro z
    exact le_trans (hy z) hyx
  exact lt_of_not_ge hyx_not

lemma sum_lt_sum_of_forall_lt (f g : G → R)
    (h : ∀ a, f a < g a) :
    (∑ a : G, f a) < ∑ a : G, g a := by
  classical
  have hle : ∀ a ∈ (Finset.univ : Finset G), f a ≤ g a := by
    intro a ha
    exact (h a).le
  have hlt : ∃ a ∈ (Finset.univ : Finset G), f a < g a := by
    exact ⟨1, by simp, h 1⟩
  simpa using (Finset.sum_lt_sum (s := (Finset.univ : Finset G)) hle hlt)

/-- Equality of the original scoring rule and the averaged one, assuming rule-neutrality
and nonemptiness on the domain. -/
lemma scoringRule_eq_averaged_of_ruleNeutral
    {D : Domain V} (S : ScoreSystem R X V)
    (hN : RuleNeutral mu nu D (scoringRule (D := D) S))
    (hNE : NonemptyOnDomain D (scoringRule (D := D) S)) :
    scoringRule (D := D) S =
      scoringRule (D := D) (averagedScoreSystem (mu := mu) (nu := nu) S) := by
  funext d
  ext x
  constructor
  · intro hx z
    have hle_g :
        ∀ g : G,
          scoreAt S ((mu g) z) (permuteNProfile (nu g) d.1) ≤
            scoreAt S ((mu g) x) (permuteNProfile (nu g) d.1) := by
      intro g
      have hEqg := hN.equivariant g d.2
      have hximg : (mu g) x ∈ permuteSet (mu g) (scoringRule (D := D) S d) :=
        ⟨x, hx, rfl⟩
      have hxg :
          (mu g) x ∈ scoringRule (D := D) S
            ⟨permuteNProfile (nu g) d.1, hN.domainInvariant g d.2⟩ := by
        exact hEqg.symm ▸ hximg
      exact hxg ((mu g) z)
    have hsumle :
        ∑ g : G, scoreAt S ((mu g) z) (permuteNProfile (nu g) d.1)
          ≤ ∑ g : G, scoreAt S ((mu g) x) (permuteNProfile (nu g) d.1) := by
      exact Finset.sum_le_sum (s := (Finset.univ : Finset G)) (fun g hg => hle_g g)
    calc
      scoreAt (averagedScoreSystem (mu := mu) (nu := nu) S) z d.1
          = ∑ g : G, scoreAt S ((mu g) z) (permuteNProfile (nu g) d.1) :=
              scoreAt_averaged_eq_sum (mu := mu) (nu := nu) S z d.1
      _ ≤ ∑ g : G, scoreAt S ((mu g) x) (permuteNProfile (nu g) d.1) := hsumle
      _ = scoreAt (averagedScoreSystem (mu := mu) (nu := nu) S) x d.1 := by
          symm
          exact scoreAt_averaged_eq_sum (mu := mu) (nu := nu) S x d.1
  · intro hx
    by_contra hxnot
    rcases hNE d with ⟨y, hy⟩
    have hlt_g :
        ∀ g : G,
          scoreAt S ((mu g) x) (permuteNProfile (nu g) d.1) <
            scoreAt S ((mu g) y) (permuteNProfile (nu g) d.1) := by
      intro g
      have hEqg := hN.equivariant g d.2
      have hyimg : (mu g) y ∈ permuteSet (mu g) (scoringRule (D := D) S d) :=
        ⟨y, hy, rfl⟩
      have hyg :
          (mu g) y ∈ scoringRule (D := D) S
            ⟨permuteNProfile (nu g) d.1, hN.domainInvariant g d.2⟩ := by
        exact hEqg.symm ▸ hyimg
      have hxnotg :
          (mu g) x ∉ scoringRule (D := D) S
            ⟨permuteNProfile (nu g) d.1, hN.domainInvariant g d.2⟩ := by
        intro hxg
        have hximg : (mu g) x ∈ permuteSet (mu g) (scoringRule (D := D) S d) := by
          exact hEqg ▸ hxg
        have hxorig : x ∈ scoringRule (D := D) S d := by
          simpa using
            (mem_permuteSet_iff (π := mu g) (S := scoringRule (D := D) S d)
              (x := (mu g) x)).1 hximg
        exact hxnot hxorig
      exact scoreAt_lt_of_mem_not_mem_scoringRule (S := S) hyg hxnotg
    have hlt_sum :
        ∑ g : G, scoreAt S ((mu g) x) (permuteNProfile (nu g) d.1) <
          ∑ g : G, scoreAt S ((mu g) y) (permuteNProfile (nu g) d.1) :=
      sum_lt_sum_of_forall_lt (f := fun g => scoreAt S ((mu g) x) (permuteNProfile (nu g) d.1))
        (g := fun g => scoreAt S ((mu g) y) (permuteNProfile (nu g) d.1)) hlt_g
    have hlt_avg :
        scoreAt (averagedScoreSystem (mu := mu) (nu := nu) S) x d.1
          < scoreAt (averagedScoreSystem (mu := mu) (nu := nu) S) y d.1 := by
      calc
        scoreAt (averagedScoreSystem (mu := mu) (nu := nu) S) x d.1
            = ∑ g : G, scoreAt S ((mu g) x) (permuteNProfile (nu g) d.1) :=
                scoreAt_averaged_eq_sum (mu := mu) (nu := nu) S x d.1
        _ < ∑ g : G, scoreAt S ((mu g) y) (permuteNProfile (nu g) d.1) := hlt_sum
        _ = scoreAt (averagedScoreSystem (mu := mu) (nu := nu) S) y d.1 := by
              symm
              exact scoreAt_averaged_eq_sum (mu := mu) (nu := nu) S y d.1
    exact (not_lt_of_ge (hx y)) hlt_avg

/-- Proposition 1 converse (core form): assumes nonemptiness on the represented rule. -/
theorem exists_scoreNeutral_of_ruleNeutral_scoringRule_with_nonempty
    {D : Domain V} {F : RuleOn D X}
    (hN : RuleNeutral mu nu D F)
    (hScore : ∃ S : ScoreSystem R X V, F = scoringRule (D := D) S)
    (hNE : NonemptyOnDomain D F) :
    ∃ Sbar : ScoreSystem R X V,
      ScoreNeutral mu nu Sbar ∧ F = scoringRule (D := D) Sbar := by
  rcases hScore with ⟨S, hFS⟩
  have hN' : RuleNeutral mu nu D (scoringRule (D := D) S) := by
    simpa [hFS] using hN
  have hNE' : NonemptyOnDomain D (scoringRule (D := D) S) := by
    simpa [hFS] using hNE
  refine ⟨averagedScoreSystem (mu := mu) (nu := nu) S, ?_, ?_⟩
  · exact averagedScoreSystem_scoreNeutral (mu := mu) (nu := nu) S
  · calc
      F = scoringRule (D := D) S := hFS
      _ = scoringRule (D := D) (averagedScoreSystem (mu := mu) (nu := nu) S) :=
            scoringRule_eq_averaged_of_ruleNeutral (mu := mu) (nu := nu) S hN' hNE'

/-- Proposition 1 converse packaging: if alternatives are finite/nonempty,
nonemptiness of scoring outcomes is automatic. -/
theorem exists_scoreNeutral_of_ruleNeutral_scoringRule
    [Finite X] [Nonempty X]
    {D : Domain V} {F : RuleOn D X}
    (hN : RuleNeutral mu nu D F)
    (hScore : ∃ S : ScoreSystem R X V, F = scoringRule (D := D) S) :
    ∃ Sbar : ScoreSystem R X V,
      ScoreNeutral mu nu Sbar ∧ F = scoringRule (D := D) Sbar := by
  rcases hScore with ⟨S, hFS⟩
  have hNE : NonemptyOnDomain D F := by
    intro d
    have hNE_S : (scoringRule (D := D) S d).Nonempty :=
      scoringRule_nonempty (D := D) S d
    simpa [hFS] using hNE_S
  exact exists_scoreNeutral_of_ruleNeutral_scoringRule_with_nonempty
    (mu := mu) (nu := nu) (D := D) (F := F) hN ⟨S, hFS⟩ hNE

/-- Proposition 1 packaged `iff` (core form): under explicit domain invariance,
representation as a scoring rule, and explicit nonemptiness on the represented
rule, rule-neutrality is equivalent to existence of a neutral score-system
representation. -/
theorem proposition1_of_scoringRepresentation_with_nonempty
    {D : Domain V} {F : RuleOn D X}
    (hInv : DomainInvariant nu D)
    (hScore : ∃ S : ScoreSystem R X V, F = scoringRule (D := D) S)
    (hNE : NonemptyOnDomain D F) :
    (RuleNeutral mu nu D F ↔
      ∃ Sbar : ScoreSystem R X V,
        ScoreNeutral mu nu Sbar ∧ F = scoringRule (D := D) Sbar) := by
  constructor
  · intro hN
    exact
      exists_scoreNeutral_of_ruleNeutral_scoringRule_with_nonempty
        (mu := mu) (nu := nu) (D := D) (F := F) hN hScore hNE
  · intro hRep
    rcases hRep with ⟨Sbar, hSbarN, hFSbar⟩
    have hNbar : RuleNeutral mu nu D (scoringRule (D := D) Sbar) :=
      scoringRule_ruleNeutral_of_scoreNeutral
        (mu := mu) (nu := nu) (S := Sbar) hInv hSbarN
    simpa [hFSbar] using hNbar

/-- Proposition 1 packaged `iff` with automatic nonemptiness from finite,
nonempty alternatives. -/
theorem proposition1_of_scoringRepresentation
    [Finite X] [Nonempty X]
    {D : Domain V} {F : RuleOn D X}
    (hInv : DomainInvariant nu D)
    (hScore : ∃ S : ScoreSystem R X V, F = scoringRule (D := D) S) :
    (RuleNeutral mu nu D F ↔
      ∃ Sbar : ScoreSystem R X V,
        ScoreNeutral mu nu Sbar ∧ F = scoringRule (D := D) Sbar) := by
  constructor
  · intro hN
    exact
      exists_scoreNeutral_of_ruleNeutral_scoringRule
        (mu := mu) (nu := nu) (D := D) (F := F) hN hScore
  · intro hRep
    rcases hRep with ⟨Sbar, hSbarN, hFSbar⟩
    have hNbar : RuleNeutral mu nu D (scoringRule (D := D) Sbar) :=
      scoringRule_ruleNeutral_of_scoreNeutral
        (mu := mu) (nu := nu) (S := Sbar) hInv hSbarN
    simpa [hFSbar] using hNbar

end Proposition1Converse

section Proposition1ConverseFiniteGroup

variable {G V X R : Type*} [Group G] [Finite G]
variable [AddCommMonoid R] [LinearOrder R] [IsOrderedCancelAddMonoid R]
variable [Finite X] [Nonempty X]
variable (mu : G →* Equiv.Perm X) (nu : G →* Equiv.Perm V)

/-- Finite-group wrapper for Proposition 1 converse packaging. -/
theorem exists_scoreNeutral_of_ruleNeutral_scoringRule_of_finiteGroup
    {D : Domain V} {F : RuleOn D X}
    (hN : RuleNeutral mu nu D F)
    (hScore : ∃ S : ScoreSystem R X V, F = scoringRule (D := D) S) :
    ∃ Sbar : ScoreSystem R X V,
      ScoreNeutral mu nu Sbar ∧ F = scoringRule (D := D) Sbar := by
  classical
  let : Fintype G := Fintype.ofFinite G
  exact exists_scoreNeutral_of_ruleNeutral_scoringRule
    (mu := mu) (nu := nu) (D := D) (F := F) hN hScore

end Proposition1ConverseFiniteGroup

end Pivato
