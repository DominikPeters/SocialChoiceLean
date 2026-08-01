import SocialChoice.Axioms.Neutrality
import SocialChoice.Rules.UncoveredSet.Defs
import SocialChoice.Margin

namespace SocialChoice

open Finset

lemma covers_permuteCandidates_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) (x y : A) :
    covers (permuteCandidates P σ) x y ↔ covers P (σ.symm x) (σ.symm y) := by
  constructor
  · intro h
    rcases h with ⟨hxy, h1, h2⟩
    refine ⟨?_, ?_, ?_⟩
    ·
      simpa using
        (margin_pos_permuteCandidates_iff (P := P) (σ := σ) (a := x) (b := y)).1 hxy
    · intro z hyz
      have hyz'' : margin_pos P (σ.symm y) (σ.symm (σ z)) := by
        simpa using hyz
      have hyz' : margin_pos (permuteCandidates P σ) y (σ z) := by
        exact
          (margin_pos_permuteCandidates_iff (P := P) (σ := σ) (a := y) (b := σ z)).2 hyz''
      have hxz' : margin_pos (permuteCandidates P σ) x (σ z) := h1 (σ z) hyz'
      have hxz : margin_pos P (σ.symm x) z := by
        simpa using
          (margin_pos_permuteCandidates_iff (P := P) (σ := σ) (a := x) (b := σ z)).1 hxz'
      exact hxz
    · intro z hzx
      have hzx'' : margin_pos P (σ.symm (σ z)) (σ.symm x) := by
        simpa using hzx
      have hzx' : margin_pos (permuteCandidates P σ) (σ z) x := by
        exact
          (margin_pos_permuteCandidates_iff (P := P) (σ := σ) (a := σ z) (b := x)).2 hzx''
      have hzy' : margin_pos (permuteCandidates P σ) (σ z) y := h2 (σ z) hzx'
      have hzy : margin_pos P z (σ.symm y) := by
        simpa using
          (margin_pos_permuteCandidates_iff (P := P) (σ := σ) (a := σ z) (b := y)).1 hzy'
      exact hzy
  · intro h
    rcases h with ⟨hxy, h1, h2⟩
    refine ⟨?_, ?_, ?_⟩
    ·
      simpa using
        (margin_pos_permuteCandidates_iff (P := P) (σ := σ) (a := x) (b := y)).2 hxy
    · intro z hyz
      have hyz' : margin_pos P (σ.symm y) (σ.symm z) := by
        simpa using
          (margin_pos_permuteCandidates_iff (P := P) (σ := σ) (a := y) (b := z)).1 hyz
      have hxz' : margin_pos P (σ.symm x) (σ.symm z) := h1 (σ.symm z) hyz'
      have hxz : margin_pos (permuteCandidates P σ) x z := by
        simpa using
          (margin_pos_permuteCandidates_iff (P := P) (σ := σ) (a := x) (b := z)).2 hxz'
      exact hxz
    · intro z hzx
      have hzx' : margin_pos P (σ.symm z) (σ.symm x) := by
        simpa using
          (margin_pos_permuteCandidates_iff (P := P) (σ := σ) (a := z) (b := x)).1 hzx
      have hzy' : margin_pos P (σ.symm z) (σ.symm y) := h2 (σ.symm z) hzx'
      have hzy : margin_pos (permuteCandidates P σ) z y := by
        simpa using
          (margin_pos_permuteCandidates_iff (P := P) (σ := σ) (a := z) (b := y)).2 hzy'
      exact hzy

lemma uncovered_permuteCandidates_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) (x : A) :
    uncovered (permuteCandidates P σ) x ↔ uncovered P (σ.symm x) := by
  constructor
  · intro h y hy hcov
    have hcov' : covers (permuteCandidates P σ) (σ y) x := by
      have : covers P (σ.symm (σ y)) (σ.symm x) := by
        simpa using hcov
      exact (covers_permuteCandidates_iff (P := P) (σ := σ) (x := σ y) (y := x)).2 this
    have hne : σ y ≠ x := by
      intro hEq
      apply hy
      have := congrArg σ.symm hEq
      simpa using this
    exact (h (σ y) hne) hcov'
  · intro h y hy hcov
    have hcov' : covers P (σ.symm y) (σ.symm x) :=
      (covers_permuteCandidates_iff (P := P) (σ := σ) (x := y) (y := x)).1 hcov
    have hne : σ.symm y ≠ σ.symm x := by
      intro hEq
      apply hy
      have := congrArg σ hEq
      simpa using this
    exact (h (σ.symm y) hne) hcov'

lemma mem_permuteWinners_iff {A : Type} [DecidableEq A] (σ : Equiv.Perm A)
    (s : Finset A) (a : A) :
    a ∈ permuteWinners σ s ↔ σ.symm a ∈ s := by
  classical
  constructor
  · intro ha
    rcases Finset.mem_map.mp ha with ⟨b, hb, hEq⟩
    have : b = σ.symm a := by
      simpa using congrArg σ.symm hEq
    subst this
    simpa using hb
  · intro ha
    refine Finset.mem_map.mpr ?_
    refine ⟨σ.symm a, ha, ?_⟩
    simp

lemma uncoveredSet_permuteCandidates {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) :
    uncoveredSetOf (P := permuteCandidates P σ) =
      permuteWinners σ (uncoveredSetOf (P := P)) := by
  classical
  ext a
  constructor
  · intro ha
    have ha' : uncovered (permuteCandidates P σ) a :=
      (Finset.mem_filter.mp ha).2
    have ha'' : uncovered P (σ.symm a) :=
      (uncovered_permuteCandidates_iff (P := P) (σ := σ) (x := a)).1 ha'
    have : σ.symm a ∈ uncoveredSetOf (P := P) := by
      exact (Finset.mem_filter.mpr ⟨by simp, ha''⟩)
    exact (mem_permuteWinners_iff (σ := σ) (s := uncoveredSetOf (P := P)) (a := a)).2 this
  · intro ha
    have ha' : σ.symm a ∈ uncoveredSetOf (P := P) :=
      (mem_permuteWinners_iff (σ := σ) (s := uncoveredSetOf (P := P)) (a := a)).1 ha
    have ha'' : uncovered P (σ.symm a) :=
      (Finset.mem_filter.mp ha').2
    have ha''' : uncovered (permuteCandidates P σ) a :=
      (uncovered_permuteCandidates_iff (P := P) (σ := σ) (x := a)).2 ha''
    exact Finset.mem_filter.mpr ⟨by simp, ha'''⟩

/-- uncoveredSet is neutral. -/
theorem uncoveredSet_neutral : Neutrality uncoveredSet := by
  intro V A _ _ P σ
  classical
  have hset :
      uncoveredSetOf (P := permuteCandidates P σ) =
        permuteWinners σ (uncoveredSetOf (P := P)) :=
    uncoveredSet_permuteCandidates (P := P) (σ := σ)
  simpa [uncoveredSet] using hset.symm

end SocialChoice
