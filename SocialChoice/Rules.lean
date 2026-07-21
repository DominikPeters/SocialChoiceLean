import SocialChoice.Profile
import SocialChoice.Rules.ScoringRules.Defs

namespace SocialChoice

open Finset

noncomputable def topCount {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) : Nat :=
  (votersTop P c).card

@[simp] lemma topCount_permuteVoters {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm V) (c : A) :
    topCount (permuteVoters P σ) c = topCount P c := by
  classical
  have hcard :
      (votersTop (permuteVoters P σ) c).card = (votersTop P c).card := by
    refine Finset.card_bij
      (s := votersTop (permuteVoters P σ) c)
      (t := votersTop P c)
      (i := fun v _ => σ v) ?_ ?_ ?_
    · intro v hv
      have hv' : TopRank (permuteVoters P σ) v c := (Finset.mem_filter.mp hv).2
      have hv'' : TopRank P (σ v) c := by
        intro d hd
        have : Prefers (permuteVoters P σ) v c d := hv' d hd
        exact this
      exact Finset.mem_filter.mpr ⟨by simp, hv''⟩
    · intro v1 hv1 v2 hv2 h
      exact σ.injective h
    · intro v hv
      have hv' : TopRank P v c := (Finset.mem_filter.mp hv).2
      refine ⟨σ.symm v, ?_, by simp⟩
      have : TopRank (permuteVoters P σ) (σ.symm v) c := by
        intro d hd
        have : Prefers P v c d := hv' d hd
        change (P.pref (σ (σ.symm v))).lt c d
        rw [Equiv.apply_symm_apply]
        exact this
      exact Finset.mem_filter.mpr ⟨by simp, this⟩
  simpa [topCount] using hcard

lemma exists_prefers_of_not_top {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (d : A) (hnot : ¬ TopRank P v d) :
    ∃ c : A, c ≠ d ∧ Prefers P v c d := by
  classical
  have hnot' : ∃ b : A, b ≠ d ∧ ¬ Prefers P v d b := by
    by_contra h
    apply hnot
    intro b hb
    by_contra hdb
    exact h ⟨b, hb, hdb⟩
  rcases hnot' with ⟨b, hb, hdb⟩
  let _ := P.pref v
  have htrich : Prefers P v d b ∨ Prefers P v b d := by
    have : d < b ∨ b < d := lt_or_gt_of_ne (Ne.symm hb)
    simpa [Prefers] using this
  cases htrich with
  | inl hdb' => exact (hdb hdb').elim
  | inr hbd' => exact ⟨b, hb, hbd'⟩

lemma topRank_restrictProfile_iff_of_not_top {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (d : A) (hnot_top : ∀ v, ¬ TopRank P v d)
    (v : V) (a : A) (hne : a ≠ d) :
    TopRank (restrictProfile P d) v ⟨a, hne⟩ ↔ TopRank P v a := by
  classical
  constructor
  · intro htop b hb
    by_cases hbd : b = d
    · subst b
      by_contra had
      let _ := P.pref v
      have htrich : Prefers P v a d ∨ Prefers P v d a := by
        have : a < d ∨ d < a := lt_or_gt_of_ne hne
        simpa [Prefers] using this
      cases htrich with
      | inl had' => exact (had had').elim
      | inr hda =>
          rcases exists_prefers_of_not_top (P := P) (v := v) (d := d)
              (hnot := hnot_top v) with ⟨c, hcne, hcd⟩
          have hca : Prefers P v c a := by
            let _ := P.pref v
            exact lt_trans hcd hda
          have hcne' : (c : A) ≠ d := hcne
          have hca' : c ≠ a := by
            intro hca_eq
            subst hca_eq
            exact (had hcd).elim
          have htop_ac :
              Prefers (restrictProfile P d) v ⟨a, hne⟩ ⟨c, hcne'⟩ := by
            refine htop ⟨c, hcne'⟩ ?_
            intro hEq
            apply hca'
            exact congrArg Subtype.val hEq
          have htop_ac' : Prefers P v a c := by
            simpa using
              (prefers_restrictProfile_iff (P := P) (c := d) (v := v)
                (a := ⟨a, hne⟩) (b := ⟨c, hcne'⟩)).1 htop_ac
          let _ := P.pref v
          exact (lt_asymm htop_ac' hca).elim
    · have hb' : (⟨b, hbd⟩ : {x : A // x ≠ d}) ≠ ⟨a, hne⟩ := by
        intro hEq
        apply hb
        exact congrArg Subtype.val hEq
      have htop' := htop ⟨b, hbd⟩ hb'
      simpa using
        (prefers_restrictProfile_iff (P := P) (c := d) (v := v)
          (a := ⟨a, hne⟩) (b := ⟨b, hbd⟩)).1 htop'
  · intro htop b hb
    have hb' : (b : A) ≠ a := by
      intro hEq
      apply hb
      ext
      simpa using hEq
    have hpref : Prefers P v a b := htop b hb'
    simpa using
      (prefers_restrictProfile_iff (P := P) (c := d) (v := v)
        (a := ⟨a, hne⟩) (b := b)).2 hpref

lemma topCount_restrictProfile_eq {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (d : A) (hnot_top : ∀ v, ¬ TopRank P v d)
    (a : A) (hne : a ≠ d) :
    topCount (restrictProfile P d) ⟨a, hne⟩ = topCount P a := by
  classical
  unfold topCount
  apply congrArg Finset.card
  ext v
  simp [votersTop, topRank_restrictProfile_iff_of_not_top
    (P := P) (d := d) (hnot_top := hnot_top) (v := v) (a := a) (hne := hne)]

lemma no_top_of_topCount_zero {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (d : A) (hd : topCount P d = 0) :
    ∀ v, ¬ TopRank P v d := by
  intro v htop
  have hv : v ∈ votersTop P d := by
    simp [votersTop, htop]
  have hpos : 0 < (votersTop P d).card := Finset.card_pos.mpr ⟨v, hv⟩
  have hd' : (votersTop P d).card = 0 := by
    simpa [topCount] using hd
  exact (Nat.ne_of_gt hpos) hd'

lemma topCount_eq_zero_of_dominated {V A : Type} [Fintype V] [Fintype A] [Nonempty V]
    (P : Profile V A) (c d : A) (hpref : ∀ v : V, Prefers P v c d) :
    topCount P d = 0 := by
  classical
  rcases Classical.choice (inferInstance : Nonempty V) with v0
  let _ := P.pref v0
  have hcd : c ≠ d := by
    intro hEq
    subst hEq
    exact (lt_irrefl _ (hpref v0))
  unfold topCount
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have htop : TopRank P v d := (Finset.mem_filter.mp hv).2
  let _ := P.pref v
  have hdc : Prefers P v d c := htop c hcd
  have hcd' : Prefers P v c d := hpref v
  exact (lt_asymm hdc hcd')

-- Concrete rules.
noncomputable def trivialRule : VotingRule :=
  fun {V A} _ _ (_ : Profile V A) => (Finset.univ : Finset A)

end SocialChoice
