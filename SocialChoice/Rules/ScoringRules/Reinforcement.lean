import Mathlib.Tactic
import SocialChoice.Axioms.Reinforcement
import SocialChoice.Rules.ScoringRules.Defs

namespace SocialChoice

lemma scoreCandidate_unionProfiles {V W A : Type} [Fintype V] [Fintype W] [Fintype A]
    (P₁ : Profile V A) (P₂ : Profile W A) (score : Nat → Int) (c : A) :
    scoreCandidate (unionProfiles P₁ P₂) score c =
      scoreCandidate P₁ score c + scoreCandidate P₂ score c := by
  classical
  unfold scoreCandidate
  set_option linter.unnecessarySimpa false in
  simpa [unionProfiles] using
    (Fintype.sum_sum_type
      (f := fun v : V ⊕ W => score (rank ((unionProfiles P₁ P₂).pref v) c)))

/-!  Reindexing voters along an equivalence preserves scores. -/
lemma scoreCandidate_equiv {V W A : Type} [Fintype V] [Fintype W] [Fintype A]
    (e : V ≃ W) (P : Profile V A) (score : Nat → Int) (c : A) :
    scoreCandidate ({ pref := fun w => P.pref (e.symm w) }) score c =
      scoreCandidate P score c := by
  classical
  unfold scoreCandidate
  -- Reindex the finite sum along the equivalence.
  have h := Fintype.sum_equiv (e := e.symm)
      (f := fun w => score (rank (P.pref (e.symm w)) c))
      (g := fun v => score (rank (P.pref v) c))
      (by intro w; simp)
  simpa using h

/-!  Equivalence between the combined electorate and a disjoint sum of electorates. -/
noncomputable def unionElectorateEquivSum {U : Type} [DecidableEq U]
    {V W : Finset U} (hdisj : Disjoint V W) :
    Electorate U (V ∪ W) ≃ (Electorate U V ⊕ Electorate U W) := by
  classical
  have hdisj_left := Finset.disjoint_left.mp hdisj
  let toSum : Electorate U (V ∪ W) → Electorate U V ⊕ Electorate U W := fun v => by
    by_cases hv : v.1 ∈ V
    · exact Sum.inl ⟨v.1, hv⟩
    · have hw : v.1 ∈ W := by
        rcases Finset.mem_union.mp v.2 with hv' | hw'
        · exact (False.elim (hv hv'))
        · exact hw'
      exact Sum.inr ⟨v.1, hw⟩
  let fromSum : Electorate U V ⊕ Electorate U W → Electorate U (V ∪ W)
    | Sum.inl v => ⟨v.1, Finset.mem_union.mpr (Or.inl v.2)⟩
    | Sum.inr w => ⟨w.1, Finset.mem_union.mpr (Or.inr w.2)⟩
  have to_from : ∀ v, fromSum (toSum v) = v := by
    intro v
    by_cases hv : v.1 ∈ V
    · apply Subtype.ext; simp [toSum, hv, fromSum]
    · have hw : v.1 ∈ W := by
        rcases Finset.mem_union.mp v.2 with hv' | hw'
        · exact (False.elim (hv hv'))
        · exact hw'
      apply Subtype.ext; simp [toSum, hv, fromSum]
  have from_to : ∀ vw, toSum (fromSum vw) = vw := by
    intro vw
    cases vw with
    | inl v => simp [toSum, fromSum, v.property]
    | inr w =>
        have hv : w.1 ∉ V := by intro hv; exact hdisj_left hv w.2
        simp [toSum, fromSum, hv]
  exact { toFun := toSum, invFun := fromSum, left_inv := to_from, right_inv := from_to }

/-!  Winners on a disjoint union profile equal the intersection of winners
    when a common winner exists. -/
lemma scoringWinners_unionProfiles_inter_of_mem {V W A : Type} [Fintype V] [Fintype W] [Fintype A]
    [DecidableEq A] (score : Nat → Int) (P : Profile V A) (Q : Profile W A)
    {x : A} (hA : (Finset.univ : Finset A).Nonempty)
    (hx1 : x ∈ scoringWinners P score) (hx2 : x ∈ scoringWinners Q score) :
    scoringWinners (unionProfiles P Q) score =
      scoringWinners P score ∩ scoringWinners Q score := by
  classical
  -- Max scores on each part.
  let scoreSet₁ : Finset Int := (Finset.univ.image (fun c => scoreCandidate P score c))
  let max₁ : Int := scoreSet₁.max' (hA.image _)
  let scoreSet₂ : Finset Int := (Finset.univ.image (fun c => scoreCandidate Q score c))
  let max₂ : Int := scoreSet₂.max' (hA.image _)
  have hx1' : scoreCandidate P score x = max₁ := by
    simpa [scoringWinners, hA, scoreSet₁, max₁] using hx1
  have hx2' : scoreCandidate Q score x = max₂ := by
    simpa [scoringWinners, hA, scoreSet₂, max₂] using hx2
  have hle1 : ∀ c, scoreCandidate P score c ≤ max₁ := by
    intro c
    have hmem : scoreCandidate P score c ∈ scoreSet₁ :=
      Finset.mem_image.mpr ⟨c, by simp, rfl⟩
    exact Finset.le_max' scoreSet₁ _ hmem
  have hle2 : ∀ c, scoreCandidate Q score c ≤ max₂ := by
    intro c
    have hmem : scoreCandidate Q score c ∈ scoreSet₂ :=
      Finset.mem_image.mpr ⟨c, by simp, rfl⟩
    exact Finset.le_max' scoreSet₂ _ hmem

  -- Max score on the union profile is the sum of the separate maxima.
  have hsum_x : scoreCandidate (unionProfiles P Q) score x = max₁ + max₂ := by
    calc
      scoreCandidate (unionProfiles P Q) score x =
          scoreCandidate P score x + scoreCandidate Q score x := by
            simpa using
              (scoreCandidate_unionProfiles (P₁ := P) (P₂ := Q) (score := score) (c := x))
      _ = max₁ + max₂ := by simp [hx1', hx2']
  let scoreSet : Finset Int :=
    (Finset.univ.image (fun c => scoreCandidate (unionProfiles P Q) score c))
  let maxScore : Int := scoreSet.max' (hA.image _)
  have hmax_le : maxScore ≤ max₁ + max₂ := by
    have hscoreSet_nonempty : scoreSet.Nonempty := hA.image _
    refine (Finset.max'_le_iff scoreSet hscoreSet_nonempty).2 ?_
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨c, _hc, rfl⟩
    calc
      scoreCandidate (unionProfiles P Q) score c =
          scoreCandidate P score c + scoreCandidate Q score c := by
            simpa using
              (scoreCandidate_unionProfiles (P₁ := P) (P₂ := Q) (score := score) (c := c))
      _ ≤ max₁ + max₂ := by exact add_le_add (hle1 c) (hle2 c)
  have hle_max : max₁ + max₂ ≤ maxScore := by
    have hmem : scoreCandidate (unionProfiles P Q) score x ∈ scoreSet :=
      Finset.mem_image.mpr ⟨x, by simp, rfl⟩
    have hle : scoreCandidate (unionProfiles P Q) score x ≤ maxScore :=
      Finset.le_max' scoreSet _ hmem
    simpa [hsum_x] using hle
  have hmax_eq : maxScore = max₁ + max₂ := le_antisymm hmax_le hle_max

  -- Now show winner set equality.
  apply Finset.ext
  intro y; constructor
  · intro hy
    have hy_score : scoreCandidate (unionProfiles P Q) score y = maxScore := by
      have : y ∈ scoringWinners (unionProfiles P Q) score := hy
      simpa [scoringWinners, hA, scoreSet, maxScore] using this
    have hy_sum : scoreCandidate P score y + scoreCandidate Q score y = max₁ + max₂ := by
      have hy_union : scoreCandidate (unionProfiles P Q) score y =
            scoreCandidate P score y + scoreCandidate Q score y := by
        simpa using
          (scoreCandidate_unionProfiles (P₁ := P) (P₂ := Q) (score := score) (c := y))
      simpa [hy_union, hmax_eq] using hy_score
    have hle1y : scoreCandidate P score y ≤ max₁ := hle1 y
    have hle2y : scoreCandidate Q score y ≤ max₂ := hle2 y
    have hy1 : scoreCandidate P score y = max₁ := by linarith
    have hy2 : scoreCandidate Q score y = max₂ := by linarith
    have hy1' : y ∈ scoringWinners P score := by
      have : y ∈ (Finset.univ.filter (fun c => scoreCandidate P score c = max₁)) :=
        Finset.mem_filter.mpr ⟨by simp, hy1⟩
      simpa [scoringWinners, hA, scoreSet₁, max₁] using this
    have hy2' : y ∈ scoringWinners Q score := by
      have : y ∈ (Finset.univ.filter (fun c => scoreCandidate Q score c = max₂)) :=
        Finset.mem_filter.mpr ⟨by simp, hy2⟩
      simpa [scoringWinners, hA, scoreSet₂, max₂] using this
    exact Finset.mem_inter.mpr ⟨hy1', hy2'⟩
  · intro hy
    have hy1 : y ∈ scoringWinners P score := (Finset.mem_inter.mp hy).1
    have hy2 : y ∈ scoringWinners Q score := (Finset.mem_inter.mp hy).2
    have hy1' : scoreCandidate P score y = max₁ :=
      by simpa [scoringWinners, hA, scoreSet₁, max₁] using hy1
    have hy2' : scoreCandidate Q score y = max₂ :=
      by simpa [scoringWinners, hA, scoreSet₂, max₂] using hy2
    have hy_union : scoreCandidate (unionProfiles P Q) score y = maxScore := by
      calc
        scoreCandidate (unionProfiles P Q) score y =
            scoreCandidate P score y + scoreCandidate Q score y := by
              simpa using
                (scoreCandidate_unionProfiles (P₁ := P) (P₂ := Q) (score := score) (c := y))
        _ = max₁ + max₂ := by simp [hy1', hy2']
        _ = maxScore := by simp [hmax_eq]
    have : y ∈ (Finset.univ.filter (fun c => scoreCandidate (unionProfiles P Q) score c = maxScore)) :=
      Finset.mem_filter.mpr ⟨by simp, hy_union⟩
    exact by
      simpa [scoringWinners, hA, scoreSet, maxScore] using this

theorem scoringRule_reinforcement (score : Nat → Nat → Int) :
    Reinforcement (scoringRule score) := by
  classical
  intro U A _ _ _ V W hdisj P Q R hRV hRW hnonempty
  rcases hnonempty with ⟨x, hx⟩
  let scoreFun : Nat → Int := fun r => score (Fintype.card A) r

  -- Equivalence between the combined electorate and the disjoint sum.
  let e := unionElectorateEquivSum (U := U) (V := V) (W := W) hdisj

  -- Transport the profile along the equivalence.
  let R' : Profile (Electorate U V ⊕ Electorate U W) A :=
    { pref := fun vw => R.pref (e.symm vw) }

  -- Show the transported profile agrees with `unionProfiles P Q`.
  have hR' : R' = unionProfiles P Q := by
    apply Profile.ext
    intro vw
    cases vw with
    | inl v =>
        have := congrArg (fun prof => prof.pref v) hRV
        change R.pref (e.symm (Sum.inl v)) = P.pref v
        rw [show e.symm (Sum.inl v) = ⟨v.1, by simp⟩ by
          apply Subtype.ext
          rfl]
        exact this
    | inr w =>
        have := congrArg (fun prof => prof.pref w) hRW
        change R.pref (e.symm (Sum.inr w)) = Q.pref w
        rw [show e.symm (Sum.inr w) = ⟨w.1, by simp⟩ by
          apply Subtype.ext
          rfl]
        exact this

  -- Scores/Winners are invariant under reindexing along `e`.
  have hscoreCand : ∀ c, scoreCandidate R' scoreFun c = scoreCandidate R scoreFun c := by
    intro c
    simpa [R'] using (scoreCandidate_equiv (e := e) (P := R) (score := scoreFun) (c := c))
  have hA : (Finset.univ : Finset A).Nonempty := ⟨x, by simp⟩
  have hscore_eq : scoringWinners R scoreFun = scoringWinners R' scoreFun := by
    classical
    ext c
    have hfor :
        (∀ d, scoreCandidate R scoreFun d ≤ scoreCandidate R scoreFun c) ↔
          (∀ d, scoreCandidate R' scoreFun d ≤ scoreCandidate R' scoreFun c) := by
      constructor
      · intro hd d; have := hd d; simpa [hscoreCand] using this
      · intro hd d; have := hd d; simpa [hscoreCand] using this
    constructor
    · intro hc
      have hc' := (scoringWinners_iff_forall_le (P := R) (score := scoreFun) hA c).1 hc
      exact (scoringWinners_iff_forall_le (P := R') (score := scoreFun) hA c).2 ((hfor).1 hc')
    · intro hc
      have hc' := (scoringWinners_iff_forall_le (P := R') (score := scoreFun) hA c).1 hc
      exact (scoringWinners_iff_forall_le (P := R) (score := scoreFun) hA c).2 ((hfor).2 hc')

  -- Reduce to the union-of-profiles case on the sum electorate.
  have hx1 : x ∈ scoringWinners P scoreFun := by
    simpa [scoringRule, scoreFun] using (Finset.mem_inter.mp hx).1
  have hx2 : x ∈ scoringWinners Q scoreFun := by
    simpa [scoringRule, scoreFun] using (Finset.mem_inter.mp hx).2

  -- Winners of the union profile are exactly the intersection of winners (using the witness x).
  have h_union_eq :
      scoringWinners (unionProfiles P Q) scoreFun =
        scoringWinners P scoreFun ∩ scoringWinners Q scoreFun :=
    scoringWinners_unionProfiles_inter_of_mem (score := scoreFun) (P := P) (Q := Q)
      hA hx1 hx2

  -- Transport back to the original electorate.
  have hR_eq : scoringWinners R scoreFun = scoringWinners P scoreFun ∩ scoringWinners Q scoreFun := by
    calc
      scoringWinners R scoreFun
          = scoringWinners R' scoreFun := hscore_eq
      _ = scoringWinners (unionProfiles P Q) scoreFun := by
        simp [hR']
      _ = scoringWinners P scoreFun ∩ scoringWinners Q scoreFun := h_union_eq

  -- Conclude the reinforcement equality.
  simp [scoringRule, scoreFun, hR_eq]

end SocialChoice
