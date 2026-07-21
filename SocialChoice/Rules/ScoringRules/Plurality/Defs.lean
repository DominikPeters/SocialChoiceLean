import SocialChoice.Margin
import SocialChoice.Rules
import SocialChoice.Meta

namespace SocialChoice

@[scRule]
noncomputable def plurality : VotingRule :=
  fun {V A} _ _ (P : Profile V A) =>
    (Finset.univ.filter (fun c => ∀ d : A, topCount P d ≤ topCount P c))

lemma plurality_nonempty {V A : Type} [Fintype V] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : Profile V A) : (plurality P).Nonempty := by
  classical
  let scoreSet : Finset Nat := (Finset.univ.image (fun c => topCount P c))
  have hscoreSet : scoreSet.Nonempty :=
    (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty).image (fun c => topCount P c)
  let maxScore : Nat := scoreSet.max' hscoreSet
  have hmaxmem : maxScore ∈ scoreSet := Finset.max'_mem scoreSet hscoreSet
  rcases Finset.mem_image.mp hmaxmem with ⟨c, _hc, hscore⟩
  have hmax : ∀ d : A, topCount P d ≤ topCount P c := by
    intro d
    have hmem : topCount P d ∈ scoreSet := by
      exact Finset.mem_image.mpr ⟨d, by simp, rfl⟩
    have hle : topCount P d ≤ maxScore := Finset.le_max' scoreSet _ hmem
    simpa [hscore] using hle
  refine ⟨c, ?_⟩
  simp [plurality, hmax]

theorem plurality_isVotingRule : IsVotingRule plurality := by
  intro V A _ _ _ P
  classical
  simpa using (plurality_nonempty (P := P))

/-! ### Equivalent definition as a scoring rule -/

@[reducible] def pluralityScore (_m r : Nat) : Int := if r = 0 then 1 else 0

/-- Plurality score equals cards of votersTop. -/
lemma pluralityScore_eq_votersTop_card {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) :
    scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) c =
      (votersTop P c).card := by
  classical
  have h :
      scoreCandidate P (fun r => if r = 0 then 1 else 0) c =
        (votersTop P c).card := by
    -- rank = 0 iff TopRank
    have hrankTop : ∀ v, rank (P.pref v) c = 0 ↔ TopRank P v c := by
      intro v
      constructor
      · intro hr d hd
        -- rank c = 0 means no one is above c
        unfold rank at hr
        have hempty : (Finset.univ.filter (fun x => (P.pref v).lt x c)) = ∅ := by
          exact Finset.card_eq_zero.mp hr
        have hd_not_above : d ∉ Finset.univ.filter (fun x => (P.pref v).lt x c) := by
          simp [hempty]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd_not_above
        -- d is not above c, and d ≠ c, so c < d
        let _ := P.pref v
        have hord : c < d ∨ d < c := lt_or_gt_of_ne (Ne.symm hd)
        cases hord with
        | inl hlt => exact hlt
        | inr hgt => exact (hd_not_above hgt).elim
      · intro htop
        unfold rank
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro d hd
        have hdlt : (P.pref v).lt d c := (Finset.mem_filter.mp hd).2
        have hdc : d ≠ c := by
          intro heq; subst heq
          let _ := P.pref v
          exact lt_irrefl _ hdlt
        have hcd : (P.pref v).lt c d := htop d hdc
        let _ := P.pref v
        exact lt_asymm hcd hdlt
    -- Rewrite to use TopRank instead of rank = 0
    have heq :
        (∑ v : V, (fun r => if r = 0 then (1 : Int) else 0) (rank (P.pref v) c)) =
          ∑ v : V, if TopRank P v c then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      simp only [hrankTop v]
    have hsum :
        (∑ v : V, if TopRank P v c then (1 : Int) else 0) =
          ((Finset.univ.filter (fun v => TopRank P v c)).card : Int) := by
      classical
      have hsum_univ :
          (∑ v : V, if TopRank P v c then (1 : Int) else 0) =
            (Finset.univ : Finset V).sum (fun v => if TopRank P v c then (1 : Int) else 0) := by
        simp
      have hsum_filtered :
          ((Finset.univ : Finset V).sum (fun v => if TopRank P v c then (1 : Int) else 0)) =
            (Finset.univ.filter (fun v => TopRank P v c)).sum (fun _ => (1 : Int)) := by
        have h := (Finset.sum_filter
          (s := (Finset.univ : Finset V))
          (p := fun v => TopRank P v c)
          (f := fun _ => (1 : Int)))
        exact h.symm
      have hsum_card :
          ((Finset.univ.filter (fun v => TopRank P v c)).sum (fun _ => (1 : Int))) =
            ((Finset.univ.filter (fun v => TopRank P v c)).card : Int) := by
        simp
      exact hsum_univ.trans (hsum_filtered.trans hsum_card)
    have hscore :
        scoreCandidate P (fun r => if r = 0 then 1 else 0) c =
          ∑ v : V, if TopRank P v c then (1 : Int) else 0 := by
      simpa [scoreCandidate] using heq
    calc
      scoreCandidate P (fun r => if r = 0 then 1 else 0) c
          = ∑ v : V, if TopRank P v c then (1 : Int) else 0 := hscore
      _ = ((Finset.univ.filter fun v => TopRank P v c).card : Int) := hsum
      _ = (votersTop P c).card := by
            simp [votersTop]
  simpa [pluralityScore] using h

lemma pluralityScore_eq_topCount {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) :
    scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) c =
      topCount P c := by
  simpa [topCount] using (pluralityScore_eq_votersTop_card (P := P) (c := c))

theorem plurality_eq_scoringRule :
    (plurality : VotingRule) = (scoringRule pluralityScore : VotingRule) := by
  funext V A _ _ P
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · apply Finset.ext
    intro c
    constructor
    · intro hc
      have hmax : ∀ d : A, topCount P d ≤ topCount P c :=
        (Finset.mem_filter.mp hc).2
      have hle : ∀ d : A,
          scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) d ≤
            scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) c := by
        intro d
        have hd :
            scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) d =
              (topCount P d) := by
          simpa [pluralityScore, topCount] using
            (pluralityScore_eq_votersTop_card (P := P) (c := d))
        have hc' :
            scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) c =
              (topCount P c) := by
          simpa [pluralityScore, topCount] using
            (pluralityScore_eq_votersTop_card (P := P) (c := c))
        have hmax' : (topCount P d : Int) ≤ topCount P c := by
          exact_mod_cast (hmax d)
        simpa [hd, hc'] using hmax'
      have hc' : c ∈ scoringWinners P (fun r => pluralityScore (Fintype.card A) r) :=
        (scoringWinners_iff_forall_le (P := P) (score := _) hA c).2 hle
      simpa [scoringRule] using hc'
    · intro hc
      have hle :
          ∀ d : A,
            scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) d ≤
              scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) c :=
        (scoringWinners_iff_forall_le (P := P) (score := _) hA c).1
          (by simpa [scoringRule] using hc)
      have hmax : ∀ d : A, topCount P d ≤ topCount P c := by
        intro d
        have hd :
            scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) d =
              (topCount P d) := by
          simpa [pluralityScore, topCount] using
            (pluralityScore_eq_votersTop_card (P := P) (c := d))
        have hc' :
            scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) c =
              (topCount P c) := by
          simpa [pluralityScore, topCount] using
            (pluralityScore_eq_votersTop_card (P := P) (c := c))
        have hle' : (topCount P d : Int) ≤ topCount P c := by
          simpa [hd, hc'] using hle d
        exact_mod_cast hle'
      exact Finset.mem_filter.mpr ⟨by simp, hmax⟩
  · have hA' : (Finset.univ : Finset A) = ∅ := by
      simpa [Finset.nonempty_iff_ne_empty] using hA
    apply Finset.ext
    intro c
    simp [plurality, scoringRule, scoringWinners, hA']

/-! ### Two-candidate election lemmas -/

/-- In a two-candidate election, TopRank is equivalent to pairwise preference. -/
lemma topRank_iff_prefers_of_two {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (hcard : Fintype.card A = 2)
    (c d : A) (hcd : c ≠ d) (v : V) :
    TopRank P v c ↔ Prefers P v c d := by
  constructor
  · intro htop
    exact htop d hcd.symm
  · intro hpref e he
    rcases two_elems_eq_or_eq hcard c d hcd e with rfl | rfl
    · exact (he rfl).elim
    · exact hpref

/-- In a two-candidate election, the number of top-ranks equals
    the number of voters who prefer that candidate. -/
lemma votersTop_eq_votersPreferring_of_two {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (hcard : Fintype.card A = 2)
    (c d : A) (hcd : c ≠ d) :
    votersTop P c = votersPreferring P c d := by
  classical
  ext v
  simp only [votersTop, votersPreferring, Finset.mem_filter, Finset.mem_univ, true_and]
  exact topRank_iff_prefers_of_two P hcard c d hcd v

/-- In two candidates, plurality score = number preferring you to the other. -/
lemma pluralityScore_eq_votersPreferring_of_two {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (hcard : Fintype.card A = 2)
    (c d : A) (hcd : c ≠ d) :
    scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) c =
      (votersPreferring P c d).card := by
  rw [pluralityScore_eq_votersTop_card, votersTop_eq_votersPreferring_of_two P hcard c d hcd]

lemma margin_nonneg_iff_topCount_le_of_two
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (hcard : Fintype.card A = 2) {a b : A} (hab : a ≠ b) :
    0 ≤ margin P a b ↔ topCount P b ≤ topCount P a := by
  classical
  have htop_a :
      topCount P a = (votersPreferring P a b).card := by
    have h :=
      congrArg Finset.card
        (votersTop_eq_votersPreferring_of_two (P := P) hcard a b hab)
    simpa [topCount] using h
  have htop_b :
      topCount P b = (votersPreferring P b a).card := by
    have h :=
      congrArg Finset.card
        (votersTop_eq_votersPreferring_of_two (P := P) hcard b a (Ne.symm hab))
    simpa [topCount] using h
  have hmargin_int :
      0 ≤ margin P a b ↔
        Int.ofNat (votersPreferring P b a).card ≤ Int.ofNat (votersPreferring P a b).card := by
    dsimp [margin]
    exact
      (sub_nonneg
        (a := Int.ofNat (votersPreferring P a b).card)
        (b := Int.ofNat (votersPreferring P b a).card))
  have hmargin_nat :
      0 ≤ margin P a b ↔
        (votersPreferring P b a).card ≤ (votersPreferring P a b).card := by
    constructor
    · intro h
      have h' := (hmargin_int.mp h)
      exact Int.le_of_ofNat_le_ofNat h'
    · intro h
      have h' : Int.ofNat (votersPreferring P b a).card ≤
          Int.ofNat (votersPreferring P a b).card :=
        Int.ofNat_le_ofNat_of_le h
      exact hmargin_int.mpr h'
  simpa [htop_a, htop_b] using hmargin_nat

end SocialChoice
