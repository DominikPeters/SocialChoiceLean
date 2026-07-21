import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import SocialChoice.Profile
import SocialChoice.Rules
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Neutrality
import SocialChoice.Rules.ScoringRules.Plurality.Defs
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.Defs
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.Clones
import SocialChoice.Axioms.Clones
import SocialChoice.Axioms.Independence

namespace SocialChoice

open Finset

variable {V A : Type} [Fintype V] [Fintype A]

lemma lowestScoring_mem_of_topCount_zero
    [DecidableEq A]
    (P : Profile V A) (d : A) (hd : topCount P d = 0) :
    d ∈ lowestScoring P (fun r => pluralityScore (Fintype.card A) r) := by
  classical
  have hA : (Finset.univ : Finset A).Nonempty := by
    have : Nonempty A := ⟨d⟩
    exact Finset.univ_nonempty
  have hscore_d : scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) d = 0 := by
    have hd' : (votersTop P d).card = 0 := by
      simpa [topCount] using hd
    calc
      scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) d =
          (votersTop P d).card := by
            simpa [pluralityScore] using (pluralityScore_eq_votersTop_card (P := P) (c := d))
      _ = 0 := by
            exact_mod_cast hd'
  have hle : ∀ c : A,
      scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) d ≤
        scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) c := by
    intro c
    have hnonneg :
        0 ≤ scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) c := by
      have hscore_c :
          scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) c =
            (votersTop P c).card := by
        simpa [pluralityScore] using (pluralityScore_eq_votersTop_card (P := P) (c := c))
      have : 0 ≤ ((votersTop P c).card : Int) := by
        exact_mod_cast (Nat.zero_le _)
      simp [hscore_c]
    simpa [hscore_d] using hnonneg
  exact (lowestScoring_iff_forall_le (P := P) (score := fun r => pluralityScore (Fintype.card A) r)
    hA d).2 hle

lemma topCount_zero_of_mem_lowestScoring
    [DecidableEq A]
    (P : Profile V A) (d : A) (hd : topCount P d = 0)
    {c : A} (hc : c ∈ lowestScoring P (fun r => pluralityScore (Fintype.card A) r)) :
    topCount P c = 0 := by
  classical
  have hscore_d :
      scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) d = 0 := by
    have hd' : (votersTop P d).card = 0 := by
      simpa [topCount] using hd
    calc
      scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) d =
          (votersTop P d).card := by
            simpa [pluralityScore] using (pluralityScore_eq_votersTop_card (P := P) (c := d))
      _ = 0 := by
            exact_mod_cast hd'
  have hle :=
    scoreCandidate_le_of_mem_lowestScoring (P := P)
      (score := fun r => pluralityScore (Fintype.card A) r) (c := c) (e := d) hc
  have hle0 :
      scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) c ≤ 0 := by
    simpa [hscore_d] using hle
  have hnonneg :
      0 ≤ scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) c := by
    have hscore_c :
        scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) c =
          (votersTop P c).card := by
      simpa [pluralityScore] using (pluralityScore_eq_votersTop_card (P := P) (c := c))
    simp [hscore_c]
  have hscore_c :
      scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) c = 0 :=
    le_antisymm hle0 hnonneg
  have hscore_c' :
      scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) c = topCount P c := by
    simpa [topCount] using (pluralityScore_eq_votersTop_card (P := P) (c := c))
  have htc_int : (topCount P c : Int) = 0 := by
    exact hscore_c'.symm.trans hscore_c
  exact_mod_cast htc_int

lemma mem_scoringEliminationAux_relabel_iff'
    {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (score : Nat → Nat → Int) (P : Profile V A) (e : A ≃ B) (b : B) :
    b ∈ scoringEliminationAux score B (relabelProfile P e) ↔
      e.symm b ∈ scoringEliminationAux score A P := by
  classical
  have heq := scoringEliminationAux_equiv (score := score) (P := P) (e := e)
  constructor
  · intro hb
    have hb_map : b ∈ (scoringEliminationAux score A P).map e.toEmbedding := by
      simpa [heq] using hb
    exact (mem_relabelWinners (e := e) (s := scoringEliminationAux score A P) (b := b)).1 hb_map
  · intro hb
    have hb_map : b ∈ (scoringEliminationAux score A P).map e.toEmbedding := by
      exact (mem_relabelWinners (e := e) (s := scoringEliminationAux score A P) (b := b)).2 hb
    simpa [heq] using hb_map

noncomputable def liftFinset2 {A : Type} [DecidableEq A] {p : A → Prop}
    {q : {a : A // p a} → Prop} (s : Finset {x : {a : A // p a} // q x}) : Finset A := by
  classical
  exact s.image (fun x => x.1.1)

lemma mem_liftFinset2_iff_exists {A : Type} [DecidableEq A] {p : A → Prop}
    {q : {a : A // p a} → Prop} (s : Finset {x : {a : A // p a} // q x}) (a : A) :
    a ∈ liftFinset2 s ↔ ∃ x ∈ s, x.1.1 = a := by
  classical
  simp [liftFinset2, Finset.mem_image]

lemma liftFinset2_map_eq {A : Type} [DecidableEq A] {p : A → Prop} {q : {a : A // p a} → Prop}
    {p' : A → Prop} {q' : {a : A // p' a} → Prop}
    (s : Finset {x : {a : A // p a} // q x})
    (e : {x : {a : A // p a} // q x} ≃ {x : {a : A // p' a} // q' x})
    (hval : ∀ x, (e x).1.1 = x.1.1) :
    liftFinset2 (s.map e.toEmbedding) = liftFinset2 s := by
  classical
  ext a
  constructor
  · intro ha
    rcases (mem_liftFinset2_iff_exists (s := s.map e.toEmbedding) (a := a)).1 ha with ⟨x, hx, hxa⟩
    rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hya : y.1.1 = a := by
      simpa [hval y] using hxa
    exact (mem_liftFinset2_iff_exists (s := s) (a := a)).2 ⟨y, hy, hya⟩
  · intro ha
    rcases (mem_liftFinset2_iff_exists (s := s) (a := a)).1 ha with ⟨x, hx, hxa⟩
    have hxa' : (e x).1.1 = a := by
      simpa [hval x] using hxa
    have hx' : e x ∈ s.map e.toEmbedding := by
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    exact (mem_liftFinset2_iff_exists (s := s.map e.toEmbedding) (a := a)).2 ⟨e x, hx', hxa'⟩

lemma liftWinners_map_eq_liftFinset2 {A : Type} [DecidableEq A] {p : A → Prop}
    {q : {a : A // p a} → Prop} {r : A → Prop} [DecidablePred r]
    (s : Finset {x : {a : A // p a} // q x})
    (e : {x : {a : A // p a} // q x} ≃ {a : A // r a})
    (hval : ∀ x, (e x).1 = x.1.1) :
    liftWinners (s.map e.toEmbedding) = liftFinset2 s := by
  classical
  ext a
  constructor
  · intro ha
    have ha' : a ∈ (s.map e.toEmbedding).image (fun x => x.1) := by
      simpa [liftWinners] using ha
    rcases Finset.mem_image.mp ha' with ⟨x, hx, hxa⟩
    rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hya : y.1.1 = a := by
      exact (hval y).symm.trans hxa
    exact (mem_liftFinset2_iff_exists (s := s) (a := a)).2 ⟨y, hy, hya⟩
  · intro ha
    rcases (mem_liftFinset2_iff_exists (s := s) (a := a)).1 ha with ⟨y, hy, hya⟩
    have hx : e y ∈ s.map e.toEmbedding := by
      exact Finset.mem_map.mpr ⟨y, hy, rfl⟩
    have ha' : (e y).1 = a := (hval y).trans hya
    have : ∃ x ∈ s.map e.toEmbedding, x.1 = a := ⟨e y, hx, ha'⟩
    exact (by
      -- Expand membership in the image explicitly.
      simpa [liftWinners] using (Finset.mem_image.mpr this))

lemma liftFinset2_eq_liftFinset_liftFinset {A : Type} [DecidableEq A] {p : A → Prop}
    {q : {a : A // p a} → Prop} (s : Finset {x : {a : A // p a} // q x}) :
    liftFinset (liftFinset s) = liftFinset2 s := by
  classical
  ext a
  constructor
  · intro ha
    rcases (mem_liftFinset_iff (s := liftFinset s) (x := a)).1 ha with ⟨y, hy, hya⟩
    rcases (mem_liftFinset_iff (s := s) (x := y)).1 hy with ⟨x, hx, hxy⟩
    refine (mem_liftFinset2_iff_exists (s := s) (a := a)).2 ?_
    refine ⟨x, hx, ?_⟩
    simp [hxy, hya]
  · intro ha
    rcases (mem_liftFinset2_iff_exists (s := s) (a := a)).1 ha with ⟨x, hx, hxa⟩
    have hy : x.1 ∈ liftFinset s := by
      exact (mem_liftFinset_iff (s := s) (x := x.1)).2 ⟨x, hx, rfl⟩
    exact (mem_liftFinset_iff (s := liftFinset s) (x := a)).2 ⟨x.1, hy, by simp [hxa]⟩

lemma liftFinset2_eq_liftFinset_liftWinners {A : Type} [DecidableEq A] {p : A → Prop}
    {q : {a : A // p a} → Prop} [DecidablePred q]
    (s : Finset {x : {a : A // p a} // q x}) :
    liftFinset (liftWinners s) = liftFinset2 s := by
  classical
  ext a
  constructor
  · intro ha
    rcases (mem_liftFinset_iff (s := liftWinners s) (x := a)).1 ha with ⟨y, hy, hya⟩
    have hy' : y ∈ s.image (fun x => x.1) := by
      simpa [liftWinners] using hy
    rcases Finset.mem_image.mp hy' with ⟨x, hx, hxy⟩
    have hxa : x.1.1 = a := by
      simp [hxy, hya]
    exact (mem_liftFinset2_iff_exists (s := s) (a := a)).2 ⟨x, hx, hxa⟩
  · intro ha
    rcases (mem_liftFinset2_iff_exists (s := s) (a := a)).1 ha with ⟨x, hx, hxa⟩
    have hy : x.1 ∈ liftWinners s := by
      have : ∃ y ∈ s, y.1 = x.1 := ⟨x, hx, rfl⟩
      have : x.1 ∈ s.image (fun y => y.1) := Finset.mem_image.mpr this
      simpa [liftWinners] using this
    exact (mem_liftFinset_iff (s := liftWinners s) (x := a)).2 ⟨x.1, hy, by simp [hxa]⟩

noncomputable def restrictProfileSwapEquiv {A : Type} [DecidableEq A]
    (c d : A) (hcd : c ≠ d) :
    {x : {a : A // a ≠ c} // x ≠ ⟨d, Ne.symm hcd⟩} ≃
      {x : {a : A // a ≠ d} // x ≠ ⟨c, hcd⟩} := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rcases x with ⟨⟨a, ha⟩, hne⟩
    have hda : a ≠ d := by
      intro hEq
      apply hne
      apply Subtype.ext
      simp [hEq]
    refine ⟨⟨a, hda⟩, ?_⟩
    intro hEq
    apply ha
    exact congrArg Subtype.val hEq
  · intro x
    rcases x with ⟨⟨a, ha⟩, hne⟩
    have hca : a ≠ c := by
      intro hEq
      apply hne
      apply Subtype.ext
      simp [hEq]
    refine ⟨⟨a, hca⟩, ?_⟩
    intro hEq
    apply ha
    exact congrArg Subtype.val hEq
  · intro x
    cases x with
    | mk x hx =>
        cases x with
        | mk a ha =>
            apply Subtype.ext
            apply Subtype.ext
            rfl
  · intro x
    cases x with
    | mk x hx =>
        cases x with
        | mk a ha =>
            apply Subtype.ext
            apply Subtype.ext
            rfl

@[simp] lemma restrictProfileSwapEquiv_val {A : Type} [DecidableEq A]
    (c d : A) (hcd : c ≠ d)
    (x : {x : {a : A // a ≠ c} // x ≠ ⟨d, Ne.symm hcd⟩}) :
    (restrictProfileSwapEquiv c d hcd x).1.1 = x.1.1 := by
  cases x with
  | mk x hx =>
      cases x with
      | mk a ha =>
          simp [restrictProfileSwapEquiv]

@[simp] lemma restrictProfileSwapEquiv_symm_val {A : Type} [DecidableEq A]
    (c d : A) (hcd : c ≠ d)
    (x : {x : {a : A // a ≠ d} // x ≠ ⟨c, hcd⟩}) :
    ((restrictProfileSwapEquiv c d hcd).symm x).1.1 = x.1.1 := by
  cases x with
  | mk x hx =>
      cases x with
      | mk a ha =>
          simp [restrictProfileSwapEquiv]

lemma liftFinset_scoringEliminationAux_restrictProfile_swap
    [DecidableEq A] (P : Profile V A) (c d : A) (hcd : c ≠ d) :
    liftFinset2
        (scoringEliminationAux pluralityScore _
          (restrictProfile (restrictProfile P c) ⟨d, Ne.symm hcd⟩)) =
      liftFinset2
        (scoringEliminationAux pluralityScore _
          (restrictProfile (restrictProfile P d) ⟨c, hcd⟩)) := by
  classical
  let e := restrictProfileSwapEquiv (c := c) (d := d) hcd
  have hrel :
      relabelProfile (restrictProfile (restrictProfile P c) ⟨d, Ne.symm hcd⟩) e =
        restrictProfile (restrictProfile P d) ⟨c, hcd⟩ := by
    apply Profile.ext
    intro v
    apply LinearOrder.ext_lt
    intro a b
    simp [e]
    rfl
  have haux :=
    scoringEliminationAux_equiv (score := pluralityScore)
      (P := restrictProfile (restrictProfile P c) ⟨d, Ne.symm hcd⟩) (e := e)
  have haux' :
      scoringEliminationAux pluralityScore _
        (restrictProfile (restrictProfile P d) ⟨c, hcd⟩) =
      (scoringEliminationAux pluralityScore _
        (restrictProfile (restrictProfile P c) ⟨d, Ne.symm hcd⟩)).map e.toEmbedding := by
    simpa [hrel] using haux
  have hval : ∀ x, (e x).1.1 = x.1.1 := by
    intro x
    simp [e]
  calc
    liftFinset2
        (scoringEliminationAux pluralityScore _
          (restrictProfile (restrictProfile P c) ⟨d, Ne.symm hcd⟩)) =
      liftFinset2
        ((scoringEliminationAux pluralityScore _
          (restrictProfile (restrictProfile P c) ⟨d, Ne.symm hcd⟩)).map e.toEmbedding) := by
        symm
        exact liftFinset2_map_eq (s := scoringEliminationAux pluralityScore _
          (restrictProfile (restrictProfile P c) ⟨d, Ne.symm hcd⟩)) (e := e) hval
    _ = liftFinset2
        (scoringEliminationAux pluralityScore _
          (restrictProfile (restrictProfile P d) ⟨c, hcd⟩)) := by
        simp [haux']

lemma instantRunoffVoting_remove_zero_top
    [DecidableEq A] [Nonempty V]
    (P : Profile V A) (d : A) (hd : topCount P d = 0) :
    scoringEliminationAux pluralityScore A P =
      liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P d)) := by
  classical
  set n := Fintype.card A with hn
  let Motive : Nat → Prop := fun k =>
    ∀ {A : Type} [Fintype A] [DecidableEq A]
      {V : Type} [Fintype V] [Nonempty V]
      (P : Profile V A) (d : A),
      topCount P d = 0 →
      Fintype.card A = k →
      scoringEliminationAux pluralityScore A P =
        liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P d))
  have hStrong : Motive n := by
    classical
    refine Nat.strongRecOn (motive := Motive) n ?_
    intro k ih A _ _ V _ _ P d hd hcard
    by_cases hle : Fintype.card A ≤ 1
    · exfalso
      rcases Classical.choice (inferInstance : Nonempty V) with v0
      have hsub : ∀ a b : A, a = b := (Fintype.card_le_one_iff.mp hle)
      have htop : TopRank P v0 d := by
        intro b hb
        exact False.elim (hb (hsub b d))
      have hv : v0 ∈ votersTop P d := by
        simp [votersTop, htop]
      have hpos : 0 < topCount P d := by
        unfold topCount
        exact Finset.card_pos.mpr ⟨v0, hv⟩
      exact (Nat.ne_of_gt hpos) hd
    ·
      have haux :=
        scoringEliminationAux_eq_biUnion_of_not_card_le_one
          (score := pluralityScore) (P := P) (hcard := hle)
      let m := Fintype.card A
      let scoreVec : Nat → Int := fun r => pluralityScore m r
      let L : Finset A := lowestScoring P scoreVec
      have haux' :
          scoringEliminationAux pluralityScore A P =
            L.biUnion (fun c => liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P c))) := by
        simpa [m, scoreVec, L] using haux
      have hdL : d ∈ L := by
        simpa [scoreVec, L, m] using
          (lowestScoring_mem_of_topCount_zero (P := P) (d := d) hd)
      have hEq :
          ∀ c ∈ L,
            liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P c)) =
              liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P d)) := by
        intro c hcL
        by_cases hcd : c = d
        · subst hcd
          rfl
        ·
          have hc0 : topCount P c = 0 :=
            topCount_zero_of_mem_lowestScoring (P := P) (d := d) (hd := hd) hcL
          have hnot_top_c : ∀ v, ¬ TopRank P v c :=
            no_top_of_topCount_zero (P := P) (d := c) hc0
          have hnot_top_d : ∀ v, ¬ TopRank P v d :=
            no_top_of_topCount_zero (P := P) (d := d) hd
          have hcard_sub_lt :
              Fintype.card {x : A // x ≠ c} < k := by
            have hlt := card_restrict_lt c
            simpa [hcard] using hlt
          have hd_restrict : topCount (restrictProfile P c) ⟨d, Ne.symm hcd⟩ = 0 := by
            simpa [hd] using
              (topCount_restrictProfile_eq (P := P) (d := c)
                (hnot_top := hnot_top_c) (a := d) (hne := Ne.symm hcd))
          have hrec_c :=
            (ih (Fintype.card {x : A // x ≠ c}) hcard_sub_lt)
              (P := restrictProfile P c) (d := ⟨d, Ne.symm hcd⟩) hd_restrict rfl
          have hrec_c_lift :
              liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P c)) =
                liftFinset2
                  (scoringEliminationAux pluralityScore _
                    (restrictProfile (restrictProfile P c) ⟨d, Ne.symm hcd⟩)) := by
            have := congrArg liftFinset hrec_c
            simpa [liftFinset2_eq_liftFinset_liftFinset] using this
          have hcard_sub_lt' :
              Fintype.card {x : A // x ≠ d} < k := by
            have hlt := card_restrict_lt d
            simpa [hcard] using hlt
          have hc_restrict : topCount (restrictProfile P d) ⟨c, hcd⟩ = 0 := by
            simpa [hc0] using
              (topCount_restrictProfile_eq (P := P) (d := d)
                (hnot_top := hnot_top_d) (a := c) (hne := hcd))
          have hrec_d :=
            (ih (Fintype.card {x : A // x ≠ d}) hcard_sub_lt')
              (P := restrictProfile P d) (d := ⟨c, hcd⟩) hc_restrict rfl
          have hrec_d_lift :
              liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P d)) =
                liftFinset2
                  (scoringEliminationAux pluralityScore _
                    (restrictProfile (restrictProfile P d) ⟨c, hcd⟩)) := by
            have := congrArg liftFinset hrec_d
            simpa [liftFinset2_eq_liftFinset_liftFinset] using this
          calc
            liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P c)) =
              liftFinset2
                (scoringEliminationAux pluralityScore _
                  (restrictProfile (restrictProfile P c) ⟨d, Ne.symm hcd⟩)) := hrec_c_lift
            _ =
              liftFinset2
                (scoringEliminationAux pluralityScore _
                  (restrictProfile (restrictProfile P d) ⟨c, hcd⟩)) := by
                simpa using
                  (liftFinset_scoringEliminationAux_restrictProfile_swap (P := P) (c := c) (d := d) hcd)
            _ =
              liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P d)) := by
                symm
                exact hrec_d_lift
      apply Finset.ext
      intro a
      constructor
      · intro ha
        have ha' :
            a ∈ L.biUnion
                (fun c => liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P c))) := by
          simpa [haux'] using ha
        rcases Finset.mem_biUnion.mp ha' with ⟨c, hcL, haC⟩
        simpa [hEq c hcL] using haC
      · intro ha
        have ha' :
            a ∈ L.biUnion
                (fun c => liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P c))) := by
          refine Finset.mem_biUnion.mpr ?_
          refine ⟨d, hdL, ?_⟩
          simpa using ha
        simpa [haux'] using ha'
  exact hStrong (P := P) (d := d) hd hn

theorem instantRunoffVoting_independent_of_non_top
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A] [Nonempty V]
    (P : Profile V A) (p : A → Prop) [DecidablePred p]
    (hzero : ∀ a, ¬ p a → topCount P a = 0) :
    liftWinners (instantRunoffVoting (restrictCandidates P p)) = instantRunoffVoting P := by
  classical
  set n := Fintype.card A with hn
  let Motive : Nat → Prop := fun k =>
    ∀ {A : Type} [Fintype A] [DecidableEq A]
      {V : Type} [Fintype V] [Nonempty V]
      (P : Profile V A) (p : A → Prop) [DecidablePred p],
      (∀ a, ¬ p a → topCount P a = 0) →
      Fintype.card A = k →
      liftWinners (scoringEliminationAux pluralityScore _ (restrictCandidates P p)) =
        scoringEliminationAux pluralityScore A P
  have hStrong : Motive n := by
    classical
    refine Nat.strongRecOn (motive := Motive) n ?_
    intro k ih A _ _ V _ _ P p _ hp hcard
    by_cases hp_all : ∀ a : A, p a
    ·
      have hp_eq : p = fun _ : A => True := by
        funext a
        apply propext
        constructor
        · intro _; trivial
        · intro _; exact hp_all a
      let e : {a : A // True} ≃ A :=
        Equiv.subtypeUnivEquiv (p := fun _ : A => True) (by intro _; trivial)
      have hrel :
          relabelProfile (restrictCandidates P (fun _ : A => True)) e = P := by
        ext v
        rfl
      have haux :=
        scoringEliminationAux_equiv (score := pluralityScore)
          (P := restrictCandidates P (fun _ : A => True)) (e := e)
      have haux' :
          scoringEliminationAux pluralityScore A P =
            (scoringEliminationAux pluralityScore _ (restrictCandidates P (fun _ : A => True))).map
              e.toEmbedding := by
        simpa [hrel] using haux
      have hmap :
          liftWinners (scoringEliminationAux pluralityScore _ (restrictCandidates P (fun _ : A => True))) =
            (scoringEliminationAux pluralityScore _ (restrictCandidates P (fun _ : A => True))).map
              e.toEmbedding := by
        classical
        letI : DecidableEq A := Classical.decEq A
        ext a
        constructor
        · intro ha
          rcases Finset.mem_image.mp ha with ⟨x, hx, rfl⟩
          exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
        · intro ha
          rcases Finset.mem_map.mp ha with ⟨x, hx, rfl⟩
          exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      have hcast_lift :
          liftWinners (scoringEliminationAux pluralityScore _ (restrictCandidates P p)) =
            liftWinners (scoringEliminationAux pluralityScore _
              (restrictCandidates P (fun _ : A => True))) := by
        simpa using
          (liftWinners_scoringEliminationAux_restrictCandidates_congr
            (score := pluralityScore) (P := P) (p := p) (q := fun _ : A => True) hp_eq)
      calc
        liftWinners (scoringEliminationAux pluralityScore _ (restrictCandidates P p)) =
            liftWinners (scoringEliminationAux pluralityScore _ (restrictCandidates P (fun _ : A => True))) := by
              simpa using hcast_lift
        _ =
            (scoringEliminationAux pluralityScore _ (restrictCandidates P (fun _ : A => True))).map
              e.toEmbedding := hmap
        _ = scoringEliminationAux pluralityScore A P := by
              simpa using haux'.symm
    ·
      rcases not_forall.mp hp_all with ⟨d, hpd⟩
      have hd0 : topCount P d = 0 := hp d hpd
      have hremove : scoringEliminationAux pluralityScore A P =
          liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P d)) :=
        instantRunoffVoting_remove_zero_top (P := P) (d := d) hd0
      let p' : {a : A // a ≠ d} → Prop := fun x => p x.1
      have hp' : ∀ x : {a : A // a ≠ d}, ¬ p' x → topCount (restrictProfile P d) x = 0 := by
        intro x hx
        have hx0 : topCount P x.1 = 0 := hp x.1 hx
        have hnot_top_d : ∀ v, ¬ TopRank P v d :=
          no_top_of_topCount_zero (P := P) (d := d) hd0
        simpa [hx0] using
          (topCount_restrictProfile_eq (P := P) (d := d)
            (hnot_top := hnot_top_d) (a := x.1) (hne := x.2))
      have hcard_sub_lt : Fintype.card {x : A // x ≠ d} < k := by
        have hlt := card_restrict_lt d
        simpa [hcard] using hlt
      have hrec :=
        (ih (Fintype.card {x : A // x ≠ d}) hcard_sub_lt)
          (P := restrictProfile P d) (p := p') hp' rfl
      have hp_imp_ne : ∀ a, p a → a ≠ d := by
        intro a ha hEq
        subst hEq
        exact hpd ha
      have hp_eq : (fun a => a ≠ d ∧ p a) = p := by
        funext a
        apply propext
        constructor
        · intro h
          exact h.2
        · intro ha
          exact ⟨hp_imp_ne a ha, ha⟩
      have hp_eq' : (fun a => ¬a = d ∧ p a) = p := by
        funext a
        have h := congrArg (fun f => f a) hp_eq
        simpa using h
      have hrel :
          relabelProfile (restrictCandidates (restrictProfile P d) (fun x : {a : A // a ≠ d} => p x.1))
              (Equiv.subtypeSubtypeEquivSubtypeInter (fun a => a ≠ d) p) =
            restrictCandidates P (fun a => a ≠ d ∧ p a) := by
        simpa [restrictProfile] using
          (relabelProfile_restrictCandidates_subtypeSubtypeEquivSubtypeInter
            (P := P) (p := fun a => a ≠ d) (q := p))
      have haux :=
        scoringEliminationAux_equiv (score := pluralityScore)
          (P := restrictCandidates (restrictProfile P d) (fun x : {a : A // a ≠ d} => p x.1))
          (e := Equiv.subtypeSubtypeEquivSubtypeInter (fun a => a ≠ d) p)
      have haux' :
          scoringEliminationAux pluralityScore _ (restrictCandidates P (fun a => a ≠ d ∧ p a)) =
            (scoringEliminationAux pluralityScore _
              (restrictCandidates (restrictProfile P d) (fun x : {a : A // a ≠ d} => p x.1))).map
              (Equiv.subtypeSubtypeEquivSubtypeInter (fun a => a ≠ d) p).toEmbedding := by
        simpa [hrel] using haux
      have hval :
          ∀ x, (Equiv.subtypeSubtypeEquivSubtypeInter (fun a => a ≠ d) p x).1 = x.1.1 := by
        intro x
        rfl
      have hmap' :
          liftWinners (scoringEliminationAux pluralityScore _
              (restrictCandidates P (fun a => a ≠ d ∧ p a))) =
            liftFinset2 (scoringEliminationAux pluralityScore _
              (restrictCandidates (restrictProfile P d) (fun x : {a : A // a ≠ d} => p x.1))) := by
        calc
          liftWinners (scoringEliminationAux pluralityScore _
              (restrictCandidates P (fun a => a ≠ d ∧ p a))) =
              liftWinners
                ((scoringEliminationAux pluralityScore _
                  (restrictCandidates (restrictProfile P d) (fun x : {a : A // a ≠ d} => p x.1))).map
                  (Equiv.subtypeSubtypeEquivSubtypeInter (fun a => a ≠ d) p).toEmbedding) := by
                    simp [haux']
          _ = liftFinset2 (scoringEliminationAux pluralityScore _
                (restrictCandidates (restrictProfile P d) (fun x : {a : A // a ≠ d} => p x.1))) := by
                exact liftWinners_map_eq_liftFinset2
                  (s := scoringEliminationAux pluralityScore _
                    (restrictCandidates (restrictProfile P d) (fun x : {a : A // a ≠ d} => p x.1)))
                  (e := Equiv.subtypeSubtypeEquivSubtypeInter (fun a => a ≠ d) p) hval
      have hmap :
          liftWinners (scoringEliminationAux pluralityScore _ (restrictCandidates P p)) =
            liftFinset2 (scoringEliminationAux pluralityScore _
              (restrictCandidates (restrictProfile P d) (fun x : {a : A // a ≠ d} => p x.1))) := by
        have hpred :
            liftWinners (scoringEliminationAux pluralityScore _ (restrictCandidates P p)) =
              liftWinners (scoringEliminationAux pluralityScore _
                (restrictCandidates P (fun a => ¬a = d ∧ p a))) := by
          simpa using
            (liftWinners_scoringEliminationAux_restrictCandidates_congr
              (score := pluralityScore) (P := P) (p := p) (q := fun a => ¬a = d ∧ p a) hp_eq'.symm)
        calc
          liftWinners (scoringEliminationAux pluralityScore _ (restrictCandidates P p)) =
              liftWinners (scoringEliminationAux pluralityScore _
                (restrictCandidates P (fun a => ¬a = d ∧ p a))) := hpred
          _ =
              liftFinset2 (scoringEliminationAux pluralityScore _
                (restrictCandidates (restrictProfile P d) (fun x : {a : A // a ≠ d} => p x.1))) := hmap'
      have hrec_lift :
          liftFinset2 (scoringEliminationAux pluralityScore _
              (restrictCandidates (restrictProfile P d) (fun x : {a : A // a ≠ d} => p x.1))) =
            liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P d)) := by
        have hrec' := congrArg liftFinset hrec
        simpa [liftFinset2_eq_liftFinset_liftWinners] using hrec'
      have hleft :
          liftWinners (scoringEliminationAux pluralityScore _ (restrictCandidates P p)) =
            liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P d)) := by
        calc
          liftWinners (scoringEliminationAux pluralityScore _ (restrictCandidates P p)) =
              liftFinset2 (scoringEliminationAux pluralityScore _
                (restrictCandidates (restrictProfile P d) (fun x : {a : A // a ≠ d} => p x.1))) := hmap
          _ = liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P d)) := hrec_lift
      calc
        liftWinners (scoringEliminationAux pluralityScore _ (restrictCandidates P p)) =
            liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P d)) := hleft
        _ = scoringEliminationAux pluralityScore A P := by
            simpa using hremove.symm
  classical
  have hmain :=
    hStrong (P := P) (p := p) hzero hn
  have hdec :
      @scoringEliminationAux V _ pluralityScore { a // p a } (Subtype.fintype p)
          (inferInstance : DecidableEq {a : A // p a}) (restrictCandidates P p) =
        @scoringEliminationAux V _ pluralityScore { a // p a } (Subtype.fintype p)
          (fun a b => Classical.propDecidable (a = b)) (restrictCandidates P p) := by
    classical
    have hinst :
        (inferInstance : DecidableEq {a : A // p a}) =
          (fun a b => Classical.propDecidable (a = b)) := by
      funext a b
      apply Subsingleton.elim
    rw [hinst]
  have hmain' :
      liftWinners
          (@scoringEliminationAux V _ pluralityScore { a // p a } (Subtype.fintype p)
            (fun a b => Classical.propDecidable (a = b)) (restrictCandidates P p)) =
        scoringEliminationAux pluralityScore A P := by
    simpa [hdec] using hmain
  calc
    liftWinners (instantRunoffVoting (restrictCandidates P p)) =
        liftWinners
          (@scoringEliminationAux V _ pluralityScore { a // p a } (Subtype.fintype p)
            (fun a b => Classical.propDecidable (a = b)) (restrictCandidates P p)) := by
          simp [instantRunoffVoting, scoringEliminationRule]
    _ = scoringEliminationAux pluralityScore A P := hmain'
    _ = instantRunoffVoting P := by
          classical
          unfold instantRunoffVoting scoringEliminationRule
          have hinst :
              (inferInstance : DecidableEq A) =
                (fun a b => Classical.propDecidable (a = b)) := by
            funext a b
            apply Subsingleton.elim
          exact scoringEliminationAux_decidableEq_congr
            (score := pluralityScore) (P := P)
            (inst1 := inferInstance)
            (inst2 := fun a b => Classical.propDecidable (a = b))

theorem instantRunoffVoting_independenceOfDominated : IndependenceOfDominated instantRunoffVoting := by
  intro V A _ _ _ _ P c d hpref
  have hd0 : topCount P d = 0 :=
    topCount_eq_zero_of_dominated (P := P) (c := c) (d := d) hpref
  have hzero : ∀ a, ¬ a ≠ d → topCount P a = 0 := by
    intro a hnot
    have hEq : a = d := by
      by_contra hne
      exact hnot hne
    subst hEq
    exact hd0
  simpa using (instantRunoffVoting_independent_of_non_top (P := P) (p := fun a => a ≠ d) hzero)
