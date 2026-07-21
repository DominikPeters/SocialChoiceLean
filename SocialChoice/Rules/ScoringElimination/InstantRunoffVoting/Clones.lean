import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import SocialChoice.Axioms.Clones
import SocialChoice.Rules.ScoringElimination.Defs
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Neutrality
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.Defs
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.CondorcetLoser

namespace SocialChoice

open Finset

/-!
# IRV Satisfies Independence of Clones

This proof follows the proof from the paper
"Generalizing Instant Runoff Voting to Allow Indifferences" by Théo Delemazure and Dominik Peters
-/

variable {V A : Type} [Fintype V] [Fintype A]

/-! ## Clone sets and restriction helpers -/

lemma relabelProfile_removeClonesExcept_swap_rep
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x x' : A)
    (hX : CloneSet P X)
    (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    relabelProfile (removeClonesExcept P X x)
        (cloneSwapEquiv X x x' hx hx' hxx') =
      removeClonesExcept P X x' := by
  classical
  let e := cloneSwapEquiv X x x' hx hx' hxx'

  -- Helper: clones are interchangeable when comparing to a non-clone.
  have hclone_eq :
      ∀ v c, c ∉ X →
        (Prefers P v x c ↔ Prefers P v x' c) ∧ (Prefers P v c x ↔ Prefers P v c x') := by
    intro v c hc
    -- Work in the linear order given by voter `v`.
    let _ := P.pref v
    rcases hX with ⟨_, hclone⟩
    have hcase := hclone v c hc
    cases hcase with
    | inl hall =>
        have hxpref : Prefers P v x c := hall x hx
        have hx'pref : Prefers P v x' c := hall x' hx'
        have hxfalse : ¬ Prefers P v c x := by
          intro h
          exact lt_asymm hxpref h
        have hx'false : ¬ Prefers P v c x' := by
          intro h
          exact lt_asymm hx'pref h
        refine ⟨?_, ?_⟩
        · exact ⟨(fun _ => hx'pref), (fun _ => hxpref)⟩
        · exact ⟨(fun h => (hxfalse h).elim), (fun h => (hx'false h).elim)⟩
    | inr hall =>
        have hxpref : Prefers P v c x := hall x hx
        have hx'pref : Prefers P v c x' := hall x' hx'
        have hxfalse : ¬ Prefers P v x c := by
          intro h
          exact lt_asymm h hxpref
        have hx'false : ¬ Prefers P v x' c := by
          intro h
          exact lt_asymm h hx'pref
        refine ⟨?_, ?_⟩
        · exact ⟨(fun h => (hxfalse h).elim), (fun h => (hx'false h).elim)⟩
        · exact ⟨(fun _ => hx'pref), (fun _ => hxpref)⟩

  -- Helper: `e.symm` fixes non-clones.
  have esymm_nonclone :
      ∀ {c : A} (hc : c ∉ X),
        e.symm (⟨c, Or.inl hc⟩ : {a : A // clonePred X x' a}) =
          (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) := by
    intro c hc
    have hcx : c ≠ x := by
      intro h
      apply hc
      simpa [h] using hx
    have hcx' : c ≠ x' := by
      intro h
      apply hc
      simpa [h] using hx'
    apply Subtype.ext
    -- `e.symm` is induced by `swap x x'`, which fixes non-clones.
    simp [e, cloneSwapEquiv, Equiv.swap_apply_def, hcx, hcx']

  -- Helper: `e.symm` sends the representative `x'` back to `x`.
  have esymm_rep :
      e.symm (⟨x', Or.inr rfl⟩ : {a : A // clonePred X x' a}) =
        (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := by
    apply Subtype.ext
    simp [e, cloneSwapEquiv, Equiv.swap_apply_right]

  -- Main proof: ext by ballots and compare `<`.
  ext v : 1
  apply LinearOrder.ext_lt
  intro a b
  let _ := P.pref v
  change Prefers P v (e.symm a) (e.symm b) ↔ Prefers P v a b
  cases a with
  | mk a ha =>
    cases b with
    | mk b hb =>
      cases ha with
      | inl ha_not =>
        cases hb with
        | inl hb_not =>
          have ha_fix := esymm_nonclone (c := a) ha_not
          have hb_fix := esymm_nonclone (c := b) hb_not
          simp [ha_fix, hb_fix]
        | inr hb_eq =>
          subst hb_eq
          have ha_fix := esymm_nonclone (c := a) ha_not
          have hrel := (hclone_eq v a ha_not).2
          simpa [ha_fix, esymm_rep] using hrel
      | inr ha_eq =>
        subst ha_eq
        cases hb with
        | inl hb_not =>
          have hb_fix := esymm_nonclone (c := b) hb_not
          have hrel := (hclone_eq v b hb_not).1
          simpa [hb_fix, esymm_rep] using hrel
        | inr hb_eq =>
          subst hb_eq
          have hleft : ¬ Prefers P v x x := by
            simp [Prefers]
          have hright : ¬ Prefers P v b b := by
            simp [Prefers]
          constructor
          · intro h
            have h' : Prefers P v x x := by
              simpa [esymm_rep] using h
            exact (hleft h').elim
          · intro h
            exact (hright h).elim

lemma mem_liftWinners_iff {A : Type} [DecidableEq A] {p : A → Prop} [DecidablePred p]
    {s : Finset {a : A // p a}} {a : A} (ha : p a) :
    a ∈ liftWinners s ↔ (⟨a, ha⟩ : {a : A // p a}) ∈ s := by
  classical
  -- `liftWinners` is `image Subtype.val`.
  simp [liftWinners, Finset.mem_image, ha]

lemma scoringEliminationAux_swap_rep
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x x' : A)
    (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    scoringEliminationAux pluralityScore _
        (relabelProfile (removeClonesExcept P X x)
          (cloneSwapEquiv X x x' hx hx' hxx')) =
      (scoringEliminationAux pluralityScore _ (removeClonesExcept P X x)).map
        (cloneSwapEquiv X x x' hx hx' hxx').toEmbedding := by
  classical
  have h :=
    scoringEliminationAux_equiv (score := pluralityScore)
      (P := removeClonesExcept P X x) (e := cloneSwapEquiv X x x' hx hx' hxx')
  simpa using h

lemma mem_scoringEliminationAux_relabel_iff
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

lemma mem_scoringEliminationAux_of_mem_liftFinset
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) {ℓ c : A}
    (haux :
      scoringEliminationAux pluralityScore A P =
        (lowestScoring P pluralityScoreVec).biUnion
          (fun c => liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P c))))
    (hℓ_low : ℓ ∈ lowestScoring P pluralityScoreVec)
    (hc : c ∈ liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P ℓ))) :
    c ∈ scoringEliminationAux pluralityScore A P := by
  rw [haux]
  exact Finset.mem_biUnion.mpr ⟨ℓ, hℓ_low, by simpa using hc⟩

lemma nonclone_winner_swap
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x x' c : A)
    (hc : c ∉ X) (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) ∈
        scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) ↔
      (⟨c, Or.inl hc⟩ : {a : A // clonePred X x' a}) ∈
        scoringEliminationAux pluralityScore _
          (relabelProfile (removeClonesExcept P X x)
            (cloneSwapEquiv X x x' hx hx' hxx')) := by
    classical
  let e := cloneSwapEquiv X x x' hx hx' hxx'
  have hfix :
      e.symm (⟨c, Or.inl hc⟩ : {a : A // clonePred X x' a}) =
        (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) := by
    simpa [e] using
      (cloneSwapEquiv_symm_apply_nonclone (X := X) (x := x) (x' := x')
        (c := c) (hc := hc) (hx := hx) (hx' := hx') (hxx' := hxx'))
  have hrel :
      (⟨c, Or.inl hc⟩ : {a : A // clonePred X x' a}) ∈
          scoringEliminationAux pluralityScore _
            (relabelProfile (removeClonesExcept P X x) e) ↔
        e.symm (⟨c, Or.inl hc⟩ : {a : A // clonePred X x' a}) ∈
          scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) :=
    mem_scoringEliminationAux_relabel_iff (score := pluralityScore)
      (P := removeClonesExcept P X x) (e := e)
      (b := (⟨c, Or.inl hc⟩ : {a : A // clonePred X x' a}))
  constructor
  · intro hcwin
    have hcwin' :
        e.symm (⟨c, Or.inl hc⟩ : {a : A // clonePred X x' a}) ∈
          scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) := by
      simpa [hfix] using hcwin
    exact (hrel).mpr hcwin'
  · intro hcwin
    have hcwin' :
        e.symm (⟨c, Or.inl hc⟩ : {a : A // clonePred X x' a}) ∈
          scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) :=
      (hrel).mp hcwin
    simpa [hfix] using hcwin'

lemma clone_winner_swap
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x x' : A)
    (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈
        scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) ↔
      (⟨x', Or.inr rfl⟩ : {a : A // clonePred X x' a}) ∈
        scoringEliminationAux pluralityScore _
          (relabelProfile (removeClonesExcept P X x)
            (cloneSwapEquiv X x x' hx hx' hxx')) := by
  classical
  let e := cloneSwapEquiv X x x' hx hx' hxx'
  have hsymm :
      e.symm (⟨x', Or.inr rfl⟩ : {a : A // clonePred X x' a}) =
        (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := by
    simpa [e] using
      (cloneSwapEquiv_symm_apply_rep (X := X) (x := x) (x' := x')
        (hx := hx) (hx' := hx') (hxx' := hxx'))
  have hrel :
      (⟨x', Or.inr rfl⟩ : {a : A // clonePred X x' a}) ∈
          scoringEliminationAux pluralityScore _
            (relabelProfile (removeClonesExcept P X x) e) ↔
        e.symm (⟨x', Or.inr rfl⟩ : {a : A // clonePred X x' a}) ∈
          scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) :=
    mem_scoringEliminationAux_relabel_iff (score := pluralityScore)
      (P := removeClonesExcept P X x) (e := e)
      (b := (⟨x', Or.inr rfl⟩ : {a : A // clonePred X x' a}))
  constructor
  · intro hxwin
    have hxwin' :
        e.symm (⟨x', Or.inr rfl⟩ : {a : A // clonePred X x' a}) ∈
          scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) := by
      simpa [hsymm] using hxwin
    exact (hrel).mpr hxwin'
  · intro hxwin
    have hxwin' :
        e.symm (⟨x', Or.inr rfl⟩ : {a : A // clonePred X x' a}) ∈
          scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) :=
      (hrel).mp hxwin
    simpa [hsymm] using hxwin'


/-! ## Plurality score facts under clone restriction -/

noncomputable abbrev pluralityScoreVec : Nat → Int :=
  fun r => if r = 0 then 1 else 0

lemma topRank_removeClonesExcept_iff_of_nonclone
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A)
    (hX : CloneSet P X) (hx : x ∈ X) {a : A} (ha : a ∉ X) (v : V) :
    TopRank P v a ↔
      TopRank (removeClonesExcept P X x) v (⟨a, Or.inl ha⟩ : {a : A // clonePred X x a}) := by
  classical
  constructor
  · intro htop d hd
    have := htop d (by
      intro hEq
      apply hd
      ext
      simpa using hEq)
    simpa using this
  · intro htop d hd
    by_cases hdx : d ∈ X
    · -- If `d` is a clone, use clone symmetry and the fact that `x` is in the restricted profile.
      have hxa : Prefers P v a x := by
        have htop' := htop (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) (by
          intro hEq
          apply ha
          have hxEq : x = a := congrArg Subtype.val hEq
          simpa [hxEq] using hx)
        simpa using htop'
      have hrel :=
        (cloneSet_prefers_equiv P X hX hdx hx ha v).2
      -- `Prefers P v a d ↔ Prefers P v a x`
      exact (hrel.mpr hxa)
    · -- `d` is a non-clone, so it appears in the restricted profile.
      have htop' := htop (⟨d, Or.inl hdx⟩ : {a : A // clonePred X x a}) (by
        intro hEq
        apply hd
        simpa using congrArg Subtype.val hEq)
      simpa using htop'

lemma topRank_clone_implies_rep
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x y : A)
    (hX : CloneSet P X) (hx : x ∈ X) (hy : y ∈ X) (v : V) :
    TopRank P v y →
      TopRank (removeClonesExcept P X x) v (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := by
  classical
  intro htop d hd
  by_cases hdx : (d : A) ∈ X
  · -- Only `x` from `X` remains; the other case is `d = x`.
    have hxEq : (d : A) = x := by
      cases d.property with
      | inl hnot =>
        exact (hnot hdx).elim
      | inr hEq =>
        exact hEq
    exact (hd (by
      ext
      simpa using hxEq)).elim
  · -- For non-clones, use clone symmetry with `y`.
    have hrel := (cloneSet_prefers_equiv P X hX hy hx hdx v).1
    have hy_top : Prefers P v y d := htop d (by
      intro hEq
      apply hdx
      simpa [hEq] using hy)
    exact (hrel.mp hy_top)

lemma votersTop_card_nonclone_eq
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A)
    (hX : CloneSet P X) (hx : x ∈ X) {a : A} (ha : a ∉ X) :
    (votersTop P a).card =
      (votersTop (removeClonesExcept P X x) (⟨a, Or.inl ha⟩ : {a : A // clonePred X x a})).card := by
  classical
  refine cardinality_lemma2 (p := fun v => TopRank P v a)
    (q := fun v =>
      TopRank (removeClonesExcept P X x) v (⟨a, Or.inl ha⟩ : {a : A // clonePred X x a})) ?_
  intro v
  exact topRank_removeClonesExcept_iff_of_nonclone P X x hX hx ha v

lemma votersTop_card_rep_ge_clone
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x y : A)
    (hX : CloneSet P X) (hx : x ∈ X) (hy : y ∈ X) :
    (votersTop P y).card ≤
      (votersTop (removeClonesExcept P X x) (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a})).card := by
  classical
  refine cardinality_lemma (p := fun v => TopRank P v y)
    (q := fun v =>
      TopRank (removeClonesExcept P X x) v (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a})) ?_
  intro v hv
  exact topRank_clone_implies_rep P X x y hX hx hy v hv

lemma score_nonclone_eq
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A)
    (hX : CloneSet P X) (hx : x ∈ X) {a : A} (ha : a ∉ X) :
    scoreCandidate P pluralityScoreVec a =
      scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
        (⟨a, Or.inl ha⟩ : {a : A // clonePred X x a}) := by
  classical
  have hcard :=
    votersTop_card_nonclone_eq (P := P) (X := X) (x := x) (hX := hX) (hx := hx) (ha := ha)
  calc
    scoreCandidate P pluralityScoreVec a
        = ((votersTop P a).card : Int) := by
            simpa [pluralityScoreVec] using (pluralityScore_eq_votersTop_card (P := P) (c := a))
    _ = ((votersTop (removeClonesExcept P X x)
            (⟨a, Or.inl ha⟩ : {a : A // clonePred X x a})).card : Int) := by
            exact_mod_cast hcard
    _ = scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
            (⟨a, Or.inl ha⟩ : {a : A // clonePred X x a}) := by
            symm
            simpa [pluralityScoreVec] using
              (pluralityScore_eq_votersTop_card (P := removeClonesExcept P X x)
                (c := (⟨a, Or.inl ha⟩ : {a : A // clonePred X x a})))

lemma score_rep_ge_clone
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x y : A)
    (hX : CloneSet P X) (hx : x ∈ X) (hy : y ∈ X) :
    scoreCandidate P pluralityScoreVec y ≤
      scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
        (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := by
  classical
  have hcard :=
    votersTop_card_rep_ge_clone (P := P) (X := X) (x := x) (y := y) (hX := hX) (hx := hx) (hy := hy)
  have hcard' : (votersTop P y).card ≤
      (votersTop (removeClonesExcept P X x)
        (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a})).card := hcard
  have hcardInt :
      ((votersTop P y).card : Int) ≤
        ((votersTop (removeClonesExcept P X x)
          (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a})).card : Int) := by
    exact_mod_cast hcard'
  calc
    scoreCandidate P pluralityScoreVec y
        = ((votersTop P y).card : Int) := by
            simpa [pluralityScoreVec] using (pluralityScore_eq_votersTop_card (P := P) (c := y))
    _ ≤ ((votersTop (removeClonesExcept P X x)
          (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a})).card : Int) := hcardInt
    _ = scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
          (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := by
          symm
          simpa [pluralityScoreVec] using
            (pluralityScore_eq_votersTop_card (P := removeClonesExcept P X x)
              (c := (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a})))

lemma lowestScoring_nonclone_preserved
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x : A)
    (hX : CloneSet P X) (hx : x ∈ X) {ℓ : A} (hℓ : ℓ ∉ X)
    (hℓ_low : ℓ ∈ lowestScoring P pluralityScoreVec) :
    (⟨ℓ, Or.inl hℓ⟩ : {a : A // clonePred X x a}) ∈
      lowestScoring (removeClonesExcept P X x) pluralityScoreVec := by
  classical
  have hA : (Finset.univ : Finset A).Nonempty := by
    rcases hX.1 with ⟨y, _⟩
    have : Nonempty A := ⟨y⟩
    exact Finset.univ_nonempty
  have hAhat : (Finset.univ : Finset {a : A // clonePred X x a}).Nonempty := by
    letI : Nonempty {a : A // clonePred X x a} := ⟨⟨x, Or.inr rfl⟩⟩
    exact Finset.univ_nonempty
  have hℓ_low' :
      ∀ d : A, scoreCandidate P pluralityScoreVec ℓ ≤ scoreCandidate P pluralityScoreVec d :=
    (lowestScoring_iff_forall_le (P := P) (score := pluralityScoreVec) hA ℓ).1 hℓ_low
  have hle :
      ∀ d : {a : A // clonePred X x a},
        scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
            (⟨ℓ, Or.inl hℓ⟩ : {a : A // clonePred X x a})
          ≤ scoreCandidate (removeClonesExcept P X x) pluralityScoreVec d := by
    intro d
    cases d.property with
    | inl hdnot =>
      have hℓ_eq :=
        score_nonclone_eq (P := P) (X := X) (x := x) (hX := hX) (hx := hx) (ha := hℓ)
      have hd_eq :=
        score_nonclone_eq (P := P) (X := X) (x := x) (hX := hX) (hx := hx) (ha := hdnot)
      calc
        scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
              (⟨ℓ, Or.inl hℓ⟩ : {a : A // clonePred X x a})
            = scoreCandidate P pluralityScoreVec ℓ := by
                symm
                exact hℓ_eq
        _ ≤ scoreCandidate P pluralityScoreVec d := hℓ_low' d
        _ = scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
              (⟨d, Or.inl hdnot⟩ : {a : A // clonePred X x a}) := by
                exact hd_eq
    | inr hdx =>
      have hℓ_eq :=
        score_nonclone_eq (P := P) (X := X) (x := x) (hX := hX) (hx := hx) (ha := hℓ)
      have hx_le :=
        score_rep_ge_clone (P := P) (X := X) (x := x) (y := x) (hX := hX) (hx := hx) (hy := hx)
      have hℓx : scoreCandidate P pluralityScoreVec ℓ ≤ scoreCandidate P pluralityScoreVec x :=
        hℓ_low' x
      have hxEq : (d : A) = x := hdx
      have hdEq : d = (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := by
        ext
        simp [hxEq]
      calc
        scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
              (⟨ℓ, Or.inl hℓ⟩ : {a : A // clonePred X x a})
            = scoreCandidate P pluralityScoreVec ℓ := by
                symm
                exact hℓ_eq
        _ ≤ scoreCandidate P pluralityScoreVec x := hℓx
        _ ≤ scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
              (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := hx_le
        _ = scoreCandidate (removeClonesExcept P X x) pluralityScoreVec d := by
              simp [hdEq]
  exact (lowestScoring_iff_forall_le (P := removeClonesExcept P X x)
      (score := pluralityScoreVec) hAhat
      (⟨ℓ, Or.inl hℓ⟩ : {a : A // clonePred X x a})).2 hle

lemma lowestScoring_nonclone_reflect
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x : A)
    (hX : CloneSet P X) (hx : x ∈ X) {ℓ : A} (hℓ : ℓ ∉ X)
    (hℓ_low_cl :
      (⟨ℓ, Or.inl hℓ⟩ : {a : A // clonePred X x a}) ∈
        lowestScoring (removeClonesExcept P X x) pluralityScoreVec)
    (hclone_low : ¬ ∃ d, d ∈ lowestScoring P pluralityScoreVec ∧ d ∈ X) :
    ℓ ∈ lowestScoring P pluralityScoreVec := by
  classical
  have hA : (Finset.univ : Finset A).Nonempty := by
    rcases (by
      simpa using (hX.1 : X.Nonempty)) with ⟨a, _⟩
    haveI : Nonempty A := ⟨a⟩
    exact Finset.univ_nonempty
  apply (lowestScoring_iff_forall_le (P := P) (score := pluralityScoreVec) hA ℓ).2
  intro d
  by_cases hdX : d ∈ X
  · -- If a clone were lower, it would contradict `hclone_low`.
    by_contra hlt
    have hlt' : scoreCandidate P pluralityScoreVec d < scoreCandidate P pluralityScoreVec ℓ :=
      lt_of_not_ge hlt
    -- Any non-clone has score ≥ ℓ (from collapsed lowest).
    have hℓ_le_nonclone :
        ∀ a : A, a ∉ X →
          scoreCandidate P pluralityScoreVec ℓ ≤ scoreCandidate P pluralityScoreVec a := by
      intro a haX
      have hℓ_le_a_cl :
          scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
              (⟨ℓ, Or.inl hℓ⟩ : {a : A // clonePred X x a}) ≤
            scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
              (⟨a, Or.inl haX⟩ : {a : A // clonePred X x a}) :=
        scoreCandidate_le_of_mem_lowestScoring
          (P := removeClonesExcept P X x) (score := pluralityScoreVec) (hc := hℓ_low_cl)
      have hscore_a :=
        score_nonclone_eq (P := P) (X := X) (x := x) (hX := hX) (hx := hx) (ha := haX)
      have hscore_ℓ :=
        score_nonclone_eq (P := P) (X := X) (x := x) (hX := hX) (hx := hx) (ha := hℓ)
      -- Rewrite both sides to original scores.
      simpa [hscore_a, hscore_ℓ] using hℓ_le_a_cl
    -- Choose any non-clone a (exists since X ≠ univ).
    -- Pick a lowest-scoring candidate `w`.
    rcases lowestScoring_nonempty (P := P) (score := pluralityScoreVec) hA with ⟨w, hw⟩
    by_cases hwX : w ∈ X
    · exact (hclone_low ⟨w, hw, hwX⟩).elim
    · -- `w` is a non-clone, hence its score is ≥ ℓ, contradicting `d < ℓ`.
      have hℓ_le_w := hℓ_le_nonclone w hwX
      have hw_le_d :
          scoreCandidate P pluralityScoreVec w ≤ scoreCandidate P pluralityScoreVec d :=
        scoreCandidate_le_of_mem_lowestScoring
          (P := P) (score := pluralityScoreVec) (hc := hw)
      have hℓ_le_d : scoreCandidate P pluralityScoreVec ℓ ≤ scoreCandidate P pluralityScoreVec d :=
        le_trans hℓ_le_w hw_le_d
      have hcontra :
          scoreCandidate P pluralityScoreVec d < scoreCandidate P pluralityScoreVec d :=
        lt_of_lt_of_le hlt' hℓ_le_d
      exact (lt_irrefl _ hcontra).elim
  · -- d is a non-clone: use preservation of scores.
    have hℓ_le_d_cl :
        scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
            (⟨ℓ, Or.inl hℓ⟩ : {a : A // clonePred X x a}) ≤
          scoreCandidate (removeClonesExcept P X x) pluralityScoreVec
            (⟨d, Or.inl hdX⟩ : {a : A // clonePred X x a}) :=
      scoreCandidate_le_of_mem_lowestScoring
        (P := removeClonesExcept P X x) (score := pluralityScoreVec) (hc := hℓ_low_cl)
    have hscore_d :=
      score_nonclone_eq (P := P) (X := X) (x := x) (hX := hX) (hx := hx) (ha := hdX)
    have hscore_ℓ :=
      score_nonclone_eq (P := P) (X := X) (x := x) (hX := hX) (hx := hx) (ha := hℓ)
    simpa [hscore_d, hscore_ℓ] using hℓ_le_d_cl

/-! ## Main induction (proof sketch) -/

def irv_nonclone_prop
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x : A) : Prop :=
  ∀ a (ha : a ∉ X),
    a ∈ scoringEliminationAux pluralityScore A P ↔
      (⟨a, Or.inl ha⟩ : {a : A // clonePred X x a}) ∈
        scoringEliminationAux pluralityScore _ (removeClonesExcept P X x)

def irv_clone_prop
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x : A) : Prop :=
  (∃ y, y ∈ X ∧ y ∈ scoringEliminationAux pluralityScore A P) ↔
    (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈
      scoringEliminationAux pluralityScore _ (removeClonesExcept P X x)

/-! ## Restriction commutation helpers (up to relabeling) -/

/-- Deleting a non-clone candidate commutes with clone-removal (up to relabeling). -/
lemma relabelProfile_restrictProfile_removeClonesExcept_of_nonclone
  {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
  (P : Profile V A) (X : Set A) (x ℓ : A)
  (hxℓ : x ≠ ℓ) (hℓ : ℓ ∉ X) :
  ∃ e,
    (∀ t,
      ((e t).1 : {a : A // a ≠ ℓ}).1 = ((t.1 : {a : A // clonePred X x a}).1)) ∧
    (∀ b,
      ((e.symm b).1 : {a : A // clonePred X x a}).1 = ((b.1 : {a : A // a ≠ ℓ}).1)) ∧
    relabelProfile
        (restrictProfile (removeClonesExcept P X x)
          (⟨ℓ, Or.inl hℓ⟩ : {a : A // clonePred X x a}))
        e =
      removeClonesExcept (restrictProfile P ℓ) (restrictCloneSet X ℓ)
        (⟨x, hxℓ⟩ : {a : A // a ≠ ℓ}) := by
  classical
  let p : A → Prop := clonePred X x
  let q : A → Prop := fun a => a ≠ ℓ
  let ℓ' : {a : A // p a} := ⟨ℓ, Or.inl hℓ⟩
  let xℓ' : {a : A // q a} := ⟨x, hxℓ⟩
  let e_val : {t : {a : A // p a} // t ≠ ℓ'} ≃ {t : {a : A // p a} // q t.1} :=
    Equiv.subtypeEquivRight (fun t => by
      constructor
      · intro ht
        have : t.1 ≠ ℓ := by
          intro hEq
          apply ht
          ext
          simp [ℓ', hEq]
        exact this
      · intro ht hEq
        apply ht
        simpa using congrArg Subtype.val hEq)
  let e1 : {t : {a : A // p a} // q t.1} ≃ {a : A // p a ∧ q a} :=
    Equiv.subtypeSubtypeEquivSubtypeInter p q
  let ecomm : {a : A // p a ∧ q a} ≃ {a : A // q a ∧ p a} :=
    Equiv.subtypeEquivRight (fun a => by
      constructor <;> intro h <;> simpa [And.comm] using h)
  let e2 : {t : {a : A // q a} // p t.1} ≃ {a : A // q a ∧ p a} :=
    Equiv.subtypeSubtypeEquivSubtypeInter q p
  let e_mid : {t : {a : A // p a} // t ≠ ℓ'} ≃ {t : {a : A // q a} // p t.1} :=
    e_val.trans (e1.trans (ecomm.trans e2.symm))
  let e_right :
      {t : {a : A // q a} // p t.1} ≃
        {t : {a : A // q a} // clonePred (restrictCloneSet X ℓ) xℓ' t} :=
    Equiv.subtypeEquivRight (fun t => by
      have hpred :
          clonePred (restrictCloneSet X ℓ) xℓ' t ↔ clonePred X x t.1 := by
        have := congrArg (fun f => f t)
          (clonePred_restrictCloneSet_eq (X := X) (x := x) (ℓ := ℓ) (hxℓ := hxℓ))
        exact (Iff.of_eq this)
      simpa [p] using hpred.symm)
  let e : {t : {a : A // p a} // t ≠ ℓ'} ≃
      {t : {a : A // q a} // clonePred (restrictCloneSet X ℓ) xℓ' t} :=
    e_mid.trans e_right
  refine ⟨e, ?_, ?_, ?_⟩
  · intro t
    rfl
  · intro b
    rfl
  -- Unfold both sides; the induced restricted orders coincide definitionally.
  ext v
  rfl

/-! ## Main induction proof -/

/-- Combined clone properties as a single proposition for induction. -/
def clone_independence_props
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x : A) : Prop :=
  irv_nonclone_prop P X x ∧ irv_clone_prop P X x

omit [Fintype A] in
/-- The type `{a // clonePred X x a}` equals `{a // a ∉ X ∨ a = x}` -/
lemma clonePred_eq_or (X : Set A) (x : A) :
  clonePred X x = fun a => a ∉ X ∨ a = x := rfl

lemma not_card_le_one_clonePred
    {A : Type} [Fintype A] [DecidableEq A]
    (X : Set A) (x : A) (hx : x ∈ X) (hX : X ≠ Set.univ) :
    ¬ Fintype.card {a : A // clonePred X x a} ≤ 1 := by
  classical
  have hne : ∃ w : A, w ∉ X := by
    by_contra hall
    push Not at hall
    exact hX (Set.eq_univ_of_forall hall)
  rcases hne with ⟨w, hw⟩
  intro hle
  have hsub : Subsingleton {a : A // clonePred X x a} :=
    Fintype.card_le_one_iff_subsingleton.1 hle
  have hneq :
      (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ≠
        (⟨w, Or.inl hw⟩ : {a : A // clonePred X x a}) := by
    intro hEq
    have hxw : x = w := by
      simpa using congrArg Subtype.val hEq
    exact hw (hxw ▸ hx)
  exact hneq (Subsingleton.elim _ _)

/-- Key lemma: winning as non-clone is independent of representative choice (via relabeling). -/
lemma nonclone_winner_rep_independent
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x x' c : A)
    (hc : c ∉ X) (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) ∈
        scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) ↔
      (⟨c, Or.inl hc⟩ : {a : A // clonePred X x' a}) ∈
        scoringEliminationAux pluralityScore _
          (relabelProfile (removeClonesExcept P X x)
            (cloneSwapEquiv X x x' hx hx' hxx')) := by
  classical
  simpa using nonclone_winner_swap P X x x' c hc hx hx' hxx'

/-! Key lemma: clone winner status is independent under relabeling. -/
lemma clone_winner_rep_independent
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x x' : A)
    (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈
        scoringEliminationAux pluralityScore _ (removeClonesExcept P X x) ↔
      (⟨x', Or.inr rfl⟩ : {a : A // clonePred X x' a}) ∈
        scoringEliminationAux pluralityScore _
          (relabelProfile (removeClonesExcept P X x)
            (cloneSwapEquiv X x x' hx hx' hxx')) := by
  classical
  simpa using
    clone_winner_swap (P := P) (X := X) (x := x) (x' := x')
      (hx := hx) (hx' := hx') (hxx' := hxx')


theorem irv_independence_of_clones :
    @IndependenceOfClones (scoringEliminationRule pluralityScore) := by
  unfold IndependenceOfClones
  intro V A instV instA instDecEq P₀ X x hX hx
  classical
  -- `scoringEliminationRule` uses `Classical.decEq` internally; align all `DecidableEq` instances.
  letI : DecidableEq A := Classical.decEq A
  -- We prove by strong induction on the number of candidates
  set n := Fintype.card A with hn
  -- Define the motive for strong induction
  let Motive : Nat → Prop := fun k =>
    ∀ {A' : Type} [Fintype A'] [DecidableEq A'],
      Fintype.card A' = k →
        ∀ {V' : Type} [Fintype V'] (P' : Profile V' A') (X' : Set A') (x' : A'),
          CloneSet P' X' → x' ∈ X' → clone_independence_props P' X' x'
  -- Strong induction
  have hStrong : Motive n := by
    classical
    refine Nat.strongRecOn (motive := Motive) n ?_
    intro k ih A' _ _ hcard V' _ P' X' x' hX' hx'
    -- Handle trivial cases
    by_cases hX_singleton : ∀ y ∈ X', y = x'
    · -- X' = {x'}, so removeClonesExcept P' X' x' ≃ P'
      refine ⟨?_, ?_⟩
      · -- irv_nonclone_prop
        intro c hc
        -- Since hc : c ∉ X' and hX_singleton says X' = {x'}, we have c ≠ x'
        -- The restricted profile has the same candidates since only x' is in X'
        -- and x' is kept
        classical
        -- Every candidate satisfies the clone predicate when X' is a singleton.
        have hpred : ∀ a : A', clonePred X' x' a := by
          intro a
          by_cases hax : a = x'
          · subst hax
            exact Or.inr rfl
          · left
            intro haX
            exact hax (hX_singleton a haX)
        -- Equivalence between A' and the restricted candidate subtype.
        let e : A' ≃ {a : A' // clonePred X' x' a} :=
          { toFun := fun a => ⟨a, hpred a⟩
            invFun := fun s => (s : A')
            left_inv := by intro a; rfl
            right_inv := by intro s; ext; rfl }
        have hrelabel : relabelProfile P' e = removeClonesExcept P' X' x' := by
          ext v
          rfl
        -- Neutrality / equivariance of scoring elimination under relabeling.
        have hmem :
            (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' x' a}) ∈
                scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x') ↔
              c ∈ scoringEliminationAux pluralityScore A' P' := by
          let b : {a : A' // clonePred X' x' a} := ⟨c, Or.inl hc⟩
          have hb :
              b ∈ scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x') ↔
                e.symm b ∈ scoringEliminationAux pluralityScore A' P' := by
            simpa [hrelabel] using
              (mem_scoringEliminationAux_relabel_iff
                (score := pluralityScore) (P := P') (e := e) (b := b))
          have hsymm : e.symm b = c := by rfl
          simpa [b, hsymm] using hb
        exact hmem.symm
      · -- irv_clone_prop
        -- (∃ y ∈ X', y wins) ↔ x' wins in restricted
        -- Since X' = {x'}, LHS is just (x' wins in P')
        classical
        -- Every candidate satisfies the clone predicate when X' is a singleton.
        have hpred : ∀ a : A', clonePred X' x' a := by
          intro a
          by_cases hax : a = x'
          · subst hax
            exact Or.inr rfl
          · left
            intro haX
            exact hax (hX_singleton a haX)
        let e : A' ≃ {a : A' // clonePred X' x' a} :=
          { toFun := fun a => ⟨a, hpred a⟩
            invFun := fun s => (s : A')
            left_inv := by intro a; rfl
            right_inv := by intro s; ext; rfl }
        have hrelabel : relabelProfile P' e = removeClonesExcept P' X' x' := by
          ext v
          rfl
        have hxmem :
            (⟨x', Or.inr rfl⟩ : {a : A' // clonePred X' x' a}) ∈
                scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x') ↔
              x' ∈ scoringEliminationAux pluralityScore A' P' := by
          let b : {a : A' // clonePred X' x' a} := ⟨x', Or.inr rfl⟩
          have hb :
              b ∈ scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x') ↔
                e.symm b ∈ scoringEliminationAux pluralityScore A' P' := by
            simpa [hrelabel] using
              (mem_scoringEliminationAux_relabel_iff
                (score := pluralityScore) (P := P') (e := e) (b := b))
          have hsymm : e.symm b = x' := by rfl
          simpa [b, hsymm] using hb
        -- Now convert between “some clone wins” and “x' wins” using singletonness.
        constructor
        · intro hex
          rcases hex with ⟨y, hyX, hywin⟩
          have hyEq : y = x' := hX_singleton y hyX
          subst hyEq
          exact (hxmem.mpr hywin)
        · intro hxwin
          refine ⟨x', hx', ?_⟩
          exact (hxmem.mp hxwin)
    · push Not at hX_singleton
      -- There exists y ∈ X' with y ≠ x'
      rcases hX_singleton with ⟨y, hy, hyx⟩
      -- Check if all candidates are clones
      by_cases hX_all : X' = Set.univ
      · -- All candidates are clones
        -- removeClonesExcept P' X' x' has only x' as candidate
        -- scoringEliminationAux returns univ for 1-candidate elections
        refine ⟨?_, ?_⟩
        · intro c hc
          -- c ∉ X' = univ, contradiction
          exact (hc (hX_all ▸ Set.mem_univ c)).elim
        · -- (∃ y ∈ X', y wins) ↔ x' wins in restricted
          constructor
          · intro _
            -- x' wins in 1-candidate election (it's the only candidate)
            -- In 1-candidate case, univ is returned
            classical
            -- The restricted candidate type is a subsingleton when `X' = univ`.
            have hsub : Subsingleton {a : A' // clonePred X' x' a} := by
              refine ⟨?_⟩
              intro a b
              ext
              have ha : (a : A') = x' := by
                -- `a ∉ univ` is false, so the predicate forces `a = x'`.
                simpa [clonePred, hX_all] using a.property
              have hb : (b : A') = x' := by
                simpa [clonePred, hX_all] using b.property
              simp [ha, hb]
            have hcard_le : Fintype.card {a : A' // clonePred X' x' a} ≤ 1 :=
              Fintype.card_le_one_iff_subsingleton.2 hsub
            -- Base case of the elimination procedure.
            simp [scoringEliminationAux, hcard_le]
          · intro _
            -- Some clone wins in P' - in fact, all candidates win when there's 1+
            classical
            haveI : Nonempty A' := by
              -- `X' = univ` and `CloneSet` gives `X'.Nonempty`.
              rcases (by
                simpa [hX_all] using (hX'.1 : X'.Nonempty)) with ⟨a, _⟩
              exact ⟨a⟩
            rcases scoringEliminationAux_nonempty (score := pluralityScore) (P := P') with ⟨w, hw⟩
            refine ⟨w, ?_, hw⟩
            simp [hX_all]
      · push Not at hX_all
        -- General case: use strong induction
        -- Unfold scoringEliminationAux and do case analysis
        by_cases hcard_le : Fintype.card A' ≤ 1
        · -- 0 or 1 candidates
          -- With ≤ 1 candidates and X' ⊂ A', X' must be empty, contradicting hX'.1
          rcases hX' with ⟨⟨z, hz⟩, _⟩
          have hne : ∃ w, w ∉ X' := by
            by_contra hall
            push Not at hall
            have hXuniv : X' = Set.univ := Set.eq_univ_of_forall hall
            exact hX_all hXuniv
          rcases hne with ⟨w, hw⟩
          -- We have z ∈ X' and w ∉ X', so z ≠ w
          have hzw : z ≠ w := by
            intro hEq
            exact hw (hEq ▸ hz)
          -- But card A' ≤ 1 means all elements are equal
          have hsub : Subsingleton A' := Fintype.card_le_one_iff_subsingleton.1 hcard_le
          exact (hzw (Subsingleton.elim z w)).elim
        · push Not at hcard_le
          -- Card > 1, so we can recurse
          refine ⟨?_, ?_⟩
          · -- irv_nonclone_prop
            intro c hc
            constructor
            · -- c ∈ winners(P') → c ∈ winners(P' - X' + x')
              intro hcwin
              -- Unfold one step of elimination
              have haux := scoringEliminationAux_eq_biUnion_of_not_card_le_one
                (score := pluralityScore) (P := P') (by omega : ¬ Fintype.card A' ≤ 1)
              rw [haux] at hcwin
              -- c is in biUnion, so there exists ℓ ∈ lowestScoring such that c ∈ winners(P'-ℓ)
              rcases Finset.mem_biUnion.mp hcwin with ⟨ℓ, hℓ_low, hc_rec⟩
              -- Case split on whether ℓ ∈ X'
              by_cases hℓX : ℓ ∈ X'
              · -- ℓ ∈ X': use IH on P'-ℓ with clone set X'\{ℓ}
                classical
                rcases
                    (_root_.SocialChoice.mem_liftFinset_iff_subtype
                      (s := scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ}
                        (restrictProfile P' ℓ))
                      (x := c)).1 hc_rec with ⟨hcnℓ, hc_rec'⟩

                have hklt : Fintype.card {x : A' // x ≠ ℓ} < k := by
                  simpa [hcard] using (card_restrict_lt (A := A') ℓ)

                by_cases hℓeq : ℓ = x'
                ·
                  -- Prefer eliminating `ℓ` (not `x'`) so we can keep using `x'` below.
                  have hx'ℓ : x' = ℓ := hℓeq.symm
                  subst hx'ℓ
                  -- Use the witness `y ∈ X'` with `y ≠ x'` from the outer scope.
                  let xℓ : {x : A' // x ≠ x'} := ⟨y, by simpa using hyx⟩
                  have hX_restr : CloneSet (restrictProfile P' x') (restrictCloneSet X' x') :=
                    cloneSet_restrictProfile (P := P') (X := X') (ℓ := x') (hX := hX')
                      ⟨y, hy, by simpa using hyx⟩
                  have hxℓ_mem : xℓ ∈ restrictCloneSet X' x' := by
                    simpa [restrictCloneSet, xℓ] using hy
                  have hrecProps :
                      clone_independence_props (restrictProfile P' x') (restrictCloneSet X' x') xℓ := by
                    have hM : Motive (Fintype.card {x : A' // x ≠ x'}) := ih _ hklt
                    exact hM (A' := {x : A' // x ≠ x'}) rfl (P' := restrictProfile P' x')
                      (X' := restrictCloneSet X' x') (x' := xℓ) hX_restr hxℓ_mem
                  have hnon_restr :
                      irv_nonclone_prop (restrictProfile P' x') (restrictCloneSet X' x') xℓ :=
                    hrecProps.1

                  have hc_restr : (⟨c, hcnℓ⟩ : {x : A' // x ≠ x'}) ∉ restrictCloneSet X' x' := by
                    intro hmem
                    apply hc
                    simpa [restrictCloneSet] using hmem

                  have hc_after_remove :
                      (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                          {a : {x : A' // x ≠ x'} // clonePred (restrictCloneSet X' x') xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (removeClonesExcept (restrictProfile P' x') (restrictCloneSet X' x') xℓ) := by
                    have := (hnon_restr (⟨c, hcnℓ⟩ : {x : A' // x ≠ x'}) hc_restr).mp hc_rec'
                    simpa using this

                  -- Rewrite the restricted collapse as a relabeling of the full collapse with rep `y`.
                  rcases
                      relabelProfile_removeClonesExcept_restrictProfile_of_clone
                        (P := P') (X := X') (x := y) (ℓ := x') (hℓ := hx') (hxℓ := hyx)
                    with ⟨e, he_val, he_symm_val, hcomm⟩

                  have hbR' :
                      (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                          {a : {x : A' // x ≠ x'} // clonePred (restrictCloneSet X' x') xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (relabelProfile (removeClonesExcept P' X' y) e) := by
                    simpa [hcomm] using hc_after_remove

                  have hb_pre :
                      e.symm (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                        {a : {x : A' // x ≠ x'} // clonePred (restrictCloneSet X' x') xℓ a})
                        ∈ scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y) :=
                    (mem_scoringEliminationAux_relabel_iff
                      (score := pluralityScore) (P := removeClonesExcept P' X' y) (e := e)
                      (b := (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                        {a : {x : A' // x ≠ x'} // clonePred (restrictCloneSet X' x') xℓ a}))).1 hbR'

                  have hb_val :
                      (e.symm (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩)).1 = c := by
                    -- `he_symm_val` gives the underlying value of the preimage.
                    simpa using (he_symm_val (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩))
                  have hb_val' :
                      e.symm (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩) =
                        (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' y a}) := by
                    apply Subtype.ext
                    simp [hb_val]
                  have hc_win_y :
                      (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' y a}) ∈
                        scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y) := by
                    simpa [hb_val'] using hb_pre

                  -- Switch representative from `y` to `x'` (full collapse).
                  have hswapProf :
                      relabelProfile (removeClonesExcept P' X' y)
                          (cloneSwapEquiv X' y x' hy hx' (by simpa using hyx)) =
                        removeClonesExcept P' X' x' :=
                    relabelProfile_removeClonesExcept_swap_rep
                      (P := P') (X := X') (x := y) (x' := x')
                      (hX := hX')
                      (hx := hy) (hx' := hx') (hxx' := by simpa using hyx)

                  have hc_win_relabel :
                      (cloneSwapEquiv X' y x' hy hx' (by simpa using hyx))
                          (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' y a}) ∈
                        (scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y)).map
                          (cloneSwapEquiv X' y x' hy hx' (by simpa using hyx)).toEmbedding := by
                    exact Finset.mem_map_of_mem _ hc_win_y

                  -- Rewrite the target winners using `hswapProf` and equivariance.
                  have hswapW :=
                    scoringEliminationAux_equiv (score := pluralityScore)
                      (P := removeClonesExcept P' X' y)
                      (e := cloneSwapEquiv X' y x' hy hx' (by simpa using hyx))
                  -- The mapped membership is precisely membership in the relabeled winners.
                  have hc_win_relabeled :
                      (cloneSwapEquiv X' y x' hy hx' (by simpa using hyx))
                          (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' y a}) ∈
                        scoringEliminationAux pluralityScore _
                          (relabelProfile (removeClonesExcept P' X' y)
                            (cloneSwapEquiv X' y x' hy hx' (by simpa using hyx))) := by
                    -- Use `hswapW` as a rewrite.
                    simpa [hswapW] using hc_win_relabel

                  -- Finally rewrite the profile to `removeClonesExcept P' X' x'`.
                  have hfix :=
                    cloneSwapEquiv_apply_nonclone (X := X') (x := y) (x' := x') (c := c)
                      (hc := hc) (hx := hy) (hx' := hx') (hxx' := by simpa using hyx)
                  simpa [hswapProf, hfix] using hc_win_relabeled
                · -- `ℓ ≠ x'`: keep the same representative `x'` in the restricted election.
                  have hxne : x' ≠ ℓ := by
                    intro hEq
                    exact hℓeq hEq.symm
                  let xℓ : {x : A' // x ≠ ℓ} := ⟨x', hxne⟩
                  have hXne' : ∃ x0 ∈ X', x0 ≠ ℓ := ⟨x', hx', hxne⟩
                  have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                    cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX') hXne'
                  have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                    simpa [restrictCloneSet, xℓ] using hx'
                  have hrecProps :
                      clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                    have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                    exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                      (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                  have hnon_restr :
                      irv_nonclone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                    hrecProps.1
                  have hc_restr : (⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}) ∉ restrictCloneSet X' ℓ := by
                    intro hmem
                    apply hc
                    simpa [restrictCloneSet] using hmem
                  have hc_after_remove :
                      (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                          {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    have := (hnon_restr (⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}) hc_restr).mp hc_rec'
                    simpa using this
                  rcases
                      relabelProfile_removeClonesExcept_restrictProfile_of_clone
                        (P := P') (X := X') (x := x') (ℓ := ℓ) (hℓ := hℓX) (hxℓ := hxne)
                    with ⟨e, he_val, he_symm_val, hcomm⟩
                  have hbR' :
                      (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                          {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (relabelProfile (removeClonesExcept P' X' x') e) := by
                    simpa [hcomm] using hc_after_remove
                  have hb_pre :
                      e.symm (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x') :=
                    (mem_scoringEliminationAux_relabel_iff
                      (score := pluralityScore) (P := removeClonesExcept P' X' x') (e := e)
                      (b := (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}))).1 hbR'
                  have hb_val :
                      ((e.symm (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩)).1 : A') = c := by
                    simpa using (he_symm_val (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩))
                  have hb_val' :
                      e.symm (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩) =
                        (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' x' a}) := by
                    apply Subtype.ext
                    simp [hb_val]
                  simpa [hb_val'] using hb_pre
              · -- ℓ ∉ X': ℓ is also lowest in P'-X'+x', use IH on P'-ℓ with clone set X'
                classical
                have hℓnotX : ℓ ∉ X' := hℓX

                -- Extract the recursive winner and its inequality from `hc_rec`.
                rcases
                    (_root_.SocialChoice.mem_liftFinset_iff_subtype
                      (s := scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ}
                        (restrictProfile P' ℓ))
                      (x := c)).1 hc_rec with ⟨hcnℓ, hc_rec'⟩

                -- Apply IH to the restricted profile `P' - ℓ`.
                have hklt : Fintype.card {x : A' // x ≠ ℓ} < k := by
                  simpa [hcard] using (card_restrict_lt (A := A') ℓ)
                have hxne : x' ≠ ℓ := by
                  intro hEq
                  apply hℓnotX
                  simpa [hEq] using hx'
                let xℓ : {x : A' // x ≠ ℓ} := ⟨x', hxne⟩
                have hXne' : ∃ x0 ∈ X', x0 ≠ ℓ := ⟨x', hx', hxne⟩
                have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                  cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX') hXne'
                have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                  -- membership is by value
                  simpa [restrictCloneSet, xℓ] using hx'
                have hrecProps : clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                  -- specialize IH
                  have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                  exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                    (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                have hnon_restr :
                    irv_nonclone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                  hrecProps.1

                have hc_restr : (⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}) ∉ restrictCloneSet X' ℓ := by
                  intro hmem
                  apply hc
                  simpa [restrictCloneSet] using hmem

                have hc_after_remove :
                    (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                      ∈ scoringEliminationAux pluralityScore _
                          (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                  -- use the IH equivalence
                  have := (hnon_restr (⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}) hc_restr).mp hc_rec'
                  simpa using this

                -- Transport this recursive-winner fact to the clone-restricted election where
                -- `ℓ` is eliminated first.
                have hxℓ' : x' ≠ ℓ := hxne
                rcases
                    relabelProfile_restrictProfile_removeClonesExcept_of_nonclone
                      (P := P') (X := X') (x := x') (ℓ := ℓ) (hxℓ := hxℓ') (hℓ := hℓnotX)
                  with ⟨e, he_val, he_symm_val, hcomm⟩

                -- Unfold one step of elimination on the clone-restricted election.
                have hcard_cl : ¬ Fintype.card {a : A' // clonePred X' x' a} ≤ 1 :=
                  not_card_le_one_clonePred (X := X') (x := x') (hx := hx') (hX := hX_all)

                have haux_cl :=
                  scoringEliminationAux_eq_biUnion_of_not_card_le_one
                    (score := pluralityScore) (P := removeClonesExcept P' X' x') (hcard := hcard_cl)

                -- Show membership in the RHS biUnion by choosing the elimination candidate `ℓ`.
                have hℓ_low' : ℓ ∈ lowestScoring P' pluralityScoreVec := by
                  simpa [pluralityScore, pluralityScoreVec] using hℓ_low
                have hℓ_low_cl :
                    (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}) ∈
                      lowestScoring (removeClonesExcept P' X' x') pluralityScoreVec := by
                  exact
                    lowestScoring_nonclone_preserved (P := P') (X := X') (x := x')
                      (hX := hX') (hx := hx') (hℓ := hℓnotX) (hℓ_low := hℓ_low')

                -- It remains to show that `c` is a winner in the recursive call after eliminating `ℓ`.
                -- This follows by transporting `hc_after_remove` across `hcomm` and lifting.
                have hc_in_rec_cl :
                    (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' x' a}) ∈
                      liftFinset
                        (scoringEliminationAux pluralityScore _
                          (restrictProfile (removeClonesExcept P' X' x')
                            (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))) := by
                  classical
                  -- Name the RHS winner element.
                  let bR :
                      {a : {x : A' // x ≠ ℓ} //
                          clonePred (restrictCloneSet X' ℓ) xℓ a} :=
                    ⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩
                  have hbR :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    simpa [bR] using hc_after_remove

                  -- Rewrite the RHS profile using the commutation equality.
                  have hbR' :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (relabelProfile
                          (restrictProfile (removeClonesExcept P' X' x')
                            (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))
                          e) := by
                    simpa [hcomm] using hbR

                  -- Use equivariance of `scoringEliminationAux` under relabeling.
                  have hb_pre :
                      e.symm bR ∈ scoringEliminationAux pluralityScore _
                        (restrictProfile (removeClonesExcept P' X' x')
                          (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a})) :=
                    (mem_scoringEliminationAux_relabel_iff
                      (score := pluralityScore)
                      (P :=
                        restrictProfile (removeClonesExcept P' X' x')
                          (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))
                      (e := e) (b := bR)).1 hbR'

                  -- Show that the preimage winner has underlying value `c`.
                  have hb_val :
                      ((e.symm bR).1 : {a : A' // clonePred X' x' a}).1 = c := by
                    simpa [bR] using (he_symm_val bR)
                  have hb_val' :
                      e.symm bR =
                        (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' x' a}) := by
                    apply Subtype.ext
                    simp [hb_val]

                  -- Lift the winner back to the parent candidate type.
                  refine Finset.mem_image.mpr ?_
                  refine ⟨e.symm bR, hb_pre, ?_⟩
                  simp [hb_val']

                -- Combine everything to get membership in the clone-restricted winners.
                rw [haux_cl]
                refine Finset.mem_biUnion.mpr ?_
                refine ⟨(⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}), hℓ_low_cl, ?_⟩
                simpa [liftFinset] using hc_in_rec_cl
            · -- c ∈ winners(P' - X' + x') → c ∈ winners(P')
              intro hcwin
              classical
              -- Unfold one step of elimination in the original election.
              have haux_orig :=
                scoringEliminationAux_eq_biUnion_of_not_card_le_one
                  (score := pluralityScore) (P := P')
                  (by omega : ¬ Fintype.card A' ≤ 1)
              -- Case split: is some clone lowest-scoring in P'?
              by_cases hclone_low :
                  ∃ ℓ, ℓ ∈ lowestScoring P' pluralityScoreVec ∧ ℓ ∈ X'
              · -- There is a lowest-scoring clone in P'.
                rcases hclone_low with ⟨ℓ, hℓ_low, hℓX⟩
                have hcnℓ : c ≠ ℓ := by
                  intro hEq
                  exact hc (hEq ▸ hℓX)
                have hklt : Fintype.card {x : A' // x ≠ ℓ} < k := by
                  simpa [hcard] using (card_restrict_lt (A := A') ℓ)
                by_cases hℓeq : ℓ = x'
                · -- ℓ is the representative: switch to y as rep.
                  subst hℓeq
                  let xℓ : {x : A' // x ≠ ℓ} := ⟨y, by simpa using hyx⟩
                  have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                    cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX')
                      ⟨y, hy, by simpa using hyx⟩
                  have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                    simpa [restrictCloneSet, xℓ] using hy
                  have hrecProps :
                      clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                    have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                    exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                      (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                  have hnon_restr :
                      irv_nonclone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                    hrecProps.1
                  have hc_restr :
                      (⟨c, by simpa using hcnℓ⟩ : {x : A' // x ≠ ℓ}) ∉
                        restrictCloneSet X' ℓ := by
                    intro hmem
                    apply hc
                    simpa [restrictCloneSet] using hmem
                  -- Switch representatives to y in the collapsed election.
                  have hcwin_y :
                      (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' y a}) ∈
                        scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y) := by
                    have hswap :=
                      nonclone_winner_rep_independent (P := P') (X := X') (x := ℓ) (x' := y)
                        (c := c) (hc := hc) (hx := hx') (hx' := hy) (hxx' := by simpa using hyx.symm)
                    have hswapProf :=
                      relabelProfile_removeClonesExcept_swap_rep (P := P') (X := X') (x := ℓ) (x' := y)
                        (hX := hX') (hx := hx') (hx' := hy) (hxx' := by simpa using hyx.symm)
                    have := (hswap.mp hcwin)
                    simpa [hswapProf] using this
                  -- Commute restriction and clone removal.
                  rcases
                      relabelProfile_removeClonesExcept_restrictProfile_of_clone
                        (P := P') (X := X') (x := y) (ℓ := ℓ) (hℓ := hx')
                        (hxℓ := by simpa using hyx)
                    with ⟨e, he_val, he_symm_val, hcomm⟩
                  let bR :
                      {a : {x : A' // x ≠ ℓ} //
                          clonePred (restrictCloneSet X' ℓ) xℓ a} :=
                    e (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' y a})
                  have hb_map :
                      bR ∈ (scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y)).map
                        e.toEmbedding := by
                    exact Finset.mem_map_of_mem _ hcwin_y
                  have hb_relabel :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (relabelProfile (removeClonesExcept P' X' y) e) := by
                    have heq :=
                      scoringEliminationAux_equiv (score := pluralityScore)
                        (P := removeClonesExcept P' X' y) (e := e)
                    simpa [heq] using hb_map
                  have hb_after :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    simpa [hcomm] using hb_relabel
                  have hb_val :
                      ((bR).1 : {x : A' // x ≠ ℓ}).1 = c := by
                    simpa [bR] using (he_val (⟨c, Or.inl hc⟩))
                  have hb_val' :
                      bR =
                        (⟨⟨c, by simpa using hcnℓ⟩, Or.inl hc_restr⟩ :
                          {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) := by
                    apply Subtype.ext
                    ext
                    simp [hb_val]
                  have hc_after_remove :
                      (⟨⟨c, by simpa using hcnℓ⟩, Or.inl hc_restr⟩ :
                          {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    simpa [hb_val'] using hb_after
                  have hc_rec' :
                      (⟨c, by simpa using hcnℓ⟩ : {x : A' // x ≠ ℓ}) ∈
                        scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ} (restrictProfile P' ℓ) := by
                    have := (hnon_restr (⟨c, by simpa using hcnℓ⟩) hc_restr).mpr hc_after_remove
                    simpa using this
                  have hc_rec :
                      c ∈
                        liftFinset (scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ}
                          (restrictProfile P' ℓ)) := by
                    refine Finset.mem_image.mpr ?_
                    refine ⟨(⟨c, by simpa using hcnℓ⟩ : {x : A' // x ≠ ℓ}), hc_rec', ?_⟩
                    simp
                  exact mem_scoringEliminationAux_of_mem_liftFinset (P := P')
                    (haux := by simpa [pluralityScoreVec] using haux_orig)
                    (hℓ_low := hℓ_low) (hc := hc_rec)
                · -- ℓ ≠ x': keep x' as the representative.
                  have hxne : x' ≠ ℓ := by
                    intro hEq
                    exact hℓeq hEq.symm
                  let xℓ : {x : A' // x ≠ ℓ} := ⟨x', hxne⟩
                  have hXne' : ∃ x0 ∈ X', x0 ≠ ℓ := ⟨x', hx', hxne⟩
                  have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                    cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX') hXne'
                  have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                    simpa [restrictCloneSet, xℓ] using hx'
                  have hrecProps :
                      clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                    have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                    exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                      (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                  have hnon_restr :
                      irv_nonclone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                    hrecProps.1
                  have hc_restr : (⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}) ∉ restrictCloneSet X' ℓ := by
                    intro hmem
                    apply hc
                    simpa [restrictCloneSet] using hmem
                  rcases
                      relabelProfile_removeClonesExcept_restrictProfile_of_clone
                        (P := P') (X := X') (x := x') (ℓ := ℓ) (hℓ := hℓX) (hxℓ := hxne)
                    with ⟨e, he_val, he_symm_val, hcomm⟩
                  let bR :
                      {a : {x : A' // x ≠ ℓ} //
                          clonePred (restrictCloneSet X' ℓ) xℓ a} :=
                    e (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' x' a})
                  have hb_map :
                      bR ∈ (scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x')).map
                        e.toEmbedding := by
                    exact Finset.mem_map_of_mem _ hcwin
                  have hb_relabel :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (relabelProfile (removeClonesExcept P' X' x') e) := by
                    have heq :=
                      scoringEliminationAux_equiv (score := pluralityScore)
                        (P := removeClonesExcept P' X' x') (e := e)
                    simpa [heq] using hb_map
                  have hb_after :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    simpa [hcomm] using hb_relabel
                  have hb_val :
                      ((bR).1 : {x : A' // x ≠ ℓ}).1 = c := by
                    simpa [bR] using (he_val (⟨c, Or.inl hc⟩))
                  have hb_val' :
                      bR =
                        (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                          {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) := by
                    apply Subtype.ext
                    ext
                    simp [hb_val]
                  have hc_after_remove :
                      (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                          {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    simpa [hb_val'] using hb_after
                  have hc_rec' :
                      (⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}) ∈
                        scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ} (restrictProfile P' ℓ) := by
                    have := (hnon_restr (⟨c, hcnℓ⟩) hc_restr).mpr hc_after_remove
                    simpa using this
                  have hc_rec :
                      c ∈
                        liftFinset (scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ}
                          (restrictProfile P' ℓ)) := by
                    refine Finset.mem_image.mpr ?_
                    refine ⟨(⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}), hc_rec', ?_⟩
                    simp
                  exact mem_scoringEliminationAux_of_mem_liftFinset (P := P')
                    (haux := by simpa [pluralityScoreVec] using haux_orig)
                    (hℓ_low := hℓ_low) (hc := hc_rec)
              · -- No clone is lowest-scoring in P'.
                -- Unfold one step of elimination in the clone-restricted election.
                have hcard_cl : ¬ Fintype.card {a : A' // clonePred X' x' a} ≤ 1 :=
                  not_card_le_one_clonePred (X := X') (x := x') (hx := hx') (hX := hX_all)
                have haux_cl :=
                  scoringEliminationAux_eq_biUnion_of_not_card_le_one
                    (score := pluralityScore) (P := removeClonesExcept P' X' x') (hcard := hcard_cl)
                -- Extract the elimination candidate from `hcwin`.
                have hcwin' := hcwin
                rw [haux_cl] at hcwin'
                rcases Finset.mem_biUnion.mp hcwin' with ⟨ℓ, hℓ_low_cl, hc_rec_cl⟩
                rcases ℓ with ⟨ℓ, hℓ_pred⟩
                -- Show that ℓ is a non-clone.
                have hℓnotX : ℓ ∉ X' := by
                  cases hℓ_pred with
                  | inl hℓnotX => exact hℓnotX
                  | inr hℓeq =>
                      subst hℓeq
                      -- If the representative is lowest in the collapsed election,
                      -- then some clone is lowest in P', contradicting `hclone_low`.
                      have hA : (Finset.univ : Finset A').Nonempty := by
                        rcases (by
                          simpa using (hX'.1 : X'.Nonempty)) with ⟨a, _⟩
                        haveI : Nonempty A' := ⟨a⟩
                        exact Finset.univ_nonempty
                      rcases lowestScoring_nonempty (P := P') (score := pluralityScoreVec) hA with ⟨w, hw⟩
                      by_cases hwX : w ∈ X'
                      · exact (hclone_low ⟨w, hw, hwX⟩).elim
                      · -- w is a non-clone. Show ℓ is also lowest.
                        have hrep_le_w_cl :
                            scoreCandidate (removeClonesExcept P' X' ℓ) pluralityScoreVec
                                (⟨ℓ, Or.inr rfl⟩ : {a : A' // clonePred X' ℓ a}) ≤
                              scoreCandidate (removeClonesExcept P' X' ℓ) pluralityScoreVec
                                (⟨w, Or.inl hwX⟩ : {a : A' // clonePred X' ℓ a}) :=
                          scoreCandidate_le_of_mem_lowestScoring
                            (P := removeClonesExcept P' X' ℓ) (score := pluralityScoreVec) (hc := hℓ_low_cl)
                        have hrep_le_w :
                            scoreCandidate (removeClonesExcept P' X' ℓ) pluralityScoreVec
                                (⟨ℓ, Or.inr rfl⟩ : {a : A' // clonePred X' ℓ a}) ≤
                              scoreCandidate P' pluralityScoreVec w := by
                          have hscore_w :=
                            score_nonclone_eq (P := P') (X := X') (x := ℓ)
                              (hX := hX') (hx := hx') (ha := hwX)
                          simpa [hscore_w] using hrep_le_w_cl
                        have hx_le_rep :
                            scoreCandidate P' pluralityScoreVec ℓ ≤
                              scoreCandidate (removeClonesExcept P' X' ℓ) pluralityScoreVec
                                (⟨ℓ, Or.inr rfl⟩ : {a : A' // clonePred X' ℓ a}) :=
                          score_rep_ge_clone (P := P') (X := X') (x := ℓ) (y := ℓ)
                            (hX := hX') (hx := hx') (hy := hx')
                        have hx_le_w : scoreCandidate P' pluralityScoreVec ℓ ≤ scoreCandidate P' pluralityScoreVec w :=
                          le_trans hx_le_rep hrep_le_w
                        have hw_le : ∀ d : A', scoreCandidate P' pluralityScoreVec w ≤ scoreCandidate P' pluralityScoreVec d := by
                          intro d
                          exact scoreCandidate_le_of_mem_lowestScoring
                            (P := P') (score := pluralityScoreVec) (hc := hw)
                        have hx_low : ℓ ∈ lowestScoring P' pluralityScoreVec := by
                          apply (lowestScoring_iff_forall_le (P := P') (score := pluralityScoreVec) hA ℓ).2
                          intro d
                          exact le_trans hx_le_w (hw_le d)
                        exact (hclone_low ⟨ℓ, hx_low, hx'⟩).elim
                -- Extract the witness from the recursive winner in the collapsed election.
                rcases Finset.mem_image.mp hc_rec_cl with ⟨d, hd, hdval⟩
                have hcnℓ : c ≠ ℓ := by
                  intro hEq
                  have hEq' :
                      (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' x' a}) =
                        (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}) := by
                    ext
                    simp [hEq]
                  have : d.1 = (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}) := by
                    simpa [hdval] using hEq'
                  exact d.property this
                -- Apply IH to the restricted profile.
                have hklt : Fintype.card {x : A' // x ≠ ℓ} < k := by
                  simpa [hcard] using (card_restrict_lt (A := A') ℓ)
                have hxne : x' ≠ ℓ := by
                  intro hEq
                  exact hℓnotX (hEq ▸ hx')
                let xℓ : {x : A' // x ≠ ℓ} := ⟨x', hxne⟩
                have hXne' : ∃ x0 ∈ X', x0 ≠ ℓ := ⟨x', hx', hxne⟩
                have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                  cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX') hXne'
                have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                  simpa [restrictCloneSet, xℓ] using hx'
                have hrecProps : clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                  have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                  exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                    (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                have hnon_restr :
                    irv_nonclone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                  hrecProps.1
                have hc_restr : (⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}) ∉ restrictCloneSet X' ℓ := by
                  intro hmem
                  apply hc
                  simpa [restrictCloneSet] using hmem
                -- Transport membership across the commutation lemma.
                rcases
                    relabelProfile_restrictProfile_removeClonesExcept_of_nonclone
                      (P := P') (X := X') (x := x') (ℓ := ℓ) (hxℓ := hxne) (hℓ := hℓnotX)
                  with ⟨e, he_val, he_symm_val, hcomm⟩
                let bR :
                    {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a} :=
                  e d
                have hb_map :
                    bR ∈ (scoringEliminationAux pluralityScore _
                        (restrictProfile (removeClonesExcept P' X' x')
                          (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))).map
                      e.toEmbedding := by
                  exact Finset.mem_map_of_mem _ hd
                have hb_relabel :
                    bR ∈ scoringEliminationAux pluralityScore _
                      (relabelProfile
                        (restrictProfile (removeClonesExcept P' X' x')
                          (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))
                        e) := by
                  have heq :=
                    scoringEliminationAux_equiv (score := pluralityScore)
                      (P :=
                        restrictProfile (removeClonesExcept P' X' x')
                          (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))
                      (e := e)
                  simpa [heq] using hb_map
                have hb_after :
                    bR ∈ scoringEliminationAux pluralityScore _
                      (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                  simpa [hcomm] using hb_relabel
                have hb_val :
                    ((bR).1 : {x : A' // x ≠ ℓ}).1 = c := by
                  simpa [bR, hdval] using (he_val d)
                have hb_val' :
                    bR =
                      (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) := by
                  apply Subtype.ext
                  ext
                  simp [hb_val]
                have hc_after_remove :
                    (⟨⟨c, hcnℓ⟩, Or.inl hc_restr⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                      ∈ scoringEliminationAux pluralityScore _
                        (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                  simpa [hb_val'] using hb_after
                have hc_rec'' :
                    (⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}) ∈
                      scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ} (restrictProfile P' ℓ) := by
                  have := (hnon_restr (⟨c, hcnℓ⟩) hc_restr).mpr hc_after_remove
                  simpa using this
                have hc_rec :
                    c ∈
                      liftFinset (scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ}
                        (restrictProfile P' ℓ)) := by
                  refine Finset.mem_image.mpr ?_
                  refine ⟨(⟨c, hcnℓ⟩ : {x : A' // x ≠ ℓ}), hc_rec'', ?_⟩
                  simp
                -- ℓ is lowest-scoring in P' (no clone is lowest).
                have hℓ_low' :
                    ℓ ∈ lowestScoring P' pluralityScoreVec :=
                  lowestScoring_nonclone_reflect (P := P') (X := X') (x := x')
                    (hX := hX') (hx := hx') (hℓ := hℓnotX)
                    (hℓ_low_cl := hℓ_low_cl) (hclone_low := hclone_low)
                -- Conclude in the original election.
                exact mem_scoringEliminationAux_of_mem_liftFinset (P := P')
                  (haux := by simpa [pluralityScoreVec] using haux_orig)
                  (hℓ_low := hℓ_low') (hc := hc_rec)
          · -- irv_clone_prop
            constructor
            · -- (∃ y ∈ X', y wins in P') → x' wins in P'-X'+x'
              intro ⟨w, hw, hwwin⟩
              classical
              -- Unfold one step of elimination in the original election.
              have haux :=
                scoringEliminationAux_eq_biUnion_of_not_card_le_one
                  (score := pluralityScore) (P := P') (by omega : ¬ Fintype.card A' ≤ 1)
              rw [haux] at hwwin
              rcases Finset.mem_biUnion.mp hwwin with ⟨ℓ, hℓ_low, hw_rec⟩
              -- Extract `w ≠ ℓ` and the recursive winner.
              rcases
                  (_root_.SocialChoice.mem_liftFinset_iff_subtype
                    (s := scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ}
                      (restrictProfile P' ℓ))
                    (x := w)).1 hw_rec with ⟨hwnℓ, hw_rec'⟩
              by_cases hℓX : ℓ ∈ X'
              · -- ℓ is a clone: use IH on the restricted profile.
                have hklt : Fintype.card {x : A' // x ≠ ℓ} < k := by
                  simpa [hcard] using (card_restrict_lt (A := A') ℓ)
                by_cases hℓeq : ℓ = x'
                ·
                  -- ℓ is the representative: switch to `y`.
                  subst hℓeq
                  let xℓ : {x : A' // x ≠ ℓ} := ⟨y, by simpa using hyx⟩
                  have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                    cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX')
                      ⟨y, hy, by simpa using hyx⟩
                  have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                    simpa [restrictCloneSet, xℓ] using hy
                  have hrecProps :
                      clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                    have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                    exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                      (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                  have hclone_restr :
                      irv_clone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                    hrecProps.2
                  have hw_restr_mem :
                      (⟨w, hwnℓ⟩ : {x : A' // x ≠ ℓ}) ∈ restrictCloneSet X' ℓ := by
                    simpa [restrictCloneSet] using hw
                  have hxℓ_win :
                      (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    exact (hclone_restr.mp ⟨⟨w, hwnℓ⟩, hw_restr_mem, hw_rec'⟩)
                  -- Transport to the full collapse with representative `y`.
                  rcases
                      relabelProfile_removeClonesExcept_restrictProfile_of_clone
                        (P := P') (X := X') (x := y) (ℓ := ℓ) (hℓ := hx')
                        (hxℓ := by simpa using hyx)
                    with ⟨e, he_val, he_symm_val, hcomm⟩
                  have hxℓ_win' :
                      (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (relabelProfile (removeClonesExcept P' X' y) e) := by
                    simpa [hcomm] using hxℓ_win
                  have hxℓ_pre :
                      e.symm (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y) :=
                    (mem_scoringEliminationAux_relabel_iff
                      (score := pluralityScore) (P := removeClonesExcept P' X' y) (e := e)
                      (b := (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}))).1
                      hxℓ_win'
                  have hxℓ_val :
                      (e.symm (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})).1 = y := by
                    simpa [xℓ] using (he_symm_val (⟨xℓ, Or.inr rfl⟩))
                  have hxℓ_val' :
                      e.symm (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) =
                        (⟨y, Or.inr rfl⟩ : {a : A' // clonePred X' y a}) := by
                    apply Subtype.ext
                    simp [hxℓ_val]
                  have hy_win :
                      (⟨y, Or.inr rfl⟩ : {a : A' // clonePred X' y a}) ∈
                        scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y) := by
                    simpa [hxℓ_val'] using hxℓ_pre
                  -- Switch representative from `y` back to `x'`.
                  have hswap :=
                    clone_winner_rep_independent (P := P') (X := X') (x := y) (x' := ℓ)
                      (hx := hy) (hx' := hx') (hxx' := by simpa using hyx)
                  have hswapProf :=
                    relabelProfile_removeClonesExcept_swap_rep (P := P') (X := X') (x := y) (x' := ℓ)
                      (hX := hX') (hx := hy) (hx' := hx') (hxx' := by simpa using hyx)
                  have := (hswap.mp hy_win)
                  simpa [hswapProf] using this
                · -- ℓ ≠ x': keep x' as the representative.
                  have hxne : x' ≠ ℓ := by
                    intro hEq
                    exact hℓeq hEq.symm
                  let xℓ : {x : A' // x ≠ ℓ} := ⟨x', hxne⟩
                  have hXne' : ∃ x0 ∈ X', x0 ≠ ℓ := ⟨x', hx', hxne⟩
                  have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                    cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX') hXne'
                  have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                    simpa [restrictCloneSet, xℓ] using hx'
                  have hrecProps :
                      clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                    have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                    exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                      (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                  have hclone_restr :
                      irv_clone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                    hrecProps.2
                  have hw_restr_mem :
                      (⟨w, hwnℓ⟩ : {x : A' // x ≠ ℓ}) ∈ restrictCloneSet X' ℓ := by
                    simpa [restrictCloneSet] using hw
                  have hxℓ_win :
                      (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    exact (hclone_restr.mp ⟨⟨w, hwnℓ⟩, hw_restr_mem, hw_rec'⟩)
                  rcases
                      relabelProfile_removeClonesExcept_restrictProfile_of_clone
                        (P := P') (X := X') (x := x') (ℓ := ℓ) (hℓ := hℓX) (hxℓ := hxne)
                    with ⟨e, he_val, he_symm_val, hcomm⟩
                  have hxℓ_win' :
                      (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (relabelProfile (removeClonesExcept P' X' x') e) := by
                    simpa [hcomm] using hxℓ_win
                  have hxℓ_pre :
                      e.symm (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x') :=
                    (mem_scoringEliminationAux_relabel_iff
                      (score := pluralityScore) (P := removeClonesExcept P' X' x') (e := e)
                      (b := (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}))).1
                      hxℓ_win'
                  have hxℓ_val :
                      ((e.symm (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})).1 : A') = x' := by
                    simpa [xℓ] using (he_symm_val (⟨xℓ, Or.inr rfl⟩))
                  have hxℓ_val' :
                      e.symm (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) =
                        (⟨x', Or.inr rfl⟩ : {a : A' // clonePred X' x' a}) := by
                    apply Subtype.ext
                    simp [hxℓ_val]
                  simpa [hxℓ_val'] using hxℓ_pre
              · -- ℓ is a non-clone: use IH on P' - ℓ and lift to the full collapse.
                classical
                have hℓnotX : ℓ ∉ X' := hℓX
                -- Apply IH to the restricted profile `P' - ℓ`.
                have hklt : Fintype.card {x : A' // x ≠ ℓ} < k := by
                  simpa [hcard] using (card_restrict_lt (A := A') ℓ)
                have hxne : x' ≠ ℓ := by
                  intro hEq
                  apply hℓnotX
                  simpa [hEq] using hx'
                let xℓ : {x : A' // x ≠ ℓ} := ⟨x', hxne⟩
                have hXne' : ∃ x0 ∈ X', x0 ≠ ℓ := ⟨x', hx', hxne⟩
                have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                  cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX') hXne'
                have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                  simpa [restrictCloneSet, xℓ] using hx'
                have hrecProps : clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                  have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                  exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                    (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                have hclone_restr :
                    irv_clone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                  hrecProps.2
                have hw_restr_mem : (⟨w, hwnℓ⟩ : {x : A' // x ≠ ℓ}) ∈ restrictCloneSet X' ℓ := by
                  simpa [restrictCloneSet] using hw
                have hxℓ_win :
                    (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                      ∈ scoringEliminationAux pluralityScore _
                          (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                  exact (hclone_restr.mp ⟨⟨w, hwnℓ⟩, hw_restr_mem, hw_rec'⟩)
                -- Transport to the clone-restricted election where `ℓ` is eliminated first.
                rcases
                    relabelProfile_restrictProfile_removeClonesExcept_of_nonclone
                      (P := P') (X := X') (x := x') (ℓ := ℓ) (hxℓ := hxne) (hℓ := hℓnotX)
                  with ⟨e, he_val, he_symm_val, hcomm⟩
                have hx_in_rec_cl :
                    (⟨x', Or.inr rfl⟩ : {a : A' // clonePred X' x' a}) ∈
                      liftFinset
                        (scoringEliminationAux pluralityScore _
                          (restrictProfile (removeClonesExcept P' X' x')
                            (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))) := by
                  classical
                  let bR :
                      {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a} :=
                    ⟨xℓ, Or.inr rfl⟩
                  have hbR :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    simpa [bR] using hxℓ_win
                  have hbR' :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (relabelProfile
                          (restrictProfile (removeClonesExcept P' X' x')
                            (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))
                          e) := by
                    simpa [hcomm] using hbR
                  have hb_pre :
                      e.symm bR ∈ scoringEliminationAux pluralityScore _
                        (restrictProfile (removeClonesExcept P' X' x')
                          (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a})) :=
                    (mem_scoringEliminationAux_relabel_iff
                      (score := pluralityScore)
                      (P :=
                        restrictProfile (removeClonesExcept P' X' x')
                          (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))
                      (e := e) (b := bR)).1 hbR'
                  have hb_val :
                      ((e.symm bR).1 : {a : A' // clonePred X' x' a}).1 = x' := by
                    simpa [bR, xℓ] using (he_symm_val bR)
                  have hb_val' :
                      e.symm bR =
                        (⟨x', Or.inr rfl⟩ : {a : A' // clonePred X' x' a}) := by
                    apply Subtype.ext
                    simp [hb_val]
                  refine Finset.mem_image.mpr ?_
                  refine ⟨e.symm bR, hb_pre, ?_⟩
                  simp [hb_val']
                -- Unfold one step of elimination on the clone-restricted election.
                have hcard_cl : ¬ Fintype.card {a : A' // clonePred X' x' a} ≤ 1 :=
                  not_card_le_one_clonePred (X := X') (x := x') (hx := hx') (hX := hX_all)
                have haux_cl :=
                  scoringEliminationAux_eq_biUnion_of_not_card_le_one
                    (score := pluralityScore) (P := removeClonesExcept P' X' x') (hcard := hcard_cl)
                have hℓ_low' : ℓ ∈ lowestScoring P' pluralityScoreVec := by
                  simpa [pluralityScore, pluralityScoreVec] using hℓ_low
                have hℓ_low_cl :
                    (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}) ∈
                      lowestScoring (removeClonesExcept P' X' x') pluralityScoreVec := by
                  exact
                    lowestScoring_nonclone_preserved (P := P') (X := X') (x := x')
                      (hX := hX') (hx := hx') (hℓ := hℓnotX) (hℓ_low := hℓ_low')
                -- Conclude in the clone-restricted election.
                rw [haux_cl]
                refine Finset.mem_biUnion.mpr ?_
                refine ⟨(⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}), hℓ_low_cl, ?_⟩
                simpa [liftFinset] using hx_in_rec_cl
            · -- x' wins in P'-X'+x' → (∃ y ∈ X', y wins in P')
              intro hxwin
              classical
              -- Unfold one step of elimination in the original election.
              have haux_orig :=
                scoringEliminationAux_eq_biUnion_of_not_card_le_one
                  (score := pluralityScore) (P := P')
                  (by omega : ¬ Fintype.card A' ≤ 1)
              -- Case split: is some clone lowest-scoring in P'?
              by_cases hclone_low :
                  ∃ ℓ, ℓ ∈ lowestScoring P' pluralityScoreVec ∧ ℓ ∈ X'
              · -- There is a lowest-scoring clone in P'.
                rcases hclone_low with ⟨ℓ, hℓ_low, hℓX⟩
                have hklt : Fintype.card {x : A' // x ≠ ℓ} < k := by
                  simpa [hcard] using (card_restrict_lt (A := A') ℓ)
                by_cases hℓeq : ℓ = x'
                · -- ℓ is the representative: switch to y as rep.
                  subst hℓeq
                  let xℓ : {x : A' // x ≠ ℓ} := ⟨y, by simpa using hyx⟩
                  have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                    cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX')
                      ⟨y, hy, by simpa using hyx⟩
                  have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                    simpa [restrictCloneSet, xℓ] using hy
                  have hrecProps :
                      clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                    have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                    exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                      (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                  have hclone_restr :
                      irv_clone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                    hrecProps.2
                  -- Switch representatives to y in the collapsed election.
                  have hxwin_y :
                      (⟨y, Or.inr rfl⟩ : {a : A' // clonePred X' y a}) ∈
                        scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y) := by
                    have hswap :=
                      clone_winner_rep_independent (P := P') (X := X') (x := ℓ) (x' := y)
                        (hx := hx') (hx' := hy) (hxx' := by simpa using hyx.symm)
                    have hswapProf :=
                      relabelProfile_removeClonesExcept_swap_rep (P := P') (X := X') (x := ℓ) (x' := y)
                        (hX := hX') (hx := hx') (hx' := hy) (hxx' := by simpa using hyx.symm)
                    have := (hswap.mp hxwin)
                    simpa [hswapProf] using this
                  -- Commute restriction and clone removal.
                  rcases
                      relabelProfile_removeClonesExcept_restrictProfile_of_clone
                        (P := P') (X := X') (x := y) (ℓ := ℓ) (hℓ := hx')
                        (hxℓ := by simpa using hyx)
                    with ⟨e, he_val, he_symm_val, hcomm⟩
                  let bR :
                      {a : {x : A' // x ≠ ℓ} //
                          clonePred (restrictCloneSet X' ℓ) xℓ a} :=
                    e (⟨y, Or.inr rfl⟩ : {a : A' // clonePred X' y a})
                  have hb_map :
                      bR ∈ (scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' y)).map
                        e.toEmbedding := by
                    exact Finset.mem_map_of_mem _ hxwin_y
                  have hb_relabel :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (relabelProfile (removeClonesExcept P' X' y) e) := by
                    have heq :=
                      scoringEliminationAux_equiv (score := pluralityScore)
                        (P := removeClonesExcept P' X' y) (e := e)
                    simpa [heq] using hb_map
                  have hb_after :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    simpa [hcomm] using hb_relabel
                  have hb_val :
                      ((bR).1 : {x : A' // x ≠ ℓ}).1 = y := by
                    simpa [bR] using (he_val (⟨y, Or.inr rfl⟩))
                  have hb_val' :
                      bR =
                        (⟨xℓ, Or.inr rfl⟩ :
                          {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) := by
                    apply Subtype.ext
                    ext
                    simp [hb_val, xℓ]
                  have hxℓ_win :
                      (⟨xℓ, Or.inr rfl⟩ :
                          {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    simpa [hb_val'] using hb_after
                  have hxw_restr :
                      ∃ z, z ∈ restrictCloneSet X' ℓ ∧
                        z ∈ scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ} (restrictProfile P' ℓ) :=
                    (hclone_restr.mpr hxℓ_win)
                  rcases hxw_restr with ⟨z, hzmem, hzwins⟩
                  have hz_inX : (z : A') ∈ X' := by
                    simpa [restrictCloneSet] using hzmem
                  have hz_lift :
                      (z : A') ∈
                        liftFinset (scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ}
                          (restrictProfile P' ℓ)) := by
                    refine Finset.mem_image.mpr ?_
                    refine ⟨z, hzwins, ?_⟩
                    simp
                  have hz_win : (z : A') ∈ scoringEliminationAux pluralityScore A' P' :=
                    mem_scoringEliminationAux_of_mem_liftFinset (P := P')
                      (haux := by simpa [pluralityScoreVec] using haux_orig)
                      (hℓ_low := hℓ_low) (hc := hz_lift)
                  exact ⟨(z : A'), hz_inX, hz_win⟩
                · -- ℓ ≠ x': keep x' as the representative.
                  have hxne : x' ≠ ℓ := by
                    intro hEq
                    exact hℓeq hEq.symm
                  let xℓ : {x : A' // x ≠ ℓ} := ⟨x', hxne⟩
                  have hXne' : ∃ x0 ∈ X', x0 ≠ ℓ := ⟨x', hx', hxne⟩
                  have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                    cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX') hXne'
                  have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                    simpa [restrictCloneSet, xℓ] using hx'
                  have hrecProps :
                      clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                    have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                    exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                      (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                  have hclone_restr :
                      irv_clone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                    hrecProps.2
                  rcases
                      relabelProfile_removeClonesExcept_restrictProfile_of_clone
                        (P := P') (X := X') (x := x') (ℓ := ℓ) (hℓ := hℓX) (hxℓ := hxne)
                    with ⟨e, he_val, he_symm_val, hcomm⟩
                  let bR :
                      {a : {x : A' // x ≠ ℓ} //
                          clonePred (restrictCloneSet X' ℓ) xℓ a} :=
                    e (⟨x', Or.inr rfl⟩ : {a : A' // clonePred X' x' a})
                  have hb_map :
                      bR ∈ (scoringEliminationAux pluralityScore _ (removeClonesExcept P' X' x')).map
                        e.toEmbedding := by
                    exact Finset.mem_map_of_mem _ hxwin
                  have hb_relabel :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (relabelProfile (removeClonesExcept P' X' x') e) := by
                    have heq :=
                      scoringEliminationAux_equiv (score := pluralityScore)
                        (P := removeClonesExcept P' X' x') (e := e)
                    simpa [heq] using hb_map
                  have hb_after :
                      bR ∈ scoringEliminationAux pluralityScore _
                        (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    simpa [hcomm] using hb_relabel
                  have hb_val :
                      ((bR).1 : {x : A' // x ≠ ℓ}).1 = x' := by
                    simpa [bR] using (he_val (⟨x', Or.inr rfl⟩))
                  have hb_val' :
                      bR =
                        (⟨xℓ, Or.inr rfl⟩ :
                          {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) := by
                    apply Subtype.ext
                    ext
                    simp [hb_val, xℓ]
                  have hxℓ_win :
                      (⟨xℓ, Or.inr rfl⟩ :
                          {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                        ∈ scoringEliminationAux pluralityScore _
                            (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                    simpa [hb_val'] using hb_after
                  have hxw_restr :
                      ∃ z, z ∈ restrictCloneSet X' ℓ ∧
                        z ∈ scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ} (restrictProfile P' ℓ) :=
                    (hclone_restr.mpr hxℓ_win)
                  rcases hxw_restr with ⟨z, hzmem, hzwins⟩
                  have hz_inX : (z : A') ∈ X' := by
                    simpa [restrictCloneSet] using hzmem
                  have hz_lift :
                      (z : A') ∈
                        liftFinset (scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ}
                          (restrictProfile P' ℓ)) := by
                    refine Finset.mem_image.mpr ?_
                    refine ⟨z, hzwins, ?_⟩
                    simp
                  have hz_win : (z : A') ∈ scoringEliminationAux pluralityScore A' P' :=
                    mem_scoringEliminationAux_of_mem_liftFinset (P := P')
                      (haux := by simpa [pluralityScoreVec] using haux_orig)
                      (hℓ_low := hℓ_low) (hc := hz_lift)
                  exact ⟨(z : A'), hz_inX, hz_win⟩
              · -- No clone is lowest-scoring in P'.
                -- Unfold one step of elimination in the clone-restricted election.
                have hcard_cl : ¬ Fintype.card {a : A' // clonePred X' x' a} ≤ 1 :=
                  not_card_le_one_clonePred (X := X') (x := x') (hx := hx') (hX := hX_all)
                have haux_cl :=
                  scoringEliminationAux_eq_biUnion_of_not_card_le_one
                    (score := pluralityScore) (P := removeClonesExcept P' X' x') (hcard := hcard_cl)
                -- Extract the elimination candidate from `hxwin`.
                have hxwin' := hxwin
                rw [haux_cl] at hxwin'
                rcases Finset.mem_biUnion.mp hxwin' with ⟨ℓ, hℓ_low_cl, hx_rec_cl⟩
                rcases ℓ with ⟨ℓ, hℓ_pred⟩
                -- Show that ℓ is a non-clone.
                have hℓnotX : ℓ ∉ X' := by
                  cases hℓ_pred with
                  | inl hℓnotX => exact hℓnotX
                  | inr hℓeq =>
                      subst hℓeq
                      -- If the representative is lowest in the collapsed election,
                      -- then some clone is lowest in P', contradicting `hclone_low`.
                      have hA : (Finset.univ : Finset A').Nonempty := by
                        rcases (by
                          simpa using (hX'.1 : X'.Nonempty)) with ⟨a, _⟩
                        haveI : Nonempty A' := ⟨a⟩
                        exact Finset.univ_nonempty
                      rcases lowestScoring_nonempty (P := P') (score := pluralityScoreVec) hA with ⟨w, hw⟩
                      by_cases hwX : w ∈ X'
                      · exact (hclone_low ⟨w, hw, hwX⟩).elim
                      · -- w is a non-clone. Show ℓ is also lowest.
                        have hrep_le_w_cl :
                            scoreCandidate (removeClonesExcept P' X' ℓ) pluralityScoreVec
                                (⟨ℓ, Or.inr rfl⟩ : {a : A' // clonePred X' ℓ a}) ≤
                              scoreCandidate (removeClonesExcept P' X' ℓ) pluralityScoreVec
                                (⟨w, Or.inl hwX⟩ : {a : A' // clonePred X' ℓ a}) :=
                          scoreCandidate_le_of_mem_lowestScoring
                            (P := removeClonesExcept P' X' ℓ) (score := pluralityScoreVec) (hc := hℓ_low_cl)
                        have hrep_le_w :
                            scoreCandidate (removeClonesExcept P' X' ℓ) pluralityScoreVec
                                (⟨ℓ, Or.inr rfl⟩ : {a : A' // clonePred X' ℓ a}) ≤
                              scoreCandidate P' pluralityScoreVec w := by
                          have hscore_w :=
                            score_nonclone_eq (P := P') (X := X') (x := ℓ)
                              (hX := hX') (hx := hx') (ha := hwX)
                          simpa [hscore_w] using hrep_le_w_cl
                        have hx_le_rep :
                            scoreCandidate P' pluralityScoreVec ℓ ≤
                              scoreCandidate (removeClonesExcept P' X' ℓ) pluralityScoreVec
                                (⟨ℓ, Or.inr rfl⟩ : {a : A' // clonePred X' ℓ a}) :=
                          score_rep_ge_clone (P := P') (X := X') (x := ℓ) (y := ℓ)
                            (hX := hX') (hx := hx') (hy := hx')
                        have hx_le_w : scoreCandidate P' pluralityScoreVec ℓ ≤ scoreCandidate P' pluralityScoreVec w :=
                          le_trans hx_le_rep hrep_le_w
                        have hw_le : ∀ d : A', scoreCandidate P' pluralityScoreVec w ≤ scoreCandidate P' pluralityScoreVec d := by
                          intro d
                          exact scoreCandidate_le_of_mem_lowestScoring
                            (P := P') (score := pluralityScoreVec) (hc := hw)
                        have hx_low : ℓ ∈ lowestScoring P' pluralityScoreVec := by
                          apply (lowestScoring_iff_forall_le (P := P') (score := pluralityScoreVec) hA ℓ).2
                          intro d
                          exact le_trans hx_le_w (hw_le d)
                        exact (hclone_low ⟨ℓ, hx_low, hx'⟩).elim
                -- Extract the witness from the recursive winner in the collapsed election.
                rcases Finset.mem_image.mp hx_rec_cl with ⟨d, hd, hdval⟩
                have hd' :
                    d.1 = (⟨x', Or.inr rfl⟩ : {a : A' // clonePred X' x' a}) := by
                  simpa [liftFinset] using hdval
                -- Apply IH to the restricted profile.
                have hklt : Fintype.card {x : A' // x ≠ ℓ} < k := by
                  simpa [hcard] using (card_restrict_lt (A := A') ℓ)
                have hxne : x' ≠ ℓ := by
                  intro hEq
                  exact hℓnotX (hEq ▸ hx')
                let xℓ : {x : A' // x ≠ ℓ} := ⟨x', hxne⟩
                have hXne' : ∃ x0 ∈ X', x0 ≠ ℓ := ⟨x', hx', hxne⟩
                have hX_restr : CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
                  cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX') hXne'
                have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
                  simpa [restrictCloneSet, xℓ] using hx'
                have hrecProps : clone_independence_props (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ := by
                  have hM : Motive (Fintype.card {x : A' // x ≠ ℓ}) := ih _ hklt
                  exact hM (A' := {x : A' // x ≠ ℓ}) rfl (P' := restrictProfile P' ℓ)
                    (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
                have hclone_restr :
                    irv_clone_prop (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
                  hrecProps.2
                -- Transport membership across the commutation lemma.
                rcases
                    relabelProfile_restrictProfile_removeClonesExcept_of_nonclone
                      (P := P') (X := X') (x := x') (ℓ := ℓ) (hxℓ := hxne) (hℓ := hℓnotX)
                  with ⟨e, he_val, he_symm_val, hcomm⟩
                let bR :
                    {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a} :=
                  e d
                have hb_map :
                    bR ∈ (scoringEliminationAux pluralityScore _
                        (restrictProfile (removeClonesExcept P' X' x')
                          (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))).map
                      e.toEmbedding := by
                  exact Finset.mem_map_of_mem _ hd
                have hb_relabel :
                    bR ∈ scoringEliminationAux pluralityScore _
                      (relabelProfile
                        (restrictProfile (removeClonesExcept P' X' x')
                          (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))
                        e) := by
                  have heq :=
                    scoringEliminationAux_equiv (score := pluralityScore)
                      (P :=
                        restrictProfile (removeClonesExcept P' X' x')
                          (⟨ℓ, Or.inl hℓnotX⟩ : {a : A' // clonePred X' x' a}))
                      (e := e)
                  simpa [heq] using hb_map
                have hb_after :
                    bR ∈ scoringEliminationAux pluralityScore _
                      (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                  simpa [hcomm] using hb_relabel
                have hb_val :
                    ((bR).1 : {x : A' // x ≠ ℓ}).1 = x' := by
                  simpa [bR, hd'] using (he_val d)
                have hb_val' :
                    bR =
                      (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) := by
                  apply Subtype.ext
                  ext
                  simp [hb_val, xℓ]
                have hxℓ_win :
                    (⟨xℓ, Or.inr rfl⟩ :
                        {a : {x : A' // x ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})
                      ∈ scoringEliminationAux pluralityScore _
                        (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) := by
                  simpa [hb_val'] using hb_after
                have hxw_restr :
                    ∃ z, z ∈ restrictCloneSet X' ℓ ∧
                      z ∈ scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ} (restrictProfile P' ℓ) :=
                  (hclone_restr.mpr hxℓ_win)
                rcases hxw_restr with ⟨z, hzmem, hzwins⟩
                have hz_inX : (z : A') ∈ X' := by
                  simpa [restrictCloneSet] using hzmem
                have hz_lift :
                    (z : A') ∈
                      liftFinset (scoringEliminationAux pluralityScore {x : A' // x ≠ ℓ}
                        (restrictProfile P' ℓ)) := by
                  refine Finset.mem_image.mpr ?_
                  refine ⟨z, hzwins, ?_⟩
                  simp
                -- ℓ is lowest-scoring in P' (no clone is lowest).
                have hℓ_low' :
                    ℓ ∈ lowestScoring P' pluralityScoreVec :=
                  lowestScoring_nonclone_reflect (P := P') (X := X') (x := x')
                    (hX := hX') (hx := hx') (hℓ := hℓnotX)
                    (hℓ_low_cl := hℓ_low_cl) (hclone_low := hclone_low)
                -- Conclude in the original election.
                have hz_win : (z : A') ∈ scoringEliminationAux pluralityScore A' P' :=
                  mem_scoringEliminationAux_of_mem_liftFinset (P := P')
                    (haux := by simpa [pluralityScoreVec] using haux_orig)
                    (hℓ_low := hℓ_low') (hc := hz_lift)
                exact ⟨(z : A'), hz_inX, hz_win⟩
  -- Apply the strong induction result
  have h := @hStrong A instA (Classical.decEq _) rfl V instV P₀ X x hX hx
  simp only [clone_independence_props, irv_nonclone_prop, irv_clone_prop] at h
  -- Align the goal with the statement proven by `h`.
  simpa [scoringEliminationRule] using h

end SocialChoice
