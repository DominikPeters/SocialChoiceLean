import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Clones
import SocialChoice.Axioms.Independence
import SocialChoice.ListBallot
import SocialChoice.Rules
import SocialChoice.Rules.ScoringRules.Defs
import SocialChoice.Rules.ScoringRules.Plurality.Defs

namespace SocialChoice

open Finset

theorem plurality_independence_of_dominated_nonempty :
    ∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq A] [Nonempty V]
      (P : Profile V A) (c d : A),
        (∀ v : V, Prefers P v c d) →
          liftWinners (plurality (restrictCandidates P (fun a => a ≠ d))) = plurality P := by
  intro V A _ _ _ _ P c d hpref
  classical
  rcases Classical.choice (inferInstance : Nonempty V) with v0
  let _ := P.pref v0
  have hcd : c ≠ d := by
    exact ne_of_lt (hpref v0)
  have hnot_top_d : ∀ v : V, ¬ TopRank P v d := by
    intro v htop
    let _ := P.pref v
    have hdc : Prefers P v d c := htop c hcd
    have hcd' : Prefers P v c d := hpref v
    exact (lt_asymm hdc hcd')
  let P' := restrictCandidates P (fun a => a ≠ d)
  have htopcount_d : topCount P d = 0 := by
    unfold topCount
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have htop : TopRank P v d := (Finset.mem_filter.mp hv).2
    exact (hnot_top_d v htop)
  have hA : (Finset.univ : Finset A).Nonempty := ⟨c, by simp⟩
  let t : A := (Finset.univ.min' hA)
  have htopt : TopRank P v0 t := by
    intro a ha
    have hleast : IsLeast (↑(Finset.univ : Finset A)) t :=
      Finset.isLeast_min' (s := (Finset.univ : Finset A)) hA
    have hle : t ≤ a := hleast.2 (by simp)
    have hlt : t < a := lt_of_le_of_ne hle (by simpa [eq_comm] using ha)
    simpa [Prefers] using hlt
  have hv0 : v0 ∈ votersTop P t := by
    simp [votersTop, htopt]
  have hpos : 0 < topCount P t := by
    unfold topCount
    exact Finset.card_pos.mpr ⟨v0, hv0⟩
  have hlt : topCount P d < topCount P t := by
    simpa [htopcount_d] using hpos
  have hnot_winner : d ∉ plurality P := by
    intro hd
    have hmax : ∀ e : A, topCount P e ≤ topCount P d :=
      (Finset.mem_filter.mp hd).2
    exact (not_lt_of_ge (hmax t)) hlt
  have topRank_restrict_iff (v : V) (a : A) (hne : a ≠ d) :
      TopRank P' v ⟨a, hne⟩ ↔ TopRank P v a := by
    constructor
    · intro htop b hb
      by_cases hbd : b = d
      · subst b
        by_contra hnot
        have hda : Prefers P v d a := by
          let _ := P.pref v
          have htrich := lt_trichotomy (a := a) (b := d)
          cases htrich with
          | inl hlt => exact (hnot hlt).elim
          | inr hrest =>
              cases hrest with
              | inl hEq =>
                  exact (hb hEq.symm).elim
              | inr hlt => exact hlt
        have htop_d : TopRank P v d := by
          intro b hb'
          by_cases hba : b = a
          · subst hba
            exact hda
          · have hne' : b ≠ d := by
              intro hbd'
              exact hb' hbd'
            have hab : Prefers P v a b := by
              have hne'' : (⟨b, hne'⟩ : {x : A // x ≠ d}) ≠ ⟨a, hne⟩ := by
                intro hEq
                apply hba
                exact congrArg Subtype.val hEq
              have hab' := htop ⟨b, hne'⟩ hne''
              exact (prefers_restrictCandidates_iff P (fun x => x ≠ d) v
                ⟨a, hne⟩ ⟨b, hne'⟩).mp hab'
            let _ := P.pref v
            exact lt_trans hda hab
        exact (hnot_top_d v htop_d)
      · have hne' : (⟨b, hbd⟩ : {x : A // x ≠ d}) ≠ ⟨a, hne⟩ := by
          intro hEq
          apply hb
          exact congrArg Subtype.val hEq
        have hab' := htop ⟨b, hbd⟩ hne'
        exact (prefers_restrictCandidates_iff P (fun x => x ≠ d) v
          ⟨a, hne⟩ ⟨b, hbd⟩).mp hab'
    · intro htop b hb
      have hb' : (b : A) ≠ a := by
        intro hEq
        apply hb
        ext
        simpa using hEq
      have hab : Prefers P v a b := htop b hb'
      exact (prefers_restrictCandidates_iff P (fun x => x ≠ d) v
        ⟨a, hne⟩ b).mpr hab
  have topCount_restrict (a : A) (hne : a ≠ d) :
      topCount P' ⟨a, hne⟩ = topCount P a := by
    unfold topCount
    apply congrArg Finset.card
    ext v
    simp [votersTop, topRank_restrict_iff v a hne]
  apply Finset.ext
  intro a
  by_cases had : a = d
  · subst had
    have : a ∉ liftWinners (plurality P') := by
      simp [liftWinners, P']
    constructor
    · intro ha
      exact (this ha).elim
    · intro ha
      exact (hnot_winner ha).elim
  · have hne : a ≠ d := had
    constructor
    · intro ha
      have ha' : ∃ h : a ≠ d, (⟨a, h⟩ : {x : A // x ≠ d}) ∈ plurality P' := by
        simpa [liftWinners, P'] using ha
      rcases ha' with ⟨hne', ha'⟩
      have ha'' : (⟨a, hne⟩ : {x : A // x ≠ d}) ∈ plurality P' := by
        simpa using ha'
      have hmax : ∀ e : {x : A // x ≠ d}, topCount P' e ≤ topCount P' ⟨a, hne⟩ :=
        (Finset.mem_filter.mp ha'').2
      have hmax' : ∀ e : A, topCount P e ≤ topCount P a := by
        intro e
        by_cases hed : e = d
        · subst hed
          simp [htopcount_d]
        · have hne' : e ≠ d := hed
          have hmax'' := hmax ⟨e, hne'⟩
          simpa [topCount_restrict e hne', topCount_restrict a hne] using hmax''
      have ha''' : a ∈ (Finset.univ.filter
          (fun c => ∀ d : A, topCount P d ≤ topCount P c)) := by
        exact mem_filter.mpr ⟨mem_univ _, hmax'⟩
      simpa [plurality] using ha'''
    · intro ha
      have ha' : a ∈ (Finset.univ.filter
          (fun c => ∀ d : A, topCount P d ≤ topCount P c)) := by
        simpa [plurality] using ha
      have hmax : ∀ e : {x : A // x ≠ d}, topCount P' e ≤ topCount P' ⟨a, hne⟩ := by
        intro e
        have hmax' : topCount P e ≤ topCount P a := (mem_filter.mp ha').2 e
        simpa [topCount_restrict e e.2, topCount_restrict a hne] using hmax'
      have ha'' : (⟨a, hne⟩ : {x : A // x ≠ d}) ∈ plurality P' := by
        exact mem_filter.mpr ⟨mem_univ _, hmax⟩
      have ha''' :
          ∃ h : a ≠ d, (⟨a, h⟩ : {x : A // x ≠ d}) ∈ plurality P' := ⟨hne, ha''⟩
      simpa [liftWinners, P'] using ha'''

end SocialChoice

/-!
## Plurality fails independence of clones

Counterexample profile (candidates 0=a, 1=b, 2=c):
2 voters: a > b > c
2 voters: b > a > c
3 voters: c > a > b

Plurality selects c. The clone set is {a,b}. Removing b makes a the winner,
so c is no longer a winner.
-/

namespace SocialChoice

namespace PluralityIndependenceCounterexample

def ballotABC : ListBallot 3 := ListBallot.mk' [0, 1, 2]
def ballotBAC : ListBallot 3 := ListBallot.mk' [1, 0, 2]
def ballotCAB : ListBallot 3 := ListBallot.mk' [2, 0, 1]

def ballots : Fin 7 → ListBallot 3
  | ⟨0, _⟩ => ballotABC
  | ⟨1, _⟩ => ballotABC
  | ⟨2, _⟩ => ballotBAC
  | ⟨3, _⟩ => ballotBAC
  | ⟨4, _⟩ => ballotCAB
  | ⟨5, _⟩ => ballotCAB
  | ⟨6, _⟩ => ballotCAB

noncomputable def profile : Profile (Fin 7) (Fin 3) :=
  profileOfListBallots ballots

def cloneSet : Set (Fin 3) := {0, 1}

lemma cloneSet_profile : CloneSet profile cloneSet := by
  refine ⟨?_, ?_⟩
  · refine ⟨(0 : Fin 3), by simp [cloneSet]⟩
  intro v c hc
  have hc' : c = (2 : Fin 3) := by
    fin_cases c
    · have hmem : (0 : Fin 3) ∈ cloneSet := by simp [cloneSet]
      exact (hc hmem).elim
    · have hmem : (1 : Fin 3) ∈ cloneSet := by simp [cloneSet]
      exact (hc hmem).elim
    · rfl
  subst hc'
  fin_cases v <;>
    (first
      | left
        intro x hx
        have hx' : x = (0 : Fin 3) ∨ x = (1 : Fin 3) := by
          simpa [cloneSet] using hx
        cases hx' with
        | inl hx0 =>
            subst hx0
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
        | inr hx1 =>
            subst hx1
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
      | right
        intro x hx
        have hx' : x = (0 : Fin 3) ∨ x = (1 : Fin 3) := by
          simpa [cloneSet] using hx
        cases hx' with
        | inl hx0 =>
            subst hx0
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
        | inr hx1 =>
            subst hx1
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide)

abbrev scoreVec : Nat → Int := fun r => pluralityScore (Fintype.card (Fin 3)) r

lemma topCount_profile_a : topCount profile (0 : Fin 3) = 2 := by
  calc
    topCount profile (0 : Fin 3) =
        countTop (fun v => (ballots v).ranking) 0 := by
          simpa [topCount, profile] using
            (votersTop_card_eq_countTop (ballots := ballots) (c := (0 : Fin 3)))
    _ = 2 := rfl

lemma topCount_profile_b : topCount profile (1 : Fin 3) = 2 := by
  calc
    topCount profile (1 : Fin 3) =
        countTop (fun v => (ballots v).ranking) 1 := by
          simpa [topCount, profile] using
            (votersTop_card_eq_countTop (ballots := ballots) (c := (1 : Fin 3)))
    _ = 2 := rfl

lemma topCount_profile_c : topCount profile (2 : Fin 3) = 3 := by
  calc
    topCount profile (2 : Fin 3) =
        countTop (fun v => (ballots v).ranking) 2 := by
          simpa [topCount, profile] using
            (votersTop_card_eq_countTop (ballots := ballots) (c := (2 : Fin 3)))
    _ = 3 := rfl

lemma score_profile_a :
    scoreCandidate profile scoreVec (0 : Fin 3) = 2 := by
  simpa [scoreVec, topCount_profile_a] using
    (pluralityScore_eq_topCount (P := profile) (c := (0 : Fin 3)))

lemma score_profile_b :
    scoreCandidate profile scoreVec (1 : Fin 3) = 2 := by
  simpa [scoreVec, topCount_profile_b] using
    (pluralityScore_eq_topCount (P := profile) (c := (1 : Fin 3)))

lemma score_profile_c :
    scoreCandidate profile scoreVec (2 : Fin 3) = 3 := by
  simpa [scoreVec, topCount_profile_c] using
    (pluralityScore_eq_topCount (P := profile) (c := (2 : Fin 3)))

lemma plurality_profile_has_c : (2 : Fin 3) ∈ plurality profile := by
  classical
  have hA : (Finset.univ : Finset (Fin 3)).Nonempty := by simp
  have hmax :
      ∀ d : Fin 3, scoreCandidate profile scoreVec d ≤
        scoreCandidate profile scoreVec (2 : Fin 3) := by
    intro d
    fin_cases d <;> simp [score_profile_a, score_profile_b, score_profile_c]
  have hc :
      (2 : Fin 3) ∈ scoringRule pluralityScore profile := by
    have hc' :=
      (scoringWinners_iff_forall_le (P := profile) (score := scoreVec)
        (hA := hA) (c := (2 : Fin 3))).2 hmax
    simpa [scoringRule, scoreVec] using hc'
  simpa [plurality_eq_scoringRule] using hc

abbrev q : Fin 3 → Prop := fun a => a ≠ (1 : Fin 3)

instance : DecidablePred q := by
  intro a
  dsimp [q]
  infer_instance

lemma clonePred_eq_ne :
    clonePred cloneSet (0 : Fin 3) = (fun a : Fin 3 => a ≠ (1 : Fin 3)) := by
  funext a
  apply propext
  fin_cases a <;> simp [cloneSet, clonePred]

def candAq : {a : Fin 3 // q a} := ⟨0, by simp [q]⟩
def candCq : {a : Fin 3 // q a} := ⟨2, by simp [q]⟩

def candCclone : {a : Fin 3 // clonePred cloneSet (0 : Fin 3) a} :=
  ⟨2, Or.inl (by simp [cloneSet])⟩

noncomputable def profileQ : Profile (Fin 7) {a : Fin 3 // q a} :=
  restrictCandidates profile q

noncomputable abbrev scoreVecQ : Nat → Int :=
  fun r => pluralityScore (Fintype.card {a : Fin 3 // q a}) r

lemma card_q : Fintype.card {a : Fin 3 // q a} = 2 := by
  classical
  change Fintype.card {a : Fin 3 // a ≠ (1 : Fin 3)} = 2
  have h :=
    (Fintype.card_subtype_compl (α := Fin 3) (p := fun a : Fin 3 => a = (1 : Fin 3)))
  rw [h]
  simp

lemma candAq_ne_candCq : candAq ≠ candCq := by
  intro h
  have h' : (0 : Fin 3) = 2 := by
    simpa [candAq, candCq] using congrArg Subtype.val h
  exact (by decide : (0 : Fin 3) ≠ 2) h'

lemma candCq_ne_candAq : candCq ≠ candAq := by
  exact candAq_ne_candCq.symm

lemma votersPreferring_restrictCandidates_eq {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (p : A → Prop) [DecidablePred p]
    (a b : {x : A // p x}) :
    votersPreferring (restrictCandidates P p) a b = votersPreferring P a b := by
  ext v
  simp [votersPreferring, prefers_restrictCandidates_iff]

lemma votersPreferring_profile_a_c :
    (votersPreferring profile (0 : Fin 3) (2 : Fin 3)).card = 4 := by
  calc
    (votersPreferring profile (0 : Fin 3) (2 : Fin 3)).card =
        countPrefers (fun v => (ballots v).ranking) 0 2 := by
          unfold countPrefers
          simpa [profile] using
            congrArg Finset.card
              (votersPreferring_eq_filter_prefersInList
                (ballots := ballots) (a := 0) (b := 2))
    _ = 4 := rfl

lemma votersPreferring_profile_c_a :
    (votersPreferring profile (2 : Fin 3) (0 : Fin 3)).card = 3 := by
  calc
    (votersPreferring profile (2 : Fin 3) (0 : Fin 3)).card =
        countPrefers (fun v => (ballots v).ranking) 2 0 := by
          unfold countPrefers
          simpa [profile] using
            congrArg Finset.card
              (votersPreferring_eq_filter_prefersInList
                (ballots := ballots) (a := 2) (b := 0))
    _ = 3 := rfl

lemma score_restrict_a :
    scoreCandidate profileQ scoreVecQ candAq = 4 := by
  have hcard : Fintype.card {a : Fin 3 // q a} = 2 := card_q
  have hcd : candAq ≠ candCq := candAq_ne_candCq
  have h := pluralityScore_eq_votersPreferring_of_two
    (P := profileQ) (hcard := hcard) (c := candAq) (d := candCq) (hcd := hcd)
  have hvp :
      (votersPreferring profileQ candAq candCq).card =
        (votersPreferring profile (0 : Fin 3) (2 : Fin 3)).card := by
    have h' := congrArg Finset.card
      (votersPreferring_restrictCandidates_eq (P := profile) (p := q)
        (a := candAq) (b := candCq))
    exact h'
  calc
    scoreCandidate profileQ scoreVecQ candAq =
        (votersPreferring profileQ candAq candCq).card := by
          simpa [scoreVecQ] using h
    _ = (votersPreferring profile (0 : Fin 3) (2 : Fin 3)).card := by
          exact_mod_cast hvp
    _ = 4 := by
          exact_mod_cast votersPreferring_profile_a_c

lemma score_restrict_c :
    scoreCandidate profileQ scoreVecQ candCq = 3 := by
  have hcard : Fintype.card {a : Fin 3 // q a} = 2 := card_q
  have hcd : candCq ≠ candAq := candCq_ne_candAq
  have h := pluralityScore_eq_votersPreferring_of_two
    (P := profileQ) (hcard := hcard) (c := candCq) (d := candAq) (hcd := hcd)
  have hvp :
      (votersPreferring profileQ candCq candAq).card =
        (votersPreferring profile (2 : Fin 3) (0 : Fin 3)).card := by
    have h' := congrArg Finset.card
      (votersPreferring_restrictCandidates_eq (P := profile) (p := q)
        (a := candCq) (b := candAq))
    exact h'
  calc
    scoreCandidate profileQ scoreVecQ candCq =
        (votersPreferring profileQ candCq candAq).card := by
          simpa [scoreVecQ] using h
    _ = (votersPreferring profile (2 : Fin 3) (0 : Fin 3)).card := by
          exact_mod_cast hvp
    _ = 3 := by
          exact_mod_cast votersPreferring_profile_c_a

lemma cast_subtype_val {A : Type} {p q : A → Prop}
    (h : p = q) (x : {a : A // p a}) :
    (cast (congrArg (fun r => {a : A // r a}) h) x : {a : A // q a}).1 = x.1 := by
  cases x
  cases h
  rfl

lemma plurality_cloneProfile_not_c :
    candCclone ∉ plurality (removeClonesExcept profile cloneSet (0 : Fin 3)) := by
  classical
  have hcq : candCq ∉ scoringRule pluralityScore (restrictCandidates profile q) := by
    intro hcq
    have hA : (Finset.univ : Finset {a : Fin 3 // q a}).Nonempty :=
      ⟨candAq, by simp [candAq]⟩
    have hcq' :
        candCq ∈ scoringWinners (restrictCandidates profile q) scoreVecQ := by
      simpa [scoringRule, scoreVecQ] using hcq
    have hmax :=
      (scoringWinners_iff_forall_le (P := restrictCandidates profile q) (score := scoreVecQ)
        (hA := hA) (c := candCq)).1 hcq'
    have hmaxa := hmax candAq
    have hmaxa' :
        scoreCandidate profileQ scoreVecQ candAq ≤
          scoreCandidate profileQ scoreVecQ candCq := by
      exact hmaxa
    have : (4 : Int) ≤ 3 := by
      have hmaxa'' := hmaxa'
      simp [score_restrict_a, score_restrict_c] at hmaxa''
    exact (by decide : ¬ ((4 : Int) ≤ 3)) this
  have hpred : q = clonePred cloneSet (0 : Fin 3) := by
    simpa [q] using clonePred_eq_ne.symm
  have hcq_cast :
      (cast (congrArg (fun r => {a : Fin 3 // r a}) hpred) candCq :
        {a : Fin 3 // clonePred cloneSet (0 : Fin 3) a}) ∉
      scoringRule pluralityScore
        (castCandidates (p := q) (q := clonePred cloneSet (0 : Fin 3)) hpred
          (restrictCandidates profile q)) := by
    intro hc
    have hc' :
        candCq ∈ scoringRule pluralityScore (restrictCandidates profile q) :=
      (mem_scoringRule_castCandidates_iff
        (score := pluralityScore) (p := q) (q := clonePred cloneSet (0 : Fin 3))
        (dp := inferInstance) (dq := inferInstance) hpred
        candCq (restrictCandidates profile q)).2 hc
    exact (hcq hc').elim
  have hcq_cast' :
      (cast (congrArg (fun r => {a : Fin 3 // r a}) hpred) candCq :
        {a : Fin 3 // clonePred cloneSet (0 : Fin 3) a}) ∉
      scoringRule pluralityScore (restrictCandidates profile (clonePred cloneSet (0 : Fin 3))) := by
    simpa [castCandidates_restrictCandidates] using hcq_cast
  have hcast_candC :
      (cast (congrArg (fun r => {a : Fin 3 // r a}) hpred) candCq :
        {a : Fin 3 // clonePred cloneSet (0 : Fin 3) a}) = candCclone := by
    apply Subtype.ext
    simpa [candCclone, candCq] using (cast_subtype_val (h := hpred) (x := candCq))
  have hcclone :
      candCclone ∉ scoringRule pluralityScore
        (restrictCandidates profile (clonePred cloneSet (0 : Fin 3))) := by
    simpa [hcast_candC] using hcq_cast'
  simpa [plurality_eq_scoringRule, removeClonesExcept] using hcclone

end PluralityIndependenceCounterexample

open PluralityIndependenceCounterexample

theorem plurality_not_independenceOfClones : ¬ IndependenceOfClones plurality := by
  intro hind
  have hclone : CloneSet profile cloneSet := cloneSet_profile
  have hx : (0 : Fin 3) ∈ cloneSet := by
    simp [cloneSet]
  have h := hind (P := profile) (X := cloneSet) (x := (0 : Fin 3)) hclone hx
  have hc : (2 : Fin 3) ∉ cloneSet := by
    simp [cloneSet]
  have hnonclone := h.1 (2 : Fin 3) hc
  have hc_left :
      (⟨2, Or.inl hc⟩ :
        {a : Fin 3 // clonePred cloneSet (0 : Fin 3) a}) ∈
          plurality (removeClonesExcept profile cloneSet (0 : Fin 3)) := by
    simpa [candCclone] using (hnonclone).1 plurality_profile_has_c
  exact (plurality_cloneProfile_not_c hc_left).elim

end SocialChoice
