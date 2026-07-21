import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Clones
import SocialChoice.ListBallot
import SocialChoice.Rules.ScoringRules.Defs
import SocialChoice.Axioms.Independence
import SocialChoice.Rules.ScoringRules.Borda.C2Borda

namespace SocialChoice

open Finset
open scoped BigOperators

theorem borda_independence_of_universally_least_preferred_nonempty :
    ∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq A] [Nonempty V]
      (P : Profile V A) (c d : A),
        c ≠ d →
          (∀ v : V, BottomRank P v d) →
            liftWinners (borda (restrictCandidates P (fun a => a ≠ d))) = borda P := by
  intro V A _ _ _ _ P c d hcd hbottom
  classical
  let P' := restrictCandidates P (fun a => a ≠ d)
  let score : Nat → Int := fun r => bordaScore (Fintype.card A) r
  let score' : Nat → Int := fun r => bordaScore (Fintype.card {a // a ≠ d}) r
  have hA : (Finset.univ : Finset A).Nonempty := ⟨c, by simp⟩
  have hA' : (Finset.univ : Finset {a // a ≠ d}).Nonempty := ⟨⟨c, hcd⟩, by simp⟩
  have hV : (Finset.univ : Finset V).Nonempty := by
    rcases Classical.choice (inferInstance : Nonempty V) with v0
    exact ⟨v0, by simp⟩
  have hscore_voter (v : V) (a : A) (hne : a ≠ d) :
      score' (rank (P'.pref v) ⟨a, hne⟩) =
        score (rank (P.pref v) a) - 1 := by
    let below : Finset A :=
      (Finset.univ.filter (fun y => (P.pref v).lt a y))
    let below' : Finset {x : A // x ≠ d} :=
      (Finset.univ.filter (fun y => (P'.pref v).lt ⟨a, hne⟩ y))
    have hbelow_mem : d ∈ below := by
      have hbot : (P.pref v).lt a d := by
        simpa [Prefers] using (hbottom v a hne)
      exact Finset.mem_filter.mpr ⟨mem_univ _, hbot⟩
    have hlt_iff :
        ∀ y : {x : A // x ≠ d}, (P'.pref v).lt ⟨a, hne⟩ y ↔
          (P.pref v).lt a y.1 := by
      intro y
      rfl
    have himage : below'.image (fun y => y.1) = below.erase d := by
      ext y
      constructor
      · intro hy
        rcases Finset.mem_image.mp hy with ⟨y', hy', rfl⟩
        have hy'lt : (P.pref v).lt a y' := (hlt_iff y').1 (Finset.mem_filter.mp hy').2
        exact Finset.mem_erase.mpr ⟨y'.2, Finset.mem_filter.mpr ⟨by simp, hy'lt⟩⟩
      · intro hy
        have hyne : y ≠ d := (Finset.mem_erase.mp hy).1
        have hylt : (P.pref v).lt a y := (Finset.mem_filter.mp (Finset.mem_erase.mp hy).2).2
        refine Finset.mem_image.mpr ?_
        refine ⟨⟨y, hyne⟩, ?_, rfl⟩
        have hylt' : (P'.pref v).lt ⟨a, hne⟩ ⟨y, hyne⟩ := (hlt_iff ⟨y, hyne⟩).2 hylt
        exact Finset.mem_filter.mpr ⟨by simp, hylt'⟩
    have hinj : Function.Injective (fun y : {x : A // x ≠ d} => y.1) := by
      intro x y hxy
      ext
      exact hxy
    have hbelow_card : below'.card = below.card - 1 := by
      have hcard_image :=
        (Finset.card_image_of_injective (s := below') (f := fun y => y.1) hinj)
      have hcard' : below'.card = (below.erase d).card := by
        simpa [himage] using hcard_image.symm
      have hcard'' : (below.erase d).card = below.card - 1 := by
        simpa using (Finset.card_erase_of_mem (s := below) hbelow_mem)
      exact hcard'.trans hcard''
    have hpos : 1 ≤ below.card := by
      have hpos' : 0 < below.card := Finset.card_pos.mpr ⟨d, hbelow_mem⟩
      exact (Nat.succ_le_iff.2 hpos')
    have hscore' :
        score' (rank (P'.pref v) ⟨a, hne⟩) = Int.ofNat below'.card := by
      simpa [score', below', Prefers] using
        (bordaScore_eq_card_prefers (r := P'.pref v) (x := ⟨a, hne⟩))
    have hscore :
        score (rank (P.pref v) a) = Int.ofNat below.card := by
      simpa [score, below, Prefers] using
        (bordaScore_eq_card_prefers (r := P.pref v) (x := a))
    calc
      score' (rank (P'.pref v) ⟨a, hne⟩) = Int.ofNat below'.card := hscore'
      _ = Int.ofNat (below.card - 1) := by simp [hbelow_card]
      _ = (Int.ofNat below.card) - 1 := by
        simpa using (Int.ofNat_sub hpos)
      _ = score (rank (P.pref v) a) - 1 := by
        simp [hscore]
  have hscoreCandidate (a : A) (hne : a ≠ d) :
      scoreCandidate P' score' ⟨a, hne⟩ =
        scoreCandidate P score a - (Fintype.card V : Int) := by
    unfold scoreCandidate
    have hsum :
        (Finset.univ : Finset V).sum (fun v =>
            score' (rank (P'.pref v) ⟨a, hne⟩)) =
          (Finset.univ : Finset V).sum (fun v =>
            score (rank (P.pref v) a) - 1) := by
      refine Finset.sum_congr rfl ?_
      intro v hv
      exact hscore_voter v a hne
    calc
      (Finset.univ : Finset V).sum (fun v =>
          score' (rank (P'.pref v) ⟨a, hne⟩)) =
        (Finset.univ : Finset V).sum (fun v =>
          score (rank (P.pref v) a) - 1) := hsum
      _ =
        (Finset.univ : Finset V).sum (fun v =>
          score (rank (P.pref v) a)) -
          (Finset.univ : Finset V).sum (fun _v => (1 : Int)) := by
            simp [Finset.sum_sub_distrib]
      _ = scoreCandidate P score a - (Fintype.card V : Int) := by
            simp [scoreCandidate, Finset.sum_const]
  have horder (a b : A) (ha : a ≠ d) (hb : b ≠ d) :
      scoreCandidate P' score' ⟨b, hb⟩ ≤ scoreCandidate P' score' ⟨a, ha⟩ ↔
        scoreCandidate P score b ≤ scoreCandidate P score a := by
    have ha' := hscoreCandidate a ha
    have hb' := hscoreCandidate b hb
    constructor <;> intro h <;> linarith
  have hwinP (a : A) :
      a ∈ borda P ↔
        ∀ b : A, scoreCandidate P score b ≤ scoreCandidate P score a := by
    simpa [borda, scoringRule, score] using
      (scoringWinners_iff_forall_le (P := P) (score := score) (hA := hA) (c := a))
  have hwinP' (a : A) (hne : a ≠ d) :
      (⟨a, hne⟩ : {x : A // x ≠ d}) ∈ borda P' ↔
        ∀ b : {x : A // x ≠ d},
          scoreCandidate P' score' b ≤ scoreCandidate P' score' ⟨a, hne⟩ := by
    simpa [borda, scoringRule, score'] using
      (scoringWinners_iff_forall_le (P := P') (score := score') (hA := hA') (c := ⟨a, hne⟩))
  have hscore_d : scoreCandidate P score d = 0 := by
    unfold scoreCandidate
    have hzero : ∀ v : V, score (rank (P.pref v) d) = 0 := by
      intro v
      let below : Finset A :=
        (Finset.univ.filter (fun y => (P.pref v).lt d y))
      have hbelow_empty : below = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy
        let _ := P.pref v
        have hdy : (P.pref v).lt d y := (Finset.mem_filter.mp hy).2
        have hyd : (P.pref v).lt y d := by
          simpa [Prefers] using (hbottom v y (by simpa [eq_comm] using (ne_of_lt hdy)))
        exact (lt_asymm hdy hyd)
      have hscore_d' :
          score (rank (P.pref v) d) = Int.ofNat below.card := by
        simpa [score, below] using
          (bordaScore_eq_card_prefers (r := P.pref v) (x := d))
      simp [hscore_d', hbelow_empty]
    simp [hzero]
  have hscore_pos (a : A) (hne : a ≠ d) : 0 < scoreCandidate P score a := by
    unfold scoreCandidate
    have hpos_v : ∀ v : V, 0 < score (rank (P.pref v) a) := by
      intro v
      let below : Finset A :=
        (Finset.univ.filter (fun y => (P.pref v).lt a y))
      have hbelow_mem : d ∈ below := by
        have hbot : (P.pref v).lt a d := by
          simpa [Prefers] using (hbottom v a hne)
        exact Finset.mem_filter.mpr ⟨mem_univ _, hbot⟩
      have hcard_pos : 0 < below.card := Finset.card_pos.mpr ⟨d, hbelow_mem⟩
      have hscore' :
          score (rank (P.pref v) a) = Int.ofNat below.card := by
        simpa [score, below] using
          (bordaScore_eq_card_prefers (r := P.pref v) (x := a))
      have hpos_int : (0 : Int) < Int.ofNat below.card := by
        simpa using (Int.ofNat_lt.mpr hcard_pos)
      simpa [hscore'] using hpos_int
    have hsum_pos :
        0 < (Finset.univ : Finset V).sum (fun v => score (rank (P.pref v) a)) := by
      refine Finset.sum_pos (s := (Finset.univ : Finset V))
        (f := fun v => score (rank (P.pref v) a)) ?_ hV
      intro v hv
      exact hpos_v v
    simpa using hsum_pos
  have hscore_d_lt (a : A) (hne : a ≠ d) :
      scoreCandidate P score d < scoreCandidate P score a := by
    simpa [hscore_d] using hscore_pos a hne
  have hnot_winner : d ∉ borda P := by
    intro hd
    have hmax : ∀ b : A, scoreCandidate P score b ≤ scoreCandidate P score d :=
      (hwinP d).1 hd
    exact (not_lt_of_ge (hmax c)) (hscore_d_lt c hcd)
  apply Finset.ext
  intro a
  by_cases had : a = d
  · subst had
    have : a ∉ liftWinners (borda P') := by
      simp [liftWinners, P']
    constructor
    · intro ha
      exact (this ha).elim
    · intro ha
      exact (hnot_winner ha).elim
  · have hne : a ≠ d := had
    constructor
    · intro ha
      have ha' : ∃ h : a ≠ d, (⟨a, h⟩ : {x : A // x ≠ d}) ∈ borda P' := by
        simpa [liftWinners, P'] using ha
      rcases ha' with ⟨hne', ha'⟩
      have hmax' :
          ∀ b : {x : A // x ≠ d},
            scoreCandidate P' score' b ≤ scoreCandidate P' score' ⟨a, hne'⟩ :=
        (hwinP' a hne').1 ha'
      have hmax : ∀ b : A, scoreCandidate P score b ≤ scoreCandidate P score a := by
        intro b
        by_cases hbd : b = d
        · subst hbd
          exact le_of_lt (hscore_d_lt a hne')
        · have hb := hmax' ⟨b, hbd⟩
          exact (horder a b hne' hbd).1 hb
      exact (hwinP a).2 hmax
    · intro ha
      have hmax : ∀ b : A, scoreCandidate P score b ≤ scoreCandidate P score a :=
        (hwinP a).1 ha
      have hne' : a ≠ d := by
        intro hEq
        subst hEq
        exact (hnot_winner ha).elim
      have hmax' :
          ∀ b : {x : A // x ≠ d},
            scoreCandidate P' score' b ≤ scoreCandidate P' score' ⟨a, hne'⟩ := by
        intro b
        have hb : scoreCandidate P score b.1 ≤ scoreCandidate P score a := hmax b.1
        exact (horder a b.1 hne' b.2).2 hb
      have ha' : (⟨a, hne'⟩ : {x : A // x ≠ d}) ∈ borda P' :=
        (hwinP' a hne').2 hmax'
      have ha'' : ∃ h : a ≠ d, (⟨a, h⟩ : {x : A // x ≠ d}) ∈ borda P' := ⟨hne', ha'⟩
      simpa [liftWinners, P'] using ha''

end SocialChoice

namespace SocialChoice

open Classical
open Finset

attribute [instance] Classical.decEq Classical.decPred

/-!
## Borda fails independence of dominated and independence of clones

Counterexample profile (candidates 0=a, 1=b, 2=c):
3 voters: b > a > c
2 voters: a > c > b
Then a dominates c. Borda selects a, but after removing c, Borda selects b.
Also, a and c are clones, so this violates independence of clones.
-/

namespace BordaIndependenceCounterexample

def ballotBAC : ListBallot 3 := ListBallot.mk' [1, 0, 2]
def ballotACB : ListBallot 3 := ListBallot.mk' [0, 2, 1]

def ballots : Fin 5 → ListBallot 3
  | ⟨0, _⟩ => ballotBAC
  | ⟨1, _⟩ => ballotBAC
  | ⟨2, _⟩ => ballotBAC
  | ⟨3, _⟩ => ballotACB
  | ⟨4, _⟩ => ballotACB

noncomputable def profile : Profile (Fin 5) (Fin 3) :=
  profileOfListBallots ballots

lemma prefers_a_c : ∀ v : Fin 5, Prefers profile v (0 : Fin 3) (2 : Fin 3) := by
  intro v
  fin_cases v <;>
    simp [profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma borda_profile_has_a : (0 : Fin 3) ∈ borda profile := by
  decide

lemma borda_profile_not_b : (1 : Fin 3) ∉ borda profile := by
  decide

noncomputable def profile' : Profile (Fin 5) {x : Fin 3 // x ≠ (2 : Fin 3)} :=
  restrictProfile profile (2 : Fin 3)

def cand0 : {x : Fin 3 // x ≠ (2 : Fin 3)} := ⟨0, by decide⟩
def cand1 : {x : Fin 3 // x ≠ (2 : Fin 3)} := ⟨1, by decide⟩

lemma borda_profile'_has_b : cand1 ∈ borda profile' := by
  decide

lemma borda_profile'_not_a : cand0 ∉ borda profile' := by
  decide

lemma lift_borda_profile'_has_b : (1 : Fin 3) ∈ liftWinners (borda profile') := by
  have hb : cand1 ∈ borda profile' := borda_profile'_has_b
  simpa [liftWinners, cand1] using hb

def cloneSet : Set (Fin 3) := {0, 2}

lemma cloneSet_profile : CloneSet profile cloneSet := by
  refine ⟨?_, ?_⟩
  · refine ⟨(0 : Fin 3), by simp [cloneSet]⟩
  intro v c hc
  have hc' : c = (1 : Fin 3) := by
    fin_cases c
    · have hmem : (0 : Fin 3) ∈ cloneSet := by simp [cloneSet]
      exact (hc hmem).elim
    · rfl
    · have hmem : (2 : Fin 3) ∈ cloneSet := by simp [cloneSet]
      exact (hc hmem).elim
  subst hc'
  fin_cases v <;>
    (first
      | right
        intro x hx
        have hx' : x = (0 : Fin 3) ∨ x = (2 : Fin 3) := by
          simpa [cloneSet] using hx
        cases hx' with
        | inl hx0 =>
            subst hx0
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
        | inr hx2 =>
            subst hx2
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
      | left
        intro x hx
        have hx' : x = (0 : Fin 3) ∨ x = (2 : Fin 3) := by
          simpa [cloneSet] using hx
        cases hx' with
        | inl hx0 =>
            subst hx0
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
        | inr hx2 =>
            subst hx2
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide)

lemma clonePred_eq_ne :
    clonePred cloneSet (0 : Fin 3) = (fun a : Fin 3 => a ≠ (2 : Fin 3)) := by
  funext a
  apply propext
  fin_cases a <;> simp [cloneSet, clonePred]

def cand1clone : {a : Fin 3 // clonePred cloneSet (0 : Fin 3) a} :=
  ⟨1, by simp [cloneSet, clonePred]⟩

lemma cast_subtype_val {A : Type} {p q : A → Prop}
    (h : p = q) (x : {a : A // p a}) :
    (cast (congrArg (fun r => {a : A // r a}) h) x : {a : A // q a}).1 = x.1 := by
  cases x
  cases h
  rfl

lemma borda_cloneProfile_has_b_raw :
    cand1clone ∈ borda (removeClonesExcept profile cloneSet (0 : Fin 3)) := by
  classical
  let q : Fin 3 → Prop := fun a => a ≠ (2 : Fin 3)
  have hb : cand1 ∈ borda (restrictCandidates profile q) := by
    simpa [profile', restrictProfile, q] using borda_profile'_has_b
  have hb' : cand1 ∈ scoringRule bordaScore (restrictCandidates profile q) := by
    simpa [borda] using hb
  have hpred : q = clonePred cloneSet (0 : Fin 3) := by
    simpa [q] using clonePred_eq_ne.symm
  have hb_cast :
      (cast (congrArg (fun r => {a : Fin 3 // r a}) hpred) cand1 :
        {a : Fin 3 // clonePred cloneSet (0 : Fin 3) a}) ∈
        scoringRule bordaScore
          (castCandidates (p := q) (q := clonePred cloneSet (0 : Fin 3)) hpred
            (restrictCandidates profile q)) := by
    exact (mem_scoringRule_castCandidates_iff
      (score := bordaScore) (p := q) (q := clonePred cloneSet (0 : Fin 3))
      (dp := inferInstance) (dq := inferInstance) hpred
      cand1 (restrictCandidates profile q)).1 hb'
  have hb_cast' :
      (cast (congrArg (fun r => {a : Fin 3 // r a}) hpred) cand1 :
        {a : Fin 3 // clonePred cloneSet (0 : Fin 3) a}) ∈
        scoringRule bordaScore (restrictCandidates profile (clonePred cloneSet (0 : Fin 3))) := by
    simpa [castCandidates_restrictCandidates] using hb_cast
  have hcast_cand1 :
      (cast (congrArg (fun r => {a : Fin 3 // r a}) hpred) cand1 :
        {a : Fin 3 // clonePred cloneSet (0 : Fin 3) a}) = cand1clone := by
    apply Subtype.ext
    simpa [cand1clone, cand1] using (cast_subtype_val (h := hpred) (x := cand1))
  have hb_final : cand1clone ∈
        scoringRule bordaScore (restrictCandidates profile (clonePred cloneSet (0 : Fin 3))) := by
    simpa [hcast_cand1] using hb_cast'
  simpa [borda, removeClonesExcept] using hb_final

lemma borda_cloneProfile_has_b :
    (⟨1, Or.inl (by simp [cloneSet])⟩ :
        {a : Fin 3 // clonePred cloneSet (0 : Fin 3) a}) ∈
      borda (removeClonesExcept profile cloneSet (0 : Fin 3)) := by
  simpa [cand1clone] using borda_cloneProfile_has_b_raw

end BordaIndependenceCounterexample

open BordaIndependenceCounterexample

theorem borda_not_independenceOfDominated : ¬ IndependenceOfDominated borda := by
  intro hind
  have hpref : ∀ v : Fin 5, Prefers profile v (0 : Fin 3) (2 : Fin 3) :=
    prefers_a_c
  have hEq :=
    hind (P := profile) (c := (0 : Fin 3)) (d := (2 : Fin 3)) hpref
  have hb_left :
      (1 : Fin 3) ∈
        liftWinners (borda (restrictCandidates profile (fun a => a ≠ (2 : Fin 3)))) := by
    change (1 : Fin 3) ∈ liftWinners (borda (restrictProfile profile (2 : Fin 3)))
    exact lift_borda_profile'_has_b
  have hb_right : (1 : Fin 3) ∈ borda profile := by
    simpa [hEq] using hb_left
  exact (borda_profile_not_b hb_right).elim

theorem borda_not_independenceOfClones : ¬ IndependenceOfClones borda := by
  intro hind
  have hclone : CloneSet profile cloneSet := cloneSet_profile
  have hx : (0 : Fin 3) ∈ cloneSet := by
    simp [cloneSet]
  have h := hind (P := profile) (X := cloneSet) (x := (0 : Fin 3)) hclone hx
  have hc : (1 : Fin 3) ∉ cloneSet := by
    simp [cloneSet]
  have hnonclone := h.1 (1 : Fin 3) hc
  have hb_left :
      (⟨1, Or.inl hc⟩ :
        {a : Fin 3 // clonePred cloneSet (0 : Fin 3) a}) ∈
          borda (removeClonesExcept profile cloneSet (0 : Fin 3)) := by
    simpa using borda_cloneProfile_has_b
  have hb_right : (1 : Fin 3) ∈ borda profile := (hnonclone).2 hb_left
  exact (borda_profile_not_b hb_right).elim

end SocialChoice
