import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Implications
import SocialChoice.Axioms.Participation
import SocialChoice.ListBallot
import SocialChoice.ListBallotProfiles
import SocialChoice.Margin
import SocialChoice.Profile
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Baldwin.Defs
import SocialChoice.Rules.ScoringRules.Plurality.Defs
import SocialChoice.Rules.ScoringRules.Veto.Common

namespace SocialChoice

open Finset

open Classical
attribute [instance] Classical.decEq Classical.decPred

set_option maxHeartbeats 5000000

/-!
# Baldwin fails positive involvement

Counterexample with 3 candidates and 7 voters:

Full profile (7 voters):
2 voters: 0 > 2 > 1
2 voters: 1 > 0 > 2
1 voter : 2 > 0 > 1
2 voters: 2 > 1 > 0
Baldwin selects {0}.

Remove the voter with ballot 2 > 0 > 1:
Baldwin selects {0,1,2}.

Read backwards, this violates Positive Involvement for candidate 2.
-/

namespace BaldwinPositiveInvolvementCounterexample

-- Ballots

def ballot021 : ListBallot 3 := ListBallot.mk' [0, 2, 1]
def ballot102 : ListBallot 3 := ListBallot.mk' [1, 0, 2]
def ballot201 : ListBallot 3 := ListBallot.mk' [2, 0, 1]
def ballot210 : ListBallot 3 := ListBallot.mk' [2, 1, 0]

-- 7 voters: two 021, two 102, one 201 (to be removed), two 210

def ballots7 : Fin 7 → ListBallot 3
  | ⟨0, _⟩ => ballot021
  | ⟨1, _⟩ => ballot021
  | ⟨2, _⟩ => ballot102
  | ⟨3, _⟩ => ballot201
  | ⟨4, _⟩ => ballot102
  | ⟨5, _⟩ => ballot210
  | ⟨6, _⟩ => ballot210

-- 6 voters: remove the 201 ballot

def ballots6 : Fin 6 → ListBallot 3
  | ⟨0, _⟩ => ballot021
  | ⟨1, _⟩ => ballot021
  | ⟨2, _⟩ => ballot102
  | ⟨3, _⟩ => ballot102
  | ⟨4, _⟩ => ballot210
  | ⟨5, _⟩ => ballot210

-- Electorates for adding/removing a single voter

def voters6 : Finset (Fin 7) := {0, 1, 2, 4, 5, 6}
def voters7 : Finset (Fin 7) := insert (3 : Fin 7) voters6

lemma voters6_not_mem : (3 : Fin 7) ∉ voters6 := by
  simp [voters6]

lemma voters7_eq_univ : (voters7 : Finset (Fin 7)) = Finset.univ := by
  ext x
  fin_cases x <;> simp [voters7, voters6]

noncomputable def fullProfile : Profile (Electorate (Fin 7) (Finset.univ)) (Fin 3) :=
  { pref := fun v => (ballots7 v.1).toLinearOrder }

noncomputable def profile6 : Profile (Electorate (Fin 7) voters6) (Fin 3) :=
  restrictElectorate fullProfile voters6 (by
    intro x hx; exact (Finset.mem_univ x))

noncomputable def profile7 : Profile (Electorate (Fin 7) voters7) (Fin 3) :=
  restrictElectorate fullProfile voters7 (by
    intro x hx; exact (Finset.mem_univ x))

noncomputable def profile7_list : Profile (Fin 7) (Fin 3) :=
  profileOfListBallots ballots7

noncomputable def profile6_list : Profile (Fin 6) (Fin 3) :=
  profileOfListBallots ballots6

noncomputable def e7 : Fin 7 ≃ Electorate (Fin 7) voters7 :=
  { toFun := fun x => ⟨x, by simp [voters7_eq_univ]⟩
    invFun := fun v => v.1
    left_inv := by intro x; rfl
    right_inv := by intro v; cases v; rfl }

noncomputable def e6_to : Fin 6 → Electorate (Fin 7) voters6
  | ⟨0, _⟩ => ⟨0, by simp [voters6]⟩
  | ⟨1, _⟩ => ⟨1, by simp [voters6]⟩
  | ⟨2, _⟩ => ⟨2, by simp [voters6]⟩
  | ⟨3, _⟩ => ⟨4, by simp [voters6]⟩
  | ⟨4, _⟩ => ⟨5, by simp [voters6]⟩
  | ⟨5, _⟩ => ⟨6, by simp [voters6]⟩

noncomputable def e6_inv : Electorate (Fin 7) voters6 → Fin 6
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨1, by decide⟩
  | ⟨2, _⟩ => ⟨2, by decide⟩
  | ⟨3, h⟩ => (False.elim (by simp [voters6] at h))
  | ⟨4, _⟩ => ⟨3, by decide⟩
  | ⟨5, _⟩ => ⟨4, by decide⟩
  | ⟨6, _⟩ => ⟨5, by decide⟩

noncomputable def e6 : Fin 6 ≃ Electorate (Fin 7) voters6 :=
  { toFun := e6_to
    invFun := e6_inv
    left_inv := by
      intro v
      fin_cases v <;> rfl
    right_inv := by
      intro v
      cases v with
      | mk val hmem =>
          fin_cases val <;> simp [e6_to, e6_inv, voters6] at hmem ⊢ }

lemma relabel_profile7_eq_profile7_list :
    relabelProfileVoters e7 profile7 = profile7_list := by
  ext v
  rfl

lemma relabel_profile6_eq_profile6_list :
    relabelProfileVoters e6 profile6 = profile6_list := by
  ext v
  fin_cases v <;> rfl

lemma scoreCandidate_relabelProfileVoters {V W A : Type} [Fintype V] [Fintype W] [Fintype A]
    (e : W ≃ V) (P : Profile V A) (score : Nat → Int) (c : A) :
    scoreCandidate (relabelProfileVoters e P) score c = scoreCandidate P score c := by
  classical
  unfold scoreCandidate relabelProfileVoters
  refine Finset.sum_bij (fun w _ => e w) ?_ ?_ ?_ ?_
  · intro w hw
    simp
  · intro w1 _ w2 _ h
    exact e.injective h
  · intro v hv
    refine ⟨e.symm v, by simp, by simp⟩
  · intro w hw
    simp

lemma profiles_agree :
    ∀ v : Electorate (Fin 7) voters6,
      profile7.pref (liftVoter (u := (3 : Fin 7)) v) = profile6.pref v := by
  intro v
  simpa [profile6, profile7, voters7] using
    (restrictElectorate_agrees (Q := fullProfile) (S := voters6)
      (hS := by intro x hx; exact (Finset.mem_univ x))
      (u := (3 : Fin 7))
      (hSu := by intro x hx; exact (Finset.mem_univ x)) v)

lemma ballot201_top_2 : BallotTop ballot201.toLinearOrder (2 : Fin 3) := by
  intro x hx
  fin_cases x <;> simp [ballot201, ListBallot.lt_iff_idxOf, ListBallot.mk'] at hx ⊢

lemma newVoter_top_2 :
    BallotTop (profile7.pref (newVoter (u := (3 : Fin 7)) (V := voters6) voters6_not_mem))
      (2 : Fin 3) := by
  have hpref :
      profile7.pref (newVoter (u := (3 : Fin 7)) (V := voters6) voters6_not_mem) =
        ballot201.toLinearOrder := by
    simp [profile7, fullProfile, restrictElectorate, ballots7, voters7, voters6, newVoter]
  simpa [hpref] using ballot201_top_2

/-! ## Rank and Borda helpers (3 candidates) -/

lemma rank_eq_zero_iff_topRank {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (c : A) :
    rank (P.pref v) c = 0 ↔ TopRank P v c := by
  classical
  let r := P.pref v
  constructor
  · intro hr d hd
    unfold rank at hr
    have hempty : (Finset.univ.filter (fun x => r.lt x c)) = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa using hr
    have hd_not_above : ¬ r.lt d c := by
      intro hdc
      have : d ∈ Finset.univ.filter (fun x => r.lt x c) :=
        Finset.mem_filter.mpr ⟨by simp, hdc⟩
      simp [hempty] at this
    have hord : r.lt c d ∨ r.lt d c := by
      let _ := r
      have : c < d ∨ d < c := lt_or_gt_of_ne (Ne.symm hd)
      simpa using this
    cases hord with
    | inl hlt => exact hlt
    | inr hgt => exact (hd_not_above hgt).elim
  · intro htop
    unfold rank
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro d hd
    have hdlt : r.lt d c := by
      simpa [Finset.mem_filter] using hd
    have hdc : d ≠ c := by
      intro heq; subst heq
      exact lt_irrefl _ hdlt
    have hcd : r.lt c d := by
      simpa [Prefers] using (htop d hdc)
    exact lt_asymm hcd hdlt

lemma bordaScore_fin3 (r : Nat) (hr : r < 3) :
    bordaScore 3 r = (1 : Int) + (if r = 0 then 1 else 0) - (if r = 2 then 1 else 0) := by
  by_cases h0 : r = 0
  · simp [h0, bordaScore]
  · by_cases h2 : r = 2
    · simp [h2, bordaScore]
    · have h1 : r = 1 := by
        omega
      simp [h1, bordaScore]

lemma scoreCandidate_borda_fin3 {V : Type} [Fintype V]
    (P : Profile V (Fin 3)) (c : Fin 3) :
    scoreCandidate P (fun r => bordaScore 3 r) c =
      (Fintype.card V : Int) + (votersTop P c).card - (votersBottom P c).card := by
  classical
  have hrankTop : ∀ v, rank (P.pref v) c = 0 ↔ TopRank P v c := by
    intro v
    exact rank_eq_zero_iff_topRank (P := P) (v := v) (c := c)
  have hrankBottom : ∀ v, rank (P.pref v) c = 2 ↔ BottomRank P v c := by
    intro v
    -- card (Fin 3) = 3, so rank = 2 iff bottom
    simpa using (rank_eq_card_sub_one_iff_bottomRank (P := P) (v := v) (c := c))
  have hborda : ∀ v,
      bordaScore 3 (rank (P.pref v) c) =
        (1 : Int) + (if rank (P.pref v) c = 0 then 1 else 0) -
          (if rank (P.pref v) c = 2 then 1 else 0) := by
    intro v
    have hr : rank (P.pref v) c < 3 := by
      simpa using (rank_lt_card (P.pref v) c)
    exact bordaScore_fin3 _ hr
  have hscore :
      scoreCandidate P (fun r => bordaScore 3 r) c =
        ∑ v : V,
          ((1 : Int) + (if rank (P.pref v) c = 0 then 1 else 0) -
            (if rank (P.pref v) c = 2 then 1 else 0)) := by
    unfold scoreCandidate
    refine Finset.sum_congr rfl ?_
    intro v _
    exact hborda v
  have hsum_top :
      (∑ v : V, if rank (P.pref v) c = 0 then (1 : Int) else 0) =
        ((votersTop P c).card : Int) := by
    have hsum' :
        (∑ v : V, if rank (P.pref v) c = 0 then (1 : Int) else 0) =
          ∑ v : V, if TopRank P v c then (1 : Int) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      simp [hrankTop v]
    have hsum'' :
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
    calc
      (∑ v : V, if rank (P.pref v) c = 0 then (1 : Int) else 0)
          = ∑ v : V, if TopRank P v c then (1 : Int) else 0 := hsum'
      _ = ((Finset.univ.filter (fun v => TopRank P v c)).card : Int) := hsum''
      _ = (votersTop P c).card := by
            simp [votersTop]
  have hsum_bottom :
      (∑ v : V, if rank (P.pref v) c = 2 then (1 : Int) else 0) =
        ((votersBottom P c).card : Int) := by
    have hsum' :
        (∑ v : V, if rank (P.pref v) c = 2 then (1 : Int) else 0) =
          ∑ v : V, if BottomRank P v c then (1 : Int) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      simp [hrankBottom v]
    have hsum'' :
        (∑ v : V, if BottomRank P v c then (1 : Int) else 0) =
          ((Finset.univ.filter (fun v => BottomRank P v c)).card : Int) := by
      classical
      have hsum_univ :
          (∑ v : V, if BottomRank P v c then (1 : Int) else 0) =
            (Finset.univ : Finset V).sum (fun v => if BottomRank P v c then (1 : Int) else 0) := by
        simp
      have hsum_filtered :
          ((Finset.univ : Finset V).sum (fun v => if BottomRank P v c then (1 : Int) else 0)) =
            (Finset.univ.filter (fun v => BottomRank P v c)).sum (fun _ => (1 : Int)) := by
        have h := (Finset.sum_filter
          (s := (Finset.univ : Finset V))
          (p := fun v => BottomRank P v c)
          (f := fun _ => (1 : Int)))
        exact h.symm
      have hsum_card :
          ((Finset.univ.filter (fun v => BottomRank P v c)).sum (fun _ => (1 : Int))) =
            ((Finset.univ.filter (fun v => BottomRank P v c)).card : Int) := by
        simp
      exact hsum_univ.trans (hsum_filtered.trans hsum_card)
    calc
      (∑ v : V, if rank (P.pref v) c = 2 then (1 : Int) else 0)
          = ∑ v : V, if BottomRank P v c then (1 : Int) else 0 := hsum'
      _ = ((Finset.univ.filter (fun v => BottomRank P v c)).card : Int) := hsum''
      _ = (votersBottom P c).card := by
            simp [votersBottom]
  calc
    scoreCandidate P (fun r => bordaScore 3 r) c
        = ∑ v : V,
          ((1 : Int) + (if rank (P.pref v) c = 0 then 1 else 0) -
            (if rank (P.pref v) c = 2 then 1 else 0)) := hscore
    _ = (Fintype.card V : Int) +
          (∑ v : V, if rank (P.pref v) c = 0 then (1 : Int) else 0) -
          (∑ v : V, if rank (P.pref v) c = 2 then (1 : Int) else 0) := by
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (Fintype.card V : Int) + (votersTop P c).card - (votersBottom P c).card := by
          simp [hsum_top, hsum_bottom]

lemma bordaScore_two_eq (r : Nat) : bordaScore 2 r = (if r = 0 then 1 else 0) := by
  cases r <;> simp [bordaScore]

/-! ## Top and bottom counts (list profiles) -/

lemma votersTop_profile7_list_card (c : Fin 3) :
    (votersTop profile7_list c).card =
      countTop (fun v => (ballots7 v).ranking) c := by
  simpa [profile7_list] using
    (votersTop_card_eq_countTop_list (ballots := ballots7) (c := c))

lemma votersBottom_profile7_list_card (c : Fin 3) :
    (votersBottom profile7_list c).card =
      countBottom (fun v => (ballots7 v).ranking) c := by
  simpa [profile7_list] using
    (votersBottom_card_eq_countBottom (ballots := ballots7) (c := c))

lemma votersTop_profile6_list_card (c : Fin 3) :
    (votersTop profile6_list c).card =
      countTop (fun v => (ballots6 v).ranking) c := by
  simpa [profile6_list] using
    (votersTop_card_eq_countTop_list (ballots := ballots6) (c := c))

lemma votersBottom_profile6_list_card (c : Fin 3) :
    (votersBottom profile6_list c).card =
      countBottom (fun v => (ballots6 v).ranking) c := by
  simpa [profile6_list] using
    (votersBottom_card_eq_countBottom (ballots := ballots6) (c := c))

lemma votersTop_profile7_list_0_card : (votersTop profile7_list (0 : Fin 3)).card = 2 := by
  have h : countTop (fun v => (ballots7 v).ranking) (0 : Fin 3) = 2 := by decide
  simpa [votersTop_profile7_list_card] using h

lemma votersTop_profile7_list_1_card : (votersTop profile7_list (1 : Fin 3)).card = 2 := by
  have h : countTop (fun v => (ballots7 v).ranking) (1 : Fin 3) = 2 := by decide
  simpa [votersTop_profile7_list_card] using h

lemma votersTop_profile7_list_2_card : (votersTop profile7_list (2 : Fin 3)).card = 3 := by
  have h : countTop (fun v => (ballots7 v).ranking) (2 : Fin 3) = 3 := by decide
  simpa [votersTop_profile7_list_card] using h

lemma votersBottom_profile7_list_0_card : (votersBottom profile7_list (0 : Fin 3)).card = 2 := by
  have h : countBottom (fun v => (ballots7 v).ranking) (0 : Fin 3) = 2 := by decide
  simpa [votersBottom_profile7_list_card] using h

lemma votersBottom_profile7_list_1_card : (votersBottom profile7_list (1 : Fin 3)).card = 3 := by
  have h : countBottom (fun v => (ballots7 v).ranking) (1 : Fin 3) = 3 := by decide
  simpa [votersBottom_profile7_list_card] using h

lemma votersBottom_profile7_list_2_card : (votersBottom profile7_list (2 : Fin 3)).card = 2 := by
  have h : countBottom (fun v => (ballots7 v).ranking) (2 : Fin 3) = 2 := by decide
  simpa [votersBottom_profile7_list_card] using h

lemma votersTop_profile6_list_0_card : (votersTop profile6_list (0 : Fin 3)).card = 2 := by
  have h : countTop (fun v => (ballots6 v).ranking) (0 : Fin 3) = 2 := by decide
  simpa [votersTop_profile6_list_card] using h

lemma votersTop_profile6_list_1_card : (votersTop profile6_list (1 : Fin 3)).card = 2 := by
  have h : countTop (fun v => (ballots6 v).ranking) (1 : Fin 3) = 2 := by decide
  simpa [votersTop_profile6_list_card] using h

lemma votersTop_profile6_list_2_card : (votersTop profile6_list (2 : Fin 3)).card = 2 := by
  have h : countTop (fun v => (ballots6 v).ranking) (2 : Fin 3) = 2 := by decide
  simpa [votersTop_profile6_list_card] using h

lemma votersBottom_profile6_list_0_card : (votersBottom profile6_list (0 : Fin 3)).card = 2 := by
  have h : countBottom (fun v => (ballots6 v).ranking) (0 : Fin 3) = 2 := by decide
  simpa [votersBottom_profile6_list_card] using h

lemma votersBottom_profile6_list_1_card : (votersBottom profile6_list (1 : Fin 3)).card = 2 := by
  have h : countBottom (fun v => (ballots6 v).ranking) (1 : Fin 3) = 2 := by decide
  simpa [votersBottom_profile6_list_card] using h

lemma votersBottom_profile6_list_2_card : (votersBottom profile6_list (2 : Fin 3)).card = 2 := by
  have h : countBottom (fun v => (ballots6 v).ranking) (2 : Fin 3) = 2 := by decide
  simpa [votersBottom_profile6_list_card] using h

/-! ## Borda scores (full and reduced profiles) -/

local notation "scoreVec" => fun r => bordaScore 3 r

lemma scoreCandidate_profile7_list_0 :
    scoreCandidate profile7_list scoreVec (0 : Fin 3) = (7 : Int) := by
  have h := scoreCandidate_borda_fin3 (P := profile7_list) (c := (0 : Fin 3))
  simpa [votersTop_profile7_list_0_card, votersBottom_profile7_list_0_card] using h

lemma scoreCandidate_profile7_list_1 :
    scoreCandidate profile7_list scoreVec (1 : Fin 3) = (6 : Int) := by
  have h := scoreCandidate_borda_fin3 (P := profile7_list) (c := (1 : Fin 3))
  simpa [votersTop_profile7_list_1_card, votersBottom_profile7_list_1_card] using h

lemma scoreCandidate_profile7_list_2 :
    scoreCandidate profile7_list scoreVec (2 : Fin 3) = (8 : Int) := by
  have h := scoreCandidate_borda_fin3 (P := profile7_list) (c := (2 : Fin 3))
  simpa [votersTop_profile7_list_2_card, votersBottom_profile7_list_2_card] using h

lemma scoreCandidate_profile6_list_0 :
    scoreCandidate profile6_list scoreVec (0 : Fin 3) = (6 : Int) := by
  have h := scoreCandidate_borda_fin3 (P := profile6_list) (c := (0 : Fin 3))
  simpa [votersTop_profile6_list_0_card, votersBottom_profile6_list_0_card] using h

lemma scoreCandidate_profile6_list_1 :
    scoreCandidate profile6_list scoreVec (1 : Fin 3) = (6 : Int) := by
  have h := scoreCandidate_borda_fin3 (P := profile6_list) (c := (1 : Fin 3))
  simpa [votersTop_profile6_list_1_card, votersBottom_profile6_list_1_card] using h

lemma scoreCandidate_profile6_list_2 :
    scoreCandidate profile6_list scoreVec (2 : Fin 3) = (6 : Int) := by
  have h := scoreCandidate_borda_fin3 (P := profile6_list) (c := (2 : Fin 3))
  simpa [votersTop_profile6_list_2_card, votersBottom_profile6_list_2_card] using h

lemma scoreCandidate_profile7_0 :
    scoreCandidate profile7 scoreVec (0 : Fin 3) = (7 : Int) := by
  have hrel :=
    scoreCandidate_relabelProfileVoters (e := e7) (P := profile7) (score := scoreVec) (c := (0 : Fin 3))
  have hlist : scoreCandidate profile7_list scoreVec (0 : Fin 3) = (7 : Int) :=
    scoreCandidate_profile7_list_0
  have hrel' : scoreCandidate profile7_list scoreVec (0 : Fin 3) =
      scoreCandidate profile7 scoreVec (0 : Fin 3) := by
    simpa [relabel_profile7_eq_profile7_list] using hrel
  simpa [hrel'] using hlist

lemma scoreCandidate_profile7_1 :
    scoreCandidate profile7 scoreVec (1 : Fin 3) = (6 : Int) := by
  have hrel :=
    scoreCandidate_relabelProfileVoters (e := e7) (P := profile7) (score := scoreVec) (c := (1 : Fin 3))
  have hlist : scoreCandidate profile7_list scoreVec (1 : Fin 3) = (6 : Int) :=
    scoreCandidate_profile7_list_1
  have hrel' : scoreCandidate profile7_list scoreVec (1 : Fin 3) =
      scoreCandidate profile7 scoreVec (1 : Fin 3) := by
    simpa [relabel_profile7_eq_profile7_list] using hrel
  simpa [hrel'] using hlist

lemma scoreCandidate_profile7_2 :
    scoreCandidate profile7 scoreVec (2 : Fin 3) = (8 : Int) := by
  have hrel :=
    scoreCandidate_relabelProfileVoters (e := e7) (P := profile7) (score := scoreVec) (c := (2 : Fin 3))
  have hlist : scoreCandidate profile7_list scoreVec (2 : Fin 3) = (8 : Int) :=
    scoreCandidate_profile7_list_2
  have hrel' : scoreCandidate profile7_list scoreVec (2 : Fin 3) =
      scoreCandidate profile7 scoreVec (2 : Fin 3) := by
    simpa [relabel_profile7_eq_profile7_list] using hrel
  simpa [hrel'] using hlist

lemma scoreCandidate_profile6_0 :
    scoreCandidate profile6 scoreVec (0 : Fin 3) = (6 : Int) := by
  have hrel :=
    scoreCandidate_relabelProfileVoters (e := e6) (P := profile6) (score := scoreVec) (c := (0 : Fin 3))
  have hlist : scoreCandidate profile6_list scoreVec (0 : Fin 3) = (6 : Int) :=
    scoreCandidate_profile6_list_0
  have hrel' : scoreCandidate profile6_list scoreVec (0 : Fin 3) =
      scoreCandidate profile6 scoreVec (0 : Fin 3) := by
    simpa [relabel_profile6_eq_profile6_list] using hrel
  simpa [hrel'] using hlist

lemma scoreCandidate_profile6_1 :
    scoreCandidate profile6 scoreVec (1 : Fin 3) = (6 : Int) := by
  have hrel :=
    scoreCandidate_relabelProfileVoters (e := e6) (P := profile6) (score := scoreVec) (c := (1 : Fin 3))
  have hlist : scoreCandidate profile6_list scoreVec (1 : Fin 3) = (6 : Int) :=
    scoreCandidate_profile6_list_1
  have hrel' : scoreCandidate profile6_list scoreVec (1 : Fin 3) =
      scoreCandidate profile6 scoreVec (1 : Fin 3) := by
    simpa [relabel_profile6_eq_profile6_list] using hrel
  simpa [hrel'] using hlist

lemma scoreCandidate_profile6_2 :
    scoreCandidate profile6 scoreVec (2 : Fin 3) = (6 : Int) := by
  have hrel :=
    scoreCandidate_relabelProfileVoters (e := e6) (P := profile6) (score := scoreVec) (c := (2 : Fin 3))
  have hlist : scoreCandidate profile6_list scoreVec (2 : Fin 3) = (6 : Int) :=
    scoreCandidate_profile6_list_2
  have hrel' : scoreCandidate profile6_list scoreVec (2 : Fin 3) =
      scoreCandidate profile6 scoreVec (2 : Fin 3) := by
    simpa [relabel_profile6_eq_profile6_list] using hrel
  simpa [hrel'] using hlist

lemma score1_lt_score0 :
    scoreCandidate profile7 scoreVec (1 : Fin 3) < scoreCandidate profile7 scoreVec (0 : Fin 3) := by
  simp [scoreCandidate_profile7_1, scoreCandidate_profile7_0]

lemma score1_lt_score2 :
    scoreCandidate profile7 scoreVec (1 : Fin 3) < scoreCandidate profile7 scoreVec (2 : Fin 3) := by
  simp [scoreCandidate_profile7_1, scoreCandidate_profile7_2]

lemma lowestScoring_profile7_eq_singleton_1 :
    lowestScoring profile7 scoreVec = ({1} : Finset (Fin 3)) := by
  classical
  have hLne :
      (lowestScoring profile7 scoreVec).Nonempty := by
    exact lowestScoring_nonempty (P := profile7) (score := scoreVec)
      (hA := (Finset.univ_nonempty : (Finset.univ : Finset (Fin 3)).Nonempty))
  have hsubset : lowestScoring profile7 scoreVec ⊆ ({1} : Finset (Fin 3)) := by
    intro x hx
    fin_cases x
    · have hle :=
        scoreCandidate_le_of_mem_lowestScoring (P := profile7) (score := scoreVec)
          (c := (0 : Fin 3)) (e := (1 : Fin 3)) hx
      have hcontra : False := (not_lt_of_ge hle) score1_lt_score0
      exact (False.elim hcontra)
    · simp
    · have hle :=
        scoreCandidate_le_of_mem_lowestScoring (P := profile7) (score := scoreVec)
          (c := (2 : Fin 3)) (e := (1 : Fin 3)) hx
      have hcontra : False := (not_lt_of_ge hle) score1_lt_score2
      exact (False.elim hcontra)
  rcases hLne with ⟨x, hx⟩
  have hx' : x = (1 : Fin 3) := by
    simpa using (hsubset hx)
  have h1mem : (1 : Fin 3) ∈ lowestScoring profile7 scoreVec := by
    simpa [hx'] using hx
  apply Finset.ext
  intro x
  constructor
  · intro hxmem
    exact hsubset hxmem
  · intro hxmem
    have hx' : x = (1 : Fin 3) := by simpa using hxmem
    simpa [hx'] using h1mem

lemma lowestScoring_profile6_eq_univ :
    lowestScoring profile6 scoreVec = (Finset.univ : Finset (Fin 3)) := by
  classical
  have hA : (Finset.univ : Finset (Fin 3)).Nonempty := Finset.univ_nonempty
  apply Finset.ext
  intro x
  constructor
  · intro hx
    simp
  · intro hx
    apply (lowestScoring_iff_forall_le (P := profile6) (score := scoreVec) hA x).2
    intro d
    fin_cases x <;> fin_cases d <;>
      simp [scoreCandidate_profile6_0, scoreCandidate_profile6_1, scoreCandidate_profile6_2]

/-! ## Pairwise preferences (list profiles) -/

lemma votersPreferring_profile7_list_0_2 :
    votersPreferring profile7_list (0 : Fin 3) (2 : Fin 3) =
      ({0, 1, 2, 4} : Finset (Fin 7)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile7_list, ballots7, votersPreferring, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile7_list_2_0 :
    votersPreferring profile7_list (2 : Fin 3) (0 : Fin 3) =
      ({3, 5, 6} : Finset (Fin 7)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile7_list, ballots7, votersPreferring, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile6_list_2_1 :
    votersPreferring profile6_list (2 : Fin 3) (1 : Fin 3) =
      ({0, 1, 4, 5} : Finset (Fin 6)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile6_list, ballots6, votersPreferring, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile6_list_1_2 :
    votersPreferring profile6_list (1 : Fin 3) (2 : Fin 3) =
      ({2, 3} : Finset (Fin 6)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile6_list, ballots6, votersPreferring, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_card_relabelProfileVoters {V W A : Type} [Fintype V] [Fintype W] [Fintype A]
    (e : W ≃ V) (P : Profile V A) (a b : A) :
    (votersPreferring (relabelProfileVoters e P) a b).card =
      (votersPreferring P a b).card := by
  classical
  refine Finset.card_bij
    (s := votersPreferring (relabelProfileVoters e P) a b)
    (t := votersPreferring P a b)
    (i := fun w _ => e w) ?_ ?_ ?_
  · intro w hw
    have hw' : Prefers (relabelProfileVoters e P) w a b := (Finset.mem_filter.mp hw).2
    have hw'' : Prefers P (e w) a b := by
      have hpref : (relabelProfileVoters e P).pref w = P.pref (e w) := rfl
      change @LT.lt A ((relabelProfileVoters e P).pref w).toLT a b at hw'
      rw [hpref] at hw'
      exact hw'
    exact Finset.mem_filter.mpr ⟨by simp, hw''⟩
  · intro w1 _ w2 _ h
    exact e.injective h
  · intro v hv
    have hv' : Prefers P v a b := (Finset.mem_filter.mp hv).2
    refine ⟨e.symm v, ?_, by simp⟩
    have : Prefers (relabelProfileVoters e P) (e.symm v) a b := by
      have hpref : (relabelProfileVoters e P).pref (e.symm v) = P.pref v := by
        change P.pref (e (e.symm v)) = P.pref v
        rw [e.apply_symm_apply]
      change @LT.lt A ((relabelProfileVoters e P).pref (e.symm v)).toLT a b
      rw [hpref]
      exact hv'
    exact Finset.mem_filter.mpr ⟨by simp, this⟩

lemma votersPreferring_profile7_0_2_card :
    (votersPreferring profile7 (0 : Fin 3) (2 : Fin 3)).card = 4 := by
  have hrel :=
    votersPreferring_card_relabelProfileVoters (e := e7) (P := profile7)
      (a := (0 : Fin 3)) (b := (2 : Fin 3))
  have hlist :
      (votersPreferring profile7_list (0 : Fin 3) (2 : Fin 3)).card = 4 := by
    simp [votersPreferring_profile7_list_0_2]
  have hrel' :
      (votersPreferring profile7_list (0 : Fin 3) (2 : Fin 3)).card =
        (votersPreferring profile7 (0 : Fin 3) (2 : Fin 3)).card := by
    simpa [relabel_profile7_eq_profile7_list] using hrel
  exact hrel'.symm.trans hlist

lemma votersPreferring_profile7_2_0_card :
    (votersPreferring profile7 (2 : Fin 3) (0 : Fin 3)).card = 3 := by
  have hrel :=
    votersPreferring_card_relabelProfileVoters (e := e7) (P := profile7)
      (a := (2 : Fin 3)) (b := (0 : Fin 3))
  have hlist :
      (votersPreferring profile7_list (2 : Fin 3) (0 : Fin 3)).card = 3 := by
    simp [votersPreferring_profile7_list_2_0]
  have hrel' :
      (votersPreferring profile7_list (2 : Fin 3) (0 : Fin 3)).card =
        (votersPreferring profile7 (2 : Fin 3) (0 : Fin 3)).card := by
    simpa [relabel_profile7_eq_profile7_list] using hrel
  exact hrel'.symm.trans hlist

lemma votersPreferring_profile6_2_1_card :
    (votersPreferring profile6 (2 : Fin 3) (1 : Fin 3)).card = 4 := by
  have hrel :=
    votersPreferring_card_relabelProfileVoters (e := e6) (P := profile6)
      (a := (2 : Fin 3)) (b := (1 : Fin 3))
  have hlist :
      (votersPreferring profile6_list (2 : Fin 3) (1 : Fin 3)).card = 4 := by
    simp [votersPreferring_profile6_list_2_1]
  have hrel' :
      (votersPreferring profile6_list (2 : Fin 3) (1 : Fin 3)).card =
        (votersPreferring profile6 (2 : Fin 3) (1 : Fin 3)).card := by
    simpa [relabel_profile6_eq_profile6_list] using hrel
  exact hrel'.symm.trans hlist

lemma votersPreferring_profile6_1_2_card :
    (votersPreferring profile6 (1 : Fin 3) (2 : Fin 3)).card = 2 := by
  have hrel :=
    votersPreferring_card_relabelProfileVoters (e := e6) (P := profile6)
      (a := (1 : Fin 3)) (b := (2 : Fin 3))
  have hlist :
      (votersPreferring profile6_list (1 : Fin 3) (2 : Fin 3)).card = 2 := by
    simp [votersPreferring_profile6_list_1_2]
  have hrel' :
      (votersPreferring profile6_list (1 : Fin 3) (2 : Fin 3)).card =
        (votersPreferring profile6 (1 : Fin 3) (2 : Fin 3)).card := by
    simpa [relabel_profile6_eq_profile6_list] using hrel
  exact hrel'.symm.trans hlist

/-! ## Restricted profiles (2 candidates) -/

def cand0_1 : {x : Fin 3 // x ≠ (1 : Fin 3)} := ⟨0, by decide⟩
def cand2_1 : {x : Fin 3 // x ≠ (1 : Fin 3)} := ⟨2, by decide⟩

def cand1_0 : {x : Fin 3 // x ≠ (0 : Fin 3)} := ⟨1, by decide⟩
def cand2_0 : {x : Fin 3 // x ≠ (0 : Fin 3)} := ⟨2, by decide⟩

lemma votersPreferring_restrict_cand0 :
    votersPreferring (restrictProfile profile7 (1 : Fin 3)) cand0_1 cand2_1 =
      votersPreferring profile7 (0 : Fin 3) (2 : Fin 3) := by
  classical
  ext v
  simp [votersPreferring, prefers_restrictProfile_iff, cand0_1, cand2_1]

lemma votersPreferring_restrict_cand2 :
    votersPreferring (restrictProfile profile7 (1 : Fin 3)) cand2_1 cand0_1 =
      votersPreferring profile7 (2 : Fin 3) (0 : Fin 3) := by
  classical
  ext v
  simp [votersPreferring, prefers_restrictProfile_iff, cand0_1, cand2_1]

lemma votersPreferring_restrict_cand2_profile6 :
    votersPreferring (restrictProfile profile6 (0 : Fin 3)) cand2_0 cand1_0 =
      votersPreferring profile6 (2 : Fin 3) (1 : Fin 3) := by
  classical
  ext v
  simp [votersPreferring, prefers_restrictProfile_iff, cand1_0, cand2_0]

lemma votersPreferring_restrict_cand1_profile6 :
    votersPreferring (restrictProfile profile6 (0 : Fin 3)) cand1_0 cand2_0 =
      votersPreferring profile6 (1 : Fin 3) (2 : Fin 3) := by
  classical
  ext v
  simp [votersPreferring, prefers_restrictProfile_iff, cand1_0, cand2_0]

lemma scoreCandidate_restrict_profile7_cand0 :
    scoreCandidate (restrictProfile profile7 (1 : Fin 3)) (fun r => bordaScore 2 r) cand0_1 = 4 := by
  have hcard : Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} = 2 := by
    simp [card_subtype_ne_eq (1 : Fin 3)]
  have hcard' :
      (votersPreferring (restrictProfile profile7 (1 : Fin 3)) cand0_1 cand2_1).card = 4 := by
    simp [votersPreferring_restrict_cand0, votersPreferring_profile7_0_2_card]
  have hscore_eq :
      scoreCandidate (restrictProfile profile7 (1 : Fin 3)) (fun r => bordaScore 2 r) cand0_1 =
        scoreCandidate (restrictProfile profile7 (1 : Fin 3)) (fun r => if r = 0 then 1 else 0) cand0_1 := by
    unfold scoreCandidate
    refine Finset.sum_congr rfl ?_
    intro v _
    simp [bordaScore_two_eq]
  calc
    scoreCandidate (restrictProfile profile7 (1 : Fin 3)) (fun r => bordaScore 2 r) cand0_1
        = scoreCandidate (restrictProfile profile7 (1 : Fin 3)) (fun r => if r = 0 then 1 else 0) cand0_1 := hscore_eq
    _ = (votersPreferring (restrictProfile profile7 (1 : Fin 3)) cand0_1 cand2_1).card := by
          simpa [hcard, pluralityScore] using
            (pluralityScore_eq_votersPreferring_of_two
              (P := restrictProfile profile7 (1 : Fin 3)) hcard cand0_1 cand2_1 (by decide))
    _ = (4 : Int) := by
          exact_mod_cast hcard'

lemma scoreCandidate_restrict_profile7_cand2 :
    scoreCandidate (restrictProfile profile7 (1 : Fin 3)) (fun r => bordaScore 2 r) cand2_1 = 3 := by
  have hcard : Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} = 2 := by
    simp [card_subtype_ne_eq (1 : Fin 3)]
  have hcard' :
      (votersPreferring (restrictProfile profile7 (1 : Fin 3)) cand2_1 cand0_1).card = 3 := by
    simp [votersPreferring_restrict_cand2, votersPreferring_profile7_2_0_card]
  have hscore_eq :
      scoreCandidate (restrictProfile profile7 (1 : Fin 3)) (fun r => bordaScore 2 r) cand2_1 =
        scoreCandidate (restrictProfile profile7 (1 : Fin 3)) (fun r => if r = 0 then 1 else 0) cand2_1 := by
    unfold scoreCandidate
    refine Finset.sum_congr rfl ?_
    intro v _
    simp [bordaScore_two_eq]
  calc
    scoreCandidate (restrictProfile profile7 (1 : Fin 3)) (fun r => bordaScore 2 r) cand2_1
        = scoreCandidate (restrictProfile profile7 (1 : Fin 3)) (fun r => if r = 0 then 1 else 0) cand2_1 := hscore_eq
    _ = (votersPreferring (restrictProfile profile7 (1 : Fin 3)) cand2_1 cand0_1).card := by
          simpa [hcard, pluralityScore] using
            (pluralityScore_eq_votersPreferring_of_two
              (P := restrictProfile profile7 (1 : Fin 3)) hcard cand2_1 cand0_1 (by decide))
    _ = (3 : Int) := by
          exact_mod_cast hcard'

lemma score_restrict_profile7_cand2_lt_cand0 :
    scoreCandidate (restrictProfile profile7 (1 : Fin 3)) (fun r => bordaScore 2 r) cand2_1 <
      scoreCandidate (restrictProfile profile7 (1 : Fin 3)) (fun r => bordaScore 2 r) cand0_1 := by
  simp [scoreCandidate_restrict_profile7_cand2, scoreCandidate_restrict_profile7_cand0]

lemma lowestScoring_restrict_profile7_eq_singleton_cand2 :
    lowestScoring (restrictProfile profile7 (1 : Fin 3)) (fun r => bordaScore 2 r) =
      ({cand2_1} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
  classical
  haveI : Nonempty {x : Fin 3 // x ≠ (1 : Fin 3)} := by
    exact ⟨cand0_1⟩
  have hLne :
      (lowestScoring (restrictProfile profile7 (1 : Fin 3)) (fun r => bordaScore 2 r)).Nonempty := by
    exact lowestScoring_nonempty (P := restrictProfile profile7 (1 : Fin 3))
      (score := fun r => bordaScore 2 r)
      (hA := (Finset.univ_nonempty : (Finset.univ : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}).Nonempty))
  have hsubset :
      lowestScoring (restrictProfile profile7 (1 : Fin 3)) (fun r => bordaScore 2 r) ⊆
        ({cand2_1} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
    intro x hx
    rcases x with ⟨val, hmem⟩
    fin_cases val
    · have hle :=
        scoreCandidate_le_of_mem_lowestScoring
          (P := restrictProfile profile7 (1 : Fin 3)) (score := fun r => bordaScore 2 r)
          (c := cand0_1) (e := cand2_1) hx
      have hcontra : False := (not_lt_of_ge hle) score_restrict_profile7_cand2_lt_cand0
      exact (False.elim hcontra)
    · cases hmem rfl
    ·
      have hx' :
          (⟨2, hmem⟩ : {x : Fin 3 // x ≠ (1 : Fin 3)}) = cand2_1 := by
        apply Subtype.ext
        rfl
      simp [hx']
  rcases hLne with ⟨x, hx⟩
  have hx' : x = cand2_1 := by
    simpa using (hsubset hx)
  have hmem : cand2_1 ∈ lowestScoring (restrictProfile profile7 (1 : Fin 3)) (fun r => bordaScore 2 r) := by
    simpa [hx'] using hx
  apply Finset.ext
  intro x
  constructor
  · intro hxmem
    exact hsubset hxmem
  · intro hxmem
    have hx' : x = cand2_1 := by simpa using hxmem
    simpa [hx'] using hmem

lemma scoreCandidate_restrict_profile6_cand2 :
    scoreCandidate (restrictProfile profile6 (0 : Fin 3)) (fun r => bordaScore 2 r) cand2_0 = 4 := by
  have hcard : Fintype.card {x : Fin 3 // x ≠ (0 : Fin 3)} = 2 := by
    simp [card_subtype_ne_eq (0 : Fin 3)]
  have hcard' :
      (votersPreferring (restrictProfile profile6 (0 : Fin 3)) cand2_0 cand1_0).card = 4 := by
    simp [votersPreferring_restrict_cand2_profile6, votersPreferring_profile6_2_1_card]
  have hscore_eq :
      scoreCandidate (restrictProfile profile6 (0 : Fin 3)) (fun r => bordaScore 2 r) cand2_0 =
        scoreCandidate (restrictProfile profile6 (0 : Fin 3)) (fun r => if r = 0 then 1 else 0) cand2_0 := by
    unfold scoreCandidate
    refine Finset.sum_congr rfl ?_
    intro v _
    simp [bordaScore_two_eq]
  calc
    scoreCandidate (restrictProfile profile6 (0 : Fin 3)) (fun r => bordaScore 2 r) cand2_0
        = scoreCandidate (restrictProfile profile6 (0 : Fin 3)) (fun r => if r = 0 then 1 else 0) cand2_0 := hscore_eq
    _ = (votersPreferring (restrictProfile profile6 (0 : Fin 3)) cand2_0 cand1_0).card := by
          simpa [hcard, pluralityScore] using
            (pluralityScore_eq_votersPreferring_of_two
              (P := restrictProfile profile6 (0 : Fin 3)) hcard cand2_0 cand1_0 (by decide))
    _ = (4 : Int) := by
          exact_mod_cast hcard'

lemma scoreCandidate_restrict_profile6_cand1 :
    scoreCandidate (restrictProfile profile6 (0 : Fin 3)) (fun r => bordaScore 2 r) cand1_0 = 2 := by
  have hcard : Fintype.card {x : Fin 3 // x ≠ (0 : Fin 3)} = 2 := by
    simp [card_subtype_ne_eq (0 : Fin 3)]
  have hcard' :
      (votersPreferring (restrictProfile profile6 (0 : Fin 3)) cand1_0 cand2_0).card = 2 := by
    simp [votersPreferring_restrict_cand1_profile6, votersPreferring_profile6_1_2_card]
  have hscore_eq :
      scoreCandidate (restrictProfile profile6 (0 : Fin 3)) (fun r => bordaScore 2 r) cand1_0 =
        scoreCandidate (restrictProfile profile6 (0 : Fin 3)) (fun r => if r = 0 then 1 else 0) cand1_0 := by
    unfold scoreCandidate
    refine Finset.sum_congr rfl ?_
    intro v _
    simp [bordaScore_two_eq]
  calc
    scoreCandidate (restrictProfile profile6 (0 : Fin 3)) (fun r => bordaScore 2 r) cand1_0
        = scoreCandidate (restrictProfile profile6 (0 : Fin 3)) (fun r => if r = 0 then 1 else 0) cand1_0 := hscore_eq
    _ = (votersPreferring (restrictProfile profile6 (0 : Fin 3)) cand1_0 cand2_0).card := by
          simpa [hcard, pluralityScore] using
            (pluralityScore_eq_votersPreferring_of_two
              (P := restrictProfile profile6 (0 : Fin 3)) hcard cand1_0 cand2_0 (by decide))
    _ = (2 : Int) := by
          exact_mod_cast hcard'

lemma score_restrict_profile6_cand1_lt_cand2 :
    scoreCandidate (restrictProfile profile6 (0 : Fin 3)) (fun r => bordaScore 2 r) cand1_0 <
      scoreCandidate (restrictProfile profile6 (0 : Fin 3)) (fun r => bordaScore 2 r) cand2_0 := by
  simp [scoreCandidate_restrict_profile6_cand1, scoreCandidate_restrict_profile6_cand2]

lemma lowestScoring_restrict_profile6_eq_singleton_cand1 :
    lowestScoring (restrictProfile profile6 (0 : Fin 3)) (fun r => bordaScore 2 r) =
      ({cand1_0} : Finset {x : Fin 3 // x ≠ (0 : Fin 3)}) := by
  classical
  haveI : Nonempty {x : Fin 3 // x ≠ (0 : Fin 3)} := by
    exact ⟨cand1_0⟩
  have hLne :
      (lowestScoring (restrictProfile profile6 (0 : Fin 3)) (fun r => bordaScore 2 r)).Nonempty := by
    exact lowestScoring_nonempty (P := restrictProfile profile6 (0 : Fin 3))
      (score := fun r => bordaScore 2 r)
      (hA := (Finset.univ_nonempty : (Finset.univ : Finset {x : Fin 3 // x ≠ (0 : Fin 3)}).Nonempty))
  have hsubset :
      lowestScoring (restrictProfile profile6 (0 : Fin 3)) (fun r => bordaScore 2 r) ⊆
        ({cand1_0} : Finset {x : Fin 3 // x ≠ (0 : Fin 3)}) := by
    intro x hx
    rcases x with ⟨val, hmem⟩
    fin_cases val
    · cases hmem rfl
    ·
      have hx' :
          (⟨1, hmem⟩ : {x : Fin 3 // x ≠ (0 : Fin 3)}) = cand1_0 := by
        apply Subtype.ext
        rfl
      simp [hx']
    · have hle :=
        scoreCandidate_le_of_mem_lowestScoring
          (P := restrictProfile profile6 (0 : Fin 3)) (score := fun r => bordaScore 2 r)
          (c := cand2_0) (e := cand1_0) hx
      have hcontra : False := (not_lt_of_ge hle) score_restrict_profile6_cand1_lt_cand2
      exact (False.elim hcontra)
  rcases hLne with ⟨x, hx⟩
  have hx' : x = cand1_0 := by
    simpa using (hsubset hx)
  have hmem : cand1_0 ∈ lowestScoring (restrictProfile profile6 (0 : Fin 3)) (fun r => bordaScore 2 r) := by
    simpa [hx'] using hx
  apply Finset.ext
  intro x
  constructor
  · intro hxmem
    exact hsubset hxmem
  · intro hxmem
    have hx' : x = cand1_0 := by simpa using hxmem
    simpa [hx'] using hmem

/-! ## Baldwin outcomes -/

lemma baldwin_profile7_not_2 : (2 : Fin 3) ∉ baldwin profile7 := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := bordaScore) (P := profile7) (hcard := hcard)
  have haux' :
      scoringEliminationAux bordaScore (Fin 3) profile7 =
        ({1} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile7 c))) := by
    simpa [lowestScoring_profile7_eq_singleton_1] using haux
  have hbaldwin :
      baldwin profile7 = scoringEliminationAux bordaScore (Fin 3) profile7 := by
    classical
    simpa [baldwin, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := bordaScore) (P := profile7)
        (inst1 := Classical.decEq (Fin 3)) (inst2 := inferInstance))
  intro hmem
  have hmem' :
      (2 : Fin 3) ∈
        ({1} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile7 c))) := by
    simpa [hbaldwin, haux'] using hmem
  rcases Finset.mem_biUnion.mp hmem' with ⟨c, hcL, hmem_c⟩
  have hc1 : c = (1 : Fin 3) := by
    simpa using (Finset.mem_singleton.mp hcL)
  subst hc1
  have hmem_c' :
      (2 : Fin 3) ∈
        liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile7 (1 : Fin 3))) := by
    simpa using hmem_c
  have hmem_sub :
      cand2_1 ∈ scoringEliminationAux bordaScore _ (restrictProfile profile7 (1 : Fin 3)) := by
    rcases (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux bordaScore _ (restrictProfile profile7 (1 : Fin 3)))
      (x := (2 : Fin 3))).1 hmem_c'
      with ⟨hx, hmem_sub⟩
    have hx' : (⟨2, hx⟩ : {x : Fin 3 // x ≠ (1 : Fin 3)}) = cand2_1 := by
      apply Subtype.ext
      rfl
    simpa [hx'] using hmem_sub
  have hcard' : ¬ Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} ≤ 1 := by decide
  have haux_restrict :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := bordaScore) (P := restrictProfile profile7 (1 : Fin 3)) (hcard := hcard')
  have haux_restrict' :
      scoringEliminationAux bordaScore _ (restrictProfile profile7 (1 : Fin 3)) =
        ({cand2_1} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _
            (restrictProfile (restrictProfile profile7 (1 : Fin 3)) c))) := by
    simpa [lowestScoring_restrict_profile7_eq_singleton_cand2] using haux_restrict
  have hmem_union :
      cand2_1 ∈
        ({cand2_1} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _
            (restrictProfile (restrictProfile profile7 (1 : Fin 3)) c))) := by
    simpa [haux_restrict'] using hmem_sub
  rcases Finset.mem_biUnion.mp hmem_union with ⟨c, hcL, hmem_c''⟩
  have hc : c = cand2_1 := by
    simpa using (Finset.mem_singleton.mp hcL)
  subst hc
  have hnot :
      cand2_1 ∉
        liftFinset (scoringEliminationAux bordaScore _
          (restrictProfile (restrictProfile profile7 (1 : Fin 3)) cand2_1)) := by
    exact not_mem_liftFinset_removed (c := cand2_1)
      (s := scoringEliminationAux bordaScore _
        (restrictProfile (restrictProfile profile7 (1 : Fin 3)) cand2_1))
  exact (hnot hmem_c'').elim

lemma baldwin_profile6_has_2 : (2 : Fin 3) ∈ baldwin profile6 := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := bordaScore) (P := profile6) (hcard := hcard)
  have haux' :
      scoringEliminationAux bordaScore (Fin 3) profile6 =
        (Finset.univ : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile6 c))) := by
    simpa [lowestScoring_profile6_eq_univ] using haux
  have hbaldwin :
      baldwin profile6 = scoringEliminationAux bordaScore (Fin 3) profile6 := by
    classical
    simpa [baldwin, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := bordaScore) (P := profile6)
        (inst1 := Classical.decEq (Fin 3)) (inst2 := inferInstance))
  have hmem_sub :
      cand2_0 ∈ scoringEliminationAux bordaScore _ (restrictProfile profile6 (0 : Fin 3)) := by
    -- In the restricted profile, cand1_0 is lowest, so winners come from removing it
    have hcard' : ¬ Fintype.card {x : Fin 3 // x ≠ (0 : Fin 3)} ≤ 1 := by decide
    have haux_restrict :=
      scoringEliminationAux_eq_biUnion_of_not_card_le_one
        (score := bordaScore) (P := restrictProfile profile6 (0 : Fin 3)) (hcard := hcard')
    have haux_restrict' :
        scoringEliminationAux bordaScore _ (restrictProfile profile6 (0 : Fin 3)) =
          ({cand1_0} : Finset {x : Fin 3 // x ≠ (0 : Fin 3)}).biUnion
            (fun c => liftFinset (scoringEliminationAux bordaScore _
              (restrictProfile (restrictProfile profile6 (0 : Fin 3)) c))) := by
      simpa [lowestScoring_restrict_profile6_eq_singleton_cand1] using haux_restrict
    have hmem_lift :
        cand2_0 ∈
          liftFinset (scoringEliminationAux bordaScore _
            (restrictProfile (restrictProfile profile6 (0 : Fin 3)) cand1_0)) := by
      -- Base case: only cand2_0 remains
      have hbase :
          scoringEliminationAux bordaScore _
            (restrictProfile (restrictProfile profile6 (0 : Fin 3)) cand1_0) =
              (Finset.univ : Finset {x : {x : Fin 3 // x ≠ (0 : Fin 3)} // x ≠ cand1_0}) := by
        simp [scoringEliminationAux]
      have hmem_sub' :
          (⟨cand2_0, by decide⟩ :
              {x : {x : Fin 3 // x ≠ (0 : Fin 3)} // x ≠ cand1_0}) ∈
            scoringEliminationAux bordaScore _
              (restrictProfile (restrictProfile profile6 (0 : Fin 3)) cand1_0) := by
        simp [hbase]
      exact (mem_liftFinset_iff_subtype
        (s := scoringEliminationAux bordaScore _
          (restrictProfile (restrictProfile profile6 (0 : Fin 3)) cand1_0))
        (x := (cand2_0 : {x : Fin 3 // x ≠ (0 : Fin 3)}))).2 ⟨by decide, hmem_sub'⟩
    have hmem_union :
        cand2_0 ∈
          ({cand1_0} : Finset {x : Fin 3 // x ≠ (0 : Fin 3)}).biUnion
            (fun c => liftFinset (scoringEliminationAux bordaScore _
              (restrictProfile (restrictProfile profile6 (0 : Fin 3)) c))) := by
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨cand1_0, by simp, hmem_lift⟩
    simpa [haux_restrict'] using hmem_union
  have hmem_lift :
      (2 : Fin 3) ∈
        liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile6 (0 : Fin 3))) := by
    exact (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux bordaScore _ (restrictProfile profile6 (0 : Fin 3)))
      (x := (2 : Fin 3))).2 ⟨by decide, hmem_sub⟩
  have hmem_union :
      (2 : Fin 3) ∈
        (Finset.univ : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux bordaScore _ (restrictProfile profile6 c))) := by
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨(0 : Fin 3), by simp, ?_⟩
    simpa using hmem_lift
  simpa [hbaldwin, haux'] using hmem_union

end BaldwinPositiveInvolvementCounterexample

open BaldwinPositiveInvolvementCounterexample

theorem baldwin_not_positiveInvolvement : ¬ PositiveInvolvement baldwin := by
  intro hpos
  have hmem : (2 : Fin 3) ∈ baldwin profile6 := baldwin_profile6_has_2
  have htop :
      BallotTop (profile7.pref (newVoter (u := (3 : Fin 7)) (V := voters6) voters6_not_mem))
        (2 : Fin 3) := newVoter_top_2
  have hmem' :
      (2 : Fin 3) ∈ baldwin profile7 := by
    exact hpos (V := voters6) (u := (3 : Fin 7)) (hu := voters6_not_mem)
      (P := profile6) (Q := profile7) (c := (2 : Fin 3)) profiles_agree hmem htop
  exact baldwin_profile7_not_2 hmem'

end SocialChoice
