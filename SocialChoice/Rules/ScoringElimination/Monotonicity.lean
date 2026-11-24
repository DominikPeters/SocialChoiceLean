import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Monotonicity
import SocialChoice.ListBallot
import SocialChoice.ListBallotProfiles
import SocialChoice.Rules
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringRules.Veto.Common
import SocialChoice.Rules.ScoringRules.Plurality.Defs

namespace SocialChoice

open Finset


/-!
# Scoring elimination fails monotonicity (Smith 1973)

We formalize Smith's three-candidate counterexample. The proof is parameterized
by a scoring system that is weakly decreasing and strictly separates top and
bottom scores for 3 candidates, and also separates top and bottom for 2
candidates (the final runoff).
-/

/-- Bottom-count helper. -/
noncomputable def bottomCount {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) (c : A) :
    Nat :=
  (votersBottom P c).card

/-! ## Rank helpers -/

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

lemma prefers_irrefl {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (a : A) :
    ¬ Prefers P v a a := by
  classical
  let _ := P.pref v
  simp [Prefers]

/-- Decompose any score vector on 3 candidates into top/bottom indicators. -/
lemma scoreVec_fin3_decomp (scoreVec : Nat → Int) (r : Nat) (hr : r < 3) :
    scoreVec r =
      scoreVec 1 +
        (if r = 0 then (scoreVec 0 - scoreVec 1) else 0) +
        (if r = 2 then (scoreVec 2 - scoreVec 1) else 0) := by
  by_cases h0 : r = 0
  · simp [h0]
  · by_cases h2 : r = 2
    · simp [h2]
    · have h1 : r = 1 := by
        omega
      simp [h1]

/-- Score formula for 3 candidates in terms of top/bottom counts. -/
lemma scoreCandidate_fin3 {V : Type} [Fintype V] [DecidableEq (Fin 3)]
    (P : Profile V (Fin 3)) (scoreVec : Nat → Int) (c : Fin 3) :
    scoreCandidate P scoreVec c =
      (Fintype.card V : Int) * scoreVec 1 +
        (topCount P c : Int) * (scoreVec 0 - scoreVec 1) +
        (bottomCount P c : Int) * (scoreVec 2 - scoreVec 1) := by
  classical
  have hrankTop : ∀ v, rank (P.pref v) c = 0 ↔ TopRank P v c := by
    intro v
    exact rank_eq_zero_iff_topRank (P := P) (v := v) (c := c)
  have hrankBottom : ∀ v, rank (P.pref v) c = 2 ↔ BottomRank P v c := by
    intro v
    simpa using (rank_eq_card_sub_one_iff_bottomRank (P := P) (v := v) (c := c))
  have hscore :
      scoreCandidate P scoreVec c =
        ∑ v : V,
          (scoreVec 1 +
            (if rank (P.pref v) c = 0 then (scoreVec 0 - scoreVec 1) else 0) +
            (if rank (P.pref v) c = 2 then (scoreVec 2 - scoreVec 1) else 0)) := by
    unfold scoreCandidate
    refine Finset.sum_congr rfl ?_
    intro v _
    have hr : rank (P.pref v) c < 3 := by
      simpa using (rank_lt_card (P.pref v) c)
    simp [scoreVec_fin3_decomp scoreVec (rank (P.pref v) c) hr]
  have hsum_top :
      (∑ v : V, if rank (P.pref v) c = 0 then (scoreVec 0 - scoreVec 1) else 0) =
        ((votersTop P c).card : Int) * (scoreVec 0 - scoreVec 1) := by
    have hcard :
        (Finset.univ.filter (fun v => rank (P.pref v) c = 0)).card =
          (votersTop P c).card := by
      refine cardinality_lemma2 (p := fun v => rank (P.pref v) c = 0)
        (q := fun v => TopRank P v c) ?_
      intro v
      exact hrankTop v
    have hsum_filtered :
        (∑ v : V, if rank (P.pref v) c = 0 then (scoreVec 0 - scoreVec 1) else 0) =
          (Finset.univ.filter (fun v => rank (P.pref v) c = 0)).sum
            (fun _ => (scoreVec 0 - scoreVec 1)) := by
      have h :=
        (Finset.sum_filter
          (s := (Finset.univ : Finset V))
          (p := fun v => rank (P.pref v) c = 0)
          (f := fun _ => (scoreVec 0 - scoreVec 1)))
      simpa using h.symm
    calc
      (∑ v : V, if rank (P.pref v) c = 0 then (scoreVec 0 - scoreVec 1) else 0)
          = (Finset.univ.filter (fun v => rank (P.pref v) c = 0)).sum
              (fun _ => (scoreVec 0 - scoreVec 1)) := hsum_filtered
      _ = ((Finset.univ.filter (fun v => rank (P.pref v) c = 0)).card : Int) *
            (scoreVec 0 - scoreVec 1) := by
            simpa using
              (Finset.sum_const
                (s := (Finset.univ.filter (fun v => rank (P.pref v) c = 0)))
                (b := (scoreVec 0 - scoreVec 1)))
      _ = ((votersTop P c).card : Int) * (scoreVec 0 - scoreVec 1) := by
            simp [hcard]
  have hsum_bottom :
      (∑ v : V, if rank (P.pref v) c = 2 then (scoreVec 2 - scoreVec 1) else 0) =
        ((votersBottom P c).card : Int) * (scoreVec 2 - scoreVec 1) := by
    have hcard :
        (Finset.univ.filter (fun v => rank (P.pref v) c = 2)).card =
          (votersBottom P c).card := by
      refine cardinality_lemma2 (p := fun v => rank (P.pref v) c = 2)
        (q := fun v => BottomRank P v c) ?_
      intro v
      exact hrankBottom v
    have hsum_filtered :
        (∑ v : V, if rank (P.pref v) c = 2 then (scoreVec 2 - scoreVec 1) else 0) =
          (Finset.univ.filter (fun v => rank (P.pref v) c = 2)).sum
            (fun _ => (scoreVec 2 - scoreVec 1)) := by
      have h :=
        (Finset.sum_filter
          (s := (Finset.univ : Finset V))
          (p := fun v => rank (P.pref v) c = 2)
          (f := fun _ => (scoreVec 2 - scoreVec 1)))
      simpa using h.symm
    calc
      (∑ v : V, if rank (P.pref v) c = 2 then (scoreVec 2 - scoreVec 1) else 0)
          = (Finset.univ.filter (fun v => rank (P.pref v) c = 2)).sum
              (fun _ => (scoreVec 2 - scoreVec 1)) := hsum_filtered
      _ = ((Finset.univ.filter (fun v => rank (P.pref v) c = 2)).card : Int) *
            (scoreVec 2 - scoreVec 1) := by
            simpa using
              (Finset.sum_const
                (s := (Finset.univ.filter (fun v => rank (P.pref v) c = 2)))
                (b := (scoreVec 2 - scoreVec 1)))
      _ = ((votersBottom P c).card : Int) * (scoreVec 2 - scoreVec 1) := by
            simp [hcard]
  let t0 : V → Int :=
    fun v => if rank (P.pref v) c = 0 then (scoreVec 0 - scoreVec 1) else 0
  let t2 : V → Int :=
    fun v => if rank (P.pref v) c = 2 then (scoreVec 2 - scoreVec 1) else 0
  have hsum_split :
      (∑ v : V, (scoreVec 1 + t0 v + t2 v)) =
        (∑ v : V, scoreVec 1) + (∑ v : V, t0 v) + (∑ v : V, t2 v) := by
    calc
      (∑ v : V, (scoreVec 1 + t0 v + t2 v))
          = ∑ v : V, ((scoreVec 1 + t0 v) + t2 v) := by
              simp [add_assoc]
      _ = (∑ v : V, (scoreVec 1 + t0 v)) + (∑ v : V, t2 v) := by
              simpa using
                (Finset.sum_add_distrib (s := (Finset.univ : Finset V))
                  (f := fun v => scoreVec 1 + t0 v) (g := fun v => t2 v))
      _ = (∑ v : V, scoreVec 1) + (∑ v : V, t0 v) + (∑ v : V, t2 v) := by
              -- split the first sum and reassociate
              have h :=
                (Finset.sum_add_distrib (s := (Finset.univ : Finset V))
                  (f := fun _ => scoreVec 1) (g := fun v => t0 v))
              -- add (∑ v, t2 v) to both sides
              have h' :
                  (∑ v : V, (scoreVec 1 + t0 v)) + (∑ v : V, t2 v) =
                    ((∑ v : V, scoreVec 1) + (∑ v : V, t0 v)) + (∑ v : V, t2 v) := by
                  simpa using congrArg (fun x => x + (∑ v : V, t2 v)) h
              simpa [add_assoc] using h'

  calc
    scoreCandidate P scoreVec c
        = (∑ v : V,
            (scoreVec 1 +
              (if rank (P.pref v) c = 0 then (scoreVec 0 - scoreVec 1) else 0) +
              (if rank (P.pref v) c = 2 then (scoreVec 2 - scoreVec 1) else 0))) := hscore
    _ = (∑ v : V, scoreVec 1) +
          (∑ v : V, if rank (P.pref v) c = 0 then (scoreVec 0 - scoreVec 1) else 0) +
          (∑ v : V, if rank (P.pref v) c = 2 then (scoreVec 2 - scoreVec 1) else 0) := hsum_split
    _ = (Fintype.card V : Int) * scoreVec 1 +
          ((votersTop P c).card : Int) * (scoreVec 0 - scoreVec 1) +
          ((votersBottom P c).card : Int) * (scoreVec 2 - scoreVec 1) := by
          simp [hsum_top, hsum_bottom]
    _ = (Fintype.card V : Int) * scoreVec 1 +
          (topCount P c : Int) * (scoreVec 0 - scoreVec 1) +
          (bottomCount P c : Int) * (scoreVec 2 - scoreVec 1) := by
          simp [topCount, bottomCount]

/-! ## Two-candidate scores -/

lemma rank_eq_one_of_not_top_two {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (hcard : Fintype.card A = 2) (v : V) (c : A)
    (htop : ¬ TopRank P v c) :
    rank (P.pref v) c = 1 := by
  have hrank_lt : rank (P.pref v) c < 2 := by
    simpa [hcard] using (rank_lt_card (P.pref v) c)
  have hne0 : rank (P.pref v) c ≠ 0 := by
    intro h0
    exact htop ((rank_eq_zero_iff_topRank (P := P) (v := v) (c := c)).1 h0)
  omega

lemma scoreCandidate_two_topCount {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (hcard : Fintype.card A = 2)
    (scoreVec : Nat → Int) (c : A) :
    scoreCandidate P scoreVec c =
      (topCount P c : Int) * scoreVec 0 +
        ((Fintype.card V - topCount P c : Nat) : Int) * scoreVec 1 := by
  classical
  have hrankTop : ∀ v, rank (P.pref v) c = 0 ↔ TopRank P v c := by
    intro v
    exact rank_eq_zero_iff_topRank (P := P) (v := v) (c := c)
  have hscore :
      scoreCandidate P scoreVec c =
        ∑ v : V, if TopRank P v c then scoreVec 0 else scoreVec 1 := by
    unfold scoreCandidate
    refine Finset.sum_congr rfl ?_
    intro v _
    by_cases htop : TopRank P v c
    · have hrank0 : rank (P.pref v) c = 0 := (rank_eq_zero_iff_topRank (P := P) (v := v) (c := c)).2 htop
      simp [htop, hrank0]
    · have hrank1 : rank (P.pref v) c = 1 :=
        rank_eq_one_of_not_top_two (P := P) (hcard := hcard) (v := v) (c := c) htop
      simp [htop, hrank1]
  have hsum_top :
      (∑ v : V, if TopRank P v c then scoreVec 0 else 0) =
        ((votersTop P c).card : Int) * scoreVec 0 := by
    have hsum_filtered :
        (∑ v : V, if TopRank P v c then scoreVec 0 else 0) =
          (Finset.univ.filter (fun v => TopRank P v c)).sum (fun _ => scoreVec 0) := by
      have h :=
        (Finset.sum_filter
          (s := (Finset.univ : Finset V))
          (p := fun v => TopRank P v c)
          (f := fun _ => scoreVec 0))
      simpa using h.symm
    calc
      (∑ v : V, if TopRank P v c then scoreVec 0 else 0)
          = (Finset.univ.filter (fun v => TopRank P v c)).sum (fun _ => scoreVec 0) := hsum_filtered
      _ = ((Finset.univ.filter (fun v => TopRank P v c)).card : Int) * scoreVec 0 := by simp
      _ = ((votersTop P c).card : Int) * scoreVec 0 := by simp [votersTop]
  have hsum_not :
      (∑ v : V, if TopRank P v c then 0 else scoreVec 1) =
        ((Finset.univ.filter (fun v => ¬ TopRank P v c)).card : Int) * scoreVec 1 := by
    have hsum_filtered :
        (∑ v : V, if TopRank P v c then 0 else scoreVec 1) =
          (Finset.univ.filter (fun v => ¬ TopRank P v c)).sum (fun _ => scoreVec 1) := by
      have h :=
        (Finset.sum_filter
          (s := (Finset.univ : Finset V))
          (p := fun v => ¬ TopRank P v c)
          (f := fun _ => scoreVec 1))
      -- Use symmetry of sum_filter
      -- `if TopRank then 0 else scoreVec 1` = `if ¬ TopRank then scoreVec 1 else 0`
      simpa [ite_not] using h.symm
    calc
      (∑ v : V, if TopRank P v c then 0 else scoreVec 1)
          = (Finset.univ.filter (fun v => ¬ TopRank P v c)).sum (fun _ => scoreVec 1) := hsum_filtered
      _ = ((Finset.univ.filter (fun v => ¬ TopRank P v c)).card : Int) * scoreVec 1 := by simp
  have hcard_not :
      (Finset.univ.filter (fun v => ¬ TopRank P v c)).card =
        Fintype.card V - topCount P c := by
    classical
    have hsum :=
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset V))
        (p := fun v => TopRank P v c))
    -- hsum : card(filter p) + card(filter ¬p) = card univ
    have htop : (Finset.univ.filter (fun v => TopRank P v c)).card = topCount P c := by
      simp [topCount, votersTop]
    have hcard_univ : (Finset.univ : Finset V).card = Fintype.card V := by
      simp
    -- rearrange
    have hsum' : topCount P c + (Finset.univ.filter (fun v => ¬ TopRank P v c)).card =
        Fintype.card V := by
      simpa [htop, hcard_univ] using hsum
    -- solve for the complement
    omega
  have hcard_not' :
      ((Finset.univ.filter (fun v => ¬ TopRank P v c)).card : Int) =
        ((Fintype.card V - topCount P c : Nat) : Int) := by
    simpa using (congrArg (fun n : Nat => (n : Int)) hcard_not)
  calc
    scoreCandidate P scoreVec c
        = ∑ v : V, if TopRank P v c then scoreVec 0 else scoreVec 1 := hscore
    _ = (∑ v : V, if TopRank P v c then scoreVec 0 else 0) +
          (∑ v : V, if TopRank P v c then 0 else scoreVec 1) := by
          -- split the if
          have hsplit :
              ∀ v : V,
                (if TopRank P v c then scoreVec 0 else scoreVec 1) =
                  (if TopRank P v c then scoreVec 0 else 0) +
                    (if TopRank P v c then 0 else scoreVec 1) := by
            intro v
            by_cases h : TopRank P v c <;> simp [h]
          calc
            (∑ v : V, if TopRank P v c then scoreVec 0 else scoreVec 1)
                = ∑ v : V,
                    ((if TopRank P v c then scoreVec 0 else 0) +
                      (if TopRank P v c then 0 else scoreVec 1)) := by
                    refine Finset.sum_congr rfl ?_
                    intro v _
                    exact hsplit v
            _ = (∑ v : V, if TopRank P v c then scoreVec 0 else 0) +
                  (∑ v : V, if TopRank P v c then 0 else scoreVec 1) := by
                    simpa using (Finset.sum_add_distrib
                      (s := (Finset.univ : Finset V))
                      (f := fun v => if TopRank P v c then scoreVec 0 else 0)
                      (g := fun v => if TopRank P v c then 0 else scoreVec 1))
    _ = ((votersTop P c).card : Int) * scoreVec 0 +
          ((Finset.univ.filter (fun v => ¬ TopRank P v c)).card : Int) * scoreVec 1 := by
          simp [hsum_top, hsum_not]
    _ = (topCount P c : Int) * scoreVec 0 +
          ((Fintype.card V - topCount P c : Nat) : Int) * scoreVec 1 := by
          simp [topCount, hcard_not']

/-! ## Counterexample profiles -/

namespace ScoringEliminationMonotonicityCounterexample

-- Ballots

def ballotABC : ListBallot 3 := ListBallot.mk' [0, 1, 2]
def ballotACB : ListBallot 3 := ListBallot.mk' [0, 2, 1]
def ballotBAC : ListBallot 3 := ListBallot.mk' [1, 0, 2]
def ballotBCA : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballotCAB : ListBallot 3 := ListBallot.mk' [2, 0, 1]
def ballotCBA : ListBallot 3 := ListBallot.mk' [2, 1, 0]

/-- Original profile: 24 voters equally split among ABC, CAB, BCA;
    9 voters equally split among CBA, ACB, BAC; 4 voters ABC, ACB, ABC, BAC. -/
def ballots : Fin 37 → ListBallot 3
  | 0 => ballotABC
  | 1 => ballotABC
  | 2 => ballotABC
  | 3 => ballotABC
  | 4 => ballotABC
  | 5 => ballotABC
  | 6 => ballotABC
  | 7 => ballotABC
  | 8 => ballotCAB
  | 9 => ballotCAB
  | 10 => ballotCAB
  | 11 => ballotCAB
  | 12 => ballotCAB
  | 13 => ballotCAB
  | 14 => ballotCAB
  | 15 => ballotCAB
  | 16 => ballotBCA
  | 17 => ballotBCA
  | 18 => ballotBCA
  | 19 => ballotBCA
  | 20 => ballotBCA
  | 21 => ballotBCA
  | 22 => ballotBCA
  | 23 => ballotBCA
  | 24 => ballotCBA
  | 25 => ballotCBA
  | 26 => ballotCBA
  | 27 => ballotACB
  | 28 => ballotACB
  | 29 => ballotACB
  | 30 => ballotBAC
  | 31 => ballotBAC
  | 32 => ballotBAC
  | 33 => ballotABC
  | 34 => ballotACB
  | 35 => ballotABC
  | 36 => ballotBAC
  | _ => ballotBAC

/-- Modified profile: CBA -> CAB and BAC -> ABC for the second group. -/
def ballots' : Fin 37 → ListBallot 3
  | 0 => ballotABC
  | 1 => ballotABC
  | 2 => ballotABC
  | 3 => ballotABC
  | 4 => ballotABC
  | 5 => ballotABC
  | 6 => ballotABC
  | 7 => ballotABC
  | 8 => ballotCAB
  | 9 => ballotCAB
  | 10 => ballotCAB
  | 11 => ballotCAB
  | 12 => ballotCAB
  | 13 => ballotCAB
  | 14 => ballotCAB
  | 15 => ballotCAB
  | 16 => ballotBCA
  | 17 => ballotBCA
  | 18 => ballotBCA
  | 19 => ballotBCA
  | 20 => ballotBCA
  | 21 => ballotBCA
  | 22 => ballotBCA
  | 23 => ballotBCA
  | 24 => ballotCAB
  | 25 => ballotCAB
  | 26 => ballotCAB
  | 27 => ballotACB
  | 28 => ballotACB
  | 29 => ballotACB
  | 30 => ballotABC
  | 31 => ballotABC
  | 32 => ballotABC
  | 33 => ballotABC
  | 34 => ballotACB
  | 35 => ballotABC
  | 36 => ballotBAC
  | _ => ballotBAC

noncomputable def profile : Profile (Fin 37) (Fin 3) :=
  profileOfListBallots ballots

noncomputable def profile' : Profile (Fin 37) (Fin 3) :=
  profileOfListBallots ballots'

/-! ## Top/bottom counts for the profiles -/

private lemma topCount_profile_0 : topCount profile (0 : Fin 3) = 14 := by
  have hcount : countTop (fun v => (ballots v).ranking) 0 = 14 := by
    decide
  have hcard : (votersTop profile (0 : Fin 3)).card = 14 := by
    simpa [profile, votersTop_card_eq_countTop] using hcount
  simpa [topCount] using hcard

private lemma topCount_profile_1 : topCount profile (1 : Fin 3) = 12 := by
  have hcount : countTop (fun v => (ballots v).ranking) 1 = 12 := by
    decide
  have hcard : (votersTop profile (1 : Fin 3)).card = 12 := by
    simpa [profile, votersTop_card_eq_countTop] using hcount
  simpa [topCount] using hcard

private lemma topCount_profile_2 : topCount profile (2 : Fin 3) = 11 := by
  have hcount : countTop (fun v => (ballots v).ranking) 2 = 11 := by
    decide
  have hcard : (votersTop profile (2 : Fin 3)).card = 11 := by
    simpa [profile, votersTop_card_eq_countTop] using hcount
  simpa [topCount] using hcard

private lemma bottomCount_profile_0 : bottomCount profile (0 : Fin 3) = 11 := by
  have hcount : countBottom (fun v => (ballots v).ranking) 0 = 11 := by
    decide
  have hcard : (votersBottom profile (0 : Fin 3)).card = 11 := by
    simpa [profile, votersBottom_card_eq_countBottom] using hcount
  simpa [bottomCount] using hcard

private lemma bottomCount_profile_1 : bottomCount profile (1 : Fin 3) = 12 := by
  have hcount : countBottom (fun v => (ballots v).ranking) 1 = 12 := by
    decide
  have hcard : (votersBottom profile (1 : Fin 3)).card = 12 := by
    simpa [profile, votersBottom_card_eq_countBottom] using hcount
  simpa [bottomCount] using hcard

private lemma bottomCount_profile_2 : bottomCount profile (2 : Fin 3) = 14 := by
  have hcount : countBottom (fun v => (ballots v).ranking) 2 = 14 := by
    decide
  have hcard : (votersBottom profile (2 : Fin 3)).card = 14 := by
    simpa [profile, votersBottom_card_eq_countBottom] using hcount
  simpa [bottomCount] using hcard

private lemma topCount_profile'_0 : topCount profile' (0 : Fin 3) = 17 := by
  have hcount : countTop (fun v => (ballots' v).ranking) 0 = 17 := by
    decide
  have hcard : (votersTop profile' (0 : Fin 3)).card = 17 := by
    simpa [profile', votersTop_card_eq_countTop] using hcount
  simpa [topCount] using hcard

private lemma topCount_profile'_1 : topCount profile' (1 : Fin 3) = 9 := by
  have hcount : countTop (fun v => (ballots' v).ranking) 1 = 9 := by
    decide
  have hcard : (votersTop profile' (1 : Fin 3)).card = 9 := by
    simpa [profile', votersTop_card_eq_countTop] using hcount
  simpa [topCount] using hcard

private lemma topCount_profile'_2 : topCount profile' (2 : Fin 3) = 11 := by
  have hcount : countTop (fun v => (ballots' v).ranking) 2 = 11 := by
    decide
  have hcard : (votersTop profile' (2 : Fin 3)).card = 11 := by
    simpa [profile', votersTop_card_eq_countTop] using hcount
  simpa [topCount] using hcard

private lemma bottomCount_profile'_0 : bottomCount profile' (0 : Fin 3) = 8 := by
  have hcount : countBottom (fun v => (ballots' v).ranking) 0 = 8 := by
    decide
  have hcard : (votersBottom profile' (0 : Fin 3)).card = 8 := by
    simpa [profile', votersBottom_card_eq_countBottom] using hcount
  simpa [bottomCount] using hcard

private lemma bottomCount_profile'_1 : bottomCount profile' (1 : Fin 3) = 15 := by
  have hcount : countBottom (fun v => (ballots' v).ranking) 1 = 15 := by
    decide
  have hcard : (votersBottom profile' (1 : Fin 3)).card = 15 := by
    simpa [profile', votersBottom_card_eq_countBottom] using hcount
  simpa [bottomCount] using hcard

private lemma bottomCount_profile'_2 : bottomCount profile' (2 : Fin 3) = 14 := by
  have hcount : countBottom (fun v => (ballots' v).ranking) 2 = 14 := by
    decide
  have hcard : (votersBottom profile' (2 : Fin 3)).card = 14 := by
    simpa [profile', votersBottom_card_eq_countBottom] using hcount
  simpa [bottomCount] using hcard

/-! ## Lowest-scoring candidates in round 1 -/

private lemma score2_lt_score0_profile
    (score : Nat → Nat → Int) (h3 : score 3 0 > score 3 2) :
    scoreCandidate profile (fun r => score 3 r) (2 : Fin 3) <
      scoreCandidate profile (fun r => score 3 r) (0 : Fin 3) := by
  classical
  set s0 : Int := score 3 0
  set s1 : Int := score 3 1
  set s2 : Int := score 3 2
  have hscore0 :
      scoreCandidate profile (fun r => score 3 r) (0 : Fin 3) =
        (37 : Int) * s1 + (14 : Int) * (s0 - s1) + (11 : Int) * (s2 - s1) := by
    simp [scoreCandidate_fin3, topCount_profile_0, bottomCount_profile_0, s0, s1, s2]
  have hscore2 :
      scoreCandidate profile (fun r => score 3 r) (2 : Fin 3) =
        (37 : Int) * s1 + (11 : Int) * (s0 - s1) + (14 : Int) * (s2 - s1) := by
    simp [scoreCandidate_fin3, topCount_profile_2, bottomCount_profile_2, s0, s1, s2]
  have h3' : s0 > s2 := by simpa [s0, s2] using h3
  linarith [hscore0, hscore2, h3']

private lemma score2_lt_score1_profile
    (score : Nat → Nat → Int) (hweak : weaklyDecreasingScore score) (h3 : score 3 0 > score 3 2) :
    scoreCandidate profile (fun r => score 3 r) (2 : Fin 3) <
      scoreCandidate profile (fun r => score 3 r) (1 : Fin 3) := by
  classical
  set s0 : Int := score 3 0
  set s1 : Int := score 3 1
  set s2 : Int := score 3 2
  have hscore1 :
      scoreCandidate profile (fun r => score 3 r) (1 : Fin 3) =
        (37 : Int) * s1 + (12 : Int) * (s0 - s1) + (12 : Int) * (s2 - s1) := by
    simp [scoreCandidate_fin3, topCount_profile_1, bottomCount_profile_1, s0, s1, s2]
  have hscore2 :
      scoreCandidate profile (fun r => score 3 r) (2 : Fin 3) =
        (37 : Int) * s1 + (11 : Int) * (s0 - s1) + (14 : Int) * (s2 - s1) := by
    simp [scoreCandidate_fin3, topCount_profile_2, bottomCount_profile_2, s0, s1, s2]
  have h01 : s1 ≤ s0 := by
    have h := hweak 3 0 1 (by decide) (by decide) (by decide)
    simpa [s0, s1] using h
  have h12 : s2 ≤ s1 := by
    have h := hweak 3 1 2 (by decide) (by decide) (by decide)
    simpa [s1, s2] using h
  have h3' : s0 > s2 := by simpa [s0, s2] using h3
  linarith [hscore1, hscore2, h01, h12, h3']

private lemma lowestScoring_profile_eq
    (score : Nat → Nat → Int) (hweak : weaklyDecreasingScore score) (h3 : score 3 0 > score 3 2) :
    lowestScoring profile (fun r => score 3 r) = ({2} : Finset (Fin 3)) := by
  classical
  let scoreVec : Nat → Int := fun r => score 3 r
  have hlt20 : scoreCandidate profile scoreVec (2 : Fin 3) <
      scoreCandidate profile scoreVec (0 : Fin 3) :=
    score2_lt_score0_profile score h3
  have hlt21 : scoreCandidate profile scoreVec (2 : Fin 3) <
      scoreCandidate profile scoreVec (1 : Fin 3) :=
    score2_lt_score1_profile score hweak h3
  have hA : (Finset.univ : Finset (Fin 3)).Nonempty := by
    simp
  have hmem : (2 : Fin 3) ∈ lowestScoring profile scoreVec := by
    apply (lowestScoring_iff_forall_le (P := profile) (score := scoreVec) hA (2 : Fin 3)).2
    intro d
    fin_cases d
    · exact le_of_lt hlt20
    · exact le_of_lt hlt21
    · exact le_rfl
  have hsubset : lowestScoring profile scoreVec ⊆ ({2} : Finset (Fin 3)) := by
    intro x hx
    fin_cases x
    · have hle :=
        scoreCandidate_le_of_mem_lowestScoring (P := profile) (score := scoreVec)
          (c := (0 : Fin 3)) (e := (2 : Fin 3)) hx
      exact (False.elim ((not_lt_of_ge hle) hlt20))
    · have hle :=
        scoreCandidate_le_of_mem_lowestScoring (P := profile) (score := scoreVec)
          (c := (1 : Fin 3)) (e := (2 : Fin 3)) hx
      exact (False.elim ((not_lt_of_ge hle) hlt21))
    · simp
  apply Finset.ext
  intro x
  constructor
  · intro hx
    exact hsubset hx
  · intro hx
    have hx' : x = (2 : Fin 3) := by simpa using hx
    simpa [hx'] using hmem

private lemma score1_lt_score0_profile'
    (score : Nat → Nat → Int) (hweak : weaklyDecreasingScore score) (h3 : score 3 0 > score 3 2) :
    scoreCandidate profile' (fun r => score 3 r) (1 : Fin 3) <
      scoreCandidate profile' (fun r => score 3 r) (0 : Fin 3) := by
  classical
  set s0 : Int := score 3 0
  set s1 : Int := score 3 1
  set s2 : Int := score 3 2
  have hscore0 :
      scoreCandidate profile' (fun r => score 3 r) (0 : Fin 3) =
        (37 : Int) * s1 + (17 : Int) * (s0 - s1) + (8 : Int) * (s2 - s1) := by
    simp [scoreCandidate_fin3, topCount_profile'_0, bottomCount_profile'_0, s0, s1, s2]
  have hscore1 :
      scoreCandidate profile' (fun r => score 3 r) (1 : Fin 3) =
        (37 : Int) * s1 + (9 : Int) * (s0 - s1) + (15 : Int) * (s2 - s1) := by
    simp [scoreCandidate_fin3, topCount_profile'_1, bottomCount_profile'_1, s0, s1, s2]
  have h01 : s1 ≤ s0 := by
    have h := hweak 3 0 1 (by decide) (by decide) (by decide)
    simpa [s0, s1] using h
  have h12 : s2 ≤ s1 := by
    have h := hweak 3 1 2 (by decide) (by decide) (by decide)
    simpa [s1, s2] using h
  have h3' : s0 > s2 := by simpa [s0, s2] using h3
  linarith [hscore0, hscore1, h01, h12, h3']

private lemma score1_lt_score2_profile'
    (score : Nat → Nat → Int) (hweak : weaklyDecreasingScore score) (h3 : score 3 0 > score 3 2) :
    scoreCandidate profile' (fun r => score 3 r) (1 : Fin 3) <
      scoreCandidate profile' (fun r => score 3 r) (2 : Fin 3) := by
  classical
  set s0 : Int := score 3 0
  set s1 : Int := score 3 1
  set s2 : Int := score 3 2
  have hscore2 :
      scoreCandidate profile' (fun r => score 3 r) (2 : Fin 3) =
        (37 : Int) * s1 + (11 : Int) * (s0 - s1) + (14 : Int) * (s2 - s1) := by
    simp [scoreCandidate_fin3, topCount_profile'_2, bottomCount_profile'_2, s0, s1, s2]
  have hscore1 :
      scoreCandidate profile' (fun r => score 3 r) (1 : Fin 3) =
        (37 : Int) * s1 + (9 : Int) * (s0 - s1) + (15 : Int) * (s2 - s1) := by
    simp [scoreCandidate_fin3, topCount_profile'_1, bottomCount_profile'_1, s0, s1, s2]
  have h01 : s1 ≤ s0 := by
    have h := hweak 3 0 1 (by decide) (by decide) (by decide)
    simpa [s0, s1] using h
  have h12 : s2 ≤ s1 := by
    have h := hweak 3 1 2 (by decide) (by decide) (by decide)
    simpa [s1, s2] using h
  have h3' : s0 > s2 := by simpa [s0, s2] using h3
  linarith [hscore2, hscore1, h01, h12, h3']

private lemma lowestScoring_profile'_eq
    (score : Nat → Nat → Int) (hweak : weaklyDecreasingScore score) (h3 : score 3 0 > score 3 2) :
    lowestScoring profile' (fun r => score 3 r) = ({1} : Finset (Fin 3)) := by
  classical
  let scoreVec : Nat → Int := fun r => score 3 r
  have hlt10 : scoreCandidate profile' scoreVec (1 : Fin 3) <
      scoreCandidate profile' scoreVec (0 : Fin 3) :=
    score1_lt_score0_profile' score hweak h3
  have hlt12 : scoreCandidate profile' scoreVec (1 : Fin 3) <
      scoreCandidate profile' scoreVec (2 : Fin 3) :=
    score1_lt_score2_profile' score hweak h3
  have hA : (Finset.univ : Finset (Fin 3)).Nonempty := by
    simp
  have hmem : (1 : Fin 3) ∈ lowestScoring profile' scoreVec := by
    apply (lowestScoring_iff_forall_le (P := profile') (score := scoreVec) hA (1 : Fin 3)).2
    intro d
    fin_cases d
    · exact le_of_lt hlt10
    · exact le_rfl
    · exact le_of_lt hlt12
  have hsubset : lowestScoring profile' scoreVec ⊆ ({1} : Finset (Fin 3)) := by
    intro x hx
    fin_cases x
    · have hle :=
        scoreCandidate_le_of_mem_lowestScoring (P := profile') (score := scoreVec)
          (c := (0 : Fin 3)) (e := (1 : Fin 3)) hx
      exact (False.elim ((not_lt_of_ge hle) hlt10))
    · simp
    · have hle :=
        scoreCandidate_le_of_mem_lowestScoring (P := profile') (score := scoreVec)
          (c := (2 : Fin 3)) (e := (1 : Fin 3)) hx
      exact (False.elim ((not_lt_of_ge hle) hlt12))
  apply Finset.ext
  intro x
  constructor
  · intro hx
    exact hsubset hx
  · intro hx
    have hx' : x = (1 : Fin 3) := by simpa using hx
    simpa [hx'] using hmem

/-! ## Two-candidate rounds -/

noncomputable def profileAB : Profile (Fin 37) {x : Fin 3 // x ≠ (2 : Fin 3)} :=
  restrictProfile profile (2 : Fin 3)

noncomputable def profileAC' : Profile (Fin 37) {x : Fin 3 // x ≠ (1 : Fin 3)} :=
  restrictProfile profile' (1 : Fin 3)

def candA : {x : Fin 3 // x ≠ (2 : Fin 3)} := ⟨0, by decide⟩
def candB : {x : Fin 3 // x ≠ (2 : Fin 3)} := ⟨1, by decide⟩

def candA' : {x : Fin 3 // x ≠ (1 : Fin 3)} := ⟨0, by decide⟩
def candC' : {x : Fin 3 // x ≠ (1 : Fin 3)} := ⟨2, by decide⟩

private lemma votersPreferring_profile_0_1_card :
    (votersPreferring profile (0 : Fin 3) (1 : Fin 3)).card = 22 := by
  have hcount :
      (Finset.univ.filter (fun v => prefersInList (ballots v).ranking 0 1)).card = 22 := by
    decide
  simpa [profile, votersPreferring_eq_filter_prefersInList] using hcount

private lemma votersPreferring_profile_1_0_card :
    (votersPreferring profile (1 : Fin 3) (0 : Fin 3)).card = 15 := by
  have hcount :
      (Finset.univ.filter (fun v => prefersInList (ballots v).ranking 1 0)).card = 15 := by
    decide
  simpa [profile, votersPreferring_eq_filter_prefersInList] using hcount

private lemma votersPreferring_profile'_0_2_card :
    (votersPreferring profile' (0 : Fin 3) (2 : Fin 3)).card = 18 := by
  have hcount :
      (Finset.univ.filter (fun v => prefersInList (ballots' v).ranking 0 2)).card = 18 := by
    decide
  simpa [profile', votersPreferring_eq_filter_prefersInList] using hcount

private lemma votersPreferring_profile'_2_0_card :
    (votersPreferring profile' (2 : Fin 3) (0 : Fin 3)).card = 19 := by
  have hcount :
      (Finset.univ.filter (fun v => prefersInList (ballots' v).ranking 2 0)).card = 19 := by
    decide
  simpa [profile', votersPreferring_eq_filter_prefersInList] using hcount

private lemma topCount_profileAB_A : topCount profileAB candA = 22 := by
  classical
  have hcard : Fintype.card {x : Fin 3 // x ≠ (2 : Fin 3)} = 2 := by
    simp
  have htopset :
      votersTop profileAB candA = votersPreferring profileAB candA candB :=
    votersTop_eq_votersPreferring_of_two (P := profileAB) hcard candA candB (by decide)
  have hprefset :
      votersPreferring profileAB candA candB = votersPreferring profile (0 : Fin 3) (1 : Fin 3) := by
    ext v
    simp [profileAB, candA, candB]
  have hcardtop : (votersTop profileAB candA).card =
      (votersPreferring profile (0 : Fin 3) (1 : Fin 3)).card := by
    exact (congrArg Finset.card htopset).trans (congrArg Finset.card hprefset)
  have hcardpref : (votersPreferring profile (0 : Fin 3) (1 : Fin 3)).card = 22 :=
    votersPreferring_profile_0_1_card
  have hcard' : (votersTop profileAB candA).card = 22 := by
    exact hcardtop.trans hcardpref
  simpa [topCount] using hcard'

private lemma topCount_profileAB_B : topCount profileAB candB = 15 := by
  classical
  have hcard : Fintype.card {x : Fin 3 // x ≠ (2 : Fin 3)} = 2 := by
    simp
  have htopset :
      votersTop profileAB candB = votersPreferring profileAB candB candA :=
    votersTop_eq_votersPreferring_of_two (P := profileAB) hcard candB candA (by decide)
  have hprefset :
      votersPreferring profileAB candB candA = votersPreferring profile (1 : Fin 3) (0 : Fin 3) := by
    ext v
    simp [profileAB, candA, candB]
  have hcardtop : (votersTop profileAB candB).card =
      (votersPreferring profile (1 : Fin 3) (0 : Fin 3)).card := by
    exact (congrArg Finset.card htopset).trans (congrArg Finset.card hprefset)
  have hcardpref : (votersPreferring profile (1 : Fin 3) (0 : Fin 3)).card = 15 :=
    votersPreferring_profile_1_0_card
  have hcard' : (votersTop profileAB candB).card = 15 := by
    exact hcardtop.trans hcardpref
  simpa [topCount] using hcard'

private lemma topCount_profileAC'_A : topCount profileAC' candA' = 18 := by
  classical
  have hcard : Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} = 2 := by
    simp
  have htopset :
      votersTop profileAC' candA' = votersPreferring profileAC' candA' candC' :=
    votersTop_eq_votersPreferring_of_two (P := profileAC') hcard candA' candC' (by decide)
  have hprefset :
      votersPreferring profileAC' candA' candC' = votersPreferring profile' (0 : Fin 3) (2 : Fin 3) := by
    ext v
    simp [profileAC', candA', candC']
  have hcardtop : (votersTop profileAC' candA').card =
      (votersPreferring profile' (0 : Fin 3) (2 : Fin 3)).card := by
    exact (congrArg Finset.card htopset).trans (congrArg Finset.card hprefset)
  have hcardpref : (votersPreferring profile' (0 : Fin 3) (2 : Fin 3)).card = 18 :=
    votersPreferring_profile'_0_2_card
  have hcard' : (votersTop profileAC' candA').card = 18 := by
    exact hcardtop.trans hcardpref
  simpa [topCount] using hcard'

private lemma topCount_profileAC'_C : topCount profileAC' candC' = 19 := by
  classical
  have hcard : Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} = 2 := by
    simp
  have htopset :
      votersTop profileAC' candC' = votersPreferring profileAC' candC' candA' :=
    votersTop_eq_votersPreferring_of_two (P := profileAC') hcard candC' candA' (by decide)
  have hprefset :
      votersPreferring profileAC' candC' candA' = votersPreferring profile' (2 : Fin 3) (0 : Fin 3) := by
    ext v
    simp [profileAC', candA', candC']
  have hcardtop : (votersTop profileAC' candC').card =
      (votersPreferring profile' (2 : Fin 3) (0 : Fin 3)).card := by
    exact (congrArg Finset.card htopset).trans (congrArg Finset.card hprefset)
  have hcardpref : (votersPreferring profile' (2 : Fin 3) (0 : Fin 3)).card = 19 :=
    votersPreferring_profile'_2_0_card
  have hcard' : (votersTop profileAC' candC').card = 19 := by
    exact hcardtop.trans hcardpref
  simpa [topCount] using hcard'

private lemma lowestScoring_profileAB_eq
    (score : Nat → Nat → Int) (h2 : score 2 0 > score 2 1) :
    lowestScoring profileAB (fun r => score 2 r) = ({candB} : Finset {x : Fin 3 // x ≠ (2 : Fin 3)}) := by
  classical
  let scoreVec : Nat → Int := fun r => score 2 r
  have hcard : Fintype.card {x : Fin 3 // x ≠ (2 : Fin 3)} = 2 := by
    simp
  have hscoreA :
      scoreCandidate profileAB scoreVec candA =
        (topCount profileAB candA : Int) * scoreVec 0 +
          ((Fintype.card (Fin 37) - topCount profileAB candA : Nat) : Int) * scoreVec 1 := by
    simp [scoreCandidate_two_topCount, topCount_profileAB_A]
  have hscoreB :
      scoreCandidate profileAB scoreVec candB =
        (topCount profileAB candB : Int) * scoreVec 0 +
          ((Fintype.card (Fin 37) - topCount profileAB candB : Nat) : Int) * scoreVec 1 := by
    simp [scoreCandidate_two_topCount, topCount_profileAB_B]
  have h2' : scoreVec 0 > scoreVec 1 := by simpa using h2
  have hsubA : (Fintype.card (Fin 37) - 22 : Nat) = 15 := by
    decide
  have hsubB : (Fintype.card (Fin 37) - 15 : Nat) = 22 := by
    decide
  have hscoreA' :
      scoreCandidate profileAB scoreVec candA =
        (22 : Int) * scoreVec 0 + (15 : Int) * scoreVec 1 := by
    calc
      scoreCandidate profileAB scoreVec candA =
          (topCount profileAB candA : Int) * scoreVec 0 +
            ((Fintype.card (Fin 37) - topCount profileAB candA : Nat) : Int) * scoreVec 1 := hscoreA
      _ = (22 : Int) * scoreVec 0 +
            ((Fintype.card (Fin 37) - 22 : Nat) : Int) * scoreVec 1 := by
            simp [topCount_profileAB_A]
      _ = (22 : Int) * scoreVec 0 + (15 : Int) * scoreVec 1 := by
            simp
  have hscoreB' :
      scoreCandidate profileAB scoreVec candB =
        (15 : Int) * scoreVec 0 + (22 : Int) * scoreVec 1 := by
    calc
      scoreCandidate profileAB scoreVec candB =
          (topCount profileAB candB : Int) * scoreVec 0 +
            ((Fintype.card (Fin 37) - topCount profileAB candB : Nat) : Int) * scoreVec 1 := hscoreB
      _ = (15 : Int) * scoreVec 0 +
            ((Fintype.card (Fin 37) - 15 : Nat) : Int) * scoreVec 1 := by
            simp [topCount_profileAB_B]
      _ = (15 : Int) * scoreVec 0 + (22 : Int) * scoreVec 1 := by
            simp
  have hlt : scoreCandidate profileAB scoreVec candB < scoreCandidate profileAB scoreVec candA := by
    -- 15 < 22 and scoreVec 0 > scoreVec 1
    linarith [hscoreA', hscoreB', h2']
  have hA : (Finset.univ : Finset {x : Fin 3 // x ≠ (2 : Fin 3)}).Nonempty := by
    refine ⟨candA, ?_⟩
    simp
  have hmem : candB ∈ lowestScoring profileAB scoreVec := by
    apply (lowestScoring_iff_forall_le (P := profileAB) (score := scoreVec) hA candB).2
    intro d
    by_cases h : d = candB
    · simp [h]
    · -- only other candidate is candA
      have hcard' : Fintype.card {x : Fin 3 // x ≠ (2 : Fin 3)} = 2 := by
        simp
      rcases two_elems_eq_or_eq hcard' candB candA (by decide) d with rfl | rfl
      · exact le_rfl
      · exact le_of_lt hlt
  have hsubset : lowestScoring profileAB scoreVec ⊆ ({candB} : Finset {x : Fin 3 // x ≠ (2 : Fin 3)}) := by
    intro x hx
    by_cases hx' : x = candB
    · simp [hx']
    · -- then x = candA
      have hcard' : Fintype.card {x : Fin 3 // x ≠ (2 : Fin 3)} = 2 := by
        simp
      rcases two_elems_eq_or_eq hcard' candB candA (by decide) x with rfl | rfl
      · cases hx' rfl
      · have hle :=
          scoreCandidate_le_of_mem_lowestScoring (P := profileAB) (score := scoreVec)
            (c := candA) (e := candB) hx
        exact (False.elim ((not_lt_of_ge hle) hlt))
  apply Finset.ext
  intro x
  constructor
  · intro hx
    exact hsubset hx
  · intro hx
    have hx' : x = candB := by simpa using hx
    simpa [hx'] using hmem

private lemma lowestScoring_profileAC'_eq
    (score : Nat → Nat → Int) (h2 : score 2 0 > score 2 1) :
    lowestScoring profileAC' (fun r => score 2 r) = ({candA'} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
  classical
  let scoreVec : Nat → Int := fun r => score 2 r
  have hcard : Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} = 2 := by
    simp
  have hscoreA :
      scoreCandidate profileAC' scoreVec candA' =
        (topCount profileAC' candA' : Int) * scoreVec 0 +
          ((Fintype.card (Fin 37) - topCount profileAC' candA' : Nat) : Int) * scoreVec 1 := by
    simp [scoreCandidate_two_topCount, topCount_profileAC'_A]
  have hscoreC :
      scoreCandidate profileAC' scoreVec candC' =
        (topCount profileAC' candC' : Int) * scoreVec 0 +
          ((Fintype.card (Fin 37) - topCount profileAC' candC' : Nat) : Int) * scoreVec 1 := by
    simp [scoreCandidate_two_topCount, topCount_profileAC'_C]
  have h2' : scoreVec 0 > scoreVec 1 := by simpa using h2
  have hsubA : (Fintype.card (Fin 37) - 18 : Nat) = 19 := by
    decide
  have hsubC : (Fintype.card (Fin 37) - 19 : Nat) = 18 := by
    decide
  have hscoreA' :
      scoreCandidate profileAC' scoreVec candA' =
        (18 : Int) * scoreVec 0 + (19 : Int) * scoreVec 1 := by
    calc
      scoreCandidate profileAC' scoreVec candA' =
          (topCount profileAC' candA' : Int) * scoreVec 0 +
            ((Fintype.card (Fin 37) - topCount profileAC' candA' : Nat) : Int) * scoreVec 1 := hscoreA
      _ = (18 : Int) * scoreVec 0 +
            ((Fintype.card (Fin 37) - 18 : Nat) : Int) * scoreVec 1 := by
            simp [topCount_profileAC'_A]
      _ = (18 : Int) * scoreVec 0 + (19 : Int) * scoreVec 1 := by
            simp
  have hscoreC' :
      scoreCandidate profileAC' scoreVec candC' =
        (19 : Int) * scoreVec 0 + (18 : Int) * scoreVec 1 := by
    calc
      scoreCandidate profileAC' scoreVec candC' =
          (topCount profileAC' candC' : Int) * scoreVec 0 +
            ((Fintype.card (Fin 37) - topCount profileAC' candC' : Nat) : Int) * scoreVec 1 := hscoreC
      _ = (19 : Int) * scoreVec 0 +
            ((Fintype.card (Fin 37) - 19 : Nat) : Int) * scoreVec 1 := by
            simp [topCount_profileAC'_C]
      _ = (19 : Int) * scoreVec 0 + (18 : Int) * scoreVec 1 := by
            simp
  have hlt : scoreCandidate profileAC' scoreVec candA' < scoreCandidate profileAC' scoreVec candC' := by
    linarith [hscoreA', hscoreC', h2']
  have hA : (Finset.univ : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}).Nonempty := by
    refine ⟨candC', ?_⟩
    simp
  have hmem : candA' ∈ lowestScoring profileAC' scoreVec := by
    apply (lowestScoring_iff_forall_le (P := profileAC') (score := scoreVec) hA candA').2
    intro d
    by_cases h : d = candA'
    · simp [h]
    · have hcard' : Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} = 2 := by
        simp
      rcases two_elems_eq_or_eq hcard' candA' candC' (by decide) d with rfl | rfl
      · exact le_rfl
      · exact le_of_lt hlt
  have hsubset : lowestScoring profileAC' scoreVec ⊆ ({candA'} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
    intro x hx
    by_cases hx' : x = candA'
    · simp [hx']
    · have hcard' : Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} = 2 := by
        simp
      rcases two_elems_eq_or_eq hcard' candA' candC' (by decide) x with rfl | rfl
      · cases hx' rfl
      · have hle :=
          scoreCandidate_le_of_mem_lowestScoring (P := profileAC') (score := scoreVec)
            (c := candC') (e := candA') hx
        exact (False.elim ((not_lt_of_ge hle) hlt))
  apply Finset.ext
  intro x
  constructor
  · intro hx
    exact hsubset hx
  · intro hx
    have hx' : x = candA' := by simpa using hx
    simpa [hx'] using hmem

/-! ## Round 1 elimination and final winners -/

private lemma scoringElimination_profile_has_0
    (score : Nat → Nat → Int) (hweak : weaklyDecreasingScore score) (h3 : score 3 0 > score 3 2)
    (h2 : score 2 0 > score 2 1) :
    (0 : Fin 3) ∈ scoringEliminationRule score profile := by
  classical
  let scoreVec : Nat → Int := fun r => score 3 r
  have hL : lowestScoring profile scoreVec = ({2} : Finset (Fin 3)) :=
    lowestScoring_profile_eq score hweak h3
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by
    decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := score) (P := profile) (A := Fin 3) (hcard := hcard)
  -- Reduce to the two-candidate profile after eliminating 2.
  have hAB :
      scoringEliminationAux score (Fin 3) profile =
        liftFinset (scoringEliminationAux score _ (restrictProfile profile (2 : Fin 3))) := by
    simpa [scoreVec, hL] using haux
  -- Now analyze the two-candidate round.
  have hL2 :
      lowestScoring profileAB (fun r => score 2 r) = ({candB} : Finset {x : Fin 3 // x ≠ (2 : Fin 3)}) :=
    lowestScoring_profileAB_eq score h2
  have hcard2 : ¬ Fintype.card {x : Fin 3 // x ≠ (2 : Fin 3)} ≤ 1 := by
    simp
  have haux2 :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := score) (P := profileAB) (A := {x : Fin 3 // x ≠ (2 : Fin 3)}) (hcard := hcard2)
  have hAB' :
      scoringEliminationAux score {x : Fin 3 // x ≠ (2 : Fin 3)} profileAB =
        liftFinset (scoringEliminationAux score _ (restrictProfile profileAB candB)) := by
    simpa [hL2] using haux2
  -- The restriction to a single candidate yields `univ`.
  have hbase :
      scoringEliminationAux score {x : {x : Fin 3 // x ≠ (2 : Fin 3)} // x ≠ candB}
        (restrictProfile profileAB candB) =
          (Finset.univ :
            Finset {x : {x : Fin 3 // x ≠ (2 : Fin 3)} // x ≠ candB}) := by
    have hle : Fintype.card {x : {x : Fin 3 // x ≠ (2 : Fin 3)} // x ≠ candB} ≤ 1 := by
      decide
    simp [scoringEliminationAux]
  -- Conclude candA is a winner in the first elimination.
  have hmemAB : candA ∈ scoringEliminationAux score {x : Fin 3 // x ≠ (2 : Fin 3)} profileAB := by
    -- unfold via hAB'
    have hneq : candA ≠ candB := by decide
    have : candA ∈
        liftFinset (scoringEliminationAux score _ (restrictProfile profileAB candB)) := by
      refine (mem_liftFinset_iff_subtype
        (s := scoringEliminationAux score _ (restrictProfile profileAB candB))
        (x := candA)).2 ?_
      refine ⟨hneq, ?_⟩
      simp [hbase]
    simpa [hAB'] using this
  -- Lift back to the original profile.
  have hmem : (0 : Fin 3) ∈ scoringEliminationAux score (Fin 3) profile := by
    -- use hAB
    have : (0 : Fin 3) ∈
        liftFinset (scoringEliminationAux score _ (restrictProfile profile (2 : Fin 3))) := by
      have hneq : (0 : Fin 3) ≠ (2 : Fin 3) := by decide
      refine (mem_liftFinset_iff_subtype
        (s := scoringEliminationAux score _ (restrictProfile profile (2 : Fin 3)))
        (x := (0 : Fin 3))).2 ?_
      refine ⟨hneq, ?_⟩
      have hsub : (⟨0, hneq⟩ : {x : Fin 3 // x ≠ (2 : Fin 3)}) = candA := by
        ext
        rfl
      simpa [profileAB, hsub] using hmemAB
    simpa [hAB] using this
  have hmem' :
      (0 : Fin 3) ∈
        @scoringEliminationAux (Fin 37) _ score (Fin 3) _ (Classical.decEq (Fin 3)) profile := by
    simpa [scoringEliminationAux_decidableEq_congr
      (score := score) (P := profile)
      (inst1 := instDecidableEqFin 3) (inst2 := Classical.decEq (Fin 3))] using hmem
  simpa [scoringEliminationRule] using hmem'

private lemma scoringElimination_profile'_not_0
    (score : Nat → Nat → Int) (hweak : weaklyDecreasingScore score) (h3 : score 3 0 > score 3 2)
    (h2 : score 2 0 > score 2 1) :
    (0 : Fin 3) ∉ scoringEliminationRule score profile' := by
  classical
  let scoreVec : Nat → Int := fun r => score 3 r
  have hL : lowestScoring profile' scoreVec = ({1} : Finset (Fin 3)) :=
    lowestScoring_profile'_eq score hweak h3
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by
    decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := score) (P := profile') (A := Fin 3) (hcard := hcard)
  have hAC :
      scoringEliminationAux score (Fin 3) profile' =
        liftFinset (scoringEliminationAux score _ (restrictProfile profile' (1 : Fin 3))) := by
    simpa [scoreVec, hL] using haux
  -- Two-candidate round on A vs C.
  have hL2 :
      lowestScoring profileAC' (fun r => score 2 r) = ({candA'} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) :=
    lowestScoring_profileAC'_eq score h2
  have hcard2 : ¬ Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} ≤ 1 := by
    simp
  have haux2 :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := score) (P := profileAC') (A := {x : Fin 3 // x ≠ (1 : Fin 3)}) (hcard := hcard2)
  have hAC' :
      scoringEliminationAux score {x : Fin 3 // x ≠ (1 : Fin 3)} profileAC' =
        liftFinset (scoringEliminationAux score _ (restrictProfile profileAC' candA')) := by
    simpa [hL2] using haux2
  -- In the final round, candC' is the only winner, so candA' is not.
  have hnotmemAC : candA' ∉ scoringEliminationAux score {x : Fin 3 // x ≠ (1 : Fin 3)} profileAC' := by
    intro hmem
    have hmem' : candA' ∈
        liftFinset (scoringEliminationAux score _ (restrictProfile profileAC' candA')) := by
      simpa [hAC'] using hmem
    exact (not_mem_liftFinset_removed (c := candA')
      (s := scoringEliminationAux score _ (restrictProfile profileAC' candA'))) hmem'
  -- Lift back: 0 is not in the overall winner set.
  have hnotmem : (0 : Fin 3) ∉ scoringEliminationAux score (Fin 3) profile' := by
    -- if 0 were in, then candA' would be in the restricted winner set
    intro hmem
    have hmem' : (0 : Fin 3) ∈
        liftFinset (scoringEliminationAux score _ (restrictProfile profile' (1 : Fin 3))) := by
      simpa [hAC] using hmem
    have : candA' ∈ scoringEliminationAux score {x : Fin 3 // x ≠ (1 : Fin 3)} profileAC' := by
      rcases (mem_liftFinset_iff_subtype
        (s := scoringEliminationAux score _ (restrictProfile profile' (1 : Fin 3)))
        (x := (0 : Fin 3))).1 hmem' with ⟨hx, hxmem⟩
      have hsub' : (⟨0, hx⟩ : {x : Fin 3 // x ≠ (1 : Fin 3)}) = candA' := by
        ext
        rfl
      simpa [profileAC', hsub'] using hxmem
    exact hnotmemAC this
  have hnotmem' :
      (0 : Fin 3) ∉
        @scoringEliminationAux (Fin 37) _ score (Fin 3) _ (Classical.decEq (Fin 3)) profile' := by
    simpa [scoringEliminationAux_decidableEq_congr
      (score := score) (P := profile')
      (inst1 := instDecidableEqFin 3) (inst2 := Classical.decEq (Fin 3))] using hnotmem
  simpa [scoringEliminationRule] using hnotmem'

/-! ## Simple lift -/

private lemma prefers_1_2_iff (v : Fin 37) :
    Prefers profile v (1 : Fin 3) (2 : Fin 3) ↔
      Prefers profile' v (1 : Fin 3) (2 : Fin 3) := by
  fin_cases v <;>
    simp [profile, profile', ballots, ballots', prefers_iff_prefersInList, prefersInList] <;>
    decide

private lemma prefers_2_1_iff (v : Fin 37) :
    Prefers profile v (2 : Fin 3) (1 : Fin 3) ↔
      Prefers profile' v (2 : Fin 3) (1 : Fin 3) := by
  fin_cases v <;>
    simp [profile, profile', ballots, ballots', prefers_iff_prefersInList, prefersInList] <;>
    decide

private lemma prefers_0_1_imp (v : Fin 37) :
    Prefers profile v (0 : Fin 3) (1 : Fin 3) →
      Prefers profile' v (0 : Fin 3) (1 : Fin 3) := by
  fin_cases v <;>
    simp [profile, profile', ballots, ballots', prefers_iff_prefersInList, prefersInList] <;>
    decide

private lemma prefers_0_2_imp (v : Fin 37) :
    Prefers profile v (0 : Fin 3) (2 : Fin 3) →
      Prefers profile' v (0 : Fin 3) (2 : Fin 3) := by
  fin_cases v <;>
    simp [profile, profile', ballots, ballots', prefers_iff_prefersInList, prefersInList] <;>
    decide

private lemma prefers_1_0_imp (v : Fin 37) :
    Prefers profile' v (1 : Fin 3) (0 : Fin 3) →
      Prefers profile v (1 : Fin 3) (0 : Fin 3) := by
  fin_cases v <;>
    simp [profile, profile', ballots, ballots', prefers_iff_prefersInList, prefersInList] <;>
    decide

private lemma prefers_2_0_imp (v : Fin 37) :
    Prefers profile' v (2 : Fin 3) (0 : Fin 3) →
      Prefers profile v (2 : Fin 3) (0 : Fin 3) := by
  fin_cases v <;>
    simp [profile, profile', ballots, ballots', prefers_iff_prefersInList, prefersInList] <;>
    decide

private lemma simpleLift_profile : simpleLift profile' profile (0 : Fin 3) := by
  classical
  constructor
  · intro v a b ha hb
    have ha' : a = (1 : Fin 3) ∨ a = (2 : Fin 3) := by
      fin_cases a
      · cases ha rfl
      · simp
      · simp
    have hb' : b = (1 : Fin 3) ∨ b = (2 : Fin 3) := by
      fin_cases b
      · cases hb rfl
      · simp
      · simp
    rcases ha' with rfl | rfl
    · rcases hb' with rfl | rfl
      · simp [profile, profile', ballots, ballots', prefers_iff_prefersInList, prefersInList]
      · simpa using prefers_1_2_iff v
    · rcases hb' with rfl | rfl
      · simpa using prefers_2_1_iff v
      · simp [profile, profile', ballots, ballots', prefers_iff_prefersInList, prefersInList]
  · intro a v
    constructor
    · fin_cases a
      · intro h
        exact (False.elim ((prefers_irrefl (P := profile) (v := v) (a := (0 : Fin 3))) h))
      · exact prefers_0_1_imp v
      · exact prefers_0_2_imp v
    · fin_cases a
      · intro h
        exact (False.elim ((prefers_irrefl (P := profile') (v := v) (a := (0 : Fin 3))) h))
      · exact prefers_1_0_imp v
      · exact prefers_2_0_imp v

/-! ## Main theorem -/

/-- Smith's counterexample: every scoring elimination rule fails monotonicity
    under weakly decreasing scores with strict top-bottom separation. -/
theorem scoringElimination_not_monotonicity
    (score : Nat → Nat → Int)
    (hweak : weaklyDecreasingScore score)
    (h3 : score 3 0 > score 3 2)
    (h2 : score 2 0 > score 2 1) :
    ¬ Monotonicity (scoringEliminationRule score) := by
  intro hmono
  have hx : (0 : Fin 3) ∈ scoringEliminationRule score profile :=
    scoringElimination_profile_has_0 score hweak h3 h2
  have hlift : simpleLift profile' profile (0 : Fin 3) := simpleLift_profile
  have hx' : (0 : Fin 3) ∈ scoringEliminationRule score profile' :=
    hmono profile profile' 0 hx hlift
  exact (scoringElimination_profile'_not_0 score hweak h3 h2) hx'

end ScoringEliminationMonotonicityCounterexample

end SocialChoice
