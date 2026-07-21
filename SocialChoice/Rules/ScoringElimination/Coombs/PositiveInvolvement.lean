import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Implications
import SocialChoice.Axioms.Participation
import SocialChoice.ListBallot
import SocialChoice.ListBallotProfiles
import SocialChoice.Margin
import SocialChoice.Profile
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Coombs.CondorcetLoser
import SocialChoice.Rules.ScoringElimination.Coombs.Defs
import SocialChoice.Rules.ScoringRules.Veto.Common

namespace SocialChoice

open Finset

open Classical
attribute [instance] Classical.decEq Classical.decPred

set_option maxHeartbeats 5000000

/-!
# Coombs fails positive involvement

Counterexample with 3 candidates and 7 voters:

Full profile (7 voters):
1 voter : 0 > 2 > 1
2 voters: 1 > 0 > 2
1 voter : 1 > 2 > 0
1 voter : 2 > 0 > 1
2 voters: 2 > 1 > 0
Coombs selects {2}.

Remove the voter with ballot 1 > 2 > 0:
Coombs selects {0,1,2}.

Read backwards, this violates Positive Involvement for candidate 1.
-/

namespace CoombsPositiveInvolvementCounterexample

def ballot021 : ListBallot 3 := ListBallot.mk' [0, 2, 1]
def ballot102 : ListBallot 3 := ListBallot.mk' [1, 0, 2]
def ballot120 : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballot201 : ListBallot 3 := ListBallot.mk' [2, 0, 1]
def ballot210 : ListBallot 3 := ListBallot.mk' [2, 1, 0]

def ballots7 : Fin 7 → ListBallot 3
  | ⟨0, _⟩ => ballot021
  | ⟨1, _⟩ => ballot102
  | ⟨2, _⟩ => ballot102
  | ⟨3, _⟩ => ballot120
  | ⟨4, _⟩ => ballot201
  | ⟨5, _⟩ => ballot210
  | ⟨6, _⟩ => ballot210

def ballots6 : Fin 6 → ListBallot 3
  | ⟨0, _⟩ => ballot021
  | ⟨1, _⟩ => ballot102
  | ⟨2, _⟩ => ballot102
  | ⟨3, _⟩ => ballot201
  | ⟨4, _⟩ => ballot210
  | ⟨5, _⟩ => ballot210

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

lemma votersBottom_card_relabelProfileVoters {V W A : Type} [Fintype V] [Fintype W] [Fintype A]
    (e : W ≃ V) (P : Profile V A) (c : A) :
    (votersBottom (relabelProfileVoters e P) c).card = (votersBottom P c).card := by
  classical
  refine Finset.card_bij
    (s := votersBottom (relabelProfileVoters e P) c)
    (t := votersBottom P c)
    (i := fun w _ => e w) ?_ ?_ ?_
  · intro w hw
    have hw' : BottomRank (relabelProfileVoters e P) w c := (Finset.mem_filter.mp hw).2
    have hw'' : BottomRank P (e w) c := by
      intro d hd
      have : Prefers (relabelProfileVoters e P) w d c := hw' d hd
      have hpref : (relabelProfileVoters e P).pref w = P.pref (e w) := rfl
      change @LT.lt A ((relabelProfileVoters e P).pref w).toLT d c at this
      rw [hpref] at this
      exact this
    exact Finset.mem_filter.mpr ⟨by simp, hw''⟩
  · intro w1 _ w2 _ h
    exact e.injective h
  · intro v hv
    have hv' : BottomRank P v c := (Finset.mem_filter.mp hv).2
    refine ⟨e.symm v, ?_, by simp⟩
    have : BottomRank (relabelProfileVoters e P) (e.symm v) c := by
      intro d hd
      have : Prefers P v d c := hv' d hd
      have hpref : (relabelProfileVoters e P).pref (e.symm v) = P.pref v := by
        change P.pref (e (e.symm v)) = P.pref v
        rw [e.apply_symm_apply]
      change @LT.lt A ((relabelProfileVoters e P).pref (e.symm v)).toLT d c
      rw [hpref]
      exact this
    exact Finset.mem_filter.mpr ⟨by simp, this⟩

lemma profiles_agree :
    ∀ v : Electorate (Fin 7) voters6,
      profile7.pref (liftVoter (u := (3 : Fin 7)) v) = profile6.pref v := by
  intro v
  simpa [profile6, profile7, voters7] using
    (restrictElectorate_agrees (Q := fullProfile) (S := voters6)
      (hS := by intro x hx; exact (Finset.mem_univ x))
      (u := (3 : Fin 7))
      (hSu := by intro x hx; exact (Finset.mem_univ x)) v)

lemma ballot120_top_1 : BallotTop ballot120.toLinearOrder (1 : Fin 3) := by
  intro x hx
  fin_cases x <;> simp [ballot120, ListBallot.lt_iff_idxOf, ListBallot.mk'] at hx ⊢

lemma newVoter_top_1 :
    BallotTop (profile7.pref (newVoter (u := (3 : Fin 7)) (V := voters6) voters6_not_mem))
      (1 : Fin 3) := by
  have hpref :
      profile7.pref (newVoter (u := (3 : Fin 7)) (V := voters6) voters6_not_mem) =
        ballot120.toLinearOrder := by
    simp [profile7, fullProfile, restrictElectorate, ballots7, voters7, voters6, newVoter]
  simpa [hpref] using ballot120_top_1

/-! ## Bottom-rank counts (full profile) -/

lemma votersBottom_profile7_card (c : Fin 3) :
    (votersBottom profile7 c).card =
      countBottom (fun v => (ballots7 v).ranking) c := by
  have hlist :
      (votersBottom profile7_list c).card =
        countBottom (fun v => (ballots7 v).ranking) c := by
    simpa [profile7_list] using
      (votersBottom_card_eq_countBottom (ballots := ballots7) (c := c))
  have hrel :
      (votersBottom profile7 c).card = (votersBottom profile7_list c).card := by
    have h :=
      votersBottom_card_relabelProfileVoters (e := e7) (P := profile7) (c := c)
    simpa [relabel_profile7_eq_profile7_list] using h.symm
  exact hrel.trans hlist

lemma votersBottom_profile7_0_card : (votersBottom profile7 (0 : Fin 3)).card = 3 := by
  have h : countBottom (fun v => (ballots7 v).ranking) (0 : Fin 3) = 3 := by decide
  simpa [votersBottom_profile7_card] using h

lemma votersBottom_profile7_1_card : (votersBottom profile7 (1 : Fin 3)).card = 2 := by
  have h : countBottom (fun v => (ballots7 v).ranking) (1 : Fin 3) = 2 := by decide
  simpa [votersBottom_profile7_card] using h

lemma votersBottom_profile7_2_card : (votersBottom profile7 (2 : Fin 3)).card = 2 := by
  have h : countBottom (fun v => (ballots7 v).ranking) (2 : Fin 3) = 2 := by decide
  simpa [votersBottom_profile7_card] using h

lemma notBottom_card {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) {k : Nat} (hcard : (votersBottom P c).card = k) :
    (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card = Fintype.card V - k := by
  classical
  have hsum :
      (Finset.univ.filter (fun v => BottomRank P v c)).card +
        (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card =
        (Finset.univ : Finset V).card := by
    simpa using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset V)) (p := fun v => BottomRank P v c))
  have hbottom :
      (Finset.univ.filter (fun v => BottomRank P v c)).card = k := by
    simpa [votersBottom] using hcard
  have hsum' := hsum
  simp [hbottom] at hsum'
  omega

local notation "scoreVec" => fun r => vetoScore 3 r

lemma scoreCandidate_profile7_0 : scoreCandidate profile7 scoreVec (0 : Fin 3) = (4 : Int) := by
  have hcard :
      (Finset.univ.filter (fun v => ¬ BottomRank profile7 v 0)).card = 4 := by
    have h := notBottom_card (P := profile7) (c := (0 : Fin 3)) (k := 3)
      votersBottom_profile7_0_card
    simpa [voters7, voters6] using h
  calc
    scoreCandidate profile7 scoreVec (0 : Fin 3) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profile7 v 0)).card : Int) := by
          simpa [vetoScore] using
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profile7) (c := (0 : Fin 3)))
    _ = (4 : Int) := by
          exact_mod_cast hcard

lemma scoreCandidate_profile7_1 : scoreCandidate profile7 scoreVec (1 : Fin 3) = (5 : Int) := by
  have hcard :
      (Finset.univ.filter (fun v => ¬ BottomRank profile7 v 1)).card = 5 := by
    have h := notBottom_card (P := profile7) (c := (1 : Fin 3)) (k := 2)
      votersBottom_profile7_1_card
    simpa [voters7, voters6] using h
  calc
    scoreCandidate profile7 scoreVec (1 : Fin 3) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profile7 v 1)).card : Int) := by
          simpa [vetoScore] using
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profile7) (c := (1 : Fin 3)))
    _ = (5 : Int) := by
          exact_mod_cast hcard

lemma scoreCandidate_profile7_2 : scoreCandidate profile7 scoreVec (2 : Fin 3) = (5 : Int) := by
  have hcard :
      (Finset.univ.filter (fun v => ¬ BottomRank profile7 v 2)).card = 5 := by
    have h := notBottom_card (P := profile7) (c := (2 : Fin 3)) (k := 2)
      votersBottom_profile7_2_card
    simpa [voters7, voters6] using h
  calc
    scoreCandidate profile7 scoreVec (2 : Fin 3) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profile7 v 2)).card : Int) := by
          simpa [vetoScore] using
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profile7) (c := (2 : Fin 3)))
    _ = (5 : Int) := by
          exact_mod_cast hcard

lemma score0_lt_score1 :
    scoreCandidate profile7 scoreVec (0 : Fin 3) < scoreCandidate profile7 scoreVec (1 : Fin 3) := by
  simp [scoreCandidate_profile7_0, scoreCandidate_profile7_1]

lemma score0_lt_score2 :
    scoreCandidate profile7 scoreVec (0 : Fin 3) < scoreCandidate profile7 scoreVec (2 : Fin 3) := by
  simp [scoreCandidate_profile7_0, scoreCandidate_profile7_2]

lemma lowestScoring_profile7_eq_singleton_0 :
    lowestScoring profile7 scoreVec = ({0} : Finset (Fin 3)) := by
  classical
  have hLne :
      (lowestScoring profile7 scoreVec).Nonempty := by
    exact lowestScoring_nonempty (P := profile7) (score := scoreVec)
      (hA := (Finset.univ_nonempty : (Finset.univ : Finset (Fin 3)).Nonempty))
  have hsubset : lowestScoring profile7 scoreVec ⊆ ({0} : Finset (Fin 3)) := by
    intro x hx
    fin_cases x
    · simp
    · have hle :=
        scoreCandidate_le_of_mem_lowestScoring (P := profile7) (score := scoreVec)
          (c := (1 : Fin 3)) (e := (0 : Fin 3)) hx
      have hcontra : False := (not_lt_of_ge hle) score0_lt_score1
      exact (False.elim hcontra)
    · have hle :=
        scoreCandidate_le_of_mem_lowestScoring (P := profile7) (score := scoreVec)
          (c := (2 : Fin 3)) (e := (0 : Fin 3)) hx
      have hcontra : False := (not_lt_of_ge hle) score0_lt_score2
      exact (False.elim hcontra)
  rcases hLne with ⟨x, hx⟩
  have hx' : x = (0 : Fin 3) := by
    simpa using (hsubset hx)
  have h0mem : (0 : Fin 3) ∈ lowestScoring profile7 scoreVec := by
    simpa [hx'] using hx
  apply Finset.ext
  intro x
  constructor
  · intro hxmem
    exact hsubset hxmem
  · intro hxmem
    have hx' : x = (0 : Fin 3) := by simpa using hxmem
    simpa [hx'] using h0mem

/-! ## Bottom-rank counts (reduced profile) -/

lemma votersBottom_profile6_card (c : Fin 3) :
    (votersBottom profile6 c).card =
      countBottom (fun v => (ballots6 v).ranking) c := by
  have hlist :
      (votersBottom profile6_list c).card =
        countBottom (fun v => (ballots6 v).ranking) c := by
    simpa [profile6_list] using
      (votersBottom_card_eq_countBottom (ballots := ballots6) (c := c))
  have hrel :
      (votersBottom profile6 c).card = (votersBottom profile6_list c).card := by
    have h :=
      votersBottom_card_relabelProfileVoters (e := e6) (P := profile6) (c := c)
    simpa [relabel_profile6_eq_profile6_list] using h.symm
  exact hrel.trans hlist

lemma votersBottom_profile6_0_card : (votersBottom profile6 (0 : Fin 3)).card = 2 := by
  have h : countBottom (fun v => (ballots6 v).ranking) (0 : Fin 3) = 2 := by decide
  simpa [votersBottom_profile6_card] using h

lemma votersBottom_profile6_1_card : (votersBottom profile6 (1 : Fin 3)).card = 2 := by
  have h : countBottom (fun v => (ballots6 v).ranking) (1 : Fin 3) = 2 := by decide
  simpa [votersBottom_profile6_card] using h

lemma votersBottom_profile6_2_card : (votersBottom profile6 (2 : Fin 3)).card = 2 := by
  have h : countBottom (fun v => (ballots6 v).ranking) (2 : Fin 3) = 2 := by decide
  simpa [votersBottom_profile6_card] using h

lemma scoreCandidate_profile6_0 : scoreCandidate profile6 scoreVec (0 : Fin 3) = (4 : Int) := by
  have hcard :
      (Finset.univ.filter (fun v => ¬ BottomRank profile6 v 0)).card = 4 := by
    have h := notBottom_card (P := profile6) (c := (0 : Fin 3)) (k := 2)
      votersBottom_profile6_0_card
    simpa [voters6] using h
  calc
    scoreCandidate profile6 scoreVec (0 : Fin 3) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profile6 v 0)).card : Int) := by
          simpa [vetoScore] using
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profile6) (c := (0 : Fin 3)))
    _ = (4 : Int) := by
          exact_mod_cast hcard

lemma scoreCandidate_profile6_1 : scoreCandidate profile6 scoreVec (1 : Fin 3) = (4 : Int) := by
  have hcard :
      (Finset.univ.filter (fun v => ¬ BottomRank profile6 v 1)).card = 4 := by
    have h := notBottom_card (P := profile6) (c := (1 : Fin 3)) (k := 2)
      votersBottom_profile6_1_card
    simpa [voters6] using h
  calc
    scoreCandidate profile6 scoreVec (1 : Fin 3) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profile6 v 1)).card : Int) := by
          simpa [vetoScore] using
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profile6) (c := (1 : Fin 3)))
    _ = (4 : Int) := by
          exact_mod_cast hcard

lemma scoreCandidate_profile6_2 : scoreCandidate profile6 scoreVec (2 : Fin 3) = (4 : Int) := by
  have hcard :
      (Finset.univ.filter (fun v => ¬ BottomRank profile6 v 2)).card = 4 := by
    have h := notBottom_card (P := profile6) (c := (2 : Fin 3)) (k := 2)
      votersBottom_profile6_2_card
    simpa [voters6] using h
  calc
    scoreCandidate profile6 scoreVec (2 : Fin 3) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profile6 v 2)).card : Int) := by
          simpa [vetoScore] using
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profile6) (c := (2 : Fin 3)))
    _ = (4 : Int) := by
          exact_mod_cast hcard

lemma lowestScoring_profile6_eq_univ :
    lowestScoring profile6 scoreVec = (Finset.univ : Finset (Fin 3)) := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro _hx
    exact Finset.mem_univ x
  · intro _hx
    have hA : (Finset.univ : Finset (Fin 3)).Nonempty := Finset.univ_nonempty
    apply (lowestScoring_iff_forall_le (P := profile6) (score := scoreVec) hA x).2
    intro d
    fin_cases x <;> fin_cases d <;>
      simp [scoreCandidate_profile6_0, scoreCandidate_profile6_1, scoreCandidate_profile6_2]

/-! ## Pairwise margins -/

lemma marginList_profile7_1_2 :
    marginList (fun v => (ballots7 v).ranking) (1 : Fin 3) (2 : Fin 3) = (-1 : Int) := by
  decide

lemma marginList_profile6_1_0 :
    marginList (fun v => (ballots6 v).ranking) (1 : Fin 3) (0 : Fin 3) = (2 : Int) := by
  decide

lemma margin_profile7_1_2 :
    margin profile7 (1 : Fin 3) (2 : Fin 3) = (-1 : Int) := by
  have hrel :=
    margin_relabelProfileVoters (e := e7) (P := profile7) (a := (1 : Fin 3)) (b := (2 : Fin 3))
  have hlist :
      margin (relabelProfileVoters e7 profile7) (1 : Fin 3) (2 : Fin 3) =
        marginList (fun v => (ballots7 v).ranking) (1 : Fin 3) (2 : Fin 3) := by
    simpa [relabel_profile7_eq_profile7_list, profile7_list] using
      (margin_eq_marginList (ballots := ballots7) (a := (1 : Fin 3)) (b := (2 : Fin 3)))
  calc
    margin profile7 (1 : Fin 3) (2 : Fin 3)
        = margin (relabelProfileVoters e7 profile7) (1 : Fin 3) (2 : Fin 3) := by
            symm
            exact hrel
    _ = marginList (fun v => (ballots7 v).ranking) (1 : Fin 3) (2 : Fin 3) := hlist
    _ = (-1 : Int) := marginList_profile7_1_2

lemma margin_profile6_1_0 :
    margin profile6 (1 : Fin 3) (0 : Fin 3) = (2 : Int) := by
  have hrel :=
    margin_relabelProfileVoters (e := e6) (P := profile6) (a := (1 : Fin 3)) (b := (0 : Fin 3))
  have hlist :
      margin (relabelProfileVoters e6 profile6) (1 : Fin 3) (0 : Fin 3) =
        marginList (fun v => (ballots6 v).ranking) (1 : Fin 3) (0 : Fin 3) := by
    simpa [relabel_profile6_eq_profile6_list, profile6_list] using
      (margin_eq_marginList (ballots := ballots6) (a := (1 : Fin 3)) (b := (0 : Fin 3)))
  calc
    margin profile6 (1 : Fin 3) (0 : Fin 3)
        = margin (relabelProfileVoters e6 profile6) (1 : Fin 3) (0 : Fin 3) := by
            symm
            exact hrel
    _ = marginList (fun v => (ballots6 v).ranking) (1 : Fin 3) (0 : Fin 3) := hlist
    _ = (2 : Int) := marginList_profile6_1_0

/-! ## Coombs outcomes -/

def cand1_0 : {x : Fin 3 // x ≠ (0 : Fin 3)} := ⟨1, by decide⟩
def cand2_0 : {x : Fin 3 // x ≠ (0 : Fin 3)} := ⟨2, by decide⟩
def cand0_2 : {x : Fin 3 // x ≠ (2 : Fin 3)} := ⟨0, by decide⟩
def cand1_2 : {x : Fin 3 // x ≠ (2 : Fin 3)} := ⟨1, by decide⟩

lemma coombs_profile7_not_1 : (1 : Fin 3) ∉ coombs profile7 := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := profile7) (hcard := hcard)
  have haux' :
      scoringEliminationAux vetoScore (Fin 3) profile7 =
        ({0} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile7 c))) := by
    simpa [lowestScoring_profile7_eq_singleton_0] using haux
  have hcoombs :
      coombs profile7 = scoringEliminationAux vetoScore (Fin 3) profile7 := by
    classical
    simpa [coombs, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := vetoScore) (P := profile7)
        (inst1 := Classical.decEq (Fin 3)) (inst2 := inferInstance))
  intro hmem
  have hmem' :
      (1 : Fin 3) ∈
        ({0} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile7 c))) := by
    simpa [hcoombs, haux'] using hmem
  rcases Finset.mem_biUnion.mp hmem' with ⟨c, hcL, hmem_c⟩
  have hc0 : c = (0 : Fin 3) := by
    simpa using (Finset.mem_singleton.mp hcL)
  subst hc0
  have hmem_c' :
      (1 : Fin 3) ∈
        liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile7 (0 : Fin 3))) := by
    simpa using hmem_c
  have hmem_sub_aux :
      cand1_0 ∈ scoringEliminationAux vetoScore _ (restrictProfile profile7 (0 : Fin 3)) := by
    rcases (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux vetoScore _ (restrictProfile profile7 (0 : Fin 3)))
      (x := (1 : Fin 3))).1 hmem_c'
      with ⟨hx, hmem_sub⟩
    have hx' : (⟨1, hx⟩ : {x : Fin 3 // x ≠ (0 : Fin 3)}) = cand1_0 := by
      apply Subtype.ext
      rfl
    simpa [hx'] using hmem_sub
  have hcoombs_sub :
      coombs (restrictProfile profile7 (0 : Fin 3)) =
        scoringEliminationAux vetoScore _ (restrictProfile profile7 (0 : Fin 3)) := by
    classical
    simpa [coombs, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := vetoScore)
        (P := restrictProfile profile7 (0 : Fin 3))
        (inst1 := Classical.decEq _) (inst2 := inferInstance))
  have hmem_sub :
      cand1_0 ∈ coombs (restrictProfile profile7 (0 : Fin 3)) := by
    simpa [hcoombs_sub] using hmem_sub_aux
  have hcard' : Fintype.card {x : Fin 3 // x ≠ (0 : Fin 3)} = 2 := by
    simp [card_subtype_ne_eq (0 : Fin 3)]
  have hiff :
      cand1_0 ∈ coombs (restrictProfile profile7 (0 : Fin 3)) ↔
        0 ≤ margin (restrictProfile profile7 (0 : Fin 3)) cand1_0 cand2_0 := by
    simpa [cand1_0, cand2_0] using
      (coombs_of_card_two (P := restrictProfile profile7 (0 : Fin 3)) (hcard := hcard')
        (a := cand1_0) (b := cand2_0) (hab := by decide))
  have hmargin :
      margin (restrictProfile profile7 (0 : Fin 3)) cand1_0 cand2_0 =
        margin profile7 (1 : Fin 3) (2 : Fin 3) := by
    simpa [cand1_0, cand2_0] using
      (margin_eq_margin_restrictProfile (P := profile7) (c := (0 : Fin 3))
        (a := cand1_0) (b := cand2_0)).symm
  have hmargin_val :
      margin (restrictProfile profile7 (0 : Fin 3)) cand1_0 cand2_0 = (-1 : Int) := by
    simpa [hmargin] using margin_profile7_1_2
  have hnot_le : ¬ (0 ≤ margin (restrictProfile profile7 (0 : Fin 3)) cand1_0 cand2_0) := by
    simp [hmargin_val]
  have hle : 0 ≤ margin (restrictProfile profile7 (0 : Fin 3)) cand1_0 cand2_0 :=
    (hiff.mp hmem_sub)
  exact (hnot_le hle)

lemma coombs_profile6_has_1 : (1 : Fin 3) ∈ coombs profile6 := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := profile6) (hcard := hcard)
  have haux' :
      scoringEliminationAux vetoScore (Fin 3) profile6 =
        (Finset.univ : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile6 c))) := by
    simpa [lowestScoring_profile6_eq_univ] using haux
  have hcoombs :
      coombs profile6 = scoringEliminationAux vetoScore (Fin 3) profile6 := by
    classical
    simpa [coombs, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := vetoScore) (P := profile6)
        (inst1 := Classical.decEq (Fin 3)) (inst2 := inferInstance))
  have hcard' : Fintype.card {x : Fin 3 // x ≠ (2 : Fin 3)} = 2 := by
    simp [card_subtype_ne_eq (2 : Fin 3)]
  have hiff :
      cand1_2 ∈ coombs (restrictProfile profile6 (2 : Fin 3)) ↔
        0 ≤ margin (restrictProfile profile6 (2 : Fin 3)) cand1_2 cand0_2 := by
    simpa [cand1_2, cand0_2] using
      (coombs_of_card_two (P := restrictProfile profile6 (2 : Fin 3)) (hcard := hcard')
        (a := cand1_2) (b := cand0_2) (hab := by decide))
  have hmargin :
      margin (restrictProfile profile6 (2 : Fin 3)) cand1_2 cand0_2 =
        margin profile6 (1 : Fin 3) (0 : Fin 3) := by
    simpa [cand1_2, cand0_2] using
      (margin_eq_margin_restrictProfile (P := profile6) (c := (2 : Fin 3))
        (a := cand1_2) (b := cand0_2)).symm
  have hmargin_val :
      margin (restrictProfile profile6 (2 : Fin 3)) cand1_2 cand0_2 = (2 : Int) := by
    simpa [hmargin] using margin_profile6_1_0
  have hle : 0 ≤ margin (restrictProfile profile6 (2 : Fin 3)) cand1_2 cand0_2 := by
    simp [hmargin_val]
  have hmem_sub : cand1_2 ∈ coombs (restrictProfile profile6 (2 : Fin 3)) := by
    exact (hiff.mpr hle)
  have hmem_lift :
      (1 : Fin 3) ∈
        liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile6 (2 : Fin 3))) := by
    have hcoombs_sub :
        coombs (restrictProfile profile6 (2 : Fin 3)) =
          scoringEliminationAux vetoScore _ (restrictProfile profile6 (2 : Fin 3)) := by
      classical
      simpa [coombs, scoringEliminationRule] using
        (scoringEliminationAux_decidableEq_congr (score := vetoScore)
          (P := restrictProfile profile6 (2 : Fin 3))
          (inst1 := Classical.decEq _) (inst2 := inferInstance))
    have hmem_sub' :
        cand1_2 ∈ scoringEliminationAux vetoScore _ (restrictProfile profile6 (2 : Fin 3)) := by
      simpa [hcoombs_sub] using hmem_sub
    exact (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux vetoScore _ (restrictProfile profile6 (2 : Fin 3)))
      (x := (1 : Fin 3))).2 ⟨by decide, hmem_sub'⟩
  have hmem_union :
      (1 : Fin 3) ∈
        (Finset.univ : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile6 c))) := by
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨(2 : Fin 3), by simp, ?_⟩
    simpa [coombs, scoringEliminationRule] using hmem_lift
  simpa [hcoombs, haux'] using hmem_union

end CoombsPositiveInvolvementCounterexample

open CoombsPositiveInvolvementCounterexample

theorem coombs_not_positiveInvolvement : ¬ PositiveInvolvement coombs := by
  intro hpos
  have hmem : (1 : Fin 3) ∈ coombs profile6 := coombs_profile6_has_1
  have htop :
      BallotTop (profile7.pref (newVoter (u := (3 : Fin 7)) (V := voters6) voters6_not_mem))
        (1 : Fin 3) := newVoter_top_1
  have hmem' :
      (1 : Fin 3) ∈ coombs profile7 := by
    exact hpos (V := voters6) (u := (3 : Fin 7)) (hu := voters6_not_mem)
      (P := profile6) (Q := profile7) (c := (1 : Fin 3)) profiles_agree hmem htop
  exact coombs_profile7_not_1 hmem'

end SocialChoice
