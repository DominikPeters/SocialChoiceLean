import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Condorcet
import SocialChoice.ListBallot
import SocialChoice.Profile
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Coombs.Defs
import SocialChoice.Rules.ScoringRules.Veto.Common

namespace SocialChoice

open Finset

open Classical
attribute [instance] Classical.decEq Classical.decPred

/-!
# Coombs fails Condorcet consistency

We use a 13-voter profile with three candidates, where candidate 1 is the
Condorcet winner, but Coombs returns candidate 0.

Example taken from
Minimal Voting Paradoxes
Felix Brandt, Marie Matthäus, Christian Saile
-/

namespace CoombsCondorcetCounterexample

def ballot021 : ListBallot 3 := ListBallot.mk' [0, 2, 1]
def ballot120 : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballot102 : ListBallot 3 := ListBallot.mk' [1, 0, 2]
def ballot210 : ListBallot 3 := ListBallot.mk' [2, 1, 0]
def ballot012 : ListBallot 3 := ListBallot.mk' [0, 1, 2]

def ballots : Fin 13 → ListBallot 3
  | ⟨0, _⟩ => ballot021
  | ⟨1, _⟩ => ballot021
  | ⟨2, _⟩ => ballot021
  | ⟨3, _⟩ => ballot021
  | ⟨4, _⟩ => ballot021
  | ⟨5, _⟩ => ballot120
  | ⟨6, _⟩ => ballot120
  | ⟨7, _⟩ => ballot120
  | ⟨8, _⟩ => ballot102
  | ⟨9, _⟩ => ballot102
  | ⟨10, _⟩ => ballot102
  | ⟨11, _⟩ => ballot210
  | ⟨12, _⟩ => ballot012

noncomputable def profile : Profile (Fin 13) (Fin 3) :=
  profileOfListBallots ballots

lemma bottomRank_iff_prefersInList {m n : ℕ} (bs : Fin m → ListBallot n)
    (v : Fin m) (c : Fin n) :
    BottomRank (profileOfListBallots bs) v c ↔
      ∀ d : Fin n, d ≠ c → prefersInList (bs v).ranking d c = true := by
  constructor
  · intro h d hd
    exact (prefers_iff_prefersInList bs v d c).1 (h d hd)
  · intro h d hd
    exact (prefers_iff_prefersInList bs v d c).2 (h d hd)

lemma votersBottom_0 :
    votersBottom profile 0 = ({5, 6, 7, 11} : Finset (Fin 13)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersBottom, bottomRank_iff_prefersInList, prefersInList] <;>
    decide

lemma votersBottom_1 :
    votersBottom profile 1 = ({0, 1, 2, 3, 4} : Finset (Fin 13)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersBottom, bottomRank_iff_prefersInList, prefersInList] <;>
    decide

lemma votersBottom_2 :
    votersBottom profile 2 = ({8, 9, 10, 12} : Finset (Fin 13)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersBottom, bottomRank_iff_prefersInList, prefersInList] <;>
    decide

lemma votersBottom_0_card : (votersBottom profile 0).card = 4 := by
  simp [votersBottom_0]

lemma votersBottom_1_card : (votersBottom profile 1).card = 5 := by
  simp [votersBottom_1]

lemma votersBottom_2_card : (votersBottom profile 2).card = 4 := by
  simp [votersBottom_2]

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

lemma scoreCandidate_0 : scoreCandidate profile scoreVec 0 = (9 : Int) := by
  have hcard :
      (Finset.univ.filter (fun v => ¬ BottomRank profile v 0)).card = 9 := by
    have h := notBottom_card (P := profile) (c := (0 : Fin 3)) (k := 4) votersBottom_0_card
    simpa using h
  simpa [vetoScore, hcard] using
    (vetoScore_scoreCandidate_eq_notBottom_card (P := profile) (c := (0 : Fin 3)))

lemma scoreCandidate_1 : scoreCandidate profile scoreVec 1 = (8 : Int) := by
  have hcard :
      (Finset.univ.filter (fun v => ¬ BottomRank profile v 1)).card = 8 := by
    have h := notBottom_card (P := profile) (c := (1 : Fin 3)) (k := 5) votersBottom_1_card
    simpa using h
  simpa [vetoScore, hcard] using
    (vetoScore_scoreCandidate_eq_notBottom_card (P := profile) (c := (1 : Fin 3)))

lemma scoreCandidate_2 : scoreCandidate profile scoreVec 2 = (9 : Int) := by
  have hcard :
      (Finset.univ.filter (fun v => ¬ BottomRank profile v 2)).card = 9 := by
    have h := notBottom_card (P := profile) (c := (2 : Fin 3)) (k := 4) votersBottom_2_card
    simpa using h
  simpa [vetoScore, hcard] using
    (vetoScore_scoreCandidate_eq_notBottom_card (P := profile) (c := (2 : Fin 3)))

lemma score1_lt_score0 : scoreCandidate profile scoreVec 1 < scoreCandidate profile scoreVec 0 := by
  simp [scoreCandidate_1, scoreCandidate_0]

lemma score1_lt_score2 : scoreCandidate profile scoreVec 1 < scoreCandidate profile scoreVec 2 := by
  simp [scoreCandidate_1, scoreCandidate_2]

lemma lowestScoring_eq_singleton_one :
    lowestScoring profile scoreVec = ({1} : Finset (Fin 3)) := by
  classical
  have hLne :
      (lowestScoring profile scoreVec).Nonempty := by
    exact lowestScoring_nonempty (P := profile) (score := scoreVec)
      (hA := (Finset.univ_nonempty : (Finset.univ : Finset (Fin 3)).Nonempty))
  have hsubset : lowestScoring profile scoreVec ⊆ ({1} : Finset (Fin 3)) := by
    intro x hx
    fin_cases x
    · have hle :=
        scoreCandidate_le_of_mem_lowestScoring (P := profile) (score := scoreVec)
          (c := (0 : Fin 3)) (e := (1 : Fin 3)) hx
      have hcontra : False := (not_lt_of_ge hle) score1_lt_score0
      exact (False.elim hcontra)
    · simp
    · have hle :=
        scoreCandidate_le_of_mem_lowestScoring (P := profile) (score := scoreVec)
          (c := (2 : Fin 3)) (e := (1 : Fin 3)) hx
      have hcontra : False := (not_lt_of_ge hle) score1_lt_score2
      exact (False.elim hcontra)
  rcases hLne with ⟨x, hx⟩
  have hx' : x = (1 : Fin 3) := by
    simpa using (hsubset hx)
  have h1mem : (1 : Fin 3) ∈ lowestScoring profile scoreVec := by
    simpa [hx'] using hx
  apply Finset.ext
  intro x
  constructor
  · intro hxmem
    exact hsubset hxmem
  · intro hxmem
    have hx' : x = (1 : Fin 3) := by simpa using hxmem
    simpa [hx'] using h1mem

lemma marginList_1_0 :
    marginList (fun v => (ballots v).ranking) 1 0 = 1 := by
  decide

lemma marginList_1_2 :
    marginList (fun v => (ballots v).ranking) 1 2 = 1 := by
  decide

theorem condorcetWinner_one : CondorcetWinner profile (1 : Fin 3) := by
  rw [profile, CondorcetWinner_iff_marginList]
  intro d hne
  fin_cases d
  · have h : marginList (fun v => (ballots v).ranking) 1 0 = 1 := marginList_1_0
    simp [h]
  · cases hne rfl
  · have h : marginList (fun v => (ballots v).ranking) 1 2 = 1 := marginList_1_2
    simp [h]

noncomputable def profile' : Profile (Fin 13) {x : Fin 3 // x ≠ (1 : Fin 3)} :=
  restrictProfile profile (1 : Fin 3)

def cand0 : {x : Fin 3 // x ≠ (1 : Fin 3)} := ⟨0, by decide⟩
def cand2 : {x : Fin 3 // x ≠ (1 : Fin 3)} := ⟨2, by decide⟩

lemma bottomRank_restrict_cand2 (v : Fin 13) :
    BottomRank profile' v cand2 ↔ Prefers profile v (0 : Fin 3) (2 : Fin 3) := by
  constructor
  · intro h
    have h' : Prefers profile' v cand0 cand2 := h cand0 (by decide)
    change Prefers profile v (0 : Fin 3) (2 : Fin 3) at h'
    exact h'
  · intro h d hd
    have hcard : Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} = 2 := by
      simp [card_subtype_ne_eq (1 : Fin 3)]
    have hne : cand0 ≠ cand2 := by decide
    rcases two_elems_eq_or_eq (A := {x : Fin 3 // x ≠ (1 : Fin 3)}) hcard cand0 cand2 hne d with
      rfl | rfl
    · change Prefers profile' v cand0 cand2
      exact h
    · exact (hd rfl).elim

lemma bottomRank_restrict_cand0 (v : Fin 13) :
    BottomRank profile' v cand0 ↔ Prefers profile v (2 : Fin 3) (0 : Fin 3) := by
  constructor
  · intro h
    have h' : Prefers profile' v cand2 cand0 := h cand2 (by decide)
    change Prefers profile v (2 : Fin 3) (0 : Fin 3) at h'
    exact h'
  · intro h d hd
    have hcard : Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} = 2 := by
      simp [card_subtype_ne_eq (1 : Fin 3)]
    have hne : cand0 ≠ cand2 := by decide
    rcases two_elems_eq_or_eq (A := {x : Fin 3 // x ≠ (1 : Fin 3)}) hcard cand0 cand2 hne d with
      rfl | rfl
    · exact (hd rfl).elim
    · change Prefers profile' v cand2 cand0
      exact h

lemma votersPreferring_0_2 :
    votersPreferring profile 0 2 =
      ({0, 1, 2, 3, 4, 8, 9, 10, 12} : Finset (Fin 13)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersPreferring, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_2_0 :
    votersPreferring profile 2 0 = ({5, 6, 7, 11} : Finset (Fin 13)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersPreferring, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersBottom_restrict_cand2 :
    votersBottom profile' cand2 = votersPreferring profile 0 2 := by
  classical
  ext v
  simp [votersBottom, votersPreferring, bottomRank_restrict_cand2]

lemma votersBottom_restrict_cand0 :
    votersBottom profile' cand0 = votersPreferring profile 2 0 := by
  classical
  ext v
  simp [votersBottom, votersPreferring, bottomRank_restrict_cand0]

lemma votersBottom_restrict_cand2_card :
    (votersBottom profile' cand2).card = 9 := by
  simp [votersBottom_restrict_cand2, votersPreferring_0_2]

lemma votersBottom_restrict_cand0_card :
    (votersBottom profile' cand0).card = 4 := by
  simp [votersBottom_restrict_cand0, votersPreferring_2_0]

local notation "scoreVec2" => fun r => vetoScore 2 r

lemma scoreCandidate_restrict_cand2 :
    scoreCandidate profile' scoreVec2 cand2 = (4 : Int) := by
  have hcard :
      (Finset.univ.filter (fun v => ¬ BottomRank profile' v cand2)).card = 4 := by
    have h :=
      notBottom_card (P := profile') (c := cand2) (k := 9) votersBottom_restrict_cand2_card
    simpa using h
  simpa [vetoScore, hcard] using
    (vetoScore_scoreCandidate_eq_notBottom_card (P := profile') (c := cand2))

lemma scoreCandidate_restrict_cand0 :
    scoreCandidate profile' scoreVec2 cand0 = (9 : Int) := by
  have hcard :
      (Finset.univ.filter (fun v => ¬ BottomRank profile' v cand0)).card = 9 := by
    have h :=
      notBottom_card (P := profile') (c := cand0) (k := 4) votersBottom_restrict_cand0_card
    simpa using h
  simpa [vetoScore, hcard] using
    (vetoScore_scoreCandidate_eq_notBottom_card (P := profile') (c := cand0))

lemma score_restrict_cand2_lt_cand0 :
    scoreCandidate profile' scoreVec2 cand2 < scoreCandidate profile' scoreVec2 cand0 := by
  simp [scoreCandidate_restrict_cand2, scoreCandidate_restrict_cand0]

lemma lowestScoring_restrict_eq_singleton_cand2 :
    lowestScoring profile' scoreVec2 = ({cand2} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
  classical
  haveI : Nonempty {x : Fin 3 // x ≠ (1 : Fin 3)} := by
    classical
    exact ⟨cand0⟩
  have hLne :
      (lowestScoring profile' scoreVec2).Nonempty := by
    exact lowestScoring_nonempty (P := profile') (score := scoreVec2)
      (hA := (Finset.univ_nonempty : (Finset.univ : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}).Nonempty))
  have hsubset : lowestScoring profile' scoreVec2 ⊆ ({cand2} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
    intro x hx
    have hle :=
      scoreCandidate_le_of_mem_lowestScoring (P := profile') (score := scoreVec2)
        (c := x) (e := cand2) hx
    rcases two_elems_eq_or_eq
        (A := {x : Fin 3 // x ≠ (1 : Fin 3)})
        (by simp [card_subtype_ne_eq (1 : Fin 3)]) cand0 cand2 (by decide) x with
      rfl | rfl
    · have hcontra : False := (not_lt_of_ge hle) score_restrict_cand2_lt_cand0
      exact (False.elim hcontra)
    · simp
  rcases hLne with ⟨x, hx⟩
  have hx' : x = cand2 := by
    simpa using (hsubset hx)
  have hmem : cand2 ∈ lowestScoring profile' scoreVec2 := by
    simpa [hx'] using hx
  apply Finset.ext
  intro x
  constructor
  · intro hxmem
    exact hsubset hxmem
  · intro hxmem
    have hx' : x = cand2 := by simpa using hxmem
    simpa [hx'] using hmem

lemma scoringEliminationAux_restrict_singleton :
    scoringEliminationAux vetoScore {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand2}
      (restrictProfile profile' cand2) =
      (Finset.univ : Finset {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand2}) := by
  classical
  have hle : Fintype.card {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand2} ≤ 1 := by
    have hcard : Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} = 2 := by
      simp [card_subtype_ne_eq (1 : Fin 3)]
    have hcard' :
        Fintype.card {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand2} =
          Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} - 1 :=
      card_subtype_ne_eq cand2
    have hcard'' :
        Fintype.card {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand2} = 1 := by
      calc
        Fintype.card {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand2} =
            Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} - 1 := hcard'
        _ = 1 := by simp [hcard]
    exact le_of_eq hcard''
  simp [scoringEliminationAux]

lemma liftFinset_univ_restrict :
    liftFinset
      (Finset.univ : Finset {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand2}) =
        ({cand0} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro hx
    rcases (mem_liftFinset_iff_subtype (s := (Finset.univ :
      Finset {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand2})) (x := x)).1 hx with
      ⟨hxne, _⟩
    have hcard : Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} = 2 := by
      simp [card_subtype_ne_eq (1 : Fin 3)]
    have hne : cand0 ≠ cand2 := by decide
    rcases two_elems_eq_or_eq (A := {x : Fin 3 // x ≠ (1 : Fin 3)}) hcard cand0 cand2 hne x with
      rfl | rfl
    · simp
    · exact (hxne rfl).elim
  · intro hx
    have hx' : x = cand0 := by simpa using hx
    subst x
    refine (mem_liftFinset_iff_subtype
      (s := (Finset.univ :
        Finset {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand2}))
      (x := cand0)).2 ?_
    exact ⟨by decide, by simp⟩

theorem coombs_profile_winner : coombs profile = ({0} : Finset (Fin 3)) := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := profile) (hcard := hcard)
  have haux' :
      scoringEliminationAux vetoScore (Fin 3) profile =
        ({1} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile c))) := by
    simpa [lowestScoring_eq_singleton_one] using haux
  have haux'' :
      scoringEliminationAux vetoScore (Fin 3) profile =
        liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile (1 : Fin 3))) := by
    simpa using haux'
  have hcard' : ¬ Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} ≤ 1 := by
    have hcard'' : Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} = 2 := by
      simp [card_subtype_ne_eq (1 : Fin 3)]
    omega
  have haux_restrict :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := profile') (hcard := hcard')
  have haux_restrict' :
      scoringEliminationAux vetoScore {x : Fin 3 // x ≠ (1 : Fin 3)} profile' =
        ({cand2} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile' c))) := by
    simpa [lowestScoring_restrict_eq_singleton_cand2] using haux_restrict
  have haux_restrict'' :
      scoringEliminationAux vetoScore {x : Fin 3 // x ≠ (1 : Fin 3)} profile' =
        liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile' cand2)) := by
    simpa using haux_restrict'
  have hrec :
      scoringEliminationAux vetoScore {x : Fin 3 // x ≠ (1 : Fin 3)} profile' =
        ({cand0} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
    calc
      scoringEliminationAux vetoScore {x : Fin 3 // x ≠ (1 : Fin 3)} profile'
          = liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile' cand2)) := haux_restrict''
      _ = liftFinset
          (Finset.univ : Finset {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand2}) := by
            simp [scoringEliminationAux_restrict_singleton]
      _ = ({cand0} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := liftFinset_univ_restrict
  have hrec' :
      scoringEliminationAux vetoScore {x : Fin 3 // x ≠ (1 : Fin 3)}
        (restrictProfile profile (1 : Fin 3)) =
        ({cand0} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
    simpa [profile'] using hrec
  have hcoombs :
      coombs profile = scoringEliminationAux vetoScore (Fin 3) profile := by
    classical
    simpa [coombs, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := vetoScore) (P := profile)
        (inst1 := Classical.decEq (Fin 3)) (inst2 := inferInstance))
  calc
    coombs profile
        = scoringEliminationAux vetoScore (Fin 3) profile := hcoombs
    _ = liftFinset
          (scoringEliminationAux vetoScore {x : Fin 3 // x ≠ (1 : Fin 3)}
            (restrictProfile profile (1 : Fin 3))) := by
            simpa [coombs, scoringEliminationRule] using haux''
    _ = liftFinset ({cand0} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
            simp [hrec']
    _ = ({0} : Finset (Fin 3)) := by
            simp [liftFinset, cand0]

theorem coombs_not_condorcet : ¬ CondorcetConsistency coombs := by
  intro hcond
  have hcw : CondorcetWinner profile (1 : Fin 3) := condorcetWinner_one
  have hsingle := hcond (P := profile) (c := (1 : Fin 3)) hcw
  have hne : (0 : Fin 3) ∈ coombs profile := by
    simp [coombs_profile_winner]
  have hcontra : False := by
    have hmem : (0 : Fin 3) ∈ ({1} : Finset (Fin 3)) := by
      have hne' := hne
      simp [hsingle] at hne'
    simp at hmem
  exact hcontra

end CoombsCondorcetCounterexample

end SocialChoice
