import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Condorcet
import SocialChoice.ListBallot
import SocialChoice.Profile
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.Defs
import SocialChoice.Rules.ScoringRules.Plurality.Defs

namespace SocialChoice

open Finset

open Classical
attribute [instance] Classical.decEq Classical.decPred

/-!
# IRV fails Condorcet consistency

We use a 5-voter profile with three candidates, where candidate 1 is the
Condorcet winner, but IRV returns candidate 0.
-/

namespace InstantRunoffCondorcetCounterexample

def ballot012 : ListBallot 3 := ListBallot.mk' [0, 1, 2]
def ballot210 : ListBallot 3 := ListBallot.mk' [2, 1, 0]
def ballot102 : ListBallot 3 := ListBallot.mk' [1, 0, 2]

def ballots : Fin 5 → ListBallot 3
  | ⟨0, _⟩ => ballot012
  | ⟨1, _⟩ => ballot012
  | ⟨2, _⟩ => ballot210
  | ⟨3, _⟩ => ballot210
  | ⟨4, _⟩ => ballot102

noncomputable def profile : Profile (Fin 5) (Fin 3) :=
  profileOfListBallots ballots

lemma votersTop_0 :
    votersTop profile 0 = ({0, 1} : Finset (Fin 5)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersTop, topRank_iff_isTopOfList, isTopOfList] <;>
    decide

lemma votersTop_1 :
    votersTop profile 1 = ({4} : Finset (Fin 5)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersTop, topRank_iff_isTopOfList, isTopOfList] <;>
    decide

lemma votersTop_2 :
    votersTop profile 2 = ({2, 3} : Finset (Fin 5)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersTop, topRank_iff_isTopOfList, isTopOfList] <;>
    decide

lemma votersTop_0_card : (votersTop profile 0).card = 2 := by
  simp [votersTop_0]

lemma votersTop_1_card : (votersTop profile 1).card = 1 := by
  simp [votersTop_1]

lemma votersTop_2_card : (votersTop profile 2).card = 2 := by
  simp [votersTop_2]

local notation "scoreVec" => fun r => pluralityScore 3 r

lemma scoreCandidate_0 :
    scoreCandidate profile scoreVec 0 = ((votersTop profile 0).card : Int) := by
  simpa [pluralityScore] using (pluralityScore_eq_votersTop_card (P := profile) (c := (0 : Fin 3)))

lemma scoreCandidate_1 :
    scoreCandidate profile scoreVec 1 = ((votersTop profile 1).card : Int) := by
  simpa [pluralityScore] using (pluralityScore_eq_votersTop_card (P := profile) (c := (1 : Fin 3)))

lemma scoreCandidate_2 :
    scoreCandidate profile scoreVec 2 = ((votersTop profile 2).card : Int) := by
  simpa [pluralityScore] using (pluralityScore_eq_votersTop_card (P := profile) (c := (2 : Fin 3)))

lemma score1_lt_score0 : scoreCandidate profile scoreVec 1 < scoreCandidate profile scoreVec 0 := by
  simp [scoreCandidate_1, scoreCandidate_0, votersTop_1_card, votersTop_0_card]

lemma score1_lt_score2 : scoreCandidate profile scoreVec 1 < scoreCandidate profile scoreVec 2 := by
  simp [scoreCandidate_1, scoreCandidate_2, votersTop_1_card, votersTop_2_card]

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
      exact (False.elim ((not_lt_of_ge hle) score1_lt_score0))
    · simp
    · have hle :=
        scoreCandidate_le_of_mem_lowestScoring (P := profile) (score := scoreVec)
          (c := (2 : Fin 3)) (e := (1 : Fin 3)) hx
      exact (False.elim ((not_lt_of_ge hle) score1_lt_score2))
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

noncomputable def profile' : Profile (Fin 5) {x : Fin 3 // x ≠ (1 : Fin 3)} :=
  restrictProfile profile (1 : Fin 3)

def cand0 : {x : Fin 3 // x ≠ (1 : Fin 3)} := ⟨0, by decide⟩
def cand2 : {x : Fin 3 // x ≠ (1 : Fin 3)} := ⟨2, by decide⟩

lemma votersPreferring_0_2 :
    votersPreferring profile 0 2 = ({0, 1, 4} : Finset (Fin 5)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersPreferring, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_2_0 :
    votersPreferring profile 2 0 = ({2, 3} : Finset (Fin 5)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersPreferring, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_restrict_cand0 :
    votersPreferring profile' cand0 cand2 = votersPreferring profile 0 2 := by
  classical
  ext v
  simp [profile', votersPreferring, prefers_restrictProfile_iff, cand0, cand2]

lemma votersPreferring_restrict_cand2 :
    votersPreferring profile' cand2 cand0 = votersPreferring profile 2 0 := by
  classical
  ext v
  simp [profile', votersPreferring, prefers_restrictProfile_iff, cand0, cand2]

lemma scoreCandidate_restrict_cand0 :
    scoreCandidate profile' (fun r => pluralityScore 2 r) cand0 = 3 := by
  have hcard : Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} = 2 := by
    simp [card_subtype_ne_eq (1 : Fin 3)]
  have hcard' : (votersPreferring profile' cand0 cand2).card = 3 := by
    simp [votersPreferring_restrict_cand0, votersPreferring_0_2]
  calc
    scoreCandidate profile' (fun r => pluralityScore 2 r) cand0 =
        (votersPreferring profile' cand0 cand2).card := by
          simpa [hcard] using
            (pluralityScore_eq_votersPreferring_of_two (P := profile') hcard cand0 cand2 (by decide))
    _ = (3 : Int) := by
          exact_mod_cast hcard'

lemma scoreCandidate_restrict_cand2 :
    scoreCandidate profile' (fun r => pluralityScore 2 r) cand2 = 2 := by
  have hcard : Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} = 2 := by
    simp [card_subtype_ne_eq (1 : Fin 3)]
  have hcard' : (votersPreferring profile' cand2 cand0).card = 2 := by
    simp [votersPreferring_restrict_cand2, votersPreferring_2_0]
  calc
    scoreCandidate profile' (fun r => pluralityScore 2 r) cand2 =
        (votersPreferring profile' cand2 cand0).card := by
          simpa [hcard] using
            (pluralityScore_eq_votersPreferring_of_two (P := profile') hcard cand2 cand0 (by decide))
    _ = (2 : Int) := by
          exact_mod_cast hcard'

lemma score_restrict_cand2_lt_cand0 :
    scoreCandidate profile' (fun r => pluralityScore 2 r) cand2 <
      scoreCandidate profile' (fun r => pluralityScore 2 r) cand0 := by
  simp [scoreCandidate_restrict_cand2, scoreCandidate_restrict_cand0]

lemma lowestScoring_restrict_eq_singleton_cand2 :
    lowestScoring profile' (fun r => pluralityScore 2 r) =
      ({cand2} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
  classical
  have : Nonempty {x : Fin 3 // x ≠ (1 : Fin 3)} := by
    exact ⟨cand0⟩
  have hLne :
      (lowestScoring profile' (fun r => pluralityScore 2 r)).Nonempty := by
    exact lowestScoring_nonempty (P := profile') (score := fun r => pluralityScore 2 r)
      (hA := (Finset.univ_nonempty :
        (Finset.univ : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}).Nonempty))
  have hsubset :
      lowestScoring profile' (fun r => pluralityScore 2 r) ⊆
        ({cand2} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
    intro x hx
    have hle :=
      scoreCandidate_le_of_mem_lowestScoring (P := profile') (score := fun r => pluralityScore 2 r)
        (c := x) (e := cand2) hx
    rcases two_elems_eq_or_eq
        (A := {x : Fin 3 // x ≠ (1 : Fin 3)})
        (by simp [card_subtype_ne_eq (1 : Fin 3)]) cand0 cand2 (by decide) x with
      rfl | rfl
    · exact (False.elim ((not_lt_of_ge hle) score_restrict_cand2_lt_cand0))
    · simp
  rcases hLne with ⟨x, hx⟩
  have hx' : x = cand2 := by
    simpa using (hsubset hx)
  have hmem : cand2 ∈ lowestScoring profile' (fun r => pluralityScore 2 r) := by
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
    scoringEliminationAux pluralityScore {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand2}
      (restrictProfile profile' cand2) =
      (Finset.univ : Finset {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand2}) := by
  classical
  have hcard : Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} = 2 := by
    simp [card_subtype_ne_eq (1 : Fin 3)]
  have hcard' :
      Fintype.card {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand2} =
        Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} - 1 :=
    card_subtype_ne_eq cand2
  have hle :
      Fintype.card {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand2} ≤ 1 := by
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

theorem instantRunoffVoting_profile_winner :
    instantRunoffVoting profile = ({0} : Finset (Fin 3)) := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := pluralityScore) (P := profile) (hcard := hcard)
  have haux' :
      scoringEliminationAux pluralityScore (Fin 3) profile =
        ({1} : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile profile c))) := by
    simpa [lowestScoring_eq_singleton_one] using haux
  have haux'' :
      scoringEliminationAux pluralityScore (Fin 3) profile =
        liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile profile (1 : Fin 3))) := by
    simpa using haux'
  have hcard' : ¬ Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} ≤ 1 := by
    have hcard'' : Fintype.card {x : Fin 3 // x ≠ (1 : Fin 3)} = 2 := by
      simp [card_subtype_ne_eq (1 : Fin 3)]
    omega
  have haux_restrict :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := pluralityScore) (P := profile') (hcard := hcard')
  have haux_restrict' :
      scoringEliminationAux pluralityScore {x : Fin 3 // x ≠ (1 : Fin 3)} profile' =
        ({cand2} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}).biUnion
          (fun c => liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile profile' c))) := by
    simpa [lowestScoring_restrict_eq_singleton_cand2] using haux_restrict
  have haux_restrict'' :
      scoringEliminationAux pluralityScore {x : Fin 3 // x ≠ (1 : Fin 3)} profile' =
        liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile profile' cand2)) := by
    simpa using haux_restrict'
  have hrec :
      scoringEliminationAux pluralityScore {x : Fin 3 // x ≠ (1 : Fin 3)} profile' =
        ({cand0} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
    calc
      scoringEliminationAux pluralityScore {x : Fin 3 // x ≠ (1 : Fin 3)} profile'
          = liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile profile' cand2)) := haux_restrict''
      _ = liftFinset
          (Finset.univ : Finset {x : {x : Fin 3 // x ≠ (1 : Fin 3)} // x ≠ cand2}) := by
            simp [scoringEliminationAux_restrict_singleton]
      _ = ({cand0} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := liftFinset_univ_restrict
  have hrec' :
      scoringEliminationAux pluralityScore {x : Fin 3 // x ≠ (1 : Fin 3)}
        (restrictProfile profile (1 : Fin 3)) =
        ({cand0} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
    simpa [profile'] using hrec
  have hIRV :
      instantRunoffVoting profile = scoringEliminationAux pluralityScore (Fin 3) profile := by
    classical
    simpa [instantRunoffVoting, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := pluralityScore) (P := profile)
        (inst1 := Classical.decEq (Fin 3)) (inst2 := inferInstance))
  calc
    instantRunoffVoting profile
        = scoringEliminationAux pluralityScore (Fin 3) profile := hIRV
    _ = liftFinset
          (scoringEliminationAux pluralityScore {x : Fin 3 // x ≠ (1 : Fin 3)}
            (restrictProfile profile (1 : Fin 3))) := by
            simpa [instantRunoffVoting, scoringEliminationRule] using haux''
    _ = liftFinset ({cand0} : Finset {x : Fin 3 // x ≠ (1 : Fin 3)}) := by
            simp [hrec']
    _ = ({0} : Finset (Fin 3)) := by
            simp [liftFinset, cand0]

theorem instantRunoffVoting_not_condorcet : ¬ CondorcetConsistency instantRunoffVoting := by
  intro hcond
  have hcw : CondorcetWinner profile (1 : Fin 3) := condorcetWinner_one
  have hsingle := hcond (P := profile) (c := (1 : Fin 3)) hcw
  have hne : (0 : Fin 3) ∈ instantRunoffVoting profile := by
    simp [instantRunoffVoting_profile_winner]
  have hcontra : False := by
    have hmem : (0 : Fin 3) ∈ ({1} : Finset (Fin 3)) := by
      simp [hsingle] at hne
    simp at hmem
  exact hcontra

end InstantRunoffCondorcetCounterexample

end SocialChoice
