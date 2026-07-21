import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Profile
import SocialChoice.ListBallot
import SocialChoice.ListBallotProfiles
import SocialChoice.Margin
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Coombs.Defs
import SocialChoice.Rules.ScoringElimination.Coombs.CondorcetLoser
import SocialChoice.Rules.ScoringRules.Veto.Common
import SocialChoice.Axioms.Independence
import SocialChoice.Axioms.Clones

namespace SocialChoice

open Finset
open Classical
attribute [instance] Classical.decEq Classical.decPred

variable {V A : Type} [Fintype V] [Fintype A]

private lemma scoreCandidate_veto_eq_zero_of_universal_bottom
    [DecidableEq A] (P : Profile V A) (d : A) (hbottom : ∀ v, BottomRank P v d) :
    scoreCandidate P (fun r => vetoScore (Fintype.card A) r) d = 0 := by
  classical
  have hscore :
      scoreCandidate P (fun r => vetoScore (Fintype.card A) r) d =
        ((Finset.univ.filter (fun v => ¬ BottomRank P v d)).card : Int) := by
    simpa [vetoScore] using
      (vetoScore_scoreCandidate_eq_notBottom_card (P := P) (c := d))
  have hfilter :
      (Finset.univ.filter (fun v => ¬ BottomRank P v d)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact (Finset.mem_filter.mp hv).2 (hbottom v)
  simp [hscore, hfilter]

private lemma scoreCandidate_veto_eq_card_of_not_bottom
    [DecidableEq A] (P : Profile V A) (a : A) (hnot : ∀ v, ¬ BottomRank P v a) :
    scoreCandidate P (fun r => vetoScore (Fintype.card A) r) a = (Fintype.card V : Int) := by
  classical
  have hscore :
      scoreCandidate P (fun r => vetoScore (Fintype.card A) r) a =
        ((Finset.univ.filter (fun v => ¬ BottomRank P v a)).card : Int) := by
    simpa [vetoScore] using
      (vetoScore_scoreCandidate_eq_notBottom_card (P := P) (c := a))
  have hfilter :
      (Finset.univ.filter (fun v => ¬ BottomRank P v a)) = (Finset.univ : Finset V) := by
    apply Finset.ext
    intro v
    simp [hnot v]
  simp [hscore, hfilter]

private lemma lowestScoring_eq_singleton_of_universal_bottom
    [DecidableEq A] [Nonempty V]
    (P : Profile V A) (c d : A) (hcd : c ≠ d) (hbottom : ∀ v, BottomRank P v d) :
    lowestScoring P (fun r => vetoScore (Fintype.card A) r) = {d} := by
  classical
  let scoreVec : Nat → Int := fun r => vetoScore (Fintype.card A) r
  have hA : (Finset.univ : Finset A).Nonempty := ⟨c, by simp⟩
  have hscore_d : scoreCandidate P scoreVec d = 0 := by
    simpa [scoreVec] using
      (scoreCandidate_veto_eq_zero_of_universal_bottom (P := P) (d := d) hbottom)
  have hscore_other : ∀ a : A, a ≠ d →
      scoreCandidate P scoreVec a = (Fintype.card V : Int) := by
    intro a had
    have hnot : ∀ v, ¬ BottomRank P v a := by
      intro v
      exact (bottomRank_imp_not_bottomRank (P := P) (hcd := had.symm) (v := v) (hbottom v))
    simpa [scoreVec] using
      (scoreCandidate_veto_eq_card_of_not_bottom (P := P) (a := a) hnot)
  have hpos : (0 : Int) < (Fintype.card V : Int) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty V))
  apply Finset.ext
  intro a
  constructor
  · intro ha
    have hle :=
      (lowestScoring_iff_forall_le (P := P) (score := scoreVec) (hA := hA) (c := a)).1 ha
    by_cases had : a = d
    · subst a
      simp
    · have hscore_a := hscore_other a had
      have hle' : (Fintype.card V : Int) ≤ 0 := by
        simpa [hscore_a, hscore_d] using (hle d)
      exact (False.elim ((not_lt_of_ge hle') (by simpa using hpos)))
  · intro ha
    have had : a = d := by
      simpa using (Finset.mem_singleton.mp ha)
    subst a
    apply (lowestScoring_iff_forall_le (P := P) (score := scoreVec) (hA := hA) (c := d)).2
    intro e
    by_cases hed : e = d
    · subst hed
      simp [hscore_d]
    · have hscore_e := hscore_other e hed
      simp [hscore_d, hscore_e]

theorem coombs_independenceOfUniversallyLeastPreferred :
    IndependenceOfUniversallyLeastPreferred coombs := by
  intro V A _ _ _ _ P c d hcd hbottom
  classical
  have hcard : ¬ Fintype.card A ≤ 1 := by
    intro hle
    have hsub : Subsingleton A :=
      (Fintype.card_le_one_iff_subsingleton).1 hle
    exact hcd (Subsingleton.elim _ _)
  let scoreVec : Nat → Int := fun r => vetoScore (Fintype.card A) r
  let L : Finset A := lowestScoring P scoreVec
  have hL : L = {d} := by
    simpa [L, scoreVec] using
      (lowestScoring_eq_singleton_of_universal_bottom (P := P) (c := c) (d := d) hcd hbottom)
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := P) (hcard := hcard)
  have haux' :
      scoringEliminationAux vetoScore A P =
        L.biUnion (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P c))) := by
    simpa [L, scoreVec] using haux
  have hcoombs_aux :
      scoringEliminationAux vetoScore A P =
        liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P d)) := by
    calc
      scoringEliminationAux vetoScore A P =
          L.biUnion
            (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P c))) := haux'
      _ = liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P d)) := by
        apply Finset.ext
        intro a
        constructor
        · intro ha
          rcases Finset.mem_biUnion.mp ha with ⟨c', hc', ha'⟩
          have hc'd : c' = d := by
            have hc'' : c' ∈ ({d} : Finset A) := by
              simpa [hL] using hc'
            simpa using (Finset.mem_singleton.mp hc'')
          subst hc'd
          simpa using ha'
        · intro ha
          apply Finset.mem_biUnion.mpr
          refine ⟨d, ?_, ?_⟩
          · simp [hL]
          · simpa using ha
  have hcoombs :
      coombs P = liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P d)) := by
    classical
    have hcongr :
        @scoringEliminationAux V _ vetoScore A _ (fun a b => Classical.propDecidable (a = b)) P =
          @scoringEliminationAux V _ vetoScore A _ (inferInstance : DecidableEq A) P := by
      simpa using
        (scoringEliminationAux_decidableEq_congr (score := vetoScore) (P := P)
          (inst1 := fun a b => Classical.propDecidable (a = b))
          (inst2 := (inferInstance : DecidableEq A)))
    calc
      coombs P =
          @scoringEliminationAux V _ vetoScore A _ (fun a b => Classical.propDecidable (a = b)) P := by
        simp [coombs, scoringEliminationRule]
      _ =
          @scoringEliminationAux V _ vetoScore A _ (inferInstance : DecidableEq A) P := by
        simpa using hcongr
      _ = liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P d)) := by
        simpa using hcoombs_aux
  classical
  let P' := restrictCandidates P (fun a => a ≠ d)
  have hcongr' :
      @scoringEliminationAux V _ vetoScore {x // x ≠ d} _ (fun x y =>
        Classical.propDecidable (x = y)) P' =
        @scoringEliminationAux V _ vetoScore {x // x ≠ d} _ (inferInstance :
          DecidableEq {x // x ≠ d}) P' := by
    simpa using
      (scoringEliminationAux_decidableEq_congr (score := vetoScore) (P := P')
        (inst1 := fun x y => Classical.propDecidable (x = y))
        (inst2 := (inferInstance : DecidableEq {x // x ≠ d})))
  calc
    liftWinners (coombs (restrictCandidates P (fun a => a ≠ d))) =
        liftWinners (@scoringEliminationAux V _ vetoScore {x // x ≠ d} _ (fun x y =>
          Classical.propDecidable (x = y)) P') := by
          simp [coombs, scoringEliminationRule, P']
    _ =
        liftWinners (@scoringEliminationAux V _ vetoScore {x // x ≠ d} _ (inferInstance :
          DecidableEq {x // x ≠ d}) P') := by
          simp [hcongr']
    _ =
        liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P d)) := by
          classical
          simp [liftWinners, liftFinset, restrictProfile, P']
          have hinst :
              (fun a b => Classical.propDecidable (a = b)) =
                (inferInstance : DecidableEq A) := by
            funext a b
            apply Subsingleton.elim
          cases hinst
          rfl
    _ = coombs P := by
          symm
          exact hcoombs

/-!
## Coombs fails independence of dominated alternatives and independence of clones

Counterexample with 4 candidates (0,1,2,3) and 4 voters:
v0: 2 > 3 > 0 > 1
v1: 2 > 3 > 1 > 0
v2: 3 > 1 > 0 > 2
v3: 3 > 1 > 0 > 2

Candidate 0 is Pareto-dominated by 3. Coombs selects {3}, but after removing 0
the winners are {2,3}. This also violates independence of clones for clone set {0,1}.
-/

namespace CoombsIndependenceCounterexample

def ballot2301 : ListBallot 4 := ListBallot.mk' [2, 3, 0, 1]
def ballot2310 : ListBallot 4 := ListBallot.mk' [2, 3, 1, 0]
def ballot3102 : ListBallot 4 := ListBallot.mk' [3, 1, 0, 2]

def ballots : Fin 4 → ListBallot 4
  | ⟨0, _⟩ => ballot2301
  | ⟨1, _⟩ => ballot2310
  | ⟨2, _⟩ => ballot3102
  | ⟨3, _⟩ => ballot3102

noncomputable def profile : Profile (Fin 4) (Fin 4) :=
  profileOfListBallots ballots

noncomputable def profile0 : Profile (Fin 4) {x : Fin 4 // x ≠ (0 : Fin 4)} :=
  restrictProfile profile (0 : Fin 4)

def cand1_0 : {x : Fin 4 // x ≠ (0 : Fin 4)} := ⟨1, by decide⟩
def cand2_0 : {x : Fin 4 // x ≠ (0 : Fin 4)} := ⟨2, by decide⟩
def cand3_0 : {x : Fin 4 // x ≠ (0 : Fin 4)} := ⟨3, by decide⟩

@[reducible] def scoreVec : Nat → Int := fun r => vetoScore (Fintype.card (Fin 4)) r

lemma prefers_3_0 : ∀ v : Fin 4, Prefers profile v (3 : Fin 4) (0 : Fin 4) := by
  intro v
  fin_cases v
  · simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
  · simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
  · simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
  · simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide

lemma votersBottom_profile_0_card : (votersBottom profile (0 : Fin 4)).card = 1 := by
  have h : countBottom (fun v => (ballots v).ranking) (0 : Fin 4) = 1 := by decide
  simpa [profile] using
    (votersBottom_card_eq_countBottom (ballots := ballots) (c := (0 : Fin 4))).trans h

lemma votersBottom_profile_1_card : (votersBottom profile (1 : Fin 4)).card = 1 := by
  have h : countBottom (fun v => (ballots v).ranking) (1 : Fin 4) = 1 := by decide
  simpa [profile] using
    (votersBottom_card_eq_countBottom (ballots := ballots) (c := (1 : Fin 4))).trans h

lemma votersBottom_profile_2_card : (votersBottom profile (2 : Fin 4)).card = 2 := by
  have h : countBottom (fun v => (ballots v).ranking) (2 : Fin 4) = 2 := by decide
  simpa [profile] using
    (votersBottom_card_eq_countBottom (ballots := ballots) (c := (2 : Fin 4))).trans h

lemma votersBottom_profile_3_card : (votersBottom profile (3 : Fin 4)).card = 0 := by
  have h : countBottom (fun v => (ballots v).ranking) (3 : Fin 4) = 0 := by decide
  simpa [profile] using
    (votersBottom_card_eq_countBottom (ballots := ballots) (c := (3 : Fin 4))).trans h

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
  have hcardV : (Finset.univ : Finset V).card = Fintype.card V := by
    simp
  have hsum' :
      k + (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card = Fintype.card V := by
    simpa [hbottom, hcardV] using hsum
  calc
    (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card =
        k + (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card - k := by
          symm
          simp
    _ = Fintype.card V - k := by
          simp [hsum']

lemma scoreCandidate_profile_0 :
    scoreCandidate profile scoreVec (0 : Fin 4) = (3 : Int) := by
  have hnotBottom :
      (Finset.univ.filter (fun v => ¬ BottomRank profile v (0 : Fin 4))).card = 3 := by
    simpa using
      (notBottom_card (P := profile) (c := (0 : Fin 4)) (k := 1) votersBottom_profile_0_card)
  calc
    scoreCandidate profile scoreVec (0 : Fin 4) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profile v (0 : Fin 4))).card : Int) := by
          exact
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profile) (c := (0 : Fin 4)))
    _ = (3 : Int) := by exact_mod_cast hnotBottom

lemma scoreCandidate_profile_1 :
    scoreCandidate profile scoreVec (1 : Fin 4) = (3 : Int) := by
  have hnotBottom :
      (Finset.univ.filter (fun v => ¬ BottomRank profile v (1 : Fin 4))).card = 3 := by
    simpa using
      (notBottom_card (P := profile) (c := (1 : Fin 4)) (k := 1) votersBottom_profile_1_card)
  calc
    scoreCandidate profile scoreVec (1 : Fin 4) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profile v (1 : Fin 4))).card : Int) := by
          exact
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profile) (c := (1 : Fin 4)))
    _ = (3 : Int) := by exact_mod_cast hnotBottom

lemma scoreCandidate_profile_2 :
    scoreCandidate profile scoreVec (2 : Fin 4) = (2 : Int) := by
  have hnotBottom :
      (Finset.univ.filter (fun v => ¬ BottomRank profile v (2 : Fin 4))).card = 2 := by
    simpa using
      (notBottom_card (P := profile) (c := (2 : Fin 4)) (k := 2) votersBottom_profile_2_card)
  calc
    scoreCandidate profile scoreVec (2 : Fin 4) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profile v (2 : Fin 4))).card : Int) := by
          exact
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profile) (c := (2 : Fin 4)))
    _ = (2 : Int) := by exact_mod_cast hnotBottom

lemma scoreCandidate_profile_3 :
    scoreCandidate profile scoreVec (3 : Fin 4) = (4 : Int) := by
  have hnotBottom :
      (Finset.univ.filter (fun v => ¬ BottomRank profile v (3 : Fin 4))).card = 4 := by
    simpa using
      (notBottom_card (P := profile) (c := (3 : Fin 4)) (k := 0) votersBottom_profile_3_card)
  calc
    scoreCandidate profile scoreVec (3 : Fin 4) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profile v (3 : Fin 4))).card : Int) := by
          exact
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profile) (c := (3 : Fin 4)))
    _ = (4 : Int) := by exact_mod_cast hnotBottom

lemma score2_lt_score0 :
    scoreCandidate profile scoreVec (2 : Fin 4) <
      scoreCandidate profile scoreVec (0 : Fin 4) := by
  simp [scoreCandidate_profile_2, scoreCandidate_profile_0]

lemma score2_lt_score1 :
    scoreCandidate profile scoreVec (2 : Fin 4) <
      scoreCandidate profile scoreVec (1 : Fin 4) := by
  simp [scoreCandidate_profile_2, scoreCandidate_profile_1]

lemma score2_lt_score3 :
    scoreCandidate profile scoreVec (2 : Fin 4) <
      scoreCandidate profile scoreVec (3 : Fin 4) := by
  simp [scoreCandidate_profile_2, scoreCandidate_profile_3]

lemma lowestScoring_profile_eq_singleton_2 :
    lowestScoring profile scoreVec = ({2} : Finset (Fin 4)) := by
  classical
  have hLne :
      (lowestScoring profile scoreVec).Nonempty := by
    exact lowestScoring_nonempty (P := profile) (score := scoreVec)
      (hA := (Finset.univ_nonempty : (Finset.univ : Finset (Fin 4)).Nonempty))
  have hsubset : lowestScoring profile scoreVec ⊆ ({2} : Finset (Fin 4)) := by
    intro x hx
    fin_cases x
    ·
      have hle :=
        scoreCandidate_le_of_mem_lowestScoring (P := profile) (score := scoreVec)
          (c := (0 : Fin 4)) (e := (2 : Fin 4)) hx
      have hcontra : False := (not_lt_of_ge hle) score2_lt_score0
      exact (False.elim hcontra)
    ·
      have hle :=
        scoreCandidate_le_of_mem_lowestScoring (P := profile) (score := scoreVec)
          (c := (1 : Fin 4)) (e := (2 : Fin 4)) hx
      have hcontra : False := (not_lt_of_ge hle) score2_lt_score1
      exact (False.elim hcontra)
    · simp
    ·
      have hle :=
        scoreCandidate_le_of_mem_lowestScoring (P := profile) (score := scoreVec)
          (c := (3 : Fin 4)) (e := (2 : Fin 4)) hx
      have hcontra : False := (not_lt_of_ge hle) score2_lt_score3
      exact (False.elim hcontra)
  rcases hLne with ⟨x, hx⟩
  have hx' : x = (2 : Fin 4) := by
    have : x ∈ ({2} : Finset (Fin 4)) := hsubset hx
    simpa using this
  have h2mem : (2 : Fin 4) ∈ lowestScoring profile scoreVec := by
    simpa [hx'] using hx
  apply Finset.ext
  intro x
  constructor
  · intro hxmem
    exact hsubset hxmem
  · intro hxmem
    have hx' : x = (2 : Fin 4) := by simpa using hxmem
    simpa [hx'] using h2mem

lemma coombs_profile_not_2 : (2 : Fin 4) ∉ coombs profile := by
  classical
  have hcard : ¬ Fintype.card (Fin 4) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := profile) (hcard := hcard)
  have haux' :
      scoringEliminationAux vetoScore (Fin 4) profile =
        (lowestScoring profile scoreVec).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile c))) := by
    exact haux
  have haux'' :
      scoringEliminationAux vetoScore (Fin 4) profile =
        ({2} : Finset (Fin 4)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile c))) := by
    simpa [lowestScoring_profile_eq_singleton_2] using haux'
  have hcoombs :
      coombs profile = scoringEliminationAux vetoScore (Fin 4) profile := by
    classical
    simpa [coombs, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := vetoScore) (P := profile)
        (inst1 := Classical.decEq (Fin 4)) (inst2 := inferInstance))
  intro hmem
  have hmem' :
      (2 : Fin 4) ∈
        ({2} : Finset (Fin 4)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile c))) := by
    simpa [hcoombs, haux''] using hmem
  rcases Finset.mem_biUnion.mp hmem' with ⟨c, hcL, hmem_c⟩
  have hc2 : c = (2 : Fin 4) := by
    simpa using (Finset.mem_singleton.mp hcL)
  subst hc2
  have hnot :
      (2 : Fin 4) ∉
        liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile (2 : Fin 4))) := by
    exact not_mem_liftFinset_removed
      (s := scoringEliminationAux vetoScore _ (restrictProfile profile (2 : Fin 4)))
  exact hnot hmem_c

@[reducible] noncomputable def scoreVec0 : Nat → Int := fun r =>
  vetoScore (Fintype.card {x : Fin 4 // x ≠ (0 : Fin 4)}) r

lemma scoreCandidate_profile0_1 :
    scoreCandidate profile0 scoreVec0 cand1_0 = (2 : Int) := by
  decide

lemma scoreCandidate_profile0_2 :
    scoreCandidate profile0 scoreVec0 cand2_0 = (2 : Int) := by
  decide

lemma scoreCandidate_profile0_3 :
    scoreCandidate profile0 scoreVec0 cand3_0 = (4 : Int) := by
  decide

lemma lowestScoring_profile0_has_1 :
    cand1_0 ∈ lowestScoring profile0 scoreVec0 := by
  have hA : (Finset.univ : Finset {x : Fin 4 // x ≠ (0 : Fin 4)}).Nonempty := by
    exact ⟨cand1_0, by simp⟩
  apply (lowestScoring_iff_forall_le (P := profile0) (score := scoreVec0) hA cand1_0).2
  intro d
  cases d with
  | mk val h =>
      fin_cases val
      · cases h rfl
      ·
        have hd : (⟨1, h⟩ : {x : Fin 4 // x ≠ (0 : Fin 4)}) = cand1_0 := by
          apply Subtype.ext
          rfl
        simp [hd, scoreCandidate_profile0_1]
      ·
        have hd : (⟨2, h⟩ : {x : Fin 4 // x ≠ (0 : Fin 4)}) = cand2_0 := by
          apply Subtype.ext
          rfl
        simp [hd, scoreCandidate_profile0_1, scoreCandidate_profile0_2]
      ·
        have hd : (⟨3, h⟩ : {x : Fin 4 // x ≠ (0 : Fin 4)}) = cand3_0 := by
          apply Subtype.ext
          rfl
        simp [hd, scoreCandidate_profile0_1, scoreCandidate_profile0_3]

def cand2_0_1 : {x : {x : Fin 4 // x ≠ (0 : Fin 4)} // x ≠ cand1_0} :=
  ⟨cand2_0, by decide⟩

def cand3_0_1 : {x : {x : Fin 4 // x ≠ (0 : Fin 4)} // x ≠ cand1_0} :=
  ⟨cand3_0, by decide⟩

lemma marginList_profile_2_3 :
    marginList (fun v => (ballots v).ranking) (2 : Fin 4) (3 : Fin 4) = (0 : Int) := by
  decide

lemma margin_profile_2_3 :
    margin profile (2 : Fin 4) (3 : Fin 4) = (0 : Int) := by
  have h :=
    margin_eq_marginList (ballots := ballots) (a := (2 : Fin 4)) (b := (3 : Fin 4))
  simpa [profile] using h.trans marginList_profile_2_3

lemma coombs_profile0_has_2 : cand2_0 ∈ coombs profile0 := by
  classical
  have hcard : ¬ Fintype.card {x : Fin 4 // x ≠ (0 : Fin 4)} ≤ 1 := by
    have hcard' : Fintype.card {x : Fin 4 // x ≠ (0 : Fin 4)} = 3 := by
      simp [card_subtype_ne_eq (0 : Fin 4)]
    omega
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := profile0) (hcard := hcard)
  have haux' :
      scoringEliminationAux vetoScore {x : Fin 4 // x ≠ (0 : Fin 4)} profile0 =
        (lowestScoring profile0 scoreVec0).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile0 c))) := by
    exact haux
  have hcoombs :
      coombs profile0 = scoringEliminationAux vetoScore {x : Fin 4 // x ≠ (0 : Fin 4)} profile0 := by
    classical
    simpa [coombs, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := vetoScore) (P := profile0)
        (inst1 := Classical.decEq _) (inst2 := inferInstance))
  have hcard' :
      Fintype.card {x : {x : Fin 4 // x ≠ (0 : Fin 4)} // x ≠ cand1_0} = 2 := by
    simp [card_subtype_ne_eq cand1_0]
  have hiff :
      cand2_0_1 ∈ coombs (restrictProfile profile0 cand1_0) ↔
        0 ≤ margin (restrictProfile profile0 cand1_0) cand2_0_1 cand3_0_1 := by
    simpa [cand2_0_1, cand3_0_1] using
      (coombs_of_card_two (P := restrictProfile profile0 cand1_0) (hcard := hcard')
        (a := cand2_0_1) (b := cand3_0_1) (hab := by decide))
  have hmargin1 :
      margin (restrictProfile profile0 cand1_0) cand2_0_1 cand3_0_1 =
        margin profile0 cand2_0 cand3_0 := by
    simpa [cand2_0_1, cand3_0_1] using
      (margin_eq_margin_restrictProfile (P := profile0) (c := cand1_0)
        (a := cand2_0_1) (b := cand3_0_1)).symm
  have hmargin2 :
      margin profile0 cand2_0 cand3_0 = margin profile (2 : Fin 4) (3 : Fin 4) := by
    simpa [profile0, cand2_0, cand3_0] using
      (margin_eq_margin_restrictProfile (P := profile) (c := (0 : Fin 4))
        (a := cand2_0) (b := cand3_0)).symm
  have hmargin_val :
      margin (restrictProfile profile0 cand1_0) cand2_0_1 cand3_0_1 = (0 : Int) := by
    simpa [hmargin1, hmargin2] using margin_profile_2_3
  have hle : 0 ≤ margin (restrictProfile profile0 cand1_0) cand2_0_1 cand3_0_1 := by
    simp [hmargin_val]
  have hmem_sub : cand2_0_1 ∈ coombs (restrictProfile profile0 cand1_0) := hiff.mpr hle
  have hcoombs_sub :
      coombs (restrictProfile profile0 cand1_0) =
        scoringEliminationAux vetoScore _ (restrictProfile profile0 cand1_0) := by
    classical
    simpa [coombs, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := vetoScore)
        (P := restrictProfile profile0 cand1_0)
        (inst1 := Classical.decEq _) (inst2 := inferInstance))
  have hmem_sub' :
      cand2_0_1 ∈ scoringEliminationAux vetoScore _ (restrictProfile profile0 cand1_0) := by
    simpa [hcoombs_sub] using hmem_sub
  have hmem_lift :
      cand2_0 ∈
        liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile0 cand1_0)) := by
    exact (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux vetoScore _ (restrictProfile profile0 cand1_0))
      (x := cand2_0)).2 ⟨by decide, hmem_sub'⟩
  have hmem_union :
      cand2_0 ∈
        (lowestScoring profile0 scoreVec0).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile0 c))) := by
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨cand1_0, lowestScoring_profile0_has_1, ?_⟩
    simpa using hmem_lift
  have hmem_aux :
      cand2_0 ∈ scoringEliminationAux vetoScore {x : Fin 4 // x ≠ (0 : Fin 4)} profile0 := by
    simpa [haux'] using hmem_union
  simpa [hcoombs] using hmem_aux

lemma mem_liftWinners_iff {A : Type} [DecidableEq A] {p : A → Prop} [DecidablePred p]
    {s : Finset {a : A // p a}} {x : A} (hx : p x) :
    x ∈ liftWinners s ↔ (⟨x, hx⟩ : {a : A // p a}) ∈ s := by
  classical
  simp [liftWinners, Finset.mem_image, hx]

lemma coombs_profile0_lift_has_2 :
    (2 : Fin 4) ∈ liftWinners (coombs profile0) := by
  have hmem : cand2_0 ∈ coombs profile0 := coombs_profile0_has_2
  have hmem' :
      (2 : Fin 4) ∈ liftWinners (coombs profile0) := by
    simpa [cand2_0] using
      (mem_liftWinners_iff (p := fun x : Fin 4 => x ≠ (0 : Fin 4))
        (s := coombs profile0) (x := (2 : Fin 4)) (by decide)).2 hmem
  exact hmem'

def cloneSet : Set (Fin 4) := {0, 1}

lemma cloneSet_profile : CloneSet profile cloneSet := by
  refine ⟨?_, ?_⟩
  · exact ⟨0, by simp [cloneSet]⟩
  · intro v c hc
    fin_cases c
    · exact (hc (by simp [cloneSet])).elim
    · exact (hc (by simp [cloneSet])).elim
    · -- c = 2
      fin_cases v
      ·
        refine Or.inr ?_
        intro x hx
        have hx' : x = (0 : Fin 4) ∨ x = (1 : Fin 4) := by
          simpa [cloneSet] using hx
        cases hx' with
        | inl hx0 =>
            subst hx0
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
        | inr hx1 =>
            subst hx1
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
      ·
        refine Or.inr ?_
        intro x hx
        have hx' : x = (0 : Fin 4) ∨ x = (1 : Fin 4) := by
          simpa [cloneSet] using hx
        cases hx' with
        | inl hx0 =>
            subst hx0
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
        | inr hx1 =>
            subst hx1
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
      ·
        refine Or.inl ?_
        intro x hx
        have hx' : x = (0 : Fin 4) ∨ x = (1 : Fin 4) := by
          simpa [cloneSet] using hx
        cases hx' with
        | inl hx0 =>
            subst hx0
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
        | inr hx1 =>
            subst hx1
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
      ·
        refine Or.inl ?_
        intro x hx
        have hx' : x = (0 : Fin 4) ∨ x = (1 : Fin 4) := by
          simpa [cloneSet] using hx
        cases hx' with
        | inl hx0 =>
            subst hx0
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
        | inr hx1 =>
            subst hx1
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
    · -- c = 3
      fin_cases v
      ·
        refine Or.inr ?_
        intro x hx
        have hx' : x = (0 : Fin 4) ∨ x = (1 : Fin 4) := by
          simpa [cloneSet] using hx
        cases hx' with
        | inl hx0 =>
            subst hx0
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
        | inr hx1 =>
            subst hx1
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
      ·
        refine Or.inr ?_
        intro x hx
        have hx' : x = (0 : Fin 4) ∨ x = (1 : Fin 4) := by
          simpa [cloneSet] using hx
        cases hx' with
        | inl hx0 =>
            subst hx0
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
        | inr hx1 =>
            subst hx1
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
      ·
        refine Or.inr ?_
        intro x hx
        have hx' : x = (0 : Fin 4) ∨ x = (1 : Fin 4) := by
          simpa [cloneSet] using hx
        cases hx' with
        | inl hx0 =>
            subst hx0
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
        | inr hx1 =>
            subst hx1
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
      ·
        refine Or.inr ?_
        intro x hx
        have hx' : x = (0 : Fin 4) ∨ x = (1 : Fin 4) := by
          simpa [cloneSet] using hx
        cases hx' with
        | inl hx0 =>
            subst hx0
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
        | inr hx1 =>
            subst hx1
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide

lemma clonePred_eq_ne :
    clonePred cloneSet (1 : Fin 4) = (fun a : Fin 4 => a ≠ (0 : Fin 4)) := by
  funext a
  apply propext
  fin_cases a <;> simp [cloneSet, clonePred]

def cand2clone : {a : Fin 4 // clonePred cloneSet (1 : Fin 4) a} :=
  ⟨2, by simp [cloneSet, clonePred]⟩

lemma cast_subtype_val {A : Type} {p q : A → Prop}
    (h : p = q) (x : {a : A // p a}) :
    (cast (congrArg (fun r => {a : A // r a}) h) x : {a : A // q a}).1 = x.1 := by
  cases x
  cases h
  rfl

lemma mem_castCandidates_iff {V A : Type} [Fintype V] [Fintype A]
    (f : VotingRule) {p q : A → Prop}
    (dp : DecidablePred p) (dq : DecidablePred q)
    (h : p = q) (x : {a : A // p a}) (P : Profile V {a : A // p a}) :
    x ∈ f P ↔
      ((cast (congrArg (fun r => {a : A // r a}) h) x : {a : A // q a}) ∈
        f (castCandidates (p := p) (q := q) h P)) := by
  classical
  letI : DecidablePred p := dp
  letI : DecidablePred q := dq
  cases h
  cases (Subsingleton.elim dq dp)
  rfl

lemma coombs_cloneProfile_has_2_raw :
    cand2clone ∈ coombs (removeClonesExcept profile cloneSet (1 : Fin 4)) := by
  classical
  let q : Fin 4 → Prop := fun a => a ≠ (0 : Fin 4)
  have hmem : cand2_0 ∈ coombs (restrictCandidates profile q) := by
    simpa [profile0, restrictProfile, q] using coombs_profile0_has_2
  have hpred : q = clonePred cloneSet (1 : Fin 4) := by
    simpa [q] using clonePred_eq_ne.symm
  have hmem_cast :
      (cast (congrArg (fun r => {a : Fin 4 // r a}) hpred) cand2_0 :
        {a : Fin 4 // clonePred cloneSet (1 : Fin 4) a}) ∈
        coombs (castCandidates (p := q) (q := clonePred cloneSet (1 : Fin 4)) hpred
          (restrictCandidates profile q)) := by
    exact (mem_castCandidates_iff (f := coombs)
      (dp := inferInstance) (dq := inferInstance) (h := hpred)
      (x := cand2_0) (P := restrictCandidates profile q)).1 hmem
  have hmem_cast' :
      (cast (congrArg (fun r => {a : Fin 4 // r a}) hpred) cand2_0 :
        {a : Fin 4 // clonePred cloneSet (1 : Fin 4) a}) ∈
        coombs (restrictCandidates profile (clonePred cloneSet (1 : Fin 4))) := by
    simpa [castCandidates_restrictCandidates] using hmem_cast
  have hcast_cand2 :
      (cast (congrArg (fun r => {a : Fin 4 // r a}) hpred) cand2_0 :
        {a : Fin 4 // clonePred cloneSet (1 : Fin 4) a}) = cand2clone := by
    apply Subtype.ext
    simpa [cand2clone, cand2_0] using (cast_subtype_val (h := hpred) (x := cand2_0))
  have hmem_final :
      cand2clone ∈ coombs (restrictCandidates profile (clonePred cloneSet (1 : Fin 4))) := by
    simpa [hcast_cand2] using hmem_cast'
  simpa [removeClonesExcept] using hmem_final

lemma coombs_cloneProfile_has_2 :
    (⟨2, Or.inl (by simp [cloneSet])⟩ :
        {a : Fin 4 // clonePred cloneSet (1 : Fin 4) a}) ∈
      coombs (removeClonesExcept profile cloneSet (1 : Fin 4)) := by
  simpa [cand2clone] using coombs_cloneProfile_has_2_raw

end CoombsIndependenceCounterexample

open CoombsIndependenceCounterexample

theorem coombs_not_independenceOfDominated : ¬ IndependenceOfDominated coombs := by
  intro hind
  have hpref : ∀ v : Fin 4, Prefers profile v (3 : Fin 4) (0 : Fin 4) := prefers_3_0
  have hEq := hind (P := profile) (c := (3 : Fin 4)) (d := (0 : Fin 4)) hpref
  have hmem_restrict :
      (2 : Fin 4) ∈ liftWinners (coombs (restrictCandidates profile (fun a => a ≠ (0 : Fin 4)))) := by
    simpa [profile0, restrictProfile] using coombs_profile0_lift_has_2
  have hmem_full : (2 : Fin 4) ∈ coombs profile := by
    simpa [hEq] using hmem_restrict
  exact coombs_profile_not_2 hmem_full

theorem coombs_not_independenceOfClones : ¬ IndependenceOfClones coombs := by
  intro hind
  have hclone : CloneSet profile cloneSet := cloneSet_profile
  have hx : (1 : Fin 4) ∈ cloneSet := by
    simp [cloneSet]
  have h :=
    hind (P := profile) (X := cloneSet) (x := (1 : Fin 4)) hclone hx
  have hc : (2 : Fin 4) ∉ cloneSet := by
    simp [cloneSet]
  have hnonclone := h.1 (2 : Fin 4) hc
  have hb_left :
      (⟨2, Or.inl hc⟩ :
        {a : Fin 4 // clonePred cloneSet (1 : Fin 4) a}) ∈
        coombs (removeClonesExcept profile cloneSet (1 : Fin 4)) := by
    have hsub : (⟨2, Or.inl hc⟩ :
        {a : Fin 4 // clonePred cloneSet (1 : Fin 4) a}) =
        (⟨2, Or.inl (by simp [cloneSet])⟩ :
          {a : Fin 4 // clonePred cloneSet (1 : Fin 4) a}) := by
      apply Subtype.ext
      rfl
    simpa [hsub] using coombs_cloneProfile_has_2
  have hb_right : (2 : Fin 4) ∈ coombs profile :=
    (hnonclone).2 hb_left
  exact (coombs_profile_not_2 hb_right).elim

end SocialChoice
