import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Majority
import SocialChoice.ListBallot
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Coombs.CondorcetLoser
import SocialChoice.Rules.ScoringElimination.Coombs.Defs
import SocialChoice.Rules.ScoringRules.Veto.Common

namespace SocialChoice

open Finset
open Classical
attribute [instance] Classical.decEq Classical.decPred

theorem coombs_majority_loser_criterion : MajorityLoserCriterion coombs := by
  intro V A _ _ P c hmaj hne
  classical
  rcases hne with ⟨d0, hd0c⟩
  haveI : Nonempty A := ⟨d0⟩
  let m := Fintype.card A
  let scoreVec : Nat → Int := fun r => vetoScore m r
  let L : Finset A := lowestScoring P scoreVec
  have hcard : ¬ Fintype.card A ≤ 1 := by
    intro hle
    have hsub : ∀ a b : A, a = b := (Fintype.card_le_one_iff.mp hle)
    exact hd0c (hsub d0 c)
  have hnotbottom_c_eq :
      (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card =
        Fintype.card V - (votersBottom P c).card := by
    have hsum :
        (Finset.univ.filter (fun v => BottomRank P v c)).card +
          (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card =
          (Finset.univ : Finset V).card := by
      simpa using
        (Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset V)) (p := fun v => BottomRank P v c))
    have hsum' :
        (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card =
          (Finset.univ : Finset V).card -
            (Finset.univ.filter (fun v => BottomRank P v c)).card := by
      apply Nat.eq_sub_of_add_eq
      simpa [add_comm] using hsum
    simpa [votersBottom] using hsum'
  have hmaj' : 2 * (votersBottom P c).card > Fintype.card V := by
    simpa [StrictMajority] using hmaj
  have hlt_nat :
      (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card <
        (votersBottom P c).card := by
    have hlt_nat' : Fintype.card V - (votersBottom P c).card < (votersBottom P c).card := by
      omega
    simpa [hnotbottom_c_eq] using hlt_nat'
  have hscore_lt : ∀ d : A, d ≠ c →
      scoreCandidate P scoreVec c < scoreCandidate P scoreVec d := by
    intro d hdc
    have hnotbottom_d_ge :
        (votersBottom P c).card ≤
          (Finset.univ.filter (fun v => ¬ BottomRank P v d)).card := by
      have hsubset : ∀ v, BottomRank P v c → ¬ BottomRank P v d := by
        intro v hbc
        exact bottomRank_imp_not_bottomRank (P := P) (c := c) (d := d) hdc.symm v hbc
      have hcard :=
        cardinality_lemma (p := fun v => BottomRank P v c)
          (q := fun v => ¬ BottomRank P v d) hsubset
      simpa [votersBottom] using hcard
    have hscore_c :
        scoreCandidate P scoreVec c =
          ((Finset.univ.filter (fun v => ¬ BottomRank P v c)).card : Int) := by
      simpa [scoreVec, vetoScore] using
        (vetoScore_scoreCandidate_eq_notBottom_card (P := P) (c := c))
    have hscore_d :
        scoreCandidate P scoreVec d =
          ((Finset.univ.filter (fun v => ¬ BottomRank P v d)).card : Int) := by
      simpa [scoreVec, vetoScore] using
        (vetoScore_scoreCandidate_eq_notBottom_card (P := P) (c := d))
    have hlt_int :
        ((Finset.univ.filter (fun v => ¬ BottomRank P v c)).card : Int) <
          ((Finset.univ.filter (fun v => ¬ BottomRank P v d)).card : Int) := by
      have hlt_int' :
          ((Finset.univ.filter (fun v => ¬ BottomRank P v c)).card : Int) <
            ((votersBottom P c).card : Int) := by
        exact_mod_cast hlt_nat
      have hle_int :
          ((votersBottom P c).card : Int) ≤
            ((Finset.univ.filter (fun v => ¬ BottomRank P v d)).card : Int) := by
        exact_mod_cast hnotbottom_d_ge
      exact lt_of_lt_of_le hlt_int' hle_int
    simpa [hscore_c, hscore_d] using hlt_int
  have hL_subset : L ⊆ ({c} : Finset A) := by
    intro d hd
    by_cases hdc : d = c
    · simp [hdc]
    · have hle :=
        scoreCandidate_le_of_mem_lowestScoring (P := P) (score := scoreVec) (c := d) (e := c) hd
      have hlt := hscore_lt d hdc
      exact (False.elim ((not_lt_of_ge hle) hlt))
  have hLne : L.Nonempty := by
    apply lowestScoring_nonempty
    exact (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty)
  have hc_low : c ∈ L := by
    rcases hLne with ⟨d, hd⟩
    have hd' : d = c := by
      have : d ∈ ({c} : Finset A) := hL_subset hd
      simpa using this
    simpa [hd'] using hd
  have hL_eq : L = {c} := by
    apply Finset.ext
    intro d
    constructor
    · intro hd
      have : d ∈ ({c} : Finset A) := hL_subset hd
      simpa using this
    · intro hd
      have hd' : d = c := by simpa using hd
      simpa [hd'] using hc_low
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := P) (hcard := hcard)
  have haux' :
      scoringEliminationAux vetoScore A P =
        L.biUnion (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P c))) := by
    simpa [m, scoreVec, L] using haux
  have haux'' :
      scoringEliminationAux vetoScore A P =
        liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P c)) := by
    simpa [hL_eq, L] using haux'
  have hnot :
      c ∉ scoringEliminationAux vetoScore A P := by
    have hnot' :
        c ∉ liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P c)) :=
      not_mem_liftFinset_removed (s := scoringEliminationAux vetoScore _ (restrictProfile P c))
    simpa [haux''] using hnot'
  simpa [coombs, scoringEliminationRule] using hnot

/-!
# Coombs fails the majority criterion

We use a 3-voter, 3-candidate profile where candidate 2 is ranked first by
two voters, but Coombs (PUT) returns {1,2}.
-/

namespace CoombsMajorityCounterexample

def ballot102 : ListBallot 3 := ListBallot.mk' [1, 0, 2]
def ballot201 : ListBallot 3 := ListBallot.mk' [2, 0, 1]
def ballot210 : ListBallot 3 := ListBallot.mk' [2, 1, 0]

def ballots : Fin 3 → ListBallot 3
  | 0 => ballot102
  | 1 => ballot201
  | 2 => ballot210

noncomputable def profile : Profile (Fin 3) (Fin 3) :=
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
    votersBottom profile 0 = ({2} : Finset (Fin 3)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersBottom, bottomRank_iff_prefersInList, prefersInList] <;>
    decide

lemma votersBottom_1 :
    votersBottom profile 1 = ({1} : Finset (Fin 3)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersBottom, bottomRank_iff_prefersInList, prefersInList] <;>
    decide

lemma votersBottom_2 :
    votersBottom profile 2 = ({0} : Finset (Fin 3)) := by
  classical
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersBottom, bottomRank_iff_prefersInList, prefersInList] <;>
    decide

lemma votersBottom_0_card : (votersBottom profile 0).card = 1 := by
  simp [votersBottom_0]

lemma votersBottom_1_card : (votersBottom profile 1).card = 1 := by
  simp [votersBottom_1]

lemma votersBottom_2_card : (votersBottom profile 2).card = 1 := by
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

lemma scoreCandidate_0 : scoreCandidate profile scoreVec (0 : Fin 3) = (2 : Int) := by
  have hcard :
      (Finset.univ.filter (fun v => ¬ BottomRank profile v 0)).card = 2 := by
    have h := notBottom_card (P := profile) (c := (0 : Fin 3)) (k := 1) votersBottom_0_card
    simpa using h
  calc
    scoreCandidate profile scoreVec (0 : Fin 3) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profile v 0)).card : Int) := by
          simpa [vetoScore] using
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profile) (c := (0 : Fin 3)))
    _ = (2 : Int) := by
          exact_mod_cast hcard

lemma scoreCandidate_1 : scoreCandidate profile scoreVec (1 : Fin 3) = (2 : Int) := by
  have hcard :
      (Finset.univ.filter (fun v => ¬ BottomRank profile v 1)).card = 2 := by
    have h := notBottom_card (P := profile) (c := (1 : Fin 3)) (k := 1) votersBottom_1_card
    simpa using h
  calc
    scoreCandidate profile scoreVec (1 : Fin 3) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profile v 1)).card : Int) := by
          simpa [vetoScore] using
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profile) (c := (1 : Fin 3)))
    _ = (2 : Int) := by
          exact_mod_cast hcard

lemma scoreCandidate_2 : scoreCandidate profile scoreVec (2 : Fin 3) = (2 : Int) := by
  have hcard :
      (Finset.univ.filter (fun v => ¬ BottomRank profile v 2)).card = 2 := by
    have h := notBottom_card (P := profile) (c := (2 : Fin 3)) (k := 1) votersBottom_2_card
    simpa using h
  calc
    scoreCandidate profile scoreVec (2 : Fin 3) =
        ((Finset.univ.filter (fun v => ¬ BottomRank profile v 2)).card : Int) := by
          simpa [vetoScore] using
            (vetoScore_scoreCandidate_eq_notBottom_card (P := profile) (c := (2 : Fin 3)))
    _ = (2 : Int) := by
          exact_mod_cast hcard

lemma lowestScoring_profile_eq_univ :
    lowestScoring profile scoreVec = (Finset.univ : Finset (Fin 3)) := by
  classical
  apply Finset.ext
  intro x
  constructor
  · intro _hx
    exact Finset.mem_univ x
  · intro _hx
    have hA : (Finset.univ : Finset (Fin 3)).Nonempty := Finset.univ_nonempty
    apply (lowestScoring_iff_forall_le (P := profile) (score := scoreVec) hA x).2
    intro d
    fin_cases x <;> fin_cases d <;>
      simp [scoreCandidate_0, scoreCandidate_1, scoreCandidate_2]

/-! ## Pairwise margins -/

lemma marginList_profile_1_0 :
    marginList (fun v => (ballots v).ranking) (1 : Fin 3) (0 : Fin 3) = (1 : Int) := by
  decide

lemma margin_profile_1_0 :
    margin profile (1 : Fin 3) (0 : Fin 3) = (1 : Int) := by
  have hlist :=
    (margin_eq_marginList (ballots := ballots) (a := (1 : Fin 3)) (b := (0 : Fin 3)))
  calc
    margin profile (1 : Fin 3) (0 : Fin 3)
        = marginList (fun v => (ballots v).ranking) (1 : Fin 3) (0 : Fin 3) := by
            simpa [profile] using hlist
    _ = (1 : Int) := marginList_profile_1_0

/-! ## Coombs outcomes -/

def cand0_2 : {x : Fin 3 // x ≠ (2 : Fin 3)} := ⟨0, by decide⟩
def cand1_2 : {x : Fin 3 // x ≠ (2 : Fin 3)} := ⟨1, by decide⟩

lemma coombs_profile_has_1 : (1 : Fin 3) ∈ coombs profile := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) ≤ 1 := by decide
  have haux :=
    scoringEliminationAux_eq_biUnion_of_not_card_le_one
      (score := vetoScore) (P := profile) (hcard := hcard)
  have haux' :
      scoringEliminationAux vetoScore (Fin 3) profile =
        (Finset.univ : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile c))) := by
    simpa [lowestScoring_profile_eq_univ] using haux
  have hcoombs :
      coombs profile = scoringEliminationAux vetoScore (Fin 3) profile := by
    classical
    simpa [coombs, scoringEliminationRule] using
      (scoringEliminationAux_decidableEq_congr (score := vetoScore) (P := profile)
        (inst1 := Classical.decEq (Fin 3)) (inst2 := inferInstance))
  have hcard' : Fintype.card {x : Fin 3 // x ≠ (2 : Fin 3)} = 2 := by
    simp [card_subtype_ne_eq (2 : Fin 3)]
  have hiff :
      cand1_2 ∈ coombs (restrictProfile profile (2 : Fin 3)) ↔
        0 ≤ margin (restrictProfile profile (2 : Fin 3)) cand1_2 cand0_2 := by
    simpa [cand1_2, cand0_2] using
      (coombs_of_card_two (P := restrictProfile profile (2 : Fin 3)) (hcard := hcard')
        (a := cand1_2) (b := cand0_2) (hab := by decide))
  have hmargin :
      margin (restrictProfile profile (2 : Fin 3)) cand1_2 cand0_2 =
        margin profile (1 : Fin 3) (0 : Fin 3) := by
    simpa [cand1_2, cand0_2] using
      (margin_eq_margin_restrictProfile (P := profile) (c := (2 : Fin 3))
        (a := cand1_2) (b := cand0_2)).symm
  have hmargin_val :
      margin (restrictProfile profile (2 : Fin 3)) cand1_2 cand0_2 = (1 : Int) := by
    simpa [hmargin] using margin_profile_1_0
  have hle : 0 ≤ margin (restrictProfile profile (2 : Fin 3)) cand1_2 cand0_2 := by
    simp [hmargin_val]
  have hmem_sub : cand1_2 ∈ coombs (restrictProfile profile (2 : Fin 3)) := by
    exact (hiff.mpr hle)
  have hmem_lift :
      (1 : Fin 3) ∈
        liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile (2 : Fin 3))) := by
    have hcoombs_sub :
        coombs (restrictProfile profile (2 : Fin 3)) =
          scoringEliminationAux vetoScore _ (restrictProfile profile (2 : Fin 3)) := by
      classical
      simpa [coombs, scoringEliminationRule] using
        (scoringEliminationAux_decidableEq_congr (score := vetoScore)
          (P := restrictProfile profile (2 : Fin 3))
          (inst1 := Classical.decEq _) (inst2 := inferInstance))
    have hmem_sub' :
        cand1_2 ∈ scoringEliminationAux vetoScore _ (restrictProfile profile (2 : Fin 3)) := by
      simpa [hcoombs_sub] using hmem_sub
    exact (mem_liftFinset_iff_subtype
      (s := scoringEliminationAux vetoScore _ (restrictProfile profile (2 : Fin 3)))
      (x := (1 : Fin 3))).2 ⟨by decide, hmem_sub'⟩
  have hmem_union :
      (1 : Fin 3) ∈
        (Finset.univ : Finset (Fin 3)).biUnion
          (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile profile c))) := by
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨(2 : Fin 3), by simp, ?_⟩
    simpa [coombs, scoringEliminationRule] using hmem_lift
  simpa [hcoombs, haux'] using hmem_union

/-! ## Majority criterion violation -/

lemma majority_top2_count :
    countTop (fun v => (ballots v).ranking) (2 : Fin 3) = 2 := by
  decide

lemma votersTop_card_2 :
    (votersTop profile (2 : Fin 3)).card = 2 := by
  simpa [profile, votersTop_card_eq_countTop] using majority_top2_count

lemma strictMajority_votersTop_2 :
    StrictMajority (votersTop profile (2 : Fin 3)) := by
  unfold StrictMajority
  simp [votersTop_card_2]

end CoombsMajorityCounterexample

open CoombsMajorityCounterexample

theorem coombs_not_majority_criterion : ¬ MajorityCriterion coombs := by
  intro hmaj
  have hmaj' : StrictMajority (votersTop profile (2 : Fin 3)) :=
    strictMajority_votersTop_2
  have hres : coombs profile = ({2} : Finset (Fin 3)) :=
    hmaj profile (2 : Fin 3) hmaj'
  have hmem : (1 : Fin 3) ∈ coombs profile :=
    coombs_profile_has_1
  have hmem' : False := by
    have hmem' := hmem
    simp [hres] at hmem'
  exact hmem'

end SocialChoice
