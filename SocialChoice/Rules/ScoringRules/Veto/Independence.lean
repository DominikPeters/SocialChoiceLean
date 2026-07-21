import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Clones
import SocialChoice.Axioms.Independence
import SocialChoice.ListBallot
import SocialChoice.Rules.ScoringElimination.Coombs.CondorcetLoser
import SocialChoice.Rules.ScoringRules.Plurality.Defs
import SocialChoice.Rules.ScoringRules.Veto.Defs

namespace SocialChoice

open Classical
open Finset

attribute [instance] Classical.decEq Classical.decPred

/-!
## Veto fails independence of clones

Counterexample profile (candidates 0=a, 1=b, 2=c):
1 voter: b > a > c
1 voter: c > a > b

Veto selects a. The clone set is {a,b}. Removing b makes c a winner,
so c is a non-clone winner only after removing a clone.
-/

namespace VetoIndependenceCounterexample

def ballotBAC : ListBallot 3 := ListBallot.mk' [1, 0, 2]
def ballotCAB : ListBallot 3 := ListBallot.mk' [2, 0, 1]

def ballots : Fin 2 → ListBallot 3
  | ⟨0, _⟩ => ballotBAC
  | ⟨1, _⟩ => ballotCAB

noncomputable def profile : Profile (Fin 2) (Fin 3) :=
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

lemma veto_profile_has_0 : (0 : Fin 3) ∈ veto profile := by
  decide

lemma veto_profile_not_2 : (2 : Fin 3) ∉ veto profile := by
  decide

@[reducible] def q : Fin 3 → Prop := fun a => a ≠ (1 : Fin 3)

instance : DecidablePred q := by
  intro a
  dsimp [q]
  infer_instance

lemma clonePred_eq_ne :
    clonePred cloneSet (0 : Fin 3) = (fun a : Fin 3 => a ≠ (1 : Fin 3)) := by
  funext a
  apply propext
  fin_cases a <;> simp [cloneSet, clonePred]

lemma cast_subtype_val {A : Type} {p q : A → Prop}
    (h : p = q) (x : {a : A // p a}) :
    (cast (congrArg (fun r => {a : A // r a}) h) x : {a : A // q a}).1 = x.1 := by
  cases x
  cases h
  rfl

noncomputable def profileQ : Profile (Fin 2) {a : Fin 3 // q a} :=
  restrictCandidates profile q

def cand0q : {a : Fin 3 // q a} := ⟨0, by simp [q]⟩
def cand2q : {a : Fin 3 // q a} := ⟨2, by simp [q]⟩

lemma cand2q_ne_cand0q : cand2q ≠ cand0q := by
  intro h
  have h' : (2 : Fin 3) = 0 := by
    simpa [cand2q, cand0q] using congrArg Subtype.val h
  exact (by decide : (2 : Fin 3) ≠ 0) h'

lemma cand0q_ne_cand2q : cand0q ≠ cand2q := by
  exact cand2q_ne_cand0q.symm

lemma votersPreferring_restrictCandidates_eq {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (p : A → Prop) [DecidablePred p]
    (a b : {x : A // p x}) :
    votersPreferring (restrictCandidates P p) a b = votersPreferring P a b := by
  ext v
  simp [votersPreferring, prefers_restrictCandidates_iff]

lemma votersPreferring_profile_2_0 :
    (votersPreferring profile (2 : Fin 3) (0 : Fin 3)).card = 1 := by
  calc
    (votersPreferring profile (2 : Fin 3) (0 : Fin 3)).card =
        countPrefers (fun v => (ballots v).ranking) 2 0 := by
          unfold countPrefers
          simpa [profile] using
            congrArg Finset.card
              (votersPreferring_eq_filter_prefersInList
                (ballots := ballots) (a := 2) (b := 0))
    _ = 1 := rfl

lemma votersPreferring_profile_0_2 :
    (votersPreferring profile (0 : Fin 3) (2 : Fin 3)).card = 1 := by
  calc
    (votersPreferring profile (0 : Fin 3) (2 : Fin 3)).card =
        countPrefers (fun v => (ballots v).ranking) 0 2 := by
          unfold countPrefers
          simpa [profile] using
            congrArg Finset.card
              (votersPreferring_eq_filter_prefersInList
                (ballots := ballots) (a := 0) (b := 2))
    _ = 1 := rfl

@[reducible] noncomputable def scoreVecQ : Nat → Int :=
  fun r => vetoScore (Fintype.card {a : Fin 3 // q a}) r

lemma card_q : Fintype.card {a : Fin 3 // q a} = 2 := by
  classical
  change Fintype.card {a : Fin 3 // a ≠ (1 : Fin 3)} = 2
  have h :=
    (Fintype.card_subtype_compl (α := Fin 3) (p := fun a : Fin 3 => a = (1 : Fin 3)))
  rw [h]
  simp

lemma score_restrict_2 :
    scoreCandidate profileQ scoreVecQ cand2q = 1 := by
  have hcard : Fintype.card {a : Fin 3 // q a} = 2 := card_q
  have hcd : cand2q ≠ cand0q := cand2q_ne_cand0q
  have hscore :
      scoreCandidate profileQ scoreVecQ cand2q = topCount profileQ cand2q := by
    exact vetoScore_eq_topCount_of_two (P := profileQ) (hcard := hcard)
      (c := cand2q) (d := cand0q) (hcd := hcd)
  have htop :
      topCount profileQ cand2q =
        (votersPreferring profileQ cand2q cand0q).card := by
    have h :=
      congrArg Finset.card
        (votersTop_eq_votersPreferring_of_two (P := profileQ) hcard cand2q cand0q hcd)
    simpa [topCount] using h
  have hvp :
      (votersPreferring profileQ cand2q cand0q).card = 1 := by
    have h' :=
      congrArg Finset.card
        (votersPreferring_restrictCandidates_eq (P := profile) (p := q)
          (a := cand2q) (b := cand0q))
    have h'' :
        (votersPreferring profile cand2q cand0q).card = 1 := by
      simpa [cand2q, cand0q] using votersPreferring_profile_2_0
    exact h'.trans h''
  calc
    scoreCandidate profileQ scoreVecQ cand2q = topCount profileQ cand2q := hscore
    _ = (votersPreferring profileQ cand2q cand0q).card := by
          exact_mod_cast htop
    _ = 1 := by
          exact_mod_cast hvp

lemma score_restrict_0 :
    scoreCandidate profileQ scoreVecQ cand0q = 1 := by
  have hcard : Fintype.card {a : Fin 3 // q a} = 2 := card_q
  have hcd : cand0q ≠ cand2q := cand0q_ne_cand2q
  have hscore :
      scoreCandidate profileQ scoreVecQ cand0q = topCount profileQ cand0q := by
    exact vetoScore_eq_topCount_of_two (P := profileQ) (hcard := hcard)
      (c := cand0q) (d := cand2q) (hcd := hcd)
  have htop :
      topCount profileQ cand0q =
        (votersPreferring profileQ cand0q cand2q).card := by
    have h :=
      congrArg Finset.card
        (votersTop_eq_votersPreferring_of_two (P := profileQ) hcard cand0q cand2q hcd)
    simpa [topCount] using h
  have hvp :
      (votersPreferring profileQ cand0q cand2q).card = 1 := by
    have h' :=
      congrArg Finset.card
        (votersPreferring_restrictCandidates_eq (P := profile) (p := q)
          (a := cand0q) (b := cand2q))
    have h'' :
        (votersPreferring profile cand0q cand2q).card = 1 := by
      simpa [cand0q, cand2q] using votersPreferring_profile_0_2
    exact h'.trans h''
  calc
    scoreCandidate profileQ scoreVecQ cand0q = topCount profileQ cand0q := hscore
    _ = (votersPreferring profileQ cand0q cand2q).card := by
          exact_mod_cast htop
    _ = 1 := by
          exact_mod_cast hvp

def cand2clone : {a : Fin 3 // clonePred cloneSet (0 : Fin 3) a} :=
  ⟨2, by simp [cloneSet, clonePred]⟩

lemma veto_cloneProfile_has_2 :
    cand2clone ∈ veto (removeClonesExcept profile cloneSet (0 : Fin 3)) := by
  classical
  have hA : (Finset.univ : Finset {a : Fin 3 // q a}).Nonempty := by
    refine ⟨cand0q, by simp [cand0q]⟩
  have hcard : Fintype.card {a : Fin 3 // q a} = 2 := card_q
  have hmax :
      ∀ d : {a : Fin 3 // q a},
        scoreCandidate profileQ scoreVecQ d ≤ scoreCandidate profileQ scoreVecQ cand2q := by
    intro d
    rcases two_elems_eq_or_eq (A := {a : Fin 3 // q a})
      hcard cand2q cand0q cand2q_ne_cand0q d with rfl | rfl
    · exact le_rfl
    · simp [score_restrict_0, score_restrict_2]
  have hc :
      cand2q ∈ scoringRule vetoScore profileQ := by
    have hc' :=
      (scoringWinners_iff_forall_le (P := profileQ) (score := scoreVecQ)
        (hA := hA) (c := cand2q)).2 hmax
    change cand2q ∈ scoringWinners profileQ scoreVecQ
    exact hc'
  have hpred : q = clonePred cloneSet (0 : Fin 3) := by
    exact clonePred_eq_ne.symm
  have hc_cast :
      (cast (congrArg (fun r => {a : Fin 3 // r a}) hpred) cand2q :
        {a : Fin 3 // clonePred cloneSet (0 : Fin 3) a}) ∈
      scoringRule vetoScore
        (castCandidates (p := q) (q := clonePred cloneSet (0 : Fin 3)) hpred
          (restrictCandidates profile q)) := by
    exact (mem_scoringRule_castCandidates_iff
      (score := vetoScore) (p := q) (q := clonePred cloneSet (0 : Fin 3))
      (dp := inferInstance) (dq := inferInstance) hpred
      cand2q (restrictCandidates profile q)).1 hc
  have hc_cast' :
      (cast (congrArg (fun r => {a : Fin 3 // r a}) hpred) cand2q :
        {a : Fin 3 // clonePred cloneSet (0 : Fin 3) a}) ∈
      scoringRule vetoScore (restrictCandidates profile (clonePred cloneSet (0 : Fin 3))) := by
    simpa [castCandidates_restrictCandidates] using hc_cast
  have hcast_cand2 :
      (cast (congrArg (fun r => {a : Fin 3 // r a}) hpred) cand2q :
        {a : Fin 3 // clonePred cloneSet (0 : Fin 3) a}) = cand2clone := by
    apply Subtype.ext
    simpa [cand2clone, cand2q] using
      (cast_subtype_val (h := hpred) (x := cand2q))
  have hcclone :
      cand2clone ∈ scoringRule vetoScore
        (restrictCandidates profile (clonePred cloneSet (0 : Fin 3))) := by
    simpa [hcast_cand2] using hc_cast'
  simpa [veto, removeClonesExcept] using hcclone

lemma cand2clone_eq (hc : (2 : Fin 3) ∉ cloneSet) :
    (⟨2, Or.inl hc⟩ :
        {a : Fin 3 // clonePred cloneSet (0 : Fin 3) a}) = cand2clone := by
  apply Subtype.ext
  rfl

end VetoIndependenceCounterexample

open VetoIndependenceCounterexample

theorem veto_not_independenceOfClones : ¬ IndependenceOfClones veto := by
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
          veto (removeClonesExcept profile cloneSet (0 : Fin 3)) := by
    simpa [cand2clone_eq (hc := hc)] using veto_cloneProfile_has_2
  have hc_right : (2 : Fin 3) ∈ veto profile := (hnonclone).2 hc_left
  exact (veto_profile_not_2 hc_right).elim

end SocialChoice
