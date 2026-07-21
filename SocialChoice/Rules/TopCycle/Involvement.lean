import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Participation
import SocialChoice.Axioms.Condorcet
import SocialChoice.ListBallot
import SocialChoice.Rules.TopCycle.Defs
import SocialChoice.Rules.TopCycle.Condorcet

namespace SocialChoice

open Finset
open Classical
attribute [instance] Classical.decEq

set_option maxHeartbeats 5000000

/-!
# TopCycle fails negative involvement

Counterexample with 3 candidates and 2 voters:

Full profile (2 voters):
1 voter : 1 > 2 > 0
1 voter : 2 > 0 > 1
TopCycle selects {0,1,2}.

Remove the voter with ballot 1 > 2 > 0:
TopCycle selects {2}.

Read backwards, this violates Negative Involvement for candidate 0.
-/

namespace TopCycleNegativeInvolvementCounterexample

def ballot120 : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballot201 : ListBallot 3 := ListBallot.mk' [2, 0, 1]

def ballots2 : Fin 2 → ListBallot 3
  | ⟨0, _⟩ => ballot120
  | ⟨1, _⟩ => ballot201

def voters1 : Finset (Fin 2) := {1}
def voters2 : Finset (Fin 2) := insert (0 : Fin 2) voters1

noncomputable def fullProfile : Profile (Electorate (Fin 2) (Finset.univ)) (Fin 3) :=
  { pref := fun v => (ballots2 v.1).toLinearOrder }

noncomputable def profile1 : Profile (Electorate (Fin 2) voters1) (Fin 3) :=
  restrictElectorate fullProfile voters1 (by
    intro x hx; exact (Finset.mem_univ x))

noncomputable def profile2 : Profile (Electorate (Fin 2) voters2) (Fin 3) :=
  restrictElectorate fullProfile voters2 (by
    intro x hx; exact (Finset.mem_univ x))

lemma voters1_not_mem : (0 : Fin 2) ∉ voters1 := by
  simp [voters1]

lemma profiles_agree :
    ∀ v : Electorate (Fin 2) voters1,
      profile2.pref (liftVoter (u := (0 : Fin 2)) v) = profile1.pref v := by
  intro v
  simpa [profile1, profile2, voters2] using
    (restrictElectorate_agrees (Q := fullProfile) (S := voters1)
      (hS := by intro x hx; exact (Finset.mem_univ x))
      (u := (0 : Fin 2))
      (hSu := by intro x hx; exact (Finset.mem_univ x)) v)

private lemma ballot120_bottom_0 : BallotBottom (ballot120.toLinearOrder) (0 : Fin 3) := by
  intro d hd
  fin_cases d
  · cases hd rfl
  ·
    have hlt :
        ballot120.ranking.idxOf (1 : Fin 3) < ballot120.ranking.idxOf (0 : Fin 3) := by
      decide
    simpa [ballot120, ListBallot.lt_iff_idxOf] using hlt
  ·
    have hlt :
        ballot120.ranking.idxOf (2 : Fin 3) < ballot120.ranking.idxOf (0 : Fin 3) := by
      decide
    simpa [ballot120, ListBallot.lt_iff_idxOf] using hlt

lemma newVoter_bottom_0 :
    BallotBottom
      (profile2.pref (newVoter (u := (0 : Fin 2)) (V := voters1) voters1_not_mem))
      (0 : Fin 3) := by
  change BallotBottom ballot120.toLinearOrder (0 : Fin 3)
  exact ballot120_bottom_0

lemma margin_eq_card_diff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) :
    margin P a b =
      Int.ofNat (votersPreferring P a b).card -
        Int.ofNat (votersPreferring P b a).card := by
  classical
  simp [margin, votersPreferring]

private lemma prefers_profile1_2_0 :
    ∀ v : Electorate (Fin 2) voters1, Prefers profile1 v (2 : Fin 3) (0 : Fin 3) := by
  intro v
  cases v with
  | mk val hmem =>
      have hval : val = (1 : Fin 2) := by
        simpa [voters1] using hmem
      subst hval
      change Prefers (profileOfListBallots ballots2) (1 : Fin 2) (2 : Fin 3) (0 : Fin 3)
      rw [prefers_iff_prefersInList]
      decide

private lemma prefers_profile1_2_1 :
    ∀ v : Electorate (Fin 2) voters1, Prefers profile1 v (2 : Fin 3) (1 : Fin 3) := by
  intro v
  cases v with
  | mk val hmem =>
      have hval : val = (1 : Fin 2) := by
        simpa [voters1] using hmem
      subst hval
      change Prefers (profileOfListBallots ballots2) (1 : Fin 2) (2 : Fin 3) (1 : Fin 3)
      rw [prefers_iff_prefersInList]
      decide

private lemma margin_pos_profile1_2_0 : margin_pos profile1 (2 : Fin 3) (0 : Fin 3) := by
  classical
  let _ : Nonempty (Electorate (Fin 2) voters1) := ⟨⟨1, by simp [voters1]⟩⟩
  exact unanimous_margin (P := profile1) (x := (2 : Fin 3)) (y := (0 : Fin 3))
    prefers_profile1_2_0

private lemma margin_pos_profile1_2_1 : margin_pos profile1 (2 : Fin 3) (1 : Fin 3) := by
  classical
  let _ : Nonempty (Electorate (Fin 2) voters1) := ⟨⟨1, by simp [voters1]⟩⟩
  exact unanimous_margin (P := profile1) (x := (2 : Fin 3)) (y := (1 : Fin 3))
    prefers_profile1_2_1

private lemma condorcetWinner_profile1 : CondorcetWinner profile1 (2 : Fin 3) := by
  apply (CondorcetWinner_iff_margin_pos (P := profile1) (c := (2 : Fin 3))).2
  intro d hd
  fin_cases d
  · exact margin_pos_profile1_2_0
  · exact margin_pos_profile1_2_1
  · cases hd rfl

lemma topCycle_profile1_eq : topCycle profile1 = ({2} : Finset (Fin 3)) := by
  exact topCycle_condorcetConsistency (P := profile1) (c := (2 : Fin 3))
    condorcetWinner_profile1

lemma topCycle_profile1_not_0 : (0 : Fin 3) ∉ topCycle profile1 := by
  simp [topCycle_profile1_eq]

private lemma votersPreferring_profile2_eq_filter (x y : Fin 3) :
    votersPreferring profile2 x y =
      Finset.univ.filter (fun v => prefersInList (ballots2 v.1).ranking x y) := by
  ext v
  simp only [votersPreferring, Finset.mem_filter, Finset.mem_univ, true_and]
  change Prefers (profileOfListBallots ballots2) v.1 x y ↔ _
  exact prefers_iff_prefersInList ballots2 v.1 x y

lemma votersPreferring_profile2_0_1 :
    votersPreferring profile2 (0 : Fin 3) (1 : Fin 3) =
      ({⟨1, by simp [voters2, voters1]⟩} :
        Finset (Electorate (Fin 2) voters2)) := by
  classical
  rw [votersPreferring_profile2_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters2, voters1, ballots2, ballot120, ballot201, prefersInList] at hmem ⊢;
          all_goals decide +revert)

lemma votersPreferring_profile2_1_0 :
    votersPreferring profile2 (1 : Fin 3) (0 : Fin 3) =
      ({⟨0, by simp [voters2, voters1]⟩} :
        Finset (Electorate (Fin 2) voters2)) := by
  classical
  rw [votersPreferring_profile2_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters2, voters1, ballots2, ballot120, ballot201, prefersInList] at hmem ⊢;
          all_goals decide +revert)

lemma votersPreferring_profile2_2_1 :
    votersPreferring profile2 (2 : Fin 3) (1 : Fin 3) =
      ({⟨1, by simp [voters2, voters1]⟩} :
        Finset (Electorate (Fin 2) voters2)) := by
  classical
  rw [votersPreferring_profile2_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters2, voters1, ballots2, ballot120, ballot201, prefersInList] at hmem ⊢;
          all_goals decide +revert)

lemma votersPreferring_profile2_1_2 :
    votersPreferring profile2 (1 : Fin 3) (2 : Fin 3) =
      ({⟨0, by simp [voters2, voters1]⟩} :
        Finset (Electorate (Fin 2) voters2)) := by
  classical
  rw [votersPreferring_profile2_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters2, voters1, ballots2, ballot120, ballot201, prefersInList] at hmem ⊢;
          all_goals decide +revert)

private lemma margin_profile2_0_1 : margin profile2 (0 : Fin 3) (1 : Fin 3) = 0 := by
  classical
  simp [margin_eq_card_diff, votersPreferring_profile2_0_1, votersPreferring_profile2_1_0]

private lemma margin_profile2_2_1 : margin profile2 (2 : Fin 3) (1 : Fin 3) = 0 := by
  classical
  simp [margin_eq_card_diff, votersPreferring_profile2_2_1, votersPreferring_profile2_1_2]

private lemma margin_profile2_1_0 : margin profile2 (1 : Fin 3) (0 : Fin 3) = 0 := by
  classical
  simp [margin_eq_card_diff, votersPreferring_profile2_1_0, votersPreferring_profile2_0_1]

private lemma margin_profile2_1_2 : margin profile2 (1 : Fin 3) (2 : Fin 3) = 0 := by
  classical
  simp [margin_eq_card_diff, votersPreferring_profile2_1_2, votersPreferring_profile2_2_1]

private lemma not_margin_pos_profile2_0_1 : ¬ margin_pos profile2 (0 : Fin 3) (1 : Fin 3) := by
  simp [margin_pos, margin_profile2_0_1]

private lemma not_margin_pos_profile2_2_1 : ¬ margin_pos profile2 (2 : Fin 3) (1 : Fin 3) := by
  simp [margin_pos, margin_profile2_2_1]

private lemma not_margin_pos_profile2_1_0 : ¬ margin_pos profile2 (1 : Fin 3) (0 : Fin 3) := by
  simp [margin_pos, margin_profile2_1_0]

private lemma not_margin_pos_profile2_1_2 : ¬ margin_pos profile2 (1 : Fin 3) (2 : Fin 3) := by
  simp [margin_pos, margin_profile2_1_2]

lemma topCycleSet_profile2_has_1 : (1 : Fin 3) ∈ topCycleSet (P := profile2) := by
  classical
  by_contra h1
  have hdom : dominatesSet profile2 (topCycleSet (P := profile2)) :=
    topCycleSet_dominates (P := profile2)
  rcases hdom.1 with ⟨x, hx⟩
  have hpos : margin_pos profile2 x (1 : Fin 3) :=
    hdom.2 x hx (1 : Fin 3) h1
  fin_cases x
  · exact (not_margin_pos_profile2_0_1 hpos).elim
  · exact (h1 hx).elim
  · exact (not_margin_pos_profile2_2_1 hpos).elim

lemma topCycleSet_profile2_has_0 : (0 : Fin 3) ∈ topCycleSet (P := profile2) := by
  classical
  by_contra h0
  have hdom : dominatesSet profile2 (topCycleSet (P := profile2)) :=
    topCycleSet_dominates (P := profile2)
  have h1 : (1 : Fin 3) ∈ topCycleSet (P := profile2) := topCycleSet_profile2_has_1
  have hpos : margin_pos profile2 (1 : Fin 3) (0 : Fin 3) :=
    hdom.2 (1 : Fin 3) h1 (0 : Fin 3) h0
  exact (not_margin_pos_profile2_1_0 hpos).elim

lemma topCycle_profile2_has_0 : (0 : Fin 3) ∈ topCycle profile2 := by
  have hA : Nonempty (Fin 3) := inferInstance
  have hmem : (0 : Fin 3) ∈ topCycleSet (P := profile2) := topCycleSet_profile2_has_0
  simpa [topCycle, hA] using hmem

end TopCycleNegativeInvolvementCounterexample

open TopCycleNegativeInvolvementCounterexample

theorem topCycle_not_negativeInvolvement : ¬ NegativeInvolvement topCycle := by
  intro hneg
  have hnotmem : (0 : Fin 3) ∉ topCycle profile1 := topCycle_profile1_not_0
  have hbottom :
      BallotBottom
        (profile2.pref (newVoter (u := (0 : Fin 2)) (V := voters1) voters1_not_mem))
        (0 : Fin 3) :=
    newVoter_bottom_0
  have hmem : (0 : Fin 3) ∈ topCycle profile2 := topCycle_profile2_has_0
  have hcontra :=
    hneg (V := voters1) (u := (0 : Fin 2)) (hu := voters1_not_mem)
      (P := profile1) (Q := profile2) (c := (0 : Fin 3))
      profiles_agree hnotmem hbottom
  exact hcontra hmem

end SocialChoice
