import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Participation
import SocialChoice.ListBallot
import SocialChoice.Rules.UncoveredSet.Defs

namespace SocialChoice

open Finset
open Classical
attribute [instance] Classical.decEq

set_option maxHeartbeats 5000000

/-!
# Uncovered Set fails negative involvement

Counterexample with 3 candidates and 4 voters:

Full profile (4 voters):
1 voter : 0 > 2 > 1
1 voter : 1 > 0 > 2
2 voters: 2 > 1 > 0
UncoveredSet selects {0,1,2}.

Remove the voter with ballot 0 > 2 > 1:
UncoveredSet selects {2}.

Read backwards, this violates Negative Involvement for candidate 1.
-/

namespace UncoveredSetNegativeInvolvementCounterexample

def ballot021 : ListBallot 3 := ListBallot.mk' [0, 2, 1]
def ballot102 : ListBallot 3 := ListBallot.mk' [1, 0, 2]
def ballot210 : ListBallot 3 := ListBallot.mk' [2, 1, 0]

def ballots4 : Fin 4 → ListBallot 3
  | ⟨0, _⟩ => ballot021
  | ⟨1, _⟩ => ballot102
  | ⟨2, _⟩ => ballot210
  | ⟨3, _⟩ => ballot210

def voters3 : Finset (Fin 4) := {1, 2, 3}
def voters4 : Finset (Fin 4) := insert (0 : Fin 4) voters3

noncomputable def fullProfile : Profile (Electorate (Fin 4) (Finset.univ)) (Fin 3) :=
  { pref := fun v => (ballots4 v.1).toLinearOrder }

noncomputable def profile3 : Profile (Electorate (Fin 4) voters3) (Fin 3) :=
  restrictElectorate fullProfile voters3 (by
    intro x hx; exact (Finset.mem_univ x))

noncomputable def profile4 : Profile (Electorate (Fin 4) voters4) (Fin 3) :=
  restrictElectorate fullProfile voters4 (by
    intro x hx; exact (Finset.mem_univ x))

lemma voters3_not_mem : (0 : Fin 4) ∉ voters3 := by
  simp [voters3]

lemma profiles_agree :
    ∀ v : Electorate (Fin 4) voters3,
      profile4.pref (liftVoter (u := (0 : Fin 4)) v) = profile3.pref v := by
  intro v
  simpa [profile3, profile4, voters4] using
    (restrictElectorate_agrees (Q := fullProfile) (S := voters3)
      (hS := by intro x hx; exact (Finset.mem_univ x))
      (u := (0 : Fin 4))
      (hSu := by intro x hx; exact (Finset.mem_univ x)) v)

private lemma ballot021_bottom_1 : BallotBottom (ballot021.toLinearOrder) (1 : Fin 3) := by
  intro d hd
  fin_cases d
  ·
    have hlt :
        ballot021.ranking.idxOf (0 : Fin 3) < ballot021.ranking.idxOf (1 : Fin 3) := by
      decide
    simpa [ballot021, ListBallot.lt_iff_idxOf] using hlt
  · cases hd rfl
  ·
    have hlt :
        ballot021.ranking.idxOf (2 : Fin 3) < ballot021.ranking.idxOf (1 : Fin 3) := by
      decide
    simpa [ballot021, ListBallot.lt_iff_idxOf] using hlt

lemma newVoter_bottom_1 :
    BallotBottom
      (profile4.pref (newVoter (u := (0 : Fin 4)) (V := voters3) voters3_not_mem))
      (1 : Fin 3) := by
  change BallotBottom ballot021.toLinearOrder (1 : Fin 3)
  exact ballot021_bottom_1

lemma margin_eq_card_diff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) :
    margin P a b =
      Int.ofNat (votersPreferring P a b).card -
        Int.ofNat (votersPreferring P b a).card := by
  classical
  simp [margin, votersPreferring]

private lemma votersPreferring_profile3_eq_filter (x y : Fin 3) :
    votersPreferring profile3 x y =
      Finset.univ.filter (fun v => prefersInList (ballots4 v.1).ranking x y) := by
  ext v
  simp only [votersPreferring, Finset.mem_filter, Finset.mem_univ, true_and]
  change Prefers (profileOfListBallots ballots4) v.1 x y ↔ _
  exact prefers_iff_prefersInList ballots4 v.1 x y

private lemma votersPreferring_profile4_eq_filter (x y : Fin 3) :
    votersPreferring profile4 x y =
      Finset.univ.filter (fun v => prefersInList (ballots4 v.1).ranking x y) := by
  ext v
  simp only [votersPreferring, Finset.mem_filter, Finset.mem_univ, true_and]
  change Prefers (profileOfListBallots ballots4) v.1 x y ↔ _
  exact prefers_iff_prefersInList ballots4 v.1 x y

lemma votersPreferring_profile3_2_1 :
    votersPreferring profile3 (2 : Fin 3) (1 : Fin 3) =
      ({⟨2, by simp [voters3]⟩, ⟨3, by simp [voters3]⟩} :
        Finset (Electorate (Fin 4) voters3)) := by
  classical
  rw [votersPreferring_profile3_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters3, ballots4, ballot021, ballot102, ballot210, prefersInList] at hmem ⊢;
          all_goals decide +revert)

lemma votersPreferring_profile3_1_2 :
    votersPreferring profile3 (1 : Fin 3) (2 : Fin 3) =
      ({⟨1, by simp [voters3]⟩} :
        Finset (Electorate (Fin 4) voters3)) := by
  classical
  rw [votersPreferring_profile3_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters3, ballots4, ballot021, ballot102, ballot210, prefersInList] at hmem ⊢;
          all_goals decide +revert)

lemma votersPreferring_profile3_2_0 :
    votersPreferring profile3 (2 : Fin 3) (0 : Fin 3) =
      ({⟨2, by simp [voters3]⟩, ⟨3, by simp [voters3]⟩} :
        Finset (Electorate (Fin 4) voters3)) := by
  classical
  rw [votersPreferring_profile3_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters3, ballots4, ballot021, ballot102, ballot210, prefersInList] at hmem ⊢;
          all_goals decide +revert)

lemma votersPreferring_profile3_0_2 :
    votersPreferring profile3 (0 : Fin 3) (2 : Fin 3) =
      ({⟨1, by simp [voters3]⟩} :
        Finset (Electorate (Fin 4) voters3)) := by
  classical
  rw [votersPreferring_profile3_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters3, ballots4, ballot021, ballot102, ballot210, prefersInList] at hmem ⊢;
          all_goals decide +revert)

lemma votersPreferring_profile3_1_0 :
    votersPreferring profile3 (1 : Fin 3) (0 : Fin 3) =
      ({⟨1, by simp [voters3]⟩, ⟨2, by simp [voters3]⟩, ⟨3, by simp [voters3]⟩} :
        Finset (Electorate (Fin 4) voters3)) := by
  classical
  rw [votersPreferring_profile3_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters3, ballots4, ballot021, ballot102, ballot210, prefersInList] at hmem ⊢;
          all_goals decide +revert)

lemma votersPreferring_profile3_0_1 :
    votersPreferring profile3 (0 : Fin 3) (1 : Fin 3) =
      (∅ : Finset (Electorate (Fin 4) voters3)) := by
  classical
  rw [votersPreferring_profile3_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters3, ballots4, ballot021, ballot102, ballot210, prefersInList] at hmem ⊢;
          all_goals decide +revert)

private lemma margin_pos_profile3_2_1 : margin_pos profile3 (2 : Fin 3) (1 : Fin 3) := by
  have hmargin :
      margin profile3 (2 : Fin 3) (1 : Fin 3) = 1 := by
    classical
    simp [margin_eq_card_diff, votersPreferring_profile3_2_1, votersPreferring_profile3_1_2]
  simp [margin_pos, hmargin]

private lemma margin_pos_profile3_2_0 : margin_pos profile3 (2 : Fin 3) (0 : Fin 3) := by
  have hmargin :
      margin profile3 (2 : Fin 3) (0 : Fin 3) = 1 := by
    classical
    simp [margin_eq_card_diff, votersPreferring_profile3_2_0, votersPreferring_profile3_0_2]
  simp [margin_pos, hmargin]

private lemma margin_pos_profile3_1_0 : margin_pos profile3 (1 : Fin 3) (0 : Fin 3) := by
  have hmargin :
      margin profile3 (1 : Fin 3) (0 : Fin 3) = 3 := by
    classical
    simp [margin_eq_card_diff, votersPreferring_profile3_1_0, votersPreferring_profile3_0_1]
  simp [margin_pos, hmargin]

private lemma not_margin_pos_profile3_0_2 : ¬ margin_pos profile3 (0 : Fin 3) (2 : Fin 3) := by
  have hmargin :
      margin profile3 (0 : Fin 3) (2 : Fin 3) = -1 := by
    classical
    simp [margin_eq_card_diff, votersPreferring_profile3_0_2, votersPreferring_profile3_2_0]
  simp [margin_pos, hmargin]

private lemma not_margin_pos_profile3_1_2 : ¬ margin_pos profile3 (1 : Fin 3) (2 : Fin 3) := by
  have hmargin :
      margin profile3 (1 : Fin 3) (2 : Fin 3) = -1 := by
    classical
    simp [margin_eq_card_diff, votersPreferring_profile3_1_2, votersPreferring_profile3_2_1]
  simp [margin_pos, hmargin]

private lemma not_margin_pos_profile3_0_1 : ¬ margin_pos profile3 (0 : Fin 3) (1 : Fin 3) := by
  have hmargin :
      margin profile3 (0 : Fin 3) (1 : Fin 3) = -3 := by
    classical
    simp [margin_eq_card_diff, votersPreferring_profile3_0_1, votersPreferring_profile3_1_0]
  simp [margin_pos, hmargin]

private lemma covers_profile3_2_1 : covers profile3 (2 : Fin 3) (1 : Fin 3) := by
  refine ⟨margin_pos_profile3_2_1, ?_, ?_⟩
  · intro z hz
    fin_cases z
    · exact margin_pos_profile3_2_0
    · exact (margin_pos_irrefl (P := profile3) (x := (1 : Fin 3)) hz).elim
    · exact (not_margin_pos_profile3_1_2 hz).elim
  · intro z hz
    fin_cases z
    · exact (not_margin_pos_profile3_0_2 hz).elim
    · exact (not_margin_pos_profile3_1_2 hz).elim
    · exact (margin_pos_irrefl (P := profile3) (x := (2 : Fin 3)) hz).elim

private lemma not_uncovered_profile3_1 : (1 : Fin 3) ∉ uncoveredSet (P := profile3) := by
  classical
  intro hmem
  have huncov : uncovered profile3 (1 : Fin 3) := (Finset.mem_filter.mp hmem).2
  have hcov : covers profile3 (2 : Fin 3) (1 : Fin 3) := covers_profile3_2_1
  exact (huncov (2 : Fin 3) (by decide) hcov).elim

lemma votersPreferring_profile4_1_0 :
    votersPreferring profile4 (1 : Fin 3) (0 : Fin 3) =
      ({⟨1, by simp [voters4, voters3]⟩, ⟨2, by simp [voters4, voters3]⟩,
        ⟨3, by simp [voters4, voters3]⟩} :
        Finset (Electorate (Fin 4) voters4)) := by
  classical
  rw [votersPreferring_profile4_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters4, voters3, ballots4, ballot021, ballot102, ballot210,
          prefersInList] at hmem ⊢; all_goals decide +revert)

lemma votersPreferring_profile4_0_1 :
    votersPreferring profile4 (0 : Fin 3) (1 : Fin 3) =
      ({⟨0, by simp [voters4, voters3]⟩} :
        Finset (Electorate (Fin 4) voters4)) := by
  classical
  rw [votersPreferring_profile4_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters4, voters3, ballots4, ballot021, ballot102, ballot210,
          prefersInList] at hmem ⊢; all_goals decide +revert)

lemma votersPreferring_profile4_2_1 :
    votersPreferring profile4 (2 : Fin 3) (1 : Fin 3) =
      ({⟨0, by simp [voters4, voters3]⟩, ⟨2, by simp [voters4, voters3]⟩,
        ⟨3, by simp [voters4, voters3]⟩} :
        Finset (Electorate (Fin 4) voters4)) := by
  classical
  rw [votersPreferring_profile4_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters4, voters3, ballots4, ballot021, ballot102, ballot210,
          prefersInList] at hmem ⊢; all_goals decide +revert)

lemma votersPreferring_profile4_1_2 :
    votersPreferring profile4 (1 : Fin 3) (2 : Fin 3) =
      ({⟨1, by simp [voters4, voters3]⟩} :
        Finset (Electorate (Fin 4) voters4)) := by
  classical
  rw [votersPreferring_profile4_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters4, voters3, ballots4, ballot021, ballot102, ballot210,
          prefersInList] at hmem ⊢; all_goals decide +revert)

lemma votersPreferring_profile4_2_0 :
    votersPreferring profile4 (2 : Fin 3) (0 : Fin 3) =
      ({⟨2, by simp [voters4, voters3]⟩, ⟨3, by simp [voters4, voters3]⟩} :
        Finset (Electorate (Fin 4) voters4)) := by
  classical
  rw [votersPreferring_profile4_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters4, voters3, ballots4, ballot021, ballot102, ballot210,
          prefersInList] at hmem ⊢; all_goals decide +revert)

lemma votersPreferring_profile4_0_2 :
    votersPreferring profile4 (0 : Fin 3) (2 : Fin 3) =
      ({⟨0, by simp [voters4, voters3]⟩, ⟨1, by simp [voters4, voters3]⟩} :
        Finset (Electorate (Fin 4) voters4)) := by
  classical
  rw [votersPreferring_profile4_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters4, voters3, ballots4, ballot021, ballot102, ballot210,
          prefersInList] at hmem ⊢; all_goals decide +revert)

private lemma margin_pos_profile4_1_0 : margin_pos profile4 (1 : Fin 3) (0 : Fin 3) := by
  have hmargin :
      margin profile4 (1 : Fin 3) (0 : Fin 3) = 2 := by
    classical
    simp [margin_eq_card_diff, votersPreferring_profile4_1_0, votersPreferring_profile4_0_1]
  simp [margin_pos, hmargin]

private lemma not_margin_pos_profile4_2_0 : ¬ margin_pos profile4 (2 : Fin 3) (0 : Fin 3) := by
  have hmargin :
      margin profile4 (2 : Fin 3) (0 : Fin 3) = 0 := by
    classical
    simp [margin_eq_card_diff, votersPreferring_profile4_2_0, votersPreferring_profile4_0_2]
  simp [margin_pos, hmargin]

private lemma not_margin_pos_profile4_0_1 : ¬ margin_pos profile4 (0 : Fin 3) (1 : Fin 3) := by
  have hmargin :
      margin profile4 (0 : Fin 3) (1 : Fin 3) = -2 := by
    classical
    simp [margin_eq_card_diff, votersPreferring_profile4_0_1, votersPreferring_profile4_1_0]
  simp [margin_pos, hmargin]

private lemma not_covers_profile4_0_1 : ¬ covers profile4 (0 : Fin 3) (1 : Fin 3) := by
  intro hcov
  exact not_margin_pos_profile4_0_1 hcov.1

private lemma not_covers_profile4_2_1 : ¬ covers profile4 (2 : Fin 3) (1 : Fin 3) := by
  intro hcov
  have h := hcov.2.1 (0 : Fin 3) margin_pos_profile4_1_0
  exact not_margin_pos_profile4_2_0 h

private lemma not_uncovered_profile4_1 : uncovered profile4 (1 : Fin 3) := by
  intro y hy
  fin_cases y
  · exact not_covers_profile4_0_1
  · cases hy rfl
  · exact not_covers_profile4_2_1

private lemma uncoveredSet_profile4_has_1 : (1 : Fin 3) ∈ uncoveredSet (P := profile4) := by
  classical
  refine Finset.mem_filter.mpr ?_
  exact ⟨by simp, not_uncovered_profile4_1⟩

end UncoveredSetNegativeInvolvementCounterexample

open UncoveredSetNegativeInvolvementCounterexample

theorem uncoveredSet_not_negativeInvolvement : ¬ NegativeInvolvement UncoveredSet := by
  intro hneg
  have hnotmem : (1 : Fin 3) ∉ UncoveredSet profile3 :=
    not_uncovered_profile3_1
  have hbottom :
      BallotBottom
        (profile4.pref (newVoter (u := (0 : Fin 4)) (V := voters3) voters3_not_mem))
        (1 : Fin 3) :=
    newVoter_bottom_1
  have hmem : (1 : Fin 3) ∈ UncoveredSet profile4 :=
    uncoveredSet_profile4_has_1
  have hcontra :=
    hneg (V := voters3) (u := (0 : Fin 4)) (hu := voters3_not_mem)
      (P := profile3) (Q := profile4) (c := (1 : Fin 3))
      profiles_agree hnotmem hbottom
  exact hcontra hmem

end SocialChoice
