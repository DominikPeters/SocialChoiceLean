import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Participation
import SocialChoice.ListBallot
import SocialChoice.Rules.Copeland.Defs

namespace SocialChoice

open Finset

open Classical
attribute [instance] Classical.decEq

set_option maxHeartbeats 5000000

/-!
# Copeland fails positive involvement

Counterexample with 3 candidates and 6 voters:

Full profile (6 voters):
2 voters: 0 > 2 > 1
1 voter : 1 > 0 > 2
1 voter : 1 > 2 > 0
2 voters: 2 > 1 > 0
Copeland selects {2}.

Remove the voter with ballot 1 > 2 > 0:
Copeland selects {0,1,2}.

Read backwards, this violates Positive Involvement for candidate 1.
-/

namespace CopelandPositiveInvolvementCounterexample

def ballot021 : ListBallot 3 := ListBallot.mk' [0, 2, 1]
def ballot102 : ListBallot 3 := ListBallot.mk' [1, 0, 2]
def ballot120 : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballot210 : ListBallot 3 := ListBallot.mk' [2, 1, 0]

def ballots6 : Fin 6 → ListBallot 3
  | ⟨0, _⟩ => ballot021
  | ⟨1, _⟩ => ballot021
  | ⟨2, _⟩ => ballot102
  | ⟨3, _⟩ => ballot120
  | ⟨4, _⟩ => ballot210
  | ⟨5, _⟩ => ballot210

def voters5 : Finset (Fin 6) := {0, 1, 2, 4, 5}
def voters6 : Finset (Fin 6) := insert (3 : Fin 6) voters5

noncomputable def fullProfile : Profile (Electorate (Fin 6) (Finset.univ)) (Fin 3) :=
  { pref := fun v => (ballots6 v.1).toLinearOrder }

noncomputable def profile5 : Profile (Electorate (Fin 6) voters5) (Fin 3) :=
  restrictElectorate fullProfile voters5 (by
    intro x hx; exact (Finset.mem_univ x))

noncomputable def profile6 : Profile (Electorate (Fin 6) voters6) (Fin 3) :=
  restrictElectorate fullProfile voters6 (by
    intro x hx; exact (Finset.mem_univ x))

lemma voters5_not_mem : (3 : Fin 6) ∉ voters5 := by
  simp [voters5]

lemma profiles_agree :
    ∀ v : Electorate (Fin 6) voters5,
      profile6.pref (liftVoter (u := (3 : Fin 6)) v) = profile5.pref v := by
  intro v
  simpa [profile5, profile6, voters6] using
    (restrictElectorate_agrees (Q := fullProfile) (S := voters5)
      (hS := by intro x hx; exact (Finset.mem_univ x))
      (u := (3 : Fin 6))
      (hSu := by intro x hx; exact (Finset.mem_univ x)) v)

lemma ballot120_top_1 : BallotTop ballot120.toLinearOrder (1 : Fin 3) := by
  intro x hx
  fin_cases x <;> simp [ballot120, ListBallot.lt_iff_idxOf, ListBallot.mk'] at hx ⊢

lemma newVoter_top_1 :
    BallotTop (profile6.pref (newVoter (u := (3 : Fin 6)) (V := voters5) voters5_not_mem))
      (1 : Fin 3) := by
  change BallotTop ballot120.toLinearOrder (1 : Fin 3)
  exact ballot120_top_1

lemma univ_fin3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by
  ext x
  fin_cases x <;> simp

lemma sum_univ_fin3 (f : Fin 3 → Int) :
    Finset.sum (s := (Finset.univ : Finset (Fin 3))) f = f 0 + f 1 + f 2 := by
  classical
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := univ_fin3
  simp [huniv, Finset.sum_insert, add_assoc]

lemma margin_eq_card_diff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) :
    margin P a b =
      Int.ofNat (votersPreferring P a b).card -
        Int.ofNat (votersPreferring P b a).card := by
  classical
  simp [margin, votersPreferring]

private lemma votersPreferring_profile5_eq_filter (x y : Fin 3) :
    votersPreferring profile5 x y =
      Finset.univ.filter (fun v => prefersInList (ballots6 v.1).ranking x y) := by
  ext v
  simp only [votersPreferring, Finset.mem_filter, Finset.mem_univ, true_and]
  change Prefers (profileOfListBallots ballots6) v.1 x y ↔ _
  exact prefers_iff_prefersInList ballots6 v.1 x y

private lemma votersPreferring_profile6_eq_filter (x y : Fin 3) :
    votersPreferring profile6 x y =
      Finset.univ.filter (fun v => prefersInList (ballots6 v.1).ranking x y) := by
  ext v
  simp only [votersPreferring, Finset.mem_filter, Finset.mem_univ, true_and]
  change Prefers (profileOfListBallots ballots6) v.1 x y ↔ _
  exact prefers_iff_prefersInList ballots6 v.1 x y

lemma votersPreferring_profile5_0_1 :
    votersPreferring profile5 (0 : Fin 3) (1 : Fin 3) =
      ({⟨0, by simp [voters5]⟩,
        ⟨1, by simp [voters5]⟩} :
        Finset (Electorate (Fin 6) voters5)) := by
  classical
  rw [votersPreferring_profile5_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters5, ballots6, ballot021, ballot102, ballot120, ballot210,
          prefersInList] at hmem ⊢; all_goals decide +revert)

lemma votersPreferring_profile5_1_0 :
    votersPreferring profile5 (1 : Fin 3) (0 : Fin 3) =
      ({⟨2, by simp [voters5]⟩,
        ⟨4, by simp [voters5]⟩,
        ⟨5, by simp [voters5]⟩} :
        Finset (Electorate (Fin 6) voters5)) := by
  classical
  rw [votersPreferring_profile5_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters5, ballots6, ballot021, ballot102, ballot120, ballot210,
          prefersInList] at hmem ⊢; all_goals decide +revert)

lemma votersPreferring_profile5_0_2 :
    votersPreferring profile5 (0 : Fin 3) (2 : Fin 3) =
      ({⟨0, by simp [voters5]⟩,
        ⟨1, by simp [voters5]⟩,
        ⟨2, by simp [voters5]⟩} :
        Finset (Electorate (Fin 6) voters5)) := by
  classical
  rw [votersPreferring_profile5_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters5, ballots6, ballot021, ballot102, ballot120, ballot210,
          prefersInList] at hmem ⊢; all_goals decide +revert)

lemma votersPreferring_profile5_2_0 :
    votersPreferring profile5 (2 : Fin 3) (0 : Fin 3) =
      ({⟨4, by simp [voters5]⟩,
        ⟨5, by simp [voters5]⟩} :
        Finset (Electorate (Fin 6) voters5)) := by
  classical
  rw [votersPreferring_profile5_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters5, ballots6, ballot021, ballot102, ballot120, ballot210,
          prefersInList] at hmem ⊢; all_goals decide +revert)

lemma votersPreferring_profile5_1_2 :
    votersPreferring profile5 (1 : Fin 3) (2 : Fin 3) =
      ({⟨2, by simp [voters5]⟩} :
        Finset (Electorate (Fin 6) voters5)) := by
  classical
  rw [votersPreferring_profile5_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters5, ballots6, ballot021, ballot102, ballot120, ballot210,
          prefersInList] at hmem ⊢; all_goals decide +revert)

lemma votersPreferring_profile5_2_1 :
    votersPreferring profile5 (2 : Fin 3) (1 : Fin 3) =
      ({⟨0, by simp [voters5]⟩,
        ⟨1, by simp [voters5]⟩,
        ⟨4, by simp [voters5]⟩,
        ⟨5, by simp [voters5]⟩} :
        Finset (Electorate (Fin 6) voters5)) := by
  classical
  rw [votersPreferring_profile5_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters5, ballots6, ballot021, ballot102, ballot120, ballot210,
          prefersInList] at hmem ⊢; all_goals decide +revert)

lemma votersPreferring_profile6_0_1 :
    votersPreferring profile6 (0 : Fin 3) (1 : Fin 3) =
      ({⟨0, by simp [voters6, voters5]⟩,
        ⟨1, by simp [voters6, voters5]⟩} :
        Finset (Electorate (Fin 6) voters6)) := by
  classical
  rw [votersPreferring_profile6_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters6, voters5, ballots6, ballot021, ballot102, ballot120, ballot210,
          prefersInList] at hmem ⊢; all_goals decide +revert)

lemma votersPreferring_profile6_1_0 :
    votersPreferring profile6 (1 : Fin 3) (0 : Fin 3) =
      ({⟨2, by simp [voters6, voters5]⟩,
        ⟨3, by simp [voters6, voters5]⟩,
        ⟨4, by simp [voters6, voters5]⟩,
        ⟨5, by simp [voters6, voters5]⟩} :
        Finset (Electorate (Fin 6) voters6)) := by
  classical
  rw [votersPreferring_profile6_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters6, voters5, ballots6, ballot021, ballot102, ballot120, ballot210,
          prefersInList] at hmem ⊢; all_goals decide +revert)

lemma votersPreferring_profile6_0_2 :
    votersPreferring profile6 (0 : Fin 3) (2 : Fin 3) =
      ({⟨0, by simp [voters6, voters5]⟩,
        ⟨1, by simp [voters6, voters5]⟩,
        ⟨2, by simp [voters6, voters5]⟩} :
        Finset (Electorate (Fin 6) voters6)) := by
  classical
  rw [votersPreferring_profile6_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters6, voters5, ballots6, ballot021, ballot102, ballot120, ballot210,
          prefersInList] at hmem ⊢; all_goals decide +revert)

lemma votersPreferring_profile6_2_0 :
    votersPreferring profile6 (2 : Fin 3) (0 : Fin 3) =
      ({⟨3, by simp [voters6, voters5]⟩,
        ⟨4, by simp [voters6, voters5]⟩,
        ⟨5, by simp [voters6, voters5]⟩} :
        Finset (Electorate (Fin 6) voters6)) := by
  classical
  rw [votersPreferring_profile6_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters6, voters5, ballots6, ballot021, ballot102, ballot120, ballot210,
          prefersInList] at hmem ⊢; all_goals decide +revert)

lemma votersPreferring_profile6_1_2 :
    votersPreferring profile6 (1 : Fin 3) (2 : Fin 3) =
      ({⟨2, by simp [voters6, voters5]⟩,
        ⟨3, by simp [voters6, voters5]⟩} :
        Finset (Electorate (Fin 6) voters6)) := by
  classical
  rw [votersPreferring_profile6_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters6, voters5, ballots6, ballot021, ballot102, ballot120, ballot210,
          prefersInList] at hmem ⊢; all_goals decide +revert)

lemma votersPreferring_profile6_2_1 :
    votersPreferring profile6 (2 : Fin 3) (1 : Fin 3) =
      ({⟨0, by simp [voters6, voters5]⟩,
        ⟨1, by simp [voters6, voters5]⟩,
        ⟨4, by simp [voters6, voters5]⟩,
        ⟨5, by simp [voters6, voters5]⟩} :
        Finset (Electorate (Fin 6) voters6)) := by
  classical
  rw [votersPreferring_profile6_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [voters6, voters5, ballots6, ballot021, ballot102, ballot120, ballot210,
          prefersInList] at hmem ⊢; all_goals decide +revert)

lemma margin_profile5_0_1_neg : margin profile5 (0 : Fin 3) (1 : Fin 3) < 0 := by
  have h1 : (votersPreferring profile5 (0 : Fin 3) (1 : Fin 3)).card = 2 := by
    simp [votersPreferring_profile5_0_1]
  have h2 : (votersPreferring profile5 (1 : Fin 3) (0 : Fin 3)).card = 3 := by
    simp [votersPreferring_profile5_1_0]
  have hmargin : margin profile5 (0 : Fin 3) (1 : Fin 3) = (-1 : Int) := by
    norm_num [margin_eq_card_diff, h1, h2]
  nlinarith [hmargin]

lemma margin_profile5_0_2_pos : margin profile5 (0 : Fin 3) (2 : Fin 3) > 0 := by
  have h1 : (votersPreferring profile5 (0 : Fin 3) (2 : Fin 3)).card = 3 := by
    simp [votersPreferring_profile5_0_2]
  have h2 : (votersPreferring profile5 (2 : Fin 3) (0 : Fin 3)).card = 2 := by
    simp [votersPreferring_profile5_2_0]
  have hmargin : margin profile5 (0 : Fin 3) (2 : Fin 3) = (1 : Int) := by
    norm_num [margin_eq_card_diff, h1, h2]
  nlinarith [hmargin]

lemma margin_profile5_1_2_neg : margin profile5 (1 : Fin 3) (2 : Fin 3) < 0 := by
  have h1 : (votersPreferring profile5 (1 : Fin 3) (2 : Fin 3)).card = 1 := by
    simp [votersPreferring_profile5_1_2]
  have h2 : (votersPreferring profile5 (2 : Fin 3) (1 : Fin 3)).card = 4 := by
    simp [votersPreferring_profile5_2_1]
  have hmargin : margin profile5 (1 : Fin 3) (2 : Fin 3) = (-3 : Int) := by
    norm_num [margin_eq_card_diff, h1, h2]
  nlinarith [hmargin]

lemma copelandScore2_profile5_0 : copelandScore2 profile5 (0 : Fin 3) = 3 := by
  have hsum :=
    sum_univ_fin3 (f := fun b => copelandPairScore2 (margin profile5 (0 : Fin 3) b))
  have h00 : copelandPairScore2 (margin profile5 (0 : Fin 3) (0 : Fin 3)) = 1 := by
    simp [copelandPairScore2, self_margin_zero]
  have h01 : copelandPairScore2 (margin profile5 (0 : Fin 3) (1 : Fin 3)) = 0 := by
    have hneg : margin profile5 (0 : Fin 3) (1 : Fin 3) < 0 :=
      margin_profile5_0_1_neg
    have hnotpos : ¬ margin profile5 (0 : Fin 3) (1 : Fin 3) > 0 :=
      not_lt_of_ge (le_of_lt hneg)
    have hne : margin profile5 (0 : Fin 3) (1 : Fin 3) ≠ 0 := ne_of_lt hneg
    simp [copelandPairScore2, hnotpos, hne]
  have h02 : copelandPairScore2 (margin profile5 (0 : Fin 3) (2 : Fin 3)) = 2 := by
    have hpos : margin profile5 (0 : Fin 3) (2 : Fin 3) > 0 :=
      margin_profile5_0_2_pos
    simp [copelandPairScore2, hpos]
  have hsum' :
      copelandScore2 profile5 (0 : Fin 3) =
        copelandPairScore2 (margin profile5 (0 : Fin 3) (0 : Fin 3)) +
          copelandPairScore2 (margin profile5 (0 : Fin 3) (1 : Fin 3)) +
          copelandPairScore2 (margin profile5 (0 : Fin 3) (2 : Fin 3)) := by
    simpa [copelandScore2] using hsum
  simp [hsum', h00, h01, h02]

lemma copelandScore2_profile5_1 : copelandScore2 profile5 (1 : Fin 3) = 3 := by
  have hsum :=
    sum_univ_fin3 (f := fun b => copelandPairScore2 (margin profile5 (1 : Fin 3) b))
  have h11 : copelandPairScore2 (margin profile5 (1 : Fin 3) (1 : Fin 3)) = 1 := by
    simp [copelandPairScore2, self_margin_zero]
  have h10 : copelandPairScore2 (margin profile5 (1 : Fin 3) (0 : Fin 3)) = 2 := by
    have hneg : margin profile5 (0 : Fin 3) (1 : Fin 3) < 0 :=
      margin_profile5_0_1_neg
    have hskew :
        margin profile5 (1 : Fin 3) (0 : Fin 3) =
          - margin profile5 (0 : Fin 3) (1 : Fin 3) := by
      simpa [skew_symmetric] using
        (margin_antisymmetric (P := profile5) (1 : Fin 3) (0 : Fin 3))
    have hpos : margin profile5 (1 : Fin 3) (0 : Fin 3) > 0 := by
      linarith [hskew, hneg]
    simp [copelandPairScore2, hpos]
  have h12 : copelandPairScore2 (margin profile5 (1 : Fin 3) (2 : Fin 3)) = 0 := by
    have hneg : margin profile5 (1 : Fin 3) (2 : Fin 3) < 0 :=
      margin_profile5_1_2_neg
    have hnotpos : ¬ margin profile5 (1 : Fin 3) (2 : Fin 3) > 0 :=
      not_lt_of_ge (le_of_lt hneg)
    have hne : margin profile5 (1 : Fin 3) (2 : Fin 3) ≠ 0 := ne_of_lt hneg
    simp [copelandPairScore2, hnotpos, hne]
  have hsum' :
      copelandScore2 profile5 (1 : Fin 3) =
        copelandPairScore2 (margin profile5 (1 : Fin 3) (0 : Fin 3)) +
          copelandPairScore2 (margin profile5 (1 : Fin 3) (1 : Fin 3)) +
          copelandPairScore2 (margin profile5 (1 : Fin 3) (2 : Fin 3)) := by
    simpa [copelandScore2, add_assoc, add_left_comm, add_comm] using hsum
  simp [hsum', h10, h11, h12]

lemma copelandScore2_profile5_2 : copelandScore2 profile5 (2 : Fin 3) = 3 := by
  have hsum :=
    sum_univ_fin3 (f := fun b => copelandPairScore2 (margin profile5 (2 : Fin 3) b))
  have h22 : copelandPairScore2 (margin profile5 (2 : Fin 3) (2 : Fin 3)) = 1 := by
    simp [copelandPairScore2, self_margin_zero]
  have h20 : copelandPairScore2 (margin profile5 (2 : Fin 3) (0 : Fin 3)) = 0 := by
    have hpos : margin profile5 (0 : Fin 3) (2 : Fin 3) > 0 :=
      margin_profile5_0_2_pos
    have hskew :
        margin profile5 (2 : Fin 3) (0 : Fin 3) =
          - margin profile5 (0 : Fin 3) (2 : Fin 3) := by
      simpa [skew_symmetric] using
        (margin_antisymmetric (P := profile5) (2 : Fin 3) (0 : Fin 3))
    have hneg : margin profile5 (2 : Fin 3) (0 : Fin 3) < 0 := by
      linarith [hskew, hpos]
    have hnotpos : ¬ margin profile5 (2 : Fin 3) (0 : Fin 3) > 0 :=
      not_lt_of_ge (le_of_lt hneg)
    have hne : margin profile5 (2 : Fin 3) (0 : Fin 3) ≠ 0 := ne_of_lt hneg
    simp [copelandPairScore2, hnotpos, hne]
  have h21 : copelandPairScore2 (margin profile5 (2 : Fin 3) (1 : Fin 3)) = 2 := by
    have hneg : margin profile5 (1 : Fin 3) (2 : Fin 3) < 0 :=
      margin_profile5_1_2_neg
    have hskew :
        margin profile5 (2 : Fin 3) (1 : Fin 3) =
          - margin profile5 (1 : Fin 3) (2 : Fin 3) := by
      simpa [skew_symmetric] using
        (margin_antisymmetric (P := profile5) (2 : Fin 3) (1 : Fin 3))
    have hpos : margin profile5 (2 : Fin 3) (1 : Fin 3) > 0 := by
      linarith [hskew, hneg]
    simp [copelandPairScore2, hpos]
  have hsum' :
      copelandScore2 profile5 (2 : Fin 3) =
        copelandPairScore2 (margin profile5 (2 : Fin 3) (0 : Fin 3)) +
          copelandPairScore2 (margin profile5 (2 : Fin 3) (1 : Fin 3)) +
          copelandPairScore2 (margin profile5 (2 : Fin 3) (2 : Fin 3)) := by
    simpa [copelandScore2] using hsum
  simp [hsum', h20, h21, h22]

lemma copelandMaxScore2_profile5 : copelandMaxScore2 profile5 = 3 := by
  classical
  have hA : (Finset.univ : Finset (Fin 3)).Nonempty := by simp
  let scores : Finset Int := Finset.univ.image (fun a => copelandScore2 profile5 a)
  have hScores : scores.Nonempty := hA.image (fun a => copelandScore2 profile5 a)
  have hmem : (3 : Int) ∈ scores := by
    refine Finset.mem_image.mpr ?_
    exact ⟨0, by simp, copelandScore2_profile5_0⟩
  have hmax_le : Finset.max' scores hScores ≤ (3 : Int) := by
    refine (Finset.max'_le_iff _ _).2 ?_
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨a, _ha, rfl⟩
    fin_cases a <;> simp [copelandScore2_profile5_0, copelandScore2_profile5_1,
      copelandScore2_profile5_2]
  have hle_max : (3 : Int) ≤ Finset.max' scores hScores :=
    Finset.le_max' _ _ hmem
  have hmax_eq : Finset.max' scores hScores = (3 : Int) := le_antisymm hmax_le hle_max
  simp [copelandMaxScore2, hA, scores, hmax_eq]

lemma copelandScore2_profile6_0_1_neg : margin profile6 (0 : Fin 3) (1 : Fin 3) < 0 := by
  have h1 : (votersPreferring profile6 (0 : Fin 3) (1 : Fin 3)).card = 2 := by
    simp [votersPreferring_profile6_0_1]
  have h2 : (votersPreferring profile6 (1 : Fin 3) (0 : Fin 3)).card = 4 := by
    simp [votersPreferring_profile6_1_0]
  have hmargin : margin profile6 (0 : Fin 3) (1 : Fin 3) = (-2 : Int) := by
    norm_num [margin_eq_card_diff, h1, h2]
  nlinarith [hmargin]

lemma copelandScore2_profile6_0_2_eq : margin profile6 (0 : Fin 3) (2 : Fin 3) = 0 := by
  have h1 : (votersPreferring profile6 (0 : Fin 3) (2 : Fin 3)).card = 3 := by
    simp [votersPreferring_profile6_0_2]
  have h2 : (votersPreferring profile6 (2 : Fin 3) (0 : Fin 3)).card = 3 := by
    simp [votersPreferring_profile6_2_0]
  norm_num [margin_eq_card_diff, h1, h2]

lemma copelandScore2_profile6_1_2_neg : margin profile6 (1 : Fin 3) (2 : Fin 3) < 0 := by
  have h1 : (votersPreferring profile6 (1 : Fin 3) (2 : Fin 3)).card = 2 := by
    simp [votersPreferring_profile6_1_2]
  have h2 : (votersPreferring profile6 (2 : Fin 3) (1 : Fin 3)).card = 4 := by
    simp [votersPreferring_profile6_2_1]
  have hmargin : margin profile6 (1 : Fin 3) (2 : Fin 3) = (-2 : Int) := by
    norm_num [margin_eq_card_diff, h1, h2]
  nlinarith [hmargin]

lemma copelandScore2_profile6_1 : copelandScore2 profile6 (1 : Fin 3) = 3 := by
  have hsum :=
    sum_univ_fin3 (f := fun b => copelandPairScore2 (margin profile6 (1 : Fin 3) b))
  have h11 : copelandPairScore2 (margin profile6 (1 : Fin 3) (1 : Fin 3)) = 1 := by
    simp [copelandPairScore2, self_margin_zero]
  have h10 : copelandPairScore2 (margin profile6 (1 : Fin 3) (0 : Fin 3)) = 2 := by
    have hneg : margin profile6 (0 : Fin 3) (1 : Fin 3) < 0 :=
      copelandScore2_profile6_0_1_neg
    have hskew :
        margin profile6 (1 : Fin 3) (0 : Fin 3) =
          - margin profile6 (0 : Fin 3) (1 : Fin 3) := by
      simpa [skew_symmetric] using
        (margin_antisymmetric (P := profile6) (1 : Fin 3) (0 : Fin 3))
    have hpos : margin profile6 (1 : Fin 3) (0 : Fin 3) > 0 := by
      linarith [hskew, hneg]
    simp [copelandPairScore2, hpos]
  have h12 : copelandPairScore2 (margin profile6 (1 : Fin 3) (2 : Fin 3)) = 0 := by
    have hneg : margin profile6 (1 : Fin 3) (2 : Fin 3) < 0 :=
      copelandScore2_profile6_1_2_neg
    have hnotpos : ¬ margin profile6 (1 : Fin 3) (2 : Fin 3) > 0 :=
      not_lt_of_ge (le_of_lt hneg)
    have hne : margin profile6 (1 : Fin 3) (2 : Fin 3) ≠ 0 := ne_of_lt hneg
    simp [copelandPairScore2, hnotpos, hne]
  have hsum' :
      copelandScore2 profile6 (1 : Fin 3) =
        copelandPairScore2 (margin profile6 (1 : Fin 3) (0 : Fin 3)) +
          copelandPairScore2 (margin profile6 (1 : Fin 3) (1 : Fin 3)) +
          copelandPairScore2 (margin profile6 (1 : Fin 3) (2 : Fin 3)) := by
    simpa [copelandScore2, add_assoc, add_left_comm, add_comm] using hsum
  simp [hsum', h10, h11, h12]

lemma copelandScore2_profile6_2 : copelandScore2 profile6 (2 : Fin 3) = 4 := by
  have hsum :=
    sum_univ_fin3 (f := fun b => copelandPairScore2 (margin profile6 (2 : Fin 3) b))
  have h22 : copelandPairScore2 (margin profile6 (2 : Fin 3) (2 : Fin 3)) = 1 := by
    simp [copelandPairScore2, self_margin_zero]
  have h20 : copelandPairScore2 (margin profile6 (2 : Fin 3) (0 : Fin 3)) = 1 := by
    have hzero : margin profile6 (0 : Fin 3) (2 : Fin 3) = 0 :=
      copelandScore2_profile6_0_2_eq
    have hskew :
        margin profile6 (2 : Fin 3) (0 : Fin 3) =
          - margin profile6 (0 : Fin 3) (2 : Fin 3) := by
      simpa [skew_symmetric] using
        (margin_antisymmetric (P := profile6) (2 : Fin 3) (0 : Fin 3))
    have hzero' : margin profile6 (2 : Fin 3) (0 : Fin 3) = 0 := by
      simp [hskew, hzero]
    simp [copelandPairScore2, hzero']
  have h21 : copelandPairScore2 (margin profile6 (2 : Fin 3) (1 : Fin 3)) = 2 := by
    have hneg : margin profile6 (1 : Fin 3) (2 : Fin 3) < 0 :=
      copelandScore2_profile6_1_2_neg
    have hskew :
        margin profile6 (2 : Fin 3) (1 : Fin 3) =
          - margin profile6 (1 : Fin 3) (2 : Fin 3) := by
      simpa [skew_symmetric] using
        (margin_antisymmetric (P := profile6) (2 : Fin 3) (1 : Fin 3))
    have hpos : margin profile6 (2 : Fin 3) (1 : Fin 3) > 0 := by
      linarith [hskew, hneg]
    simp [copelandPairScore2, hpos]
  have hsum' :
      copelandScore2 profile6 (2 : Fin 3) =
        copelandPairScore2 (margin profile6 (2 : Fin 3) (0 : Fin 3)) +
          copelandPairScore2 (margin profile6 (2 : Fin 3) (1 : Fin 3)) +
          copelandPairScore2 (margin profile6 (2 : Fin 3) (2 : Fin 3)) := by
    simpa [copelandScore2, add_assoc, add_left_comm, add_comm] using hsum
  simp [hsum', h20, h21, h22]

end CopelandPositiveInvolvementCounterexample

open CopelandPositiveInvolvementCounterexample

theorem copeland_not_positiveInvolvement : ¬ PositiveInvolvement copeland := by
  intro hpos
  classical
  have hmem5 : (1 : Fin 3) ∈ copeland profile5 := by
    have hnonempty : Nonempty (Fin 3) := ⟨0⟩
    simp [copeland, hnonempty, copelandMaxScore2_profile5, copelandScore2_profile5_1]
  have hmem : (1 : Fin 3) ∈ copeland profile6 := by
    exact hpos (V := voters5) (u := (3 : Fin 6)) (hu := voters5_not_mem)
      (P := profile5) (Q := profile6) (c := (1 : Fin 3))
      profiles_agree hmem5 newVoter_top_1
  have hlt : copelandScore2 profile6 (1 : Fin 3) < copelandMaxScore2 profile6 := by
    have hA : (Finset.univ : Finset (Fin 3)).Nonempty := by simp
    let scores : Finset Int := Finset.univ.image (fun a => copelandScore2 profile6 a)
    have hScores : scores.Nonempty := hA.image (fun a => copelandScore2 profile6 a)
    have hmem2 : copelandScore2 profile6 (2 : Fin 3) ∈ scores := by
      exact Finset.mem_image.mpr ⟨2, by simp, rfl⟩
    have hle_max : copelandScore2 profile6 (2 : Fin 3) ≤ copelandMaxScore2 profile6 := by
      have hle' : copelandScore2 profile6 (2 : Fin 3) ≤ Finset.max' scores hScores :=
        Finset.le_max' _ _ hmem2
      have hmax_eq : copelandMaxScore2 profile6 = Finset.max' scores hScores := by
        simp [copelandMaxScore2, hA, scores]
      simpa [hmax_eq] using hle'
    have hlt' : copelandScore2 profile6 (1 : Fin 3) < copelandScore2 profile6 (2 : Fin 3) := by
      simp [copelandScore2_profile6_1, copelandScore2_profile6_2]
    exact lt_of_lt_of_le hlt' hle_max
  have hEq : copelandScore2 profile6 (1 : Fin 3) = copelandMaxScore2 profile6 := by
    have hnonempty : Nonempty (Fin 3) := ⟨0⟩
    have : (1 : Fin 3) ∈
        Finset.univ.filter (fun a => copelandScore2 profile6 a = copelandMaxScore2 profile6) := by
      simpa [copeland, hnonempty] using hmem
    exact (Finset.mem_filter.mp this).2
  linarith

end SocialChoice
