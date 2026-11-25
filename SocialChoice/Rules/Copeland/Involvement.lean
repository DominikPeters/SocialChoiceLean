import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Participation
import SocialChoice.ListBallot
import SocialChoice.Rules.Copeland.Defs

namespace SocialChoice

open Finset

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
  profileOfListBallots (fun v => ballots6 v.1)

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

private lemma profile5_eq : profile5 = profileOfListBallots (fun v => ballots6 v.1) := rfl

private lemma profile6_eq : profile6 = profileOfListBallots (fun v => ballots6 v.1) := rfl

lemma copelandScore2_profile5 (a : Fin 3) : copelandScore2 profile5 a = 3 := by
  simp only [copelandScore2, Fin.sum_univ_three, profile5_eq, margin_profileOfListBallots]
  revert a
  decide

lemma copelandMaxScore2_profile5 : copelandMaxScore2 profile5 = 3 := by
  classical
  have hA : (Finset.univ : Finset (Fin 3)).Nonempty := by simp
  let scores : Finset Int := Finset.univ.image (fun a => copelandScore2 profile5 a)
  have hScores : scores.Nonempty := hA.image (fun a => copelandScore2 profile5 a)
  have hmem : (3 : Int) ∈ scores := by
    refine Finset.mem_image.mpr ?_
    exact ⟨0, by simp, copelandScore2_profile5 0⟩
  have hmax_le : Finset.max' scores hScores ≤ (3 : Int) := by
    refine (Finset.max'_le_iff _ _).2 ?_
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨a, _ha, rfl⟩
    simp [copelandScore2_profile5]
  have hle_max : (3 : Int) ≤ Finset.max' scores hScores :=
    Finset.le_max' _ _ hmem
  have hmax_eq : Finset.max' scores hScores = (3 : Int) := le_antisymm hmax_le hle_max
  simp [copelandMaxScore2, hA, scores, hmax_eq]

lemma copelandScore2_profile6_1 : copelandScore2 profile6 (1 : Fin 3) = 3 := by
  simp only [copelandScore2, Fin.sum_univ_three, profile6_eq, margin_profileOfListBallots]
  decide

lemma copelandScore2_profile6_2 : copelandScore2 profile6 (2 : Fin 3) = 4 := by
  simp only [copelandScore2, Fin.sum_univ_three, profile6_eq, margin_profileOfListBallots]
  decide

end CopelandPositiveInvolvementCounterexample

open CopelandPositiveInvolvementCounterexample

theorem copeland_not_positiveInvolvement : ¬ PositiveInvolvement copeland := by
  intro hpos
  classical
  have hmem5 : (1 : Fin 3) ∈ copeland profile5 := by
    have hnonempty : Nonempty (Fin 3) := ⟨0⟩
    simp [copeland, hnonempty, copelandMaxScore2_profile5, copelandScore2_profile5]
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
