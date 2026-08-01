import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import SocialChoice.Profile
import SocialChoice.Margin
import SocialChoice.ArgExtrema
import SocialChoice.Meta

namespace SocialChoice

open Finset

section Copeland

variable {V A : Type} [Fintype V] [Fintype A]

/-- Double the usual Copeland score to avoid fractions: win = 2, tie = 1, loss = 0. -/
def copelandPairScore2 (m : Int) : Int :=
  if m > 0 then 2 else if m = 0 then 1 else 0

lemma copelandPairScore2_le_two (m : Int) : copelandPairScore2 m ≤ 2 := by
  by_cases hpos : m > 0
  · simp [copelandPairScore2, hpos]
  · by_cases hzero : m = 0
    · simp [copelandPairScore2, hzero]
    · simp [copelandPairScore2, hpos, hzero]

lemma copelandPairScore2_nonneg (m : Int) : 0 ≤ copelandPairScore2 m := by
  by_cases hpos : m > 0
  · simp [copelandPairScore2, hpos]
  · by_cases hzero : m = 0
    · simp [copelandPairScore2, hzero]
    · simp [copelandPairScore2, hpos, hzero]

lemma copelandPairScore2_mono {m n : Int} (h : m ≤ n) :
    copelandPairScore2 m ≤ copelandPairScore2 n := by
  by_cases hnpos : n > 0
  · have hle : copelandPairScore2 m ≤ 2 := copelandPairScore2_le_two m
    have hscore : copelandPairScore2 n = 2 := by
      simp [copelandPairScore2, hnpos]
    simpa [hscore] using hle
  · have hnle : n ≤ 0 := not_lt.mp hnpos
    by_cases hnzero : n = 0
    · have hmle : m ≤ 0 := le_trans h hnle
      have hmpos : ¬ m > 0 := not_lt_of_ge hmle
      by_cases hmzero : m = 0
      · simp [copelandPairScore2, hnzero, hmzero]
      · have hleft : copelandPairScore2 m = 0 := by
          simp [copelandPairScore2, hmpos, hmzero]
        have hright : copelandPairScore2 n = 1 := by
          simp [copelandPairScore2, hnzero]
        simp [hleft, hright]
    · have hnneg : n < 0 := lt_of_le_of_ne hnle hnzero
      have hmneg : m < 0 := lt_of_le_of_lt h hnneg
      have hmpos : ¬ m > 0 := not_lt_of_ge (le_of_lt hmneg)
      have hmzero : m ≠ 0 := ne_of_lt hmneg
      have hnpos' : ¬ n > 0 := hnpos
      have hnzero' : n ≠ 0 := hnzero
      simp [copelandPairScore2, hmpos, hmzero, hnpos', hnzero']

/-- Copeland score for a candidate, using doubled points. -/
noncomputable def copelandScore2 (P : Profile V A) (a : A) : Int := by
  classical
  exact Finset.sum Finset.univ (fun b => copelandPairScore2 (margin P a b))

/-- Maximum Copeland score (doubled) in a profile. -/
noncomputable def copelandMaxScore2 (P : Profile V A) : Int := by
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · let scores : Finset Int := Finset.univ.image (fun a => copelandScore2 P a)
    have hScores : scores.Nonempty := hA.image (fun a => copelandScore2 P a)
    exact Finset.max' scores hScores
  · exact 0

@[scRule]
noncomputable def copeland : VotingRule := by
  intro V A _ _ P
  classical
  if hA : Nonempty A then
    let maxScore := copelandMaxScore2 (V := V) (A := A) P
    exact Finset.univ.filter (fun a => copelandScore2 P a = maxScore)
  else
    exact ∅

/-- `copeland` is an instance of the generic `argmaxSet`. -/
lemma copeland_eq_argmaxSet {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) :
    copeland P = argmaxSet Finset.univ (copelandScore2 P) := by
  classical
  unfold copeland argmaxSet
  by_cases hA : Nonempty A
  · have hAuniv : (Finset.univ : Finset A).Nonempty := Finset.univ_nonempty
    simp [hA, hAuniv, copelandMaxScore2]
  · have hAuniv : ¬ (Finset.univ : Finset A).Nonempty := by
      rintro ⟨a, -⟩
      exact hA ⟨a⟩
    simp [hA, hAuniv]

theorem copeland_isVotingRule : IsVotingRule copeland := by
  intro V A _ _ _ P
  show (copeland P).Nonempty
  rw [copeland_eq_argmaxSet]
  exact argmaxSet_nonempty Finset.univ_nonempty _

end Copeland

end SocialChoice
