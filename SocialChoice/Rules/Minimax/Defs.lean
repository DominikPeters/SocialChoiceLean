import Mathlib.Data.Finset.Basic
import SocialChoice.Profile
import SocialChoice.Margin
import SocialChoice.ArgExtrema
import SocialChoice.Meta

namespace SocialChoice

open Finset

section Minimax

variable {V A : Type} [Fintype V] [Fintype A]

noncomputable def maxLoss (P : Profile V A) (a : A) : Int := by
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · let losses := Finset.univ.image (fun b => margin P b a)
    have hLosses : losses.Nonempty := by
      rcases hA with ⟨b, hb⟩
      exact ⟨margin P b a, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩
    exact Finset.max' losses hLosses
  · exact 0

noncomputable def minimaxScore (P : Profile V A) : Int := by
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · let scores := Finset.univ.image (fun a => maxLoss P a)
    have hScores : scores.Nonempty := by
      rcases hA with ⟨a, ha⟩
      exact ⟨maxLoss P a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
    exact Finset.min' scores hScores
  · exact 0

lemma margin_le_maxLoss (P : Profile V A) (a b : A) :
    margin P b a ≤ maxLoss P a := by
  classical
  have hA : (Finset.univ : Finset A).Nonempty := ⟨a, Finset.mem_univ a⟩
  set losses : Finset Int := Finset.univ.image (fun c => margin P c a)
  have hLosses : losses.Nonempty := by
    exact ⟨margin P b a, Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩⟩
  have hmem : margin P b a ∈ losses := by
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩
  have hle : margin P b a ≤ Finset.max' losses hLosses := Finset.le_max' _ _ hmem
  have hdef : maxLoss P a = Finset.max' losses hLosses := by
    simp [maxLoss, hA, losses]
  simpa [hdef] using hle

lemma maxLoss_le_of_forall_margin_le (P : Profile V A) (a : A) (k : Int)
    (h : ∀ b, margin P b a ≤ k) : maxLoss P a ≤ k := by
  classical
  have hA : (Finset.univ : Finset A).Nonempty := ⟨a, Finset.mem_univ a⟩
  set losses : Finset Int := Finset.univ.image (fun b => margin P b a)
  have hLosses : losses.Nonempty := by
    exact ⟨margin P a a, Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩
  have hle : ∀ x ∈ losses, x ≤ k := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨b, _, rfl⟩
    exact h b
  have hmax : Finset.max' losses hLosses ≤ k :=
    (Finset.max'_le_iff _ _).2 hle
  have hdef : maxLoss P a = Finset.max' losses hLosses := by
    simp [maxLoss, hA, losses]
  simpa [hdef] using hmax

lemma minimaxScore_le_of_candidate (P : Profile V A) (a : A) :
    minimaxScore P ≤ maxLoss P a := by
  classical
  have hA : (Finset.univ : Finset A).Nonempty := ⟨a, Finset.mem_univ a⟩
  set scores : Finset Int := Finset.univ.image (fun a => maxLoss P a)
  have hScores : scores.Nonempty := by
    exact ⟨maxLoss P a, Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩
  have hdef : minimaxScore P = Finset.min' scores hScores := by
    simp [minimaxScore, hA, scores]
  have hmem : maxLoss P a ∈ scores :=
    Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
  have hle : Finset.min' scores hScores ≤ maxLoss P a :=
    Finset.min'_le (s := scores) (x := maxLoss P a) (H2 := hmem)
  simpa [hdef] using hle

lemma le_minimaxScore_of_forall (P : Profile V A) (k : Int)
    (hA : (Finset.univ : Finset A).Nonempty)
    (h : ∀ a, k ≤ maxLoss P a) : k ≤ minimaxScore P := by
  classical
  set scores : Finset Int := Finset.univ.image (fun a => maxLoss P a)
  have hScores : scores.Nonempty := by
    rcases hA with ⟨a, ha⟩
    exact ⟨maxLoss P a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
  have hdef : minimaxScore P = Finset.min' scores hScores := by
    simp [minimaxScore, hA, scores]
  have hle : k ≤ Finset.min' scores hScores := by
    refine Finset.le_min' (s := scores) (H := hScores) (x := k) ?_
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨a, _, rfl⟩
    exact h a
  simpa [hdef] using hle

@[scRule]
noncomputable def minimax : VotingRule := by
  intro V A _ _ P
  classical
  if Nonempty A then
    let minScore := minimaxScore P
    exact Finset.univ.filter (fun a => maxLoss P a = minScore)
  else
    exact ∅

/-- `minimax` is an instance of the generic `argminSet`. -/
lemma minimax_eq_argminSet {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) :
    minimax P = argminSet Finset.univ (maxLoss P) := by
  classical
  unfold minimax argminSet
  by_cases hA : Nonempty A
  · have hAuniv : (Finset.univ : Finset A).Nonempty := Finset.univ_nonempty
    simp [hA, hAuniv, minimaxScore]
  · have hAuniv : ¬ (Finset.univ : Finset A).Nonempty := by
      rintro ⟨a, -⟩
      exact hA ⟨a⟩
    simp [hA, hAuniv]

theorem minimax_isVotingRule : IsVotingRule minimax := by
  intro V A _ _ _ P
  show (minimax P).Nonempty
  rw [minimax_eq_argminSet]
  exact argminSet_nonempty Finset.univ_nonempty _

end Minimax

end SocialChoice
