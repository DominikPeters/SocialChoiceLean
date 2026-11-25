import Mathlib.Data.Finset.Max
import SocialChoice.Axioms.Neutrality
import SocialChoice.Rules.Minimax.Defs

namespace SocialChoice

open Finset

lemma maxLoss_permuteCandidates {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) (a : A) :
    maxLoss (V := V) (A := A) (permuteCandidates P σ) (σ a) = maxLoss P a := by
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · have hlosses :
        (Finset.univ.image (fun b => margin P (σ.symm b) a)) =
          Finset.univ.image (fun b => margin P b a) := by
      ext m
      constructor
      · intro hm
        rcases Finset.mem_image.mp hm with ⟨b, _hb, rfl⟩
        refine Finset.mem_image.mpr ⟨σ.symm b, by simp, rfl⟩
      · intro hm
        rcases Finset.mem_image.mp hm with ⟨b, _hb, rfl⟩
        refine Finset.mem_image.mpr ⟨σ b, by simp, by simp⟩
    simp [maxLoss, hA, margin_permuteCandidates, hlosses]
  · simp [maxLoss, hA]

lemma minimaxScore_permuteCandidates {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) :
    minimaxScore (V := V) (A := A) (permuteCandidates P σ) = minimaxScore P := by
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · have hscores :
        (Finset.univ.image (fun a => maxLoss (V := V) (A := A) (permuteCandidates P σ) a)) =
          Finset.univ.image (fun a => maxLoss (V := V) (A := A) P a) := by
      ext m
      constructor
      · intro hm
        rcases Finset.mem_image.mp hm with ⟨a, _ha, rfl⟩
        refine Finset.mem_image.mpr ⟨σ.symm a, by simp, ?_⟩
        simpa using
          (maxLoss_permuteCandidates (P := P) (σ := σ) (a := σ.symm a)).symm
      · intro hm
        rcases Finset.mem_image.mp hm with ⟨a, _ha, rfl⟩
        refine Finset.mem_image.mpr ⟨σ a, by simp, ?_⟩
        simpa using (maxLoss_permuteCandidates (P := P) (σ := σ) (a := a))
    simp [minimaxScore, hA, hscores]
  · simp [minimaxScore, hA]

theorem minimax_neutral : Neutrality minimax := by
  intro V A _ _ P σ
  classical
  by_cases hA : Nonempty A
  · let : Nonempty A := hA
    apply Finset.ext
    intro c
    constructor
    · intro hc
      dsimp [permuteWinners] at hc
      rcases Finset.mem_map.mp hc with ⟨a, ha, rfl⟩
      have ha' :
          a ∈ Finset.univ.filter (fun a : A => maxLoss P a = minimaxScore P) := by
        simpa [minimax, hA] using ha
      have hEq : maxLoss P a = minimaxScore P := (Finset.mem_filter.mp ha').2
      have hmem :
          σ a ∈
            Finset.univ.filter
              (fun x : A =>
                maxLoss (permuteCandidates P σ) x =
                  minimaxScore (permuteCandidates P σ)) := by
        refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
        calc
          maxLoss (permuteCandidates P σ) (σ a) = maxLoss P a := by
            simpa using (maxLoss_permuteCandidates (P := P) (σ := σ) (a := a))
          _ = minimaxScore P := hEq
          _ = minimaxScore (permuteCandidates P σ) := by
            symm
            simpa using (minimaxScore_permuteCandidates (P := P) (σ := σ))
      simpa [minimax, hA] using hmem
    · intro hc
      have hc' :
          c ∈
            Finset.univ.filter
              (fun x : A =>
                maxLoss (permuteCandidates P σ) x =
                  minimaxScore (permuteCandidates P σ)) := by
        simpa [minimax, hA] using hc
      have hEq :
          maxLoss (permuteCandidates P σ) c =
            minimaxScore (permuteCandidates P σ) := (Finset.mem_filter.mp hc').2
      have hEq' : maxLoss P (σ.symm c) = minimaxScore P := by
        calc
          maxLoss P (σ.symm c) = maxLoss (permuteCandidates P σ) c := by
            simpa using
              (maxLoss_permuteCandidates (P := P) (σ := σ) (a := σ.symm c)).symm
          _ = minimaxScore (permuteCandidates P σ) := hEq
          _ = minimaxScore P := by
            simpa using (minimaxScore_permuteCandidates (P := P) (σ := σ))
      have hmem :
          σ.symm c ∈ Finset.univ.filter (fun a : A => maxLoss P a = minimaxScore P) := by
        exact Finset.mem_filter.mpr ⟨by simp, hEq'⟩
      have hmem' : σ.symm c ∈ minimax P := by
        simpa [minimax, hA] using hmem
      have : c ∈ (minimax P).map σ.toEmbedding := by
        exact Finset.mem_map.mpr ⟨σ.symm c, hmem', by simp⟩
      simpa [permuteWinners] using this
  · simp [minimax, hA, permuteWinners]

end SocialChoice
