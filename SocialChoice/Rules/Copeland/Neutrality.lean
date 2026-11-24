import Mathlib.Data.Finset.Max
import SocialChoice.Axioms.Neutrality
import SocialChoice.Rules.Copeland.Defs
import SocialChoice.Margin

namespace SocialChoice

open Finset

lemma copelandScore2_permuteCandidates {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) (a : A) :
    copelandScore2 (V := V) (A := A) (permuteCandidates P σ) (σ a) = copelandScore2 P a := by
  classical
  have hsum :
      Finset.sum (s := (Finset.univ : Finset A))
        (fun b => copelandPairScore2 (margin P a (σ.symm b))) =
        Finset.sum (s := (Finset.univ : Finset A))
          (fun b => copelandPairScore2 (margin P a b)) := by
    refine Finset.sum_equiv (s := Finset.univ) (t := Finset.univ) (e := σ.symm) ?_ ?_
    · intro i
      simp
    · intro i hi
      rfl
  dsimp [copelandScore2]
  simpa [margin_permuteCandidates] using hsum

lemma copelandMaxScore2_permuteCandidates {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) :
    copelandMaxScore2 (V := V) (A := A) (permuteCandidates P σ) = copelandMaxScore2 P := by
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · have hscores :
        (Finset.univ.image (fun a => copelandScore2 (V := V) (A := A)
          (permuteCandidates P σ) a)) =
          (Finset.univ.image (fun a => copelandScore2 P a)) := by
      ext m
      constructor
      · intro hm
        rcases Finset.mem_image.mp hm with ⟨a, _ha, rfl⟩
        refine Finset.mem_image.mpr ⟨σ.symm a, by simp, ?_⟩
        simpa using
          (copelandScore2_permuteCandidates (P := P) (σ := σ) (a := σ.symm a)).symm
      · intro hm
        rcases Finset.mem_image.mp hm with ⟨a, _ha, rfl⟩
        refine Finset.mem_image.mpr ⟨σ a, by simp, ?_⟩
        simpa using (copelandScore2_permuteCandidates (P := P) (σ := σ) (a := a))
    simp [copelandMaxScore2, hA, hscores]
  · simp [copelandMaxScore2, hA]

theorem copeland_neutral : Neutrality copeland := by
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
          a ∈ Finset.univ.filter (fun a : A => copelandScore2 P a = copelandMaxScore2 P) := by
        simpa [copeland, hA] using ha
      have hEq : copelandScore2 P a = copelandMaxScore2 P := (Finset.mem_filter.mp ha').2
      have hmem :
          σ a ∈
            Finset.univ.filter
              (fun x : A =>
                copelandScore2 (permuteCandidates P σ) x =
                  copelandMaxScore2 (permuteCandidates P σ)) := by
        refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
        calc
          copelandScore2 (permuteCandidates P σ) (σ a) = copelandScore2 P a := by
            simpa using (copelandScore2_permuteCandidates (P := P) (σ := σ) (a := a))
          _ = copelandMaxScore2 P := hEq
          _ = copelandMaxScore2 (permuteCandidates P σ) := by
            symm
            exact copelandMaxScore2_permuteCandidates (P := P) (σ := σ)
      simpa [copeland, hA] using hmem
    · intro hc
      have hc' :
          c ∈
            Finset.univ.filter
              (fun x : A =>
                copelandScore2 (permuteCandidates P σ) x =
                  copelandMaxScore2 (permuteCandidates P σ)) := by
        simpa [copeland, hA] using hc
      have hEq :
          copelandScore2 (permuteCandidates P σ) c =
            copelandMaxScore2 (permuteCandidates P σ) := (Finset.mem_filter.mp hc').2
      have hEq' : copelandScore2 P (σ.symm c) = copelandMaxScore2 P := by
        calc
          copelandScore2 P (σ.symm c) = copelandScore2 (permuteCandidates P σ) c := by
            simpa using
              (copelandScore2_permuteCandidates (P := P) (σ := σ) (a := σ.symm c)).symm
          _ = copelandMaxScore2 (permuteCandidates P σ) := hEq
          _ = copelandMaxScore2 P := by
            exact copelandMaxScore2_permuteCandidates (P := P) (σ := σ)
      have hmem :
          σ.symm c ∈ Finset.univ.filter (fun a : A => copelandScore2 P a = copelandMaxScore2 P) :=
        Finset.mem_filter.mpr ⟨by simp, hEq'⟩
      have hmem' : σ.symm c ∈ copeland P := by
        simpa [copeland, hA] using hmem
      have : c ∈ (copeland P).map σ.toEmbedding := by
        exact Finset.mem_map.mpr ⟨σ.symm c, hmem', by simp⟩
      simpa [permuteWinners] using this
  · simp [copeland, hA, permuteWinners]

end SocialChoice
