import Mathlib.Data.Finset.Basic
import SocialChoice.Profile
import SocialChoice.Margin
import SocialChoice.ArgExtrema
import SocialChoice.Meta

namespace SocialChoice

/-- The defensible set of a profile: `x` wins iff every pairwise attack on `x`
is matched by a counter-attack that is at least as strong, i.e. for every `y`
there is some `z` with `margin P z y ≥ margin P y x`. (For non-attackers `y`,
with `margin P y x ≤ 0`, the condition holds trivially via `z := y`.) -/
noncomputable def defensibleSetOf {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) : Finset A := by
  classical
  exact Finset.univ.filter (fun x => ∀ y, ∃ z, margin P z y ≥ margin P y x)

lemma mem_defensibleSetOf_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x : A) :
    x ∈ defensibleSetOf P ↔ ∀ y, ∃ z, margin P z y ≥ margin P y x := by
  classical
  simp [defensibleSetOf]

@[scRule]
noncomputable def defensibleSet : VotingRule := by
  intro V A _ _ P
  classical
  exact defensibleSetOf P

/-- The defensible set is nonempty: any candidate minimizing the maximal
incoming margin (i.e. any minimax winner) is defensible. -/
theorem defensibleSet_isVotingRule : IsVotingRule defensibleSet := by
  intro V A _ _ _ P
  classical
  show (defensibleSetOf P).Nonempty
  have hA : (Finset.univ : Finset A).Nonempty := Finset.univ_nonempty
  -- pick a candidate minimizing the maximal incoming margin (a minimax winner)
  obtain ⟨x, hx⟩ := argminSet_nonempty hA
    (fun a => (Finset.univ.image (fun z => margin P z a)).max' (hA.image _))
  rcases mem_argminSet_iff.mp hx with ⟨-, hxmin⟩
  refine ⟨x, (mem_defensibleSetOf_iff P x).2 ?_⟩
  intro y
  obtain ⟨z, -, hz⟩ := Finset.mem_image.mp
    (Finset.max'_mem (Finset.univ.image (fun z => margin P z y)) (hA.image _))
  refine ⟨z, ?_⟩
  have h1 : margin P y x ≤
      (Finset.univ.image (fun z => margin P z x)).max' (hA.image _) :=
    Finset.le_max' _ _ (Finset.mem_image_of_mem (fun z => margin P z x) (Finset.mem_univ y))
  have h2 := hxmin y (Finset.mem_univ y)
  rw [ge_iff_le, hz]
  exact le_trans h1 h2

end SocialChoice
