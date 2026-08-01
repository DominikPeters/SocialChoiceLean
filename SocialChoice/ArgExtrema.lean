import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Image

/-!
# Argmax / argmin sets

Shared machinery for "the set of elements of a `Finset` maximizing (resp.
minimizing) a function". Most voting rules in this library are of this shape:
scoring winners maximize a score, elimination rules remove minimizers, Copeland
maximizes the Copeland score, Minimax minimizes the maximal loss, and so on.

The definitional pattern (`by_cases` on nonemptiness, then `filter` against
`max'`/`min'` of the image) is kept identical to the historical per-rule
definitions, so per-rule bridge equations of the form
`scoringWinners P score = argmaxSet Finset.univ (scoreCandidate P score)`
hold by `rfl`-adjacent proofs, and the generic lemma kit below can replace the
per-rule boilerplate (`*_nonempty`, `*_iff_forall_le`, ...).
-/

namespace SocialChoice

open Finset

variable {α β : Type} [LinearOrder β]

/-- The set of elements of `s` that maximize `f` (empty iff `s` is empty). -/
noncomputable def argmaxSet (s : Finset α) (f : α → β) : Finset α := by
  classical
  by_cases h : s.Nonempty
  · exact s.filter (fun a => f a = (s.image f).max' (h.image f))
  · exact ∅

/-- The set of elements of `s` that minimize `f` (empty iff `s` is empty). -/
noncomputable def argminSet (s : Finset α) (f : α → β) : Finset α := by
  classical
  by_cases h : s.Nonempty
  · exact s.filter (fun a => f a = (s.image f).min' (h.image f))
  · exact ∅

lemma argmaxSet_subset (s : Finset α) (f : α → β) : argmaxSet s f ⊆ s := by
  classical
  unfold argmaxSet
  split_ifs with h
  · exact Finset.filter_subset _ _
  · exact Finset.empty_subset _

lemma argminSet_subset (s : Finset α) (f : α → β) : argminSet s f ⊆ s := by
  classical
  unfold argminSet
  split_ifs with h
  · exact Finset.filter_subset _ _
  · exact Finset.empty_subset _

/-- Fundamental characterization: `a` maximizes `f` on `s` iff `a ∈ s` and no
element of `s` has a larger value. Holds unconditionally (both sides are false
for empty `s`). -/
lemma mem_argmaxSet_iff {s : Finset α} {f : α → β} {a : α} :
    a ∈ argmaxSet s f ↔ a ∈ s ∧ ∀ b ∈ s, f b ≤ f a := by
  classical
  unfold argmaxSet
  split_ifs with h
  · simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ha, hmax⟩
      refine ⟨ha, fun b hb => ?_⟩
      rw [hmax]
      exact Finset.le_max' _ _ (Finset.mem_image_of_mem f hb)
    · rintro ⟨ha, hle⟩
      refine ⟨ha, le_antisymm (Finset.le_max' _ _ (Finset.mem_image_of_mem f ha)) ?_⟩
      refine (Finset.max'_le_iff _ _).2 ?_
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
      exact hle b hb
  · simp only [Finset.notMem_empty, false_iff, not_and]
    intro ha
    exact absurd ⟨a, ha⟩ h

/-- Fundamental characterization: `a` minimizes `f` on `s` iff `a ∈ s` and no
element of `s` has a smaller value. -/
lemma mem_argminSet_iff {s : Finset α} {f : α → β} {a : α} :
    a ∈ argminSet s f ↔ a ∈ s ∧ ∀ b ∈ s, f a ≤ f b := by
  classical
  unfold argminSet
  split_ifs with h
  · simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ha, hmin⟩
      refine ⟨ha, fun b hb => ?_⟩
      rw [hmin]
      exact Finset.min'_le _ _ (Finset.mem_image_of_mem f hb)
    · rintro ⟨ha, hle⟩
      refine ⟨ha, le_antisymm ?_ (Finset.min'_le _ _ (Finset.mem_image_of_mem f ha))⟩
      refine (Finset.le_min'_iff _ _).2 ?_
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨b, hb, rfl⟩
      exact hle b hb
  · simp only [Finset.notMem_empty, false_iff, not_and]
    intro ha
    exact absurd ⟨a, ha⟩ h

lemma argmaxSet_nonempty {s : Finset α} (h : s.Nonempty) (f : α → β) :
    (argmaxSet s f).Nonempty := by
  classical
  obtain ⟨y, hy⟩ := Finset.mem_image.mp (Finset.max'_mem (s.image f) (h.image f))
  exact ⟨y, mem_argmaxSet_iff.mpr ⟨hy.1, fun b hb => by
    rw [hy.2]; exact Finset.le_max' _ _ (Finset.mem_image_of_mem f hb)⟩⟩

lemma argminSet_nonempty {s : Finset α} (h : s.Nonempty) (f : α → β) :
    (argminSet s f).Nonempty := by
  classical
  obtain ⟨y, hy⟩ := Finset.mem_image.mp (Finset.min'_mem (s.image f) (h.image f))
  exact ⟨y, mem_argminSet_iff.mpr ⟨hy.1, fun b hb => by
    rw [hy.2]; exact Finset.min'_le _ _ (Finset.mem_image_of_mem f hb)⟩⟩

/-- All members of the argmax set have the same value. -/
lemma eq_of_mem_argmaxSet {s : Finset α} {f : α → β} {a b : α}
    (ha : a ∈ argmaxSet s f) (hb : b ∈ argmaxSet s f) : f a = f b := by
  rcases mem_argmaxSet_iff.mp ha with ⟨has, hale⟩
  rcases mem_argmaxSet_iff.mp hb with ⟨hbs, hble⟩
  exact le_antisymm (hble a has) (hale b hbs)

/-- All members of the argmin set have the same value. -/
lemma eq_of_mem_argminSet {s : Finset α} {f : α → β} {a b : α}
    (ha : a ∈ argminSet s f) (hb : b ∈ argminSet s f) : f a = f b := by
  rcases mem_argminSet_iff.mp ha with ⟨has, hale⟩
  rcases mem_argminSet_iff.mp hb with ⟨hbs, hble⟩
  exact le_antisymm (hale b hbs) (hble a has)

/-- Membership in the argmax set over `univ`, the common case for voting rules. -/
lemma mem_argmaxSet_univ_iff [Fintype α] {f : α → β} {a : α} :
    a ∈ argmaxSet Finset.univ f ↔ ∀ b, f b ≤ f a := by
  simp [mem_argmaxSet_iff]

/-- Membership in the argmin set over `univ`, the common case for voting rules. -/
lemma mem_argminSet_univ_iff [Fintype α] {f : α → β} {a : α} :
    a ∈ argminSet Finset.univ f ↔ ∀ b, f a ≤ f b := by
  simp [mem_argminSet_iff]

end SocialChoice
