import Pivato.HomogeneousSzpilrajn
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Appendix B: Homogeneous orders on abelian groups

This file formalizes the Appendix B infrastructure from Pivato's paper:

* conoid-style definitions for homogeneous relations;
* Lemma B.1(a)-style equivalences;
* a strict (`≻`) extension theorem derived from homogeneous Szpilrajn;
* Corollary B.1(a,b), where (b) is stated with the paper-facing
  "divisible proper subgroup" assumption (formalized as
  `n • a ∈ B → a ∈ B` with `B ≠ ⊤`).
-/

namespace Pivato

section BasicDefs

variable {G : Type*} [AddCommGroup G]

/-- The positive conoid associated to a homogeneous relation. -/
def positiveConoid (r : G → G → Prop) : Set G := {a | r 0 a}

/-- The relation defined by a conoid `P` via `x ≽ y :↔ y - x ∈ P`. -/
def relOfConoid (P : Set G) : G → G → Prop := fun x y => y - x ∈ P

/-- Additive closure of a subset. -/
def AdditivelyClosed (P : Set G) : Prop :=
  ∀ ⦃a b : G⦄, a ∈ P → b ∈ P → a + b ∈ P

/-- Preorder conoid: additive closure and `0 ∈ P`. -/
def IsPreorderConoid (P : Set G) : Prop :=
  AdditivelyClosed P ∧ 0 ∈ P

/-- Partial-order conoid: additive closure and pointedness. -/
def IsPartialOrderConoid (P : Set G) : Prop :=
  IsPreorderConoid P ∧ ∀ ⦃a : G⦄, a ∈ P → -a ∈ P → a = 0

/-- Completeness of a conoid. -/
def IsCompleteConoid (P : Set G) : Prop :=
  ∀ a : G, a ≠ 0 → a ∈ P ∨ -a ∈ P

/-- Linear-order cone = complete partial-order conoid. -/
def IsLinearOrderCone (P : Set G) : Prop :=
  IsPartialOrderConoid P ∧ IsCompleteConoid P

/-- Reflexive-transitive relation packaged as a proposition. -/
def IsPreorderRel (r : G → G → Prop) : Prop :=
  (∀ x, r x x) ∧ ∀ ⦃x y z⦄, r x y → r y z → r x z

/-- Partial order relation packaged as a proposition. -/
def IsPartialOrderRel (r : G → G → Prop) : Prop :=
  IsPreorderRel r ∧ Std.Antisymm r

/-- Linear order relation packaged as a proposition. -/
def IsLinearOrderRel (r : G → G → Prop) : Prop :=
  IsPartialOrderRel r ∧ Std.Total r

/-- Strict/asymmetric part of a relation. -/
def asymmPart (r : G → G → Prop) : G → G → Prop := fun x y => r x y ∧ ¬ r y x

/-- Symmetric part of a relation. -/
def symmPart (r : G → G → Prop) : G → G → Prop := fun x y => r x y ∧ r y x

/-- Homogeneous strict relation. -/
def HomogeneousStrict (p : G → G → Prop) : Prop :=
  ∀ x y, p x y ↔ p 0 (y - x)

/-- Divisibility condition for subgroups used in Appendix B:
`n • a ∈ B -> a ∈ B` for `n ≠ 0`. -/
def IsDivisibleSubgroup (B : AddSubgroup G) : Prop :=
  ∀ ⦃a : G⦄ ⦃n : ℕ⦄, n ≠ 0 → n • a ∈ B → a ∈ B

/-- Backwards-compatible alias. -/
abbrev IsPureSubgroup (B : AddSubgroup G) : Prop :=
  IsDivisibleSubgroup B

lemma relOfConoid_homogeneous (P : Set G) : Homogeneous (relOfConoid P) := by
  intro x y
  simp [relOfConoid]

lemma positiveConoid_relOfConoid (P : Set G) :
    positiveConoid (relOfConoid P) = P := by
  ext a
  simp [positiveConoid, relOfConoid]

lemma relOfConoid_positiveConoid {r : G → G → Prop} (hr : Homogeneous r) :
    relOfConoid (positiveConoid r) = r := by
  funext x
  funext y
  exact propext ((hr x y).symm)

end BasicDefs

section LemmaB1a

variable {G : Type*} [AddCommGroup G] {r : G → G → Prop}

lemma homogeneous_reflexive_iff_zero_mem (hr : Homogeneous r) :
    (∀ x, r x x) ↔ 0 ∈ positiveConoid r := by
  constructor
  · intro href
    exact href 0
  · intro h0 x
    exact (hr x x).2 (by simpa [positiveConoid] using h0)

lemma homogeneous_transitive_iff_additivelyClosed (hr : Homogeneous r) :
    (∀ ⦃x y z⦄, r x y → r y z → r x z) ↔ AdditivelyClosed (positiveConoid r) := by
  constructor
  · intro htrans a b ha hb
    have hab : r a (a + b) := by
      exact (hr a (a + b)).2 (by simpa [positiveConoid, sub_eq_add_neg] using hb)
    exact htrans ha hab
  · intro hclosed x y z hxy hyz
    have hyx : y - x ∈ positiveConoid r := (hr x y).1 hxy
    have hzy : z - y ∈ positiveConoid r := (hr y z).1 hyz
    have hzx : z - x ∈ positiveConoid r := by
      have hsum := hclosed hyx hzy
      simpa [positiveConoid, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsum
    exact (hr x z).2 hzx

lemma homogeneous_antisymm_iff_pointedConoid (hr : Homogeneous r) :
    Std.Antisymm r ↔ (∀ ⦃a : G⦄, a ∈ positiveConoid r → -a ∈ positiveConoid r → a = 0) := by
  constructor
  · intro hanti a ha hna
    have ha0 : r a 0 := (hr a 0).2 (by simpa [positiveConoid, sub_eq_add_neg] using hna)
    exact hanti.antisymm _ _ ha0 ha
  · intro hpoint
    refine ⟨?_⟩
    intro x y hxy hyx
    have h1 : y - x ∈ positiveConoid r := (hr x y).1 hxy
    have h2 : -(y - x) ∈ positiveConoid r := by
      have hxy' : x - y ∈ positiveConoid r := (hr y x).1 hyx
      simpa [positiveConoid, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxy'
    have hzero : y - x = 0 := hpoint h1 h2
    exact (sub_eq_zero.mp hzero).symm

lemma homogeneous_total_iff_completeConoid (hr : Homogeneous r) (h0 : 0 ∈ positiveConoid r) :
    Std.Total r ↔ IsCompleteConoid (positiveConoid r) := by
  constructor
  · intro htot a _
    rcases htot.total 0 a with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa [positiveConoid, sub_eq_add_neg] using (hr a 0).1 h)
  · intro hcomp
    refine ⟨?_⟩
    intro x y
    by_cases hxy : x = y
    · exact Or.inl (hxy ▸ (hr y y).2 (by simpa [positiveConoid] using h0))
    · have hne : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
      rcases hcomp (y - x) hne with hyx | hxy'
      · exact Or.inl ((hr x y).2 hyx)
      · have hxyd : x - y ∈ positiveConoid r := by
          simpa [positiveConoid, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hxy'
        exact Or.inr ((hr y x).2 hxyd)

theorem lemmaB1a_preorder (hr : Homogeneous r) :
    IsPreorderRel r ↔ IsPreorderConoid (positiveConoid r) := by
  constructor
  · rintro ⟨href, htrans⟩
    exact ⟨(homogeneous_transitive_iff_additivelyClosed hr).1 htrans,
      (homogeneous_reflexive_iff_zero_mem hr).1 href⟩
  · rintro ⟨hclosed, h0⟩
    exact ⟨(homogeneous_reflexive_iff_zero_mem hr).2 h0,
      (homogeneous_transitive_iff_additivelyClosed hr).2 hclosed⟩

theorem lemmaB1a_partial (hr : Homogeneous r) :
    IsPartialOrderRel r ↔ IsPartialOrderConoid (positiveConoid r) := by
  constructor
  · rintro ⟨hpre, hanti⟩
    refine ⟨(lemmaB1a_preorder hr).1 hpre, ?_⟩
    exact (homogeneous_antisymm_iff_pointedConoid hr).1 hanti
  · rintro ⟨hpreCone, hpoint⟩
    refine ⟨?_, (homogeneous_antisymm_iff_pointedConoid hr).2 hpoint⟩
    exact (lemmaB1a_preorder hr).2 hpreCone

theorem lemmaB1a_linear (hr : Homogeneous r) :
    IsLinearOrderRel r ↔ IsLinearOrderCone (positiveConoid r) := by
  constructor
  · rintro ⟨hpartial, htotal⟩
    exact ⟨(lemmaB1a_partial hr).1 hpartial,
      (homogeneous_total_iff_completeConoid hr ((lemmaB1a_preorder hr).1 hpartial.1).2).1 htotal⟩
  · rintro ⟨hpartialCone, hcomplete⟩
    exact ⟨(lemmaB1a_partial hr).2 hpartialCone,
      (homogeneous_total_iff_completeConoid hr hpartialCone.1.2).2 hcomplete⟩

end LemmaB1a

section StrictVersion

variable {G : Type*} [AddCommGroup G]

/-- Strict version of homogeneous Szpilrajn: extension of the asymmetric part. -/
theorem homogeneous_szpilrajn_strict
    [IsAddTorsionFree G]
    (r : G → G → Prop) [IsPartialOrder G r] (hr : Homogeneous r) :
    ∃ t : G → G → Prop,
      IsStrictTotalOrder G t ∧
      asymmPart r ≤ t ∧
      HomogeneousStrict t := by
  obtain ⟨s, hsLin, hrs, hsHom⟩ := homogeneous_szpilrajn (G := G) r hr
  let t : G → G → Prop := asymmPart s
  have : IsLinearOrder G s := hsLin
  have hconv : ∀ a b : G, s a b ↔ s (a - b) 0 := by
    intro a b
    constructor
    · intro hab
      have h0 : s 0 (b - a) := (hsHom a b).1 hab
      exact (hsHom (a - b) 0).2 (by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h0)
    · intro hab
      have h0 : s 0 (0 - (a - b)) := (hsHom (a - b) 0).1 hab
      exact (hsHom a b).2 (by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h0)
  have : Std.Irrefl t := ⟨fun x hx => hx.2 (refl (r := s) x)⟩
  have : IsTrans G t := ⟨fun x y z hxy hyz => by
    refine ⟨_root_.trans (r := s) hxy.1 hyz.1, ?_⟩
    intro hzx
    exact hxy.2 (_root_.trans (r := s) hyz.1 hzx)⟩
  have : Std.Trichotomous t := ⟨fun x y hxy hyx => by
    rcases total_of s x y with h | h
    · exact antisymm (r := s) h (not_not.1 fun h' => hxy ⟨h, h'⟩)
    · exact antisymm (r := s) (not_not.1 fun h' => hyx ⟨h, h'⟩) h⟩
  have : IsStrictOrder G t := ⟨⟩
  have : IsStrictTotalOrder G t := ⟨⟩
  have hAsymmExtend : asymmPart r ≤ t := by
    intro x y hxy
    refine ⟨hrs x y hxy.1, ?_⟩
    intro hyx
    have hEq : x = y := antisymm (r := s) (hrs x y hxy.1) hyx
    have hyx_r : r y x := by
      simpa [hEq] using (refl (r := r) y)
    exact hxy.2 hyx_r
  have hHomStrict : HomogeneousStrict t := by
    intro x y
    constructor
    · intro hxy
      refine ⟨(hsHom x y).1 hxy.1, ?_⟩
      intro hback
      exact hxy.2 ((hconv y x).2 hback)
    · intro hxy
      refine ⟨(hsHom x y).2 hxy.1, ?_⟩
      intro hyx
      exact hxy.2 ((hconv y x).1 hyx)
  exact ⟨t, inferInstance, hAsymmExtend, hHomStrict⟩

end StrictVersion

section CorollaryB1

variable {G : Type*} [AddCommGroup G]

/-- Corollary B.1(a): every torsion-free abelian group admits a homogeneous linear order. -/
theorem corollaryB1a [IsAddTorsionFree G] :
    ∃ r : G → G → Prop, IsLinearOrder G r ∧ Homogeneous r := by
  let r0 : G → G → Prop := (· = ·)
  have : Std.Refl r0 := ⟨by intro x; rfl⟩
  have : IsTrans G r0 := ⟨by intro x y z hxy hyz; exact hxy.trans hyz⟩
  have : Std.Antisymm r0 := ⟨by intro x y hxy _hyx; exact hxy⟩
  have : IsPreorder G r0 := ⟨⟩
  have : IsPartialOrder G r0 := ⟨⟩
  have hr0 : Homogeneous r0 := by
    intro x y
    constructor
    · intro h
      subst h
      simp [r0]
    · intro h
      have hyx : y = x := sub_eq_zero.mp (by simpa [r0] using h.symm)
      exact hyx.symm
  obtain ⟨r, hrLin, _hrExt, hrHom⟩ := homogeneous_szpilrajn (G := G) r0 hr0
  exact ⟨r, hrLin, hrHom⟩

/-- Quotient by an Appendix-B-divisible subgroup is torsion-free. -/
theorem quotient_isAddTorsionFree_of_divisibleSubgroup
    (B : AddSubgroup G) (hB : IsDivisibleSubgroup B) :
    IsAddTorsionFree (G ⧸ B) := by
  refine ⟨?_⟩
  intro n hn q1 q2 _ hEq
  have hsub : n • (q1 - q2) = 0 := by
    have : n • q1 - n • q2 = 0 := sub_eq_zero.mpr hEq
    simpa [nsmul_sub] using this
  have hzero : q1 - q2 = (0 : G ⧸ B) := by
    revert hsub
    refine QuotientAddGroup.induction_on (q1 - q2) ?_
    intro a ha
    have ha' : (QuotientAddGroup.mk (n • a) : G ⧸ B) = 0 := by
      simpa using ha
    have hmem : n • a ∈ B := (QuotientAddGroup.eq_zero_iff (N := B) (x := n • a)).1 ha'
    have haMem : a ∈ B := hB hn hmem
    exact (QuotientAddGroup.eq_zero_iff (N := B) (x := a)).2 haMem
  exact sub_eq_zero.mp hzero

/-- Backwards-compatible alias. -/
theorem quotient_isAddTorsionFree_of_pure
    (B : AddSubgroup G) (hB : IsPureSubgroup B) :
    IsAddTorsionFree (G ⧸ B) :=
  quotient_isAddTorsionFree_of_divisibleSubgroup (B := B) hB

/-- Corollary B.1(b) (paper-facing statement): pull back a homogeneous
linear order from `A ⧸ B` to a complete homogeneous preorder on `A`
whose symmetric kernel is exactly `B`.

Assumptions match the paper wording:
`B` is a divisible proper subgroup (formalized as
`IsDivisibleSubgroup B` and `B ≠ ⊤`). -/
theorem corollaryB1b (A : Type*) [AddCommGroup A] (B : AddSubgroup A)
    (hB : IsDivisibleSubgroup B) (_hBproper : B ≠ ⊤) :
    ∃ r : A → A → Prop,
      IsPreorderRel r ∧ Std.Total r ∧ Homogeneous r ∧ {a : A | symmPart r a 0} = B := by
  let : IsAddTorsionFree (A ⧸ B) :=
    quotient_isAddTorsionFree_of_divisibleSubgroup (B := B) hB
  obtain ⟨s, hsLin, hsHom⟩ := corollaryB1a (G := A ⧸ B)
  have : IsLinearOrder (A ⧸ B) s := hsLin
  let r : A → A → Prop := fun x y => s (QuotientAddGroup.mk x) (QuotientAddGroup.mk y)
  refine ⟨r, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun x => refl (r := s) (QuotientAddGroup.mk x), fun x y z hxy hyz => ?_⟩
    exact _root_.trans (r := s) hxy hyz
  · exact ⟨fun x y => total_of s (QuotientAddGroup.mk x) (QuotientAddGroup.mk y)⟩
  · intro x y
    simpa [r, sub_eq_add_neg] using (hsHom (QuotientAddGroup.mk x) (QuotientAddGroup.mk y))
  · ext a
    constructor
    · intro ha
      have hs1 : s (QuotientAddGroup.mk a) (QuotientAddGroup.mk (0 : A)) := ha.1
      have hs2 : s (QuotientAddGroup.mk (0 : A)) (QuotientAddGroup.mk a) := ha.2
      have hEq : QuotientAddGroup.mk a = (0 : A ⧸ B) := antisymm hs1 hs2
      exact (QuotientAddGroup.eq_zero_iff (N := B) (x := a)).1 hEq
    · intro ha
      have hEq : (QuotientAddGroup.mk a : A ⧸ B) = 0 :=
        (QuotientAddGroup.eq_zero_iff (N := B) (x := a)).2 ha
      have hs00 : s (0 : A ⧸ B) 0 := refl (r := s) 0
      refine ⟨?_, ?_⟩ <;> simpa [r, hEq] using hs00

end CorollaryB1

end Pivato
