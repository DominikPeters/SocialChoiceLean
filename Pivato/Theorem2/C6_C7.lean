import Pivato.Theorem2.C4_C5

/-!
# Appendix C.6 and C.7 cone/hull lemmas

This file contains the set-level cone and divisible-hull machinery used by the
C.8 branch argument, including the finite-family hull-selection step (C.7).
-/

namespace Pivato

section C6_C7

universe uA uI

variable {A : Type uA}

/-- Cone predicate for subsets of an additive group (set-level analogue used in
Appendix C.7). -/
def IsConeSet [AddCommGroup A] (S : Set A) : Prop :=
  AdditivelyClosed S ∧
    ∀ ⦃a : A⦄ ⦃n : ℕ⦄, n ≠ 0 → n • a ∈ S → a ∈ S

lemma additivelyClosed_inter [AddCommGroup A] {S T : Set A}
    (hS : AdditivelyClosed S) (hT : AdditivelyClosed T) :
    AdditivelyClosed (S ∩ T) := by
  intro a b ha hb
  exact ⟨hS ha.1 hb.1, hT ha.2 hb.2⟩

lemma isConeSet_inter [AddCommGroup A] {S T : Set A}
    (hS : IsConeSet S) (hT : IsConeSet T) :
    IsConeSet (S ∩ T) := by
  rcases hS with ⟨hSAdd, hSDiv⟩
  rcases hT with ⟨hTAdd, hTDiv⟩
  refine ⟨additivelyClosed_inter hSAdd hTAdd, ?_⟩
  intro a n hn han
  exact ⟨hSDiv hn han.1, hTDiv hn han.2⟩

lemma AdditivelyClosed.nsmul_mem [AddCommGroup A] {S : Set A}
    (hS : AdditivelyClosed S) (h0 : 0 ∈ S) {a : A} (ha : a ∈ S) :
    ∀ n : ℕ, n • a ∈ S := by
  intro n
  induction n with
  | zero =>
      simpa using h0
  | succ n ih =>
      simpa [Nat.succ_eq_add_one, add_nsmul, one_nsmul] using hS ih ha

lemma additivelyClosed_nonneg_of_preorder_homogeneous
    [AddCommGroup A] {r : A → A → Prop}
    (hPre : IsPreorderRel r) (hHom : Homogeneous r) :
    AdditivelyClosed {a : A | r 0 a} := by
  simpa [positiveConoid] using
    (homogeneous_transitive_iff_additivelyClosed (r := r) hHom).1 hPre.2

lemma additivelyClosed_nonpos_of_preorder_homogeneous
    [AddCommGroup A] {r : A → A → Prop}
    (hPre : IsPreorderRel r) (hHom : Homogeneous r) :
    AdditivelyClosed {a : A | r a 0} := by
  have hNonneg : AdditivelyClosed {a : A | r 0 a} :=
    additivelyClosed_nonneg_of_preorder_homogeneous (hPre := hPre) (hHom := hHom)
  intro a b ha hb
  have h0NegA : r 0 (-a) := by
    simpa [sub_eq_add_neg] using (hHom a 0).1 ha
  have h0NegB : r 0 (-b) := by
    simpa [sub_eq_add_neg] using (hHom b 0).1 hb
  have h0NegSum : r 0 (-a + -b) := hNonneg h0NegA h0NegB
  exact (hHom (a + b) 0).2 (by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, neg_add] using h0NegSum)

lemma additivelyClosed_strict_of_total_preorder_homogeneous
    [AddCommGroup A] {r : A → A → Prop}
    (hPre : IsPreorderRel r) (hHom : Homogeneous r) :
    AdditivelyClosed {a : A | r 0 a ∧ ¬ r a 0} := by
  have hNonneg : AdditivelyClosed {a : A | r 0 a} :=
    additivelyClosed_nonneg_of_preorder_homogeneous (hPre := hPre) (hHom := hHom)
  intro a b ha hb
  refine ⟨hNonneg ha.1 hb.1, ?_⟩
  intro hab0
  have h0NegSum : r 0 (0 - (a + b)) := (hHom (a + b) 0).1 hab0
  have haNegB : r a (-b) := (hHom a (-b)).2 (by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h0NegSum)
  have h0NegB : r 0 (-b) := hPre.2 ha.1 haNegB
  have hb0 : r b 0 := (hHom b 0).2 (by simpa [sub_eq_add_neg] using h0NegB)
  exact hb.2 hb0

lemma strict_mem_of_nsmul_mem_total_preorder_homogeneous
    [AddCommGroup A] {r : A → A → Prop}
    (hPre : IsPreorderRel r) (hTot : Std.Total r) (hHom : Homogeneous r)
    {a : A} {n : ℕ} (_hn : n ≠ 0)
    (hnStrict : n • a ∈ {x : A | r 0 x ∧ ¬ r x 0}) :
    a ∈ {x : A | r 0 x ∧ ¬ r x 0} := by
  have h0 : r 0 (0 : A) := hPre.1 0
  have hNonnegClosed : AdditivelyClosed {x : A | r 0 x} :=
    additivelyClosed_nonneg_of_preorder_homogeneous (hPre := hPre) (hHom := hHom)
  have hNsmulNonneg : ∀ {x : A}, r 0 x → ∀ m : ℕ, r 0 (m • x) := by
    intro x hx m
    exact AdditivelyClosed.nsmul_mem hNonnegClosed h0 hx m
  have hNsmulNonpos : ∀ {x : A}, r x 0 → ∀ m : ℕ, r (m • x) 0 := by
    intro x hx m
    have h0NegX : r 0 (-x) := by
      simpa [sub_eq_add_neg] using (hHom x 0).1 hx
    have h0NegMul : r 0 (m • (-x)) := hNsmulNonneg h0NegX m
    have h0NegMul' : r 0 (-(m • x)) := by simpa [nsmul_neg] using h0NegMul
    exact (hHom (m • x) 0).2 (by simpa [sub_eq_add_neg] using h0NegMul')
  have hNotA0 : ¬ r a 0 := by
    intro ha0
    have hMulA0 : r (n • a) 0 := hNsmulNonpos ha0 n
    exact hnStrict.2 hMulA0
  have h0A : r 0 a := by
    rcases hTot.total 0 a with h0A | hA0
    · exact h0A
    · exact False.elim (hNotA0 hA0)
  exact ⟨h0A, hNotA0⟩

lemma isConeSet_strict_of_total_preorder_homogeneous
    [AddCommGroup A] {r : A → A → Prop}
    (hPre : IsPreorderRel r) (hTot : Std.Total r) (hHom : Homogeneous r) :
    IsConeSet {a : A | r 0 a ∧ ¬ r a 0} := by
  refine ⟨additivelyClosed_strict_of_total_preorder_homogeneous
      (hPre := hPre) (hHom := hHom), ?_⟩
  intro a n hn han
  exact strict_mem_of_nsmul_mem_total_preorder_homogeneous
    (hPre := hPre) (hTot := hTot) (hHom := hHom) hn han

/-- Lemma C.6:
if `S₁ ∪ S₂` is additively closed, then the divisible hull of the union equals
one of the two individual hulls. -/
theorem lemmaC6
    [AddCommGroup A]
    (S₁ S₂ : Set A)
    (K K₁ K₂ : AddSubgroup A)
    (hHull : IsDivisibleHull (S₁ ∪ S₂) K)
    (hHull₁ : IsDivisibleHull S₁ K₁)
    (hHull₂ : IsDivisibleHull S₂ K₂)
    (hAddClosed : AdditivelyClosed (S₁ ∪ S₂)) :
    K = K₁ ∨ K = K₂ := by
  classical
  rcases hHull with ⟨hKDiv, hSsubK, hKmin⟩
  rcases hHull₁ with ⟨hK₁Div, hS₁subK₁, hK₁min⟩
  rcases hHull₂ with ⟨hK₂Div, hS₂subK₂, hK₂min⟩
  by_cases hKK₁ : K = K₁
  · exact Or.inl hKK₁
  · right
    have hNotSubUnionK₁ : ¬ (S₁ ∪ S₂ ⊆ (K₁ : Set A)) := by
      intro hUnionSubK₁
      have hKleK₁ : K ≤ K₁ := hKmin K₁ hK₁Div hUnionSubK₁
      have hS₁subK : S₁ ⊆ (K : Set A) := by
        intro s hs
        exact hSsubK (Or.inl hs)
      have hK₁leK : K₁ ≤ K := hK₁min K hKDiv hS₁subK
      exact hKK₁ (le_antisymm hKleK₁ hK₁leK)
    have hs₂Exists : ∃ s₂ : A, s₂ ∈ S₁ ∪ S₂ ∧ s₂ ∉ (K₁ : Set A) := by
      by_contra hNo
      apply hNotSubUnionK₁
      intro s hs
      by_contra hsnot
      exact hNo ⟨s, hs, hsnot⟩
    rcases hs₂Exists with ⟨s₂, hs₂Union, hs₂notK₁⟩
    have hs₂S₂ : s₂ ∈ S₂ := by
      by_cases hs₂S₁ : s₂ ∈ S₁
      · have hs₂K₁ : s₂ ∈ K₁ := hS₁subK₁ hs₂S₁
        exact False.elim (hs₂notK₁ hs₂K₁)
      · rcases hs₂Union with hs₂S₁' | hs₂S₂
        · exact False.elim (hs₂S₁ hs₂S₁')
        · exact hs₂S₂
    have hS₁subK₂ : S₁ ⊆ (K₂ : Set A) := by
      intro s₁ hs₁S₁
      let t : A := s₁ + s₂
      have hs₂K₂ : s₂ ∈ K₂ := hS₂subK₂ hs₂S₂
      have htUnion : t ∈ S₁ ∪ S₂ := hAddClosed (Or.inl hs₁S₁) hs₂Union
      have htS₂ : t ∈ S₂ := by
        have htNotS₁ : t ∉ S₁ := by
          intro htS₁
          have hs₁K₁ : s₁ ∈ K₁ := hS₁subK₁ hs₁S₁
          have htK₁ : t ∈ K₁ := hS₁subK₁ htS₁
          have hs₂K₁ : s₂ ∈ K₁ := by
            have hs₂mem : t - s₁ ∈ K₁ := K₁.sub_mem htK₁ hs₁K₁
            simpa [t, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hs₂mem
          exact hs₂notK₁ hs₂K₁
        rcases htUnion with htS₁ | htS₂
        · exact False.elim (htNotS₁ htS₁)
        · exact htS₂
      have htK₂ : t ∈ K₂ := hS₂subK₂ htS₂
      have hs₁K₂ : s₁ ∈ K₂ := by
        have hs₁mem : t - s₂ ∈ K₂ := K₂.sub_mem htK₂ hs₂K₂
        simpa [t, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hs₁mem
      exact hs₁K₂
    have hUnionSubK₂ : S₁ ∪ S₂ ⊆ (K₂ : Set A) := by
      intro s hs
      rcases hs with hs₁ | hs₂
      · exact hS₁subK₂ hs₁
      · exact hS₂subK₂ hs₂
    have hKleK₂ : K ≤ K₂ := hKmin K₂ hK₂Div hUnionSubK₂
    have hS₂subK : S₂ ⊆ (K : Set A) := by
      intro s hs₂
      exact hSsubK (Or.inr hs₂)
    have hK₂leK : K₂ ≤ K := hK₂min K hKDiv hS₂subK
    exact le_antisymm hKleK₂ hK₂leK

/-- Lemma C.7:
for a finite family of cone-sets whose union is additively closed, one member
hull already equals the hull of the whole union. -/
theorem lemmaC7
    [AddCommGroup A] {ι : Type uI} [Fintype ι] [Nonempty ι]
    (S : ι → Set A)
    (K : AddSubgroup A) (Kᵢ : ι → AddSubgroup A)
    (hHull : IsDivisibleHull (⋃ i, S i) K)
    (hHullᵢ : ∀ i, IsDivisibleHull (S i) (Kᵢ i))
    (hCone : ∀ i, IsConeSet (S i))
    (hAddClosed : AdditivelyClosed (⋃ i, S i)) :
    ∃ i, K = Kᵢ i := by
  classical
  let P : ∀ (α : Type uI) (_ : Fintype α), Prop := fun α _ =>
    Nonempty α →
      ∀ (S : α → Set A) (K : AddSubgroup A) (Kᵢ : α → AddSubgroup A),
        IsDivisibleHull (⋃ i, S i) K →
        (∀ i, IsDivisibleHull (S i) (Kᵢ i)) →
        (∀ i, IsConeSet (S i)) →
        AdditivelyClosed (⋃ i, S i) →
        ∃ i, K = Kᵢ i
  have hMain : P ι inferInstance := by
    refine Fintype.induction_subsingleton_or_nontrivial (P := P) (α := ι) ?_ ?_
    · intro α _ hSub hne S K Kᵢ hHull hHullᵢ _hCone _hAddClosed
      rcases hne with ⟨a⟩
      have hAllEq : ∀ j : α, j = a := fun j => hSub.elim _ _
      have hUnionEq : (⋃ i : α, S i) = S a := by
        ext x
        constructor
        · intro hx
          rcases Set.mem_iUnion.mp hx with ⟨j, hj⟩
          simpa [hAllEq j] using hj
        · intro hx
          exact Set.mem_iUnion.mpr ⟨a, hx⟩
      have hHullSingle : IsDivisibleHull (S a) K := by
        simpa [hUnionEq] using hHull
      exact ⟨a, IsDivisibleHull.eq hHullSingle (hHullᵢ a)⟩
    · intro α _ _ ih hne S K Kᵢ hHull hHullᵢ hCone hAddClosed
      rcases hne with ⟨a⟩
      let SAll : Set A := ⋃ i : α, S i
      have hHullAll : IsDivisibleHull SAll K := by
        simpa [SAll] using hHull
      have hHullAll' : IsDivisibleHull SAll K := hHullAll
      rcases hHullAll with ⟨hKDiv, hSAllSubK, hKMin⟩
      have hSiSubK : ∀ i : α, S i ⊆ (K : Set A) := by
        intro i s hs
        exact hSAllSubK (Set.mem_iUnion.mpr ⟨i, hs⟩)
      have hKiDiv : ∀ i : α, IsDivisibleSubgroup (Kᵢ i) := by
        intro i
        exact (hHullᵢ i).1
      have hSiSubKi : ∀ i : α, S i ⊆ (Kᵢ i : Set A) := by
        intro i
        exact (hHullᵢ i).2.1
      have hKiLeK : ∀ i : α, Kᵢ i ≤ K := by
        intro i
        exact (hHullᵢ i).2.2 K hKDiv (hSiSubK i)
      by_cases hKeqA : K = Kᵢ a
      · exact ⟨a, hKeqA⟩
      · have hKiProper : Kᵢ a ≠ ⊤ := by
          intro hTop
          have hKTop : K = ⊤ := by
            apply top_unique
            intro x _hx
            have hxTop : x ∈ Kᵢ a := by simp [hTop]
            exact hKiLeK a hxTop
          have hEqTop : K = Kᵢ a := by
            rw [hKTop, hTop]
          exact hKeqA hEqTop
        obtain ⟨r, hPre, hTot, hHom, hSymm⟩ :=
          corollaryB1b (A := A) (B := Kᵢ a) (hKiDiv a) hKiProper
        let Sge : Set A := SAll ∩ {x : A | r 0 x}
        let Sle : Set A := SAll ∩ {x : A | r x 0}
        have hSAllAdd : AdditivelyClosed SAll := by
          simpa [SAll] using hAddClosed
        have hSgeAdd : AdditivelyClosed Sge := by
          refine additivelyClosed_inter hSAllAdd ?_
          exact additivelyClosed_nonneg_of_preorder_homogeneous (hPre := hPre) (hHom := hHom)
        have hSleAdd : AdditivelyClosed Sle := by
          refine additivelyClosed_inter hSAllAdd ?_
          exact additivelyClosed_nonpos_of_preorder_homogeneous (hPre := hPre) (hHom := hHom)
        have hSAllSplit : SAll = Sge ∪ Sle := by
          ext x
          constructor
          · intro hx
            rcases hTot.total 0 x with h0x | hx0
            · exact Or.inl ⟨hx, h0x⟩
            · exact Or.inr ⟨hx, hx0⟩
          · intro hx
            rcases hx with hxge | hxle
            · exact hxge.1
            · exact hxle.1
        obtain ⟨Kge, hHullGe⟩ := Pivato.exists_divisibleHull (A := A) (S := Sge)
        obtain ⟨Kle, hHullLe⟩ := Pivato.exists_divisibleHull (A := A) (S := Sle)
        have hHullSplit : IsDivisibleHull (Sge ∪ Sle) K := by
          simpa [hSAllSplit] using hHullAll'
        have h6 : K = Kge ∨ K = Kle :=
          lemmaC6 (S₁ := Sge) (S₂ := Sle) (K := K) (K₁ := Kge) (K₂ := Kle)
            hHullSplit hHullGe hHullLe (by simpa [hSAllSplit] using hSAllAdd)
        have finish :
            ∀ (q : A → A → Prop) (Kpos : AddSubgroup A),
              IsPreorderRel q →
              Std.Total q →
              Homogeneous q →
              {x : A | symmPart q x 0} = Kᵢ a →
              IsDivisibleHull (SAll ∩ {x : A | q 0 x}) Kpos →
              K = Kpos →
              ∃ i, K = Kᵢ i := by
          intro q Kpos hPreQ hTotQ hHomQ hSymmQ hHullPos hKeqPos
          let Sstrict : Set A := SAll ∩ {x : A | q 0 x ∧ ¬ q x 0}
          let S0 : Set A := SAll ∩ {x : A | symmPart q x 0}
          obtain ⟨Kstrict, hHullStrict⟩ :=
            Pivato.exists_divisibleHull (A := A) (S := Sstrict)
          obtain ⟨K0, hHull0⟩ :=
            Pivato.exists_divisibleHull (A := A) (S := S0)
          have hSposSplit : (SAll ∩ {x : A | q 0 x}) = Sstrict ∪ S0 := by
            ext x
            constructor
            · intro hx
              by_cases hx0 : q x 0
              · exact Or.inr ⟨hx.1, ⟨hx0, hx.2⟩⟩
              · exact Or.inl ⟨hx.1, ⟨hx.2, hx0⟩⟩
            · intro hx
              rcases hx with hs | h0
              · exact ⟨hs.1, hs.2.1⟩
              · exact ⟨h0.1, h0.2.2⟩
          have hPosAdd : AdditivelyClosed (SAll ∩ {x : A | q 0 x}) := by
            refine additivelyClosed_inter hSAllAdd ?_
            exact additivelyClosed_nonneg_of_preorder_homogeneous (hPre := hPreQ) (hHom := hHomQ)
          have h7 : Kpos = Kstrict ∨ Kpos = K0 :=
            lemmaC6 (S₁ := Sstrict) (S₂ := S0) (K := Kpos) (K₁ := Kstrict) (K₂ := K0)
              (by simpa [hSposSplit] using hHullPos)
              hHullStrict hHull0
              (by simpa [hSposSplit] using hPosAdd)
          have hS0SubKi : S0 ⊆ (Kᵢ a : Set A) := by
            intro x hx
            have hxSymm : x ∈ ({y : A | symmPart q y 0} : Set A) := hx.2
            simpa [hSymmQ] using hxSymm
          have hK0LeKi : K0 ≤ Kᵢ a := by
            exact hHull0.2.2 (Kᵢ a) (hKiDiv a) hS0SubKi
          have hKposEqKstrict : Kpos = Kstrict := by
            rcases h7 with hKs | hK0
            · exact hKs
            · exfalso
              have hKLeKi : K ≤ Kᵢ a := by
                calc
                  K = Kpos := hKeqPos
                  _ = K0 := hK0
                  _ ≤ Kᵢ a := hK0LeKi
              have hEq : K = Kᵢ a := le_antisymm hKLeKi (hKiLeK a)
              exact hKeqA hEq
          have hKeqStrict : K = Kstrict := by
            calc
              K = Kpos := hKeqPos
              _ = Kstrict := hKposEqKstrict
          let β : Type uI := {i : α // i ≠ a}
          let Sβ : β → Set A := fun i => S i.1 ∩ {x : A | q 0 x ∧ ¬ q x 0}
          have hβCard : Fintype.card β < Fintype.card α := by
            dsimp [β]
            exact Fintype.card_subtype_lt (p := fun x : α => x ≠ a) (x := a) (by simp)
          have hβNonempty : Nonempty β := by
            obtain ⟨b, hb⟩ := exists_ne a
            exact ⟨⟨b, hb⟩⟩
          have hStrictCone : IsConeSet {x : A | q 0 x ∧ ¬ q x 0} := by
            exact isConeSet_strict_of_total_preorder_homogeneous
              (hPre := hPreQ) (hTot := hTotQ) (hHom := hHomQ)
          have hConeβ : ∀ i : β, IsConeSet (Sβ i) := by
            intro i
            exact isConeSet_inter (hCone i.1) hStrictCone
          have hSstrictEq : (⋃ i : β, Sβ i) = Sstrict := by
            ext x
            constructor
            · intro hx
              rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
              exact ⟨Set.mem_iUnion.mpr ⟨i.1, hi.1⟩, hi.2⟩
            · intro hx
              rcases Set.mem_iUnion.mp hx.1 with ⟨j, hj⟩
              by_cases hja : j = a
              · subst j
                have hxKi : x ∈ Kᵢ a := hSiSubKi a hj
                have hxSymm : x ∈ ({y : A | symmPart q y 0} : Set A) := by
                  simpa [hSymmQ] using hxKi
                exact False.elim (hx.2.2 hxSymm.1)
              · exact Set.mem_iUnion.mpr ⟨⟨j, hja⟩, ⟨hj, hx.2⟩⟩
          have hStrictAdd : AdditivelyClosed Sstrict := by
            refine additivelyClosed_inter hSAllAdd ?_
            exact additivelyClosed_strict_of_total_preorder_homogeneous
              (hPre := hPreQ) (hHom := hHomQ)
          have hHullβ : IsDivisibleHull (⋃ i : β, Sβ i) Kstrict := by
            simpa [hSstrictEq] using hHullStrict
          let Kβ : β → AddSubgroup A :=
            fun i => Classical.choose (Pivato.exists_divisibleHull (A := A) (S := Sβ i))
          have hHullβi : ∀ i : β, IsDivisibleHull (Sβ i) (Kβ i) := by
            intro i
            exact Classical.choose_spec (Pivato.exists_divisibleHull (A := A) (S := Sβ i))
          have hAddβ : AdditivelyClosed (⋃ i : β, Sβ i) := by
            simpa [hSstrictEq] using hStrictAdd
          have ihβ : P β inferInstance := (ih β) hβCard
          rcases ihβ hβNonempty Sβ Kstrict Kβ hHullβ hHullβi hConeβ hAddβ with
            ⟨iβ, hKstrictEqβ⟩
          have hKβLeKi : Kβ iβ ≤ Kᵢ iβ.1 := by
            exact (hHullβi iβ).2.2 (Kᵢ iβ.1) (hKiDiv iβ.1) (by
              intro x hx
              exact hSiSubKi iβ.1 hx.1)
          have hKLeKi : K ≤ Kᵢ iβ.1 := by
            calc
              K = Kstrict := hKeqStrict
              _ = Kβ iβ := hKstrictEqβ
              _ ≤ Kᵢ iβ.1 := hKβLeKi
          have hEq : K = Kᵢ iβ.1 := le_antisymm hKLeKi (hKiLeK iβ.1)
          exact ⟨iβ.1, hEq⟩
        rcases h6 with hKG | hKL
        · exact finish r Kge hPre hTot hHom hSymm hHullGe hKG
        · let rRev : A → A → Prop := fun x y => r y x
          have hPreRev : IsPreorderRel rRev := by
            refine ⟨?_, ?_⟩
            · intro x
              exact hPre.1 x
            · intro x y z hxy hyz
              exact hPre.2 hyz hxy
          have hTotRev : Std.Total rRev := by
            refine ⟨?_⟩
            intro x y
            rcases hTot.total y x with hyx | hxy
            · exact Or.inl hyx
            · exact Or.inr hxy
          have hHomRev : Homogeneous rRev := by
            intro x y
            constructor
            · intro hxy
              have h0 : r 0 (x - y) := (hHom y x).1 hxy
              exact (hHom (y - x) 0).2 (by
                simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h0)
            · intro hxy
              have h0 : r 0 (x - y) := by
                have h0' : r 0 (0 - (y - x)) := (hHom (y - x) 0).1 hxy
                simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h0'
              exact (hHom y x).2 h0
          have hSymmRev : {x : A | symmPart rRev x 0} = Kᵢ a := by
            ext x
            constructor
            · intro hx
              have hx' : symmPart r x 0 := ⟨hx.2, hx.1⟩
              have hxSet : x ∈ ({y : A | symmPart r y 0} : Set A) := hx'
              simpa [hSymm] using hxSet
            · intro hx
              have hxSet : x ∈ ({y : A | symmPart r y 0} : Set A) := by
                simpa [hSymm] using hx
              exact ⟨hxSet.2, hxSet.1⟩
          have hHullLeRev : IsDivisibleHull (SAll ∩ {x : A | rRev 0 x}) Kle := by
            simpa [rRev, Sle] using hHullLe
          exact finish rRev Kle hPreRev hTotRev hHomRev hSymmRev hHullLeRev hKL
  exact hMain (by infer_instance) S K Kᵢ hHull hHullᵢ hCone hAddClosed

/-- Finite-family helper: if every finite subunion is additively closed, then
Lemma C.7 follows by finite induction with repeated applications of Lemma C.6.

This is stronger than the paper hypothesis and is used as intermediate
infrastructure while developing the full C.7 proof. -/
theorem lemmaC7_of_allSubunionsAddClosed
    [AddCommGroup A] {ι : Type uI} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (S : ι → Set A)
    (K : AddSubgroup A) (Kᵢ : ι → AddSubgroup A)
    (hHull : IsDivisibleHull (⋃ i, S i) K)
    (hHullᵢ : ∀ i, IsDivisibleHull (S i) (Kᵢ i))
    (hAddClosedSub : ∀ t : Finset ι, AdditivelyClosed (⋃ i ∈ t, S i)) :
    ∃ i, K = Kᵢ i := by
  have hMain :
      ∀ t : Finset ι, ∀ Kt : AddSubgroup A,
        IsDivisibleHull (⋃ i ∈ t, S i) Kt →
        t.Nonempty →
        ∃ i, i ∈ t ∧ Kt = Kᵢ i := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro Kt _hHullt ht
      rcases ht with ⟨i, hi⟩
      have : False := by simp at hi
      exact False.elim this
    · intro a t ha ih Kt hHullt _ht
      obtain ⟨Krest, hHullRest⟩ :=
        Pivato.exists_divisibleHull (A := A) (S := ⋃ i ∈ t, S i)
      have hHullUnion :
          IsDivisibleHull ((S a) ∪ (⋃ i ∈ t, S i)) Kt := by
        simpa [Finset.mem_insert, ha, or_assoc, or_left_comm, or_comm] using hHullt
      have hAddClosedUnion :
          AdditivelyClosed ((S a) ∪ (⋃ i ∈ t, S i)) := by
        simpa [Finset.mem_insert, ha, or_assoc, or_left_comm, or_comm] using
          hAddClosedSub (insert a t)
      have h6 :
          Kt = Kᵢ a ∨ Kt = Krest :=
        lemmaC6 (S₁ := S a) (S₂ := ⋃ i ∈ t, S i)
          (K := Kt) (K₁ := Kᵢ a) (K₂ := Krest)
          hHullUnion (hHullᵢ a) hHullRest hAddClosedUnion
      rcases h6 with hEqA | hEqRest
      · exact ⟨a, Finset.mem_insert_self a t, hEqA⟩
      · by_cases ht' : t.Nonempty
        · rcases ih Krest hHullRest ht' with ⟨i, hiT, hiEq⟩
          exact ⟨i, Finset.mem_insert_of_mem hiT, by simpa [hEqRest] using hiEq⟩
        · have htEmpty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht'
          subst htEmpty
          have hHullSingle : IsDivisibleHull (S a) Kt := by
            simpa [Finset.mem_insert, or_true] using hHullt
          exact ⟨a, Finset.mem_insert_self a ∅, IsDivisibleHull.eq hHullSingle (hHullᵢ a)⟩
  have hUnivNonempty : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
  rcases hMain Finset.univ K (by simpa using hHull) hUnivNonempty with ⟨i, _hi, hEq⟩
  exact ⟨i, hEq⟩

end C6_C7

end Pivato
