import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Order.Group.Cone
import Mathlib.Order.Zorn

/-!
# Homogeneous Szpilrajn lemma (additive form)

This file formalizes the additive-group form used in Pivato's appendix:
on a torsion-free abelian group, every homogeneous partial order extends
to a homogeneous linear order.
-/

open Set

namespace Pivato

section AddGroupConeExtension

variable {G : Type*} [AddCommGroup G]

/-- The set obtained by adjoining a generator `a` to an additive cone `C`. -/
def adjoinCarrier (C : AddSubmonoid G) (a : G) : Set G :=
  {x | ∃ c ∈ C, ∃ n : ℕ, x = c + n • a}

/-- Pointedness property for a subset of an additive group. -/
def IsPointed (S : Set G) : Prop :=
  ∀ ⦃x : G⦄, x ∈ S → -x ∈ S → x = 0

lemma mem_adjoinCarrier_of_mem {C : AddSubmonoid G} {a x : G} (hx : x ∈ C) :
    x ∈ adjoinCarrier C a := by
  refine ⟨x, hx, 0, by simp⟩

lemma subset_adjoinCarrier (C : AddSubmonoid G) (a : G) : (C : Set G) ⊆ adjoinCarrier C a := by
  intro x hx
  exact mem_adjoinCarrier_of_mem hx

lemma mem_adjoinCarrier_self (C : AddSubmonoid G) (a : G) : a ∈ adjoinCarrier C a := by
  refine ⟨0, C.zero_mem, 1, ?_⟩
  rw [zero_add, one_nsmul]

/-- `adjoinCarrier C a` as an additive submonoid. -/
def adjoinCone (C : AddSubmonoid G) (a : G) : AddSubmonoid G where
  carrier := adjoinCarrier C a
  zero_mem' := mem_adjoinCarrier_of_mem C.zero_mem
  add_mem' := by
    intro x y hx hy
    rcases hx with ⟨cx, hcx, nx, rfl⟩
    rcases hy with ⟨cy, hcy, ny, rfl⟩
    refine ⟨cx + cy, C.add_mem hcx hcy, nx + ny, ?_⟩
    simp [add_assoc, add_left_comm, add_nsmul]

/-- Zorn: every pointed additive cone extends to a maximal pointed one. -/
theorem exists_maximal_cone_extension (C0 : AddSubmonoid G) (hC0 : C0.IsPointed) :
    ∃ M : AddSubmonoid G, C0 ≤ M ∧
      Maximal (fun D : AddSubmonoid G => C0 ≤ D ∧ D.IsPointed) M := by
  let S : Set (AddSubmonoid G) := {D | C0 ≤ D ∧ D.IsPointed}
  have hchain :
      ∀ c ⊆ S, IsChain (· ≤ ·) c →
        ∀ y ∈ c, ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcS hc y hy
    have hmem {x : G} : x ∈ sSup c ↔ ∃ D ∈ c, x ∈ D :=
      AddSubmonoid.mem_sSup_of_directedOn ⟨y, hy⟩ hc.directedOn
    refine ⟨sSup c, ⟨(hcS hy).1.trans (le_sSup hy), ?_⟩, fun z hz => le_sSup hz⟩
    intro x hx hnegx
    obtain ⟨Dx, hDx, hxDx⟩ := hmem.1 hx
    obtain ⟨Dz, hDz, hnegxDz⟩ := hmem.1 hnegx
    rcases hc.total hDx hDz with hDxz | hDzx
    · exact (hcS hDz).2 x (hDxz hxDx) hnegxDz
    · exact (hcS hDx).2 x hxDx (hDzx hnegxDz)
  exact zorn_le_nonempty₀ S hchain C0 ⟨le_rfl, hC0⟩

lemma exists_pos_nat_neg_nsmul_mem_of_not_pointed_adjoin
    {C : AddSubmonoid G} (hC : C.IsPointed) {a : G}
    (hnot : ¬ IsPointed (adjoinCarrier C a)) :
    ∃ n : ℕ, 0 < n ∧ -(n • a) ∈ C := by
  by_contra h
  apply hnot
  intro x hx hnegx
  rcases hx with ⟨c1, hc1, n1, hxEq⟩
  rcases hnegx with ⟨c2, hc2, n2, hnegEq⟩
  have hsum : c1 + c2 + (n1 + n2) • a = 0 := by
    calc
      c1 + c2 + (n1 + n2) • a = (c1 + n1 • a) + (c2 + n2 • a) := by
        simp [add_assoc, add_left_comm, add_nsmul]
      _ = (c1 + n1 • a) + (-x) := by simp [hnegEq]
      _ = x + (-x) := by simp [hxEq]
      _ = 0 := by simp
  have hnegMem : -((n1 + n2) • a) ∈ C := by
    have hEq : c1 + c2 = -((n1 + n2) • a) := eq_neg_of_add_eq_zero_left hsum
    have hc12 : c1 + c2 ∈ C := C.add_mem hc1 hc2
    simpa [hEq] using hc12
  have hNotPos : ¬ 0 < n1 + n2 := by
    intro hpos
    exact h ⟨n1 + n2, hpos, hnegMem⟩
  have hzeroNat : n1 + n2 = 0 := Nat.eq_zero_of_not_pos hNotPos
  rcases Nat.add_eq_zero_iff.mp hzeroNat with ⟨hn1, hn2⟩
  have hxC : x ∈ C := by
    simpa [hxEq, hn1] using hc1
  have hnegxC : -x ∈ C := by
    simpa [hnegEq, hn2] using hc2
  exact hC.eq_zero_of_mem_of_neg_mem hxC hnegxC

lemma not_pointed_adjoin_of_not_mem
    {C0 M : AddSubmonoid G}
    (hmax : Maximal (fun D : AddSubmonoid G => C0 ≤ D ∧ D.IsPointed) M)
    {a : G} (ha : a ∉ M) :
    ¬ IsPointed (adjoinCarrier M a) := by
  intro hpoint
  have hMD : M ≤ adjoinCone M a := subset_adjoinCarrier M a
  have hDM : adjoinCone M a ≤ M :=
    hmax.le_of_ge ⟨hmax.prop.1.trans hMD, fun _ hx hnx => hpoint hx hnx⟩ hMD
  exact ha (hDM (mem_adjoinCarrier_self M a))

/-- A maximal pointed cone in a torsion-free group is total. -/
theorem maximal_cone_mem_or_neg_mem
    [IsAddTorsionFree G] {C0 M : AddSubmonoid G}
    (hmax : Maximal (fun D : AddSubmonoid G => C0 ≤ D ∧ D.IsPointed) M) (a : G) :
    a ∈ M ∨ -a ∈ M := by
  by_cases ha : a ∈ M
  · exact Or.inl ha
  by_cases hna : -a ∈ M
  · exact Or.inr hna
  have hM : M.IsPointed := hmax.prop.2
  obtain ⟨m, hmpos, hmneg⟩ :=
    exists_pos_nat_neg_nsmul_mem_of_not_pointed_adjoin hM (not_pointed_adjoin_of_not_mem hmax ha)
  obtain ⟨n, hnpos, hnneg⟩ :=
    exists_pos_nat_neg_nsmul_mem_of_not_pointed_adjoin hM (not_pointed_adjoin_of_not_mem hmax hna)
  have hposMul : n • a ∈ M := by
    simpa [neg_nsmul, neg_neg] using hnneg
  have hmul : (m * n) • a ∈ M := by
    simpa [mul_nsmul', Nat.mul_comm] using nsmul_mem hposMul m
  have hnegMul : -((m * n) • a) ∈ M := by
    have : n • (-(m • a)) ∈ M := nsmul_mem hmneg n
    have htmp : -(n • m • a) ∈ M := by
      simpa [neg_nsmul] using this
    have hEqnm : n • m • a = (m * n) • a := by
      simpa [Nat.mul_comm] using (mul_nsmul' a n m).symm
    simpa [hEqnm] using htmp
  have hzeroMul : (m * n) • a = 0 := hM.eq_zero_of_mem_of_neg_mem hmul hnegMul
  have hmn_ne_zero : m * n ≠ 0 := Nat.mul_ne_zero (Nat.ne_of_gt hmpos) (Nat.ne_of_gt hnpos)
  have ha0 : a = 0 := (nsmul_eq_zero_iff_right hmn_ne_zero).1 hzeroMul
  exact False.elim (ha (ha0 ▸ M.zero_mem))

/-- Cone form of the homogeneous Szpilrajn lemma. -/
theorem homogeneous_szpilrajn_cone
    [IsAddTorsionFree G] (C0 : AddSubmonoid G) (hC0 : C0.IsPointed) :
    ∃ M : AddSubmonoid G, C0 ≤ M ∧ M.IsPointed ∧ M.IsSpanning := by
  obtain ⟨M, hC0M, hmax⟩ := exists_maximal_cone_extension C0 hC0
  exact ⟨M, hC0M, hmax.prop.2, maximal_cone_mem_or_neg_mem hmax⟩

end AddGroupConeExtension

section RelationForm

variable {G : Type*} [AddCommGroup G]

/-- Homogeneity in difference form. -/
def Homogeneous (r : G → G → Prop) : Prop :=
  ∀ x y, r x y ↔ r 0 (y - x)

/-- Positive cone associated to a homogeneous relation. -/
def coneOfHomogeneous (r : G → G → Prop) [IsPartialOrder G r] (hr : Homogeneous r) :
    AddSubmonoid G where
  carrier := {a : G | r 0 a}
  zero_mem' := by simpa using (refl (r := r) 0)
  add_mem' := by
    intro a b ha hb
    have hab : r a (a + b) := by
      exact (hr a (a + b)).2 (by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hb)
    exact trans ha hab

lemma coneOfHomogeneous_isPointed (r : G → G → Prop) [IsPartialOrder G r]
    (hr : Homogeneous r) : (coneOfHomogeneous r hr).IsPointed := by
  intro a ha hna
  have ha0 : r a 0 := (hr a 0).2 (by simpa using show r 0 (-a) from hna)
  exact antisymm ha0 ha

/-- Homogeneous Szpilrajn lemma (relation form). -/
theorem homogeneous_szpilrajn
    [IsAddTorsionFree G]
    (r : G → G → Prop) [IsPartialOrder G r] (hr : Homogeneous r) :
    ∃ s : G → G → Prop, IsLinearOrder G s ∧ r ≤ s ∧ Homogeneous s := by
  classical
  obtain ⟨M, hC0M, hMp, hMs⟩ :=
    homogeneous_szpilrajn_cone (coneOfHomogeneous r hr) (coneOfHomogeneous_isPointed r hr)
  let : LinearOrder G := LinearOrder.ofAddSubmonoid hMp hMs
  refine ⟨(· ≤ ·), inferInstance, ?_, ?_⟩
  · intro x y hxy
    have hmem : y - x ∈ M := hC0M ((hr x y).1 hxy)
    simpa using hmem
  · intro x y
    simp [sub_eq_add_neg]

end RelationForm

end Pivato
