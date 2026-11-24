import Pivato.HomogeneousSzpilrajn

/-!
# Ordered-additive packaging for homogeneous order extension

This file packages the homogeneous Szpilrajn construction so the extended
linear order is accompanied by ordered-additive structure (`IsOrderedAddMonoid`
and the corresponding `CovariantClass` instances).
-/

namespace Pivato

section OrderedAdditiveExtension

variable {G : Type*} [AddCommGroup G]

/-- The relation induced by an explicit `LinearOrder` witness. -/
def leOfLinearOrder (instLin : LinearOrder G) : G → G → Prop :=
  fun a b => @LE.le G instLin.toLE a b

/-- The strict relation induced by an explicit `LinearOrder` witness. -/
def ltOfLinearOrder (instLin : LinearOrder G) : G → G → Prop :=
  fun a b => @LT.lt G instLin.toLT a b

/-- Package the order from an additive cone into ordered-additive typeclass
witnesses, with an explicit characterization of the induced `≤`. -/
theorem orderedAdditiveLinearOrder_of_cone
    {M : AddSubmonoid G} (hMp : M.IsPointed) (hMs : M.IsSpanning)
    [DecidablePred (fun x : G => x ∈ M)] :
    ∃ (instLin : LinearOrder G),
      ∃ (instOrd : IsOrderedAddMonoid G),
      ∃ (instCovLe : CovariantClass G G (fun a b => a + b) (leOfLinearOrder instLin)),
      ∃ (instCovLt : CovariantClass G G (fun a b => a + b) (ltOfLinearOrder instLin)),
        letI : LinearOrder G := instLin
        letI : IsOrderedAddMonoid G := instOrd
        letI : CovariantClass G G (fun a b => a + b) (leOfLinearOrder instLin) := instCovLe
        letI : CovariantClass G G (fun a b => a + b) (ltOfLinearOrder instLin) := instCovLt
        ∀ x y, leOfLinearOrder instLin x y ↔ y - x ∈ M := by
  let instLin : LinearOrder G := LinearOrder.ofAddSubmonoid hMp hMs
  let instOrd : IsOrderedAddMonoid G := IsOrderedAddMonoid.ofAddSubmonoid hMp
  let : LinearOrder G := instLin
  let : IsOrderedAddMonoid G := instOrd
  let instCovLe : CovariantClass G G (fun a b => a + b) (leOfLinearOrder instLin) := by
    change CovariantClass G G (fun a b => a + b) (· ≤ ·)
    infer_instance
  let instCovLt : CovariantClass G G (fun a b => a + b) (ltOfLinearOrder instLin) := by
    change CovariantClass G G (fun a b => a + b) (· < ·)
    infer_instance
  refine ⟨instLin, instOrd, instCovLe, instCovLt, ?_⟩
  intro x y
  simp [leOfLinearOrder, instLin]

/-- Homogeneous Szpilrajn with ordered-additive packaging: the extended
linear order is provided together with `IsOrderedAddMonoid` and covariance
instances. -/
theorem homogeneous_szpilrajn_orderedAdditive
    [IsAddTorsionFree G]
    (r : G → G → Prop) [IsPartialOrder G r] (hr : Homogeneous r) :
    ∃ (instLin : LinearOrder G),
      ∃ (instOrd : IsOrderedAddMonoid G),
      ∃ (instCovLe : CovariantClass G G (fun a b => a + b) (leOfLinearOrder instLin)),
      ∃ (instCovLt : CovariantClass G G (fun a b => a + b) (ltOfLinearOrder instLin)),
        letI : LinearOrder G := instLin
        letI : IsOrderedAddMonoid G := instOrd
        letI : CovariantClass G G (fun a b => a + b) (leOfLinearOrder instLin) := instCovLe
        letI : CovariantClass G G (fun a b => a + b) (ltOfLinearOrder instLin) := instCovLt
        r ≤ leOfLinearOrder instLin ∧ Homogeneous (leOfLinearOrder instLin) := by
  classical
  obtain ⟨M, hC0M, hMp, hMs⟩ :=
    homogeneous_szpilrajn_cone (coneOfHomogeneous r hr) (coneOfHomogeneous_isPointed r hr)
  obtain ⟨instLin, instOrd, instCovLe, instCovLt, hleiff⟩ :=
    orderedAdditiveLinearOrder_of_cone hMp hMs
  refine ⟨instLin, instOrd, instCovLe, instCovLt, ?_⟩
  constructor
  · intro x y hxy
    have hmem : y - x ∈ M := hC0M ((hr x y).1 hxy)
    exact (hleiff x y).2 hmem
  · intro x y
    constructor
    · intro hxy
      have hmem : y - x ∈ M := (hleiff x y).1 hxy
      exact (hleiff 0 (y - x)).2 (by simpa using hmem)
    · intro h0
      have hmem : y - x ∈ M := by
        simpa using (hleiff 0 (y - x)).1 h0
      exact (hleiff x y).2 (by simpa using hmem)

end OrderedAdditiveExtension

end Pivato
