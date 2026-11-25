import Pivato.Core
import Mathlib.Data.Fintype.Perm

/-!
# Profile-level helpers

This file provides basic maps between `NProfile` and `ZProfile`, and
signal-permutation actions on finitely supported profiles.
-/

namespace Pivato

section Coercions

variable {V : Type*}

/-- Cast a nonnegative count profile to an integer-valued profile. -/
noncomputable def toZProfile (d : NProfile V) : ZProfile V :=
  d.mapRange (fun n : ℕ => (n : ℤ)) (by simp)

@[simp] lemma toZProfile_apply (d : NProfile V) (v : V) :
    toZProfile d v = (d v : ℤ) := by
  simp [toZProfile]

@[simp] lemma toZProfile_zero :
    toZProfile (0 : NProfile V) = (0 : ZProfile V) := by
  ext v
  simp [toZProfile]

@[simp] lemma toZProfile_add (d e : NProfile V) :
    toZProfile (d + e) = toZProfile d + toZProfile e := by
  ext v
  simp [toZProfile, Nat.cast_add]

lemma toZProfile_injective : Function.Injective (toZProfile (V := V)) := by
  intro d e hde
  ext v
  exact Int.ofNat.inj (by simpa [toZProfile_apply] using congrArg (fun f => f v) hde)

end Coercions

section Permutations

variable {V : Type*}

/-- Reindex a count profile by a permutation of signals. -/
def permuteNProfile (π : Equiv.Perm V) : NProfile V ≃+ NProfile V :=
  Finsupp.domCongr π

/-- Reindex an integer-valued profile by a permutation of signals. -/
def permuteZProfile (π : Equiv.Perm V) : ZProfile V ≃+ ZProfile V :=
  Finsupp.domCongr π

@[simp] lemma permuteNProfile_apply (π : Equiv.Perm V) (d : NProfile V) (v : V) :
    permuteNProfile π d v = d (π.symm v) := by
  simp [permuteNProfile, Finsupp.domCongr_apply]

@[simp] lemma permuteNProfile_one (d : NProfile V) :
    permuteNProfile (1 : Equiv.Perm V) d = d := by
  ext v
  rfl

@[simp] lemma permuteNProfile_mul (π ρ : Equiv.Perm V) (d : NProfile V) :
    permuteNProfile (π * ρ) d = permuteNProfile π (permuteNProfile ρ d) := by
  ext v
  simp [permuteNProfile_apply, Equiv.Perm.mul_def]

@[simp] lemma permuteZProfile_apply (π : Equiv.Perm V) (d : ZProfile V) (v : V) :
    permuteZProfile π d v = d (π.symm v) := by
  simp [permuteZProfile, Finsupp.domCongr_apply]

@[simp] lemma permuteZProfile_one (d : ZProfile V) :
    permuteZProfile (1 : Equiv.Perm V) d = d := by
  ext v
  rfl

@[simp] lemma permuteZProfile_mul (π ρ : Equiv.Perm V) (d : ZProfile V) :
    permuteZProfile (π * ρ) d = permuteZProfile π (permuteZProfile ρ d) := by
  ext v
  simp [permuteZProfile_apply, Equiv.Perm.mul_def]

end Permutations

end Pivato
