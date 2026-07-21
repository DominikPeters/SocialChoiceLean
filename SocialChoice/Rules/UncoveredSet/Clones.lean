import SocialChoice.Axioms.Clones
import SocialChoice.Rules.UncoveredSet.Defs
import SocialChoice.Rules.TopCycle.Clones

namespace SocialChoice

open Finset

private def repCand {A : Type} (X : Set A) (x : A) :
    {a : A // clonePred X x a} := ⟨x, Or.inr rfl⟩

section

variable {V A : Type} [Fintype V] [Fintype A]
variable (P : Profile V A) (X : Set A) (x : A)

local notation "P'" => removeClonesExcept P X x
local notation "rep" => repCand (X := X) (x := x)

lemma covers_nonclone_clone_iff_rep
    (hX : CloneSet P X) (hx : x ∈ X)
    {c y : A} (hc : c ∉ X) (hy : y ∈ X) :
    covers P c y ↔ covers P c x := by
  constructor
  · intro hcy
    rcases hcy with ⟨hcy1, hcy2, hcy3⟩
    have hcx0 : margin_pos P c x :=
      (margin_pos_nonclone_vs_clone_iff (P := P) (X := X) (hX := hX)
        (x := x) (y := y) (b := c) hx hy hc).1 hcy1
    refine ⟨?_, ?_, ?_⟩
    · exact hcx0
    · intro z hxz
      by_cases hzX : z ∈ X
      · exact (margin_pos_nonclone_vs_clone_iff (P := P) (X := X) (hX := hX)
          (x := x) (y := z) (b := c) hx hzX hc).2 hcx0
      · have hyz : margin_pos P y z :=
          (margin_pos_clone_vs_nonclone_iff (P := P) (X := X) (hX := hX)
            (x := x) (y := y) (b := z) hx hy hzX).2 hxz
        exact hcy2 z hyz
    · intro z hzc
      by_cases hzX : z ∈ X
      · have hxc : margin_pos P x c :=
          (margin_pos_clone_vs_nonclone_iff (P := P) (X := X) (hX := hX)
            (x := x) (y := z) (b := c) hx hzX hc).1 hzc
        exact (False.elim ((margin_pos_asymm (P := P) c x hcx0) hxc))
      · have hzy : margin_pos P z y := hcy3 z hzc
        exact (margin_pos_nonclone_vs_clone_iff (P := P) (X := X) (hX := hX)
          (x := x) (y := y) (b := z) hx hy hzX).1 hzy
  · intro hcx
    rcases hcx with ⟨hcx1, hcx2, hcx3⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (margin_pos_nonclone_vs_clone_iff (P := P) (X := X) (hX := hX)
        (x := x) (y := y) (b := c) hx hy hc).2 hcx1
    · intro z hyz
      by_cases hzX : z ∈ X
      · exact (margin_pos_nonclone_vs_clone_iff (P := P) (X := X) (hX := hX)
          (x := x) (y := z) (b := c) hx hzX hc).2 hcx1
      · have hxz : margin_pos P x z :=
          (margin_pos_clone_vs_nonclone_iff (P := P) (X := X) (hX := hX)
            (x := x) (y := y) (b := z) hx hy hzX).1 hyz
        exact hcx2 z hxz
    · intro z hzc
      by_cases hzX : z ∈ X
      · have hxc : margin_pos P x c :=
          (margin_pos_clone_vs_nonclone_iff (P := P) (X := X) (hX := hX)
            (x := x) (y := z) (b := c) hx hzX hc).1 hzc
        exact (False.elim ((margin_pos_asymm (P := P) c x hcx1) hxc))
      · have hzx : margin_pos P z x := hcx3 z hzc
        exact (margin_pos_nonclone_vs_clone_iff (P := P) (X := X) (hX := hX)
          (x := x) (y := y) (b := z) hx hy hzX).2 hzx

lemma covers_clone_nonclone_iff_rep
    (hX : CloneSet P X) (hx : x ∈ X)
    {c y : A} (hc : c ∉ X) (hy : y ∈ X) :
    covers P y c ↔ covers P x c := by
  constructor
  · intro hyc
    rcases hyc with ⟨hyc1, hyc2, hyc3⟩
    have hxc0 : margin_pos P x c :=
      (margin_pos_clone_vs_nonclone_iff (P := P) (X := X) (hX := hX)
        (x := x) (y := y) (b := c) hx hy hc).1 hyc1
    refine ⟨?_, ?_, ?_⟩
    · exact hxc0
    · intro z hcz
      by_cases hzX : z ∈ X
      · have hcx : margin_pos P c x :=
          (margin_pos_nonclone_vs_clone_iff (P := P) (X := X) (hX := hX)
            (x := x) (y := z) (b := c) hx hzX hc).1 hcz
        exact (False.elim ((margin_pos_asymm (P := P) x c hxc0) hcx))
      · have hyz : margin_pos P y z := hyc2 z hcz
        exact (margin_pos_clone_vs_nonclone_iff (P := P) (X := X) (hX := hX)
          (x := x) (y := y) (b := z) hx hy hzX).1 hyz
    · intro z hzx
      by_cases hzX : z ∈ X
      · exact (margin_pos_clone_vs_nonclone_iff (P := P) (X := X) (hX := hX)
          (x := x) (y := z) (b := c) hx hzX hc).2 hxc0
      · have hzy : margin_pos P z y :=
          (margin_pos_nonclone_vs_clone_iff (P := P) (X := X) (hX := hX)
            (x := x) (y := y) (b := z) hx hy hzX).2 hzx
        exact hyc3 z hzy
  · intro hxc
    rcases hxc with ⟨hxc1, hxc2, hxc3⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (margin_pos_clone_vs_nonclone_iff (P := P) (X := X) (hX := hX)
        (x := x) (y := y) (b := c) hx hy hc).2 hxc1
    · intro z hcz
      by_cases hzX : z ∈ X
      · have hcx : margin_pos P c x :=
          (margin_pos_nonclone_vs_clone_iff (P := P) (X := X) (hX := hX)
            (x := x) (y := z) (b := c) hx hzX hc).1 hcz
        exact (False.elim ((margin_pos_asymm (P := P) x c hxc1) hcx))
      · have hxz : margin_pos P x z := hxc2 z hcz
        exact (margin_pos_clone_vs_nonclone_iff (P := P) (X := X) (hX := hX)
          (x := x) (y := y) (b := z) hx hy hzX).2 hxz
    · intro z hzy
      by_cases hzX : z ∈ X
      · exact (margin_pos_clone_vs_nonclone_iff (P := P) (X := X) (hX := hX)
          (x := x) (y := z) (b := c) hx hzX hc).2 ‹margin_pos P x c›
      · have hzx : margin_pos P z x :=
          (margin_pos_nonclone_vs_clone_iff (P := P) (X := X) (hX := hX)
            (x := x) (y := y) (b := z) hx hy hzX).1 hzy
        exact hxc3 z hzx

lemma covers_reduced_nonclone_nonclone_iff
    (hX : CloneSet P X) (hx : x ∈ X)
    {c d : A} (hc : c ∉ X) (hd : d ∉ X) :
    covers P' (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a})
      (⟨d, Or.inl hd⟩ : {a : A // clonePred X x a}) ↔
    covers P c d := by
  constructor
  · intro hred
    rcases hred with ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
        (a := ⟨c, Or.inl hc⟩) (b := ⟨d, Or.inl hd⟩)).1 h1
    · intro z hdz
      by_cases hzX : z ∈ X
      · have hdx : margin_pos P d x :=
          (margin_pos_nonclone_vs_clone_iff (P := P) (X := X) (hX := hX)
            (x := x) (y := z) (b := d) hx hzX hd).1 hdz
        have hyx : margin_pos P' (⟨d, Or.inl hd⟩ : {a : A // clonePred X x a}) rep :=
          (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
            (a := ⟨d, Or.inl hd⟩) (b := rep)).2 hdx
        have hcx' : margin_pos P' (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) rep := h2 rep hyx
        have hcx : margin_pos P c x :=
          (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
            (a := ⟨c, Or.inl hc⟩) (b := rep)).1 hcx'
        exact (margin_pos_nonclone_vs_clone_iff (P := P) (X := X) (hX := hX)
          (x := x) (y := z) (b := c) hx hzX hc).2 hcx
      · have hdz' : margin_pos P' (⟨d, Or.inl hd⟩ : {a : A // clonePred X x a})
            (⟨z, Or.inl hzX⟩ : {a : A // clonePred X x a}) :=
          (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
            (a := ⟨d, Or.inl hd⟩) (b := ⟨z, Or.inl hzX⟩)).2 hdz
        have hcz' : margin_pos P' (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a})
            (⟨z, Or.inl hzX⟩ : {a : A // clonePred X x a}) := h2 _ hdz'
        exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
          (a := ⟨c, Or.inl hc⟩) (b := ⟨z, Or.inl hzX⟩)).1 hcz'
    · intro z hzc
      by_cases hzX : z ∈ X
      · have hxy : margin_pos P x c :=
          (margin_pos_clone_vs_nonclone_iff (P := P) (X := X) (hX := hX)
            (x := x) (y := z) (b := c) hx hzX hc).1 hzc
        have hxy' : margin_pos P' rep (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) :=
          (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
            (a := rep) (b := ⟨c, Or.inl hc⟩)).2 hxy
        have hdc' : margin_pos P' rep (⟨d, Or.inl hd⟩ : {a : A // clonePred X x a}) := h3 rep hxy'
        have hdc : margin_pos P x d :=
          (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
            (a := rep) (b := ⟨d, Or.inl hd⟩)).1 hdc'
        exact (margin_pos_clone_vs_nonclone_iff (P := P) (X := X) (hX := hX)
          (x := x) (y := z) (b := d) hx hzX hd).2 hdc
      · have hzc' : margin_pos P' (⟨z, Or.inl hzX⟩ : {a : A // clonePred X x a})
            (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) :=
          (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
            (a := ⟨z, Or.inl hzX⟩) (b := ⟨c, Or.inl hc⟩)).2 hzc
        have hzd' : margin_pos P' (⟨z, Or.inl hzX⟩ : {a : A // clonePred X x a})
            (⟨d, Or.inl hd⟩ : {a : A // clonePred X x a}) := h3 _ hzc'
        exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
          (a := ⟨z, Or.inl hzX⟩) (b := ⟨d, Or.inl hd⟩)).1 hzd'
  · intro hcov
    rcases hcov with ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
        (a := ⟨c, Or.inl hc⟩) (b := ⟨d, Or.inl hd⟩)).2 h1
    · intro z hz
      by_cases hzX : (z : A) ∈ X
      · have zx : (z : A) = x := by
          rcases z.2 with hzNot | hEq
          · exact (hzNot hzX).elim
          · exact hEq
        have hdx : margin_pos P d x := by
          have hdz : margin_pos P' (⟨d, Or.inl hd⟩ : {a : A // clonePred X x a}) z := hz
          have hdz' : margin_pos P d (z : A) :=
            (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
              (a := ⟨d, Or.inl hd⟩) (b := z)).1 hdz
          simpa [zx] using hdz'
        have hcx : margin_pos P c x := h2 x hdx
        exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
          (a := ⟨c, Or.inl hc⟩) (b := z)).2 (by simpa [zx] using hcx)
      · have hdz : margin_pos P d (z : A) :=
          (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
            (a := ⟨d, Or.inl hd⟩) (b := z)).1 hz
        have hcz : margin_pos P c (z : A) := h2 (z : A) hdz
        exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
          (a := ⟨c, Or.inl hc⟩) (b := z)).2 hcz
    · intro z hz
      by_cases hzX : (z : A) ∈ X
      · have zx : (z : A) = x := by
          rcases z.2 with hzNot | hEq
          · exact (hzNot hzX).elim
          · exact hEq
        have hxc : margin_pos P x c := by
          have hzc : margin_pos P' z (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) := hz
          have hzc' : margin_pos P (z : A) c :=
            (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
              (a := z) (b := ⟨c, Or.inl hc⟩)).1 hzc
          simpa [zx] using hzc'
        have hxd : margin_pos P x d := h3 x hxc
        exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
          (a := z) (b := ⟨d, Or.inl hd⟩)).2 (by simpa [zx] using hxd)
      · have hzc : margin_pos P (z : A) c :=
          (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
            (a := z) (b := ⟨c, Or.inl hc⟩)).1 hz
        have hzd : margin_pos P (z : A) d := h3 (z : A) hzc
        exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
          (a := z) (b := ⟨d, Or.inl hd⟩)).2 hzd

lemma covers_reduced_nonclone_rep_iff
    (hX : CloneSet P X) (hx : x ∈ X)
    {c : A} (hc : c ∉ X) :
    covers P' (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) rep ↔
      covers P c x := by
  constructor
  · intro hred
    rcases hred with ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
        (a := ⟨c, Or.inl hc⟩) (b := rep)).1 h1
    · intro z hxz
      by_cases hzX : z ∈ X
      · exact (margin_pos_nonclone_vs_clone_iff (P := P) (X := X) (hX := hX)
          (x := x) (y := z) (b := c) hx hzX hc).2 ‹margin_pos P c x›
      · have hxz' : margin_pos P' rep (⟨z, Or.inl hzX⟩ : {a : A // clonePred X x a}) :=
          (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
            (a := rep) (b := ⟨z, Or.inl hzX⟩)).2 hxz
        have hcz' : margin_pos P' (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a})
            (⟨z, Or.inl hzX⟩ : {a : A // clonePred X x a}) := h2 _ hxz'
        exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
          (a := ⟨c, Or.inl hc⟩) (b := ⟨z, Or.inl hzX⟩)).1 hcz'
    · intro z hzc
      by_cases hzX : z ∈ X
      · have hcx : margin_pos P c x := ‹margin_pos P c x›
        have hcz' : margin_pos P c z :=
          (margin_pos_nonclone_vs_clone_iff (P := P) (X := X) (hX := hX)
            (x := x) (y := z) (b := c) hx hzX hc).2 hcx
        exact (False.elim ((margin_pos_asymm (P := P) c z hcz') hzc))
      · have hzc' : margin_pos P' (⟨z, Or.inl hzX⟩ : {a : A // clonePred X x a})
            (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) :=
          (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
            (a := ⟨z, Or.inl hzX⟩) (b := ⟨c, Or.inl hc⟩)).2 hzc
        have hzx' : margin_pos P' (⟨z, Or.inl hzX⟩ : {a : A // clonePred X x a}) rep := h3 _ hzc'
        exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
          (a := ⟨z, Or.inl hzX⟩) (b := rep)).1 hzx'
  · intro hcov
    rcases hcov with ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
        (a := ⟨c, Or.inl hc⟩) (b := rep)).2 h1
    · intro z hz
      by_cases hzX : (z : A) ∈ X
      · have zx : (z : A) = x := by
          rcases z.2 with hzNot | hEq
          · exact (hzNot hzX).elim
          · exact hEq
        have hcx : margin_pos P c x :=
          (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
            (a := ⟨c, Or.inl hc⟩) (b := rep)).1 h1
        exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
          (a := ⟨c, Or.inl hc⟩) (b := z)).2 (by simpa [zx] using hcx)
      · have hxz : margin_pos P x (z : A) :=
          (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
            (a := rep) (b := z)).1 hz
        have hcz : margin_pos P c (z : A) := h2 (z : A) hxz
        exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
          (a := ⟨c, Or.inl hc⟩) (b := z)).2 hcz
    · intro z hz
      by_cases hzX : (z : A) ∈ X
      · have zx : (z : A) = x := by
          rcases z.2 with hzNot | hEq
          · exact (hzNot hzX).elim
          · exact hEq
        have hxc : margin_pos P x c := by
          have hzx : margin_pos P' rep (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) := by
            have hzrep : z = rep := Subtype.ext zx
            simpa [hzrep] using hz
          exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
            (a := rep) (b := ⟨c, Or.inl hc⟩)).1 hzx
        exact (False.elim ((margin_pos_asymm (P := P) c x h1) hxc))
      · have hzc : margin_pos P (z : A) c :=
          (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
            (a := z) (b := ⟨c, Or.inl hc⟩)).1 hz
        have hzx : margin_pos P (z : A) x := h3 (z : A) hzc
        exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
          (a := z) (b := rep)).2 hzx

lemma covers_reduced_rep_nonclone_iff
    (hX : CloneSet P X) (hx : x ∈ X)
    {c : A} (hc : c ∉ X) :
    covers P' rep (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) ↔
      covers P x c := by
  constructor
  · intro hred
    rcases hred with ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
        (a := rep) (b := ⟨c, Or.inl hc⟩)).1 h1
    · intro z hcz
      by_cases hzX : z ∈ X
      · have hcx : margin_pos P c x :=
          (margin_pos_nonclone_vs_clone_iff (P := P) (X := X) (hX := hX)
            (x := x) (y := z) (b := c) hx hzX hc).1 hcz
        exact (False.elim ((margin_pos_asymm (P := P) x c ‹margin_pos P x c›) hcx))
      · have hcz' : margin_pos P' (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a})
            (⟨z, Or.inl hzX⟩ : {a : A // clonePred X x a}) :=
          (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
            (a := ⟨c, Or.inl hc⟩) (b := ⟨z, Or.inl hzX⟩)).2 hcz
        have hxz' : margin_pos P' rep (⟨z, Or.inl hzX⟩ : {a : A // clonePred X x a}) := h2 _ hcz'
        exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
          (a := rep) (b := ⟨z, Or.inl hzX⟩)).1 hxz'
    · intro z hzx
      by_cases hzX : z ∈ X
      · exact (margin_pos_clone_vs_nonclone_iff (P := P) (X := X) (hX := hX)
          (x := x) (y := z) (b := c) hx hzX hc).2 ‹margin_pos P x c›
      · have hzx' : margin_pos P' (⟨z, Or.inl hzX⟩ : {a : A // clonePred X x a}) rep :=
          (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
            (a := ⟨z, Or.inl hzX⟩) (b := rep)).2 hzx
        have hzc' : margin_pos P' (⟨z, Or.inl hzX⟩ : {a : A // clonePred X x a})
            (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) := h3 _ hzx'
        exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
          (a := ⟨z, Or.inl hzX⟩) (b := ⟨c, Or.inl hc⟩)).1 hzc'
  · intro hcov
    rcases hcov with ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
        (a := rep) (b := ⟨c, Or.inl hc⟩)).2 h1
    · intro z hz
      by_cases hzX : (z : A) ∈ X
      · have zx : (z : A) = x := by
          rcases z.2 with hzNot | hEq
          · exact (hzNot hzX).elim
          · exact hEq
        have hxc : margin_pos P x c :=
          (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
            (a := rep) (b := ⟨c, Or.inl hc⟩)).1 h1
        have hcx : margin_pos P c x := by
          simpa [zx] using
            (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
              (a := ⟨c, Or.inl hc⟩) (b := z)).1 hz
        exact (False.elim ((margin_pos_asymm (P := P) x c hxc) hcx))
      · have hcz : margin_pos P c (z : A) :=
          (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
            (a := ⟨c, Or.inl hc⟩) (b := z)).1 hz
        have hxz : margin_pos P x (z : A) := h2 (z : A) hcz
        exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
          (a := rep) (b := z)).2 hxz
    · intro z hz
      by_cases hzX : (z : A) ∈ X
      · have zx : (z : A) = x := by
          rcases z.2 with hzNot | hEq
          · exact (hzNot hzX).elim
          · exact hEq
        have hxc : margin_pos P x c := h1
        exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
          (a := z) (b := ⟨c, Or.inl hc⟩)).2 (by simpa [zx] using hxc)
      · have hzx : margin_pos P (z : A) x :=
          (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
            (a := z) (b := rep)).1 hz
        have hzc : margin_pos P (z : A) c := h3 (z : A) hzx
        exact (margin_pos_removeClonesExcept_iff (P := P) (X := X) (x := x)
          (a := z) (b := ⟨c, Or.inl hc⟩)).2 hzc

lemma uncovered_nonclone_iff_reduced
    (hX : CloneSet P X) (hx : x ∈ X)
    {c : A} (hc : c ∉ X) :
    uncovered P c ↔ uncovered P' (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) := by
  constructor
  · intro hunc t htc hcov
    by_cases htX : (t : A) ∈ X
    · have tx : (t : A) = x := by
        rcases t.2 with htNot | hEq
        · exact (htNot htX).elim
        · exact hEq
      have trep : t = rep := by
        apply Subtype.ext
        exact tx
      have hxc : covers P x c :=
        (covers_reduced_rep_nonclone_iff (P := P) (X := X) (x := x) (hX := hX) (hx := hx)
          (c := c) hc).1 (by simpa [trep] using hcov)
      have hneq : x ≠ c := by
        intro hEq
        exact hc (by simpa [hEq] using hx)
      exact (hunc x hneq hxc).elim
    · have hyc : covers P (t : A) c :=
        (covers_reduced_nonclone_nonclone_iff (P := P) (X := X) (x := x) (hX := hX) (hx := hx)
          (c := (t : A)) (d := c) htX hc).1 (by simpa using hcov)
      have hneq : (t : A) ≠ c := by
        intro hEq
        apply htc
        apply Subtype.ext
        exact hEq
      exact (hunc (t : A) hneq hyc).elim
  · intro hunc y hyc hcov
    by_cases hyX : y ∈ X
    · have hxc : covers P x c :=
        (covers_clone_nonclone_iff_rep (P := P) (X := X) (x := x) (hX := hX) (hx := hx)
          (c := c) (y := y) hc hyX).1 hcov
      have hred : covers P' rep (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) :=
        (covers_reduced_rep_nonclone_iff (P := P) (X := X) (x := x) (hX := hX) (hx := hx)
          (c := c) hc).2 hxc
      have hneq : rep ≠ (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) := by
        intro hEq
        have : x = c := congrArg Subtype.val hEq
        exact hc (by simpa [this] using hx)
      exact (hunc rep hneq hred).elim
    · have hred : covers P' (⟨y, Or.inl hyX⟩ : {a : A // clonePred X x a})
          (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) :=
        (covers_reduced_nonclone_nonclone_iff (P := P) (X := X) (x := x) (hX := hX) (hx := hx)
          (c := y) (d := c) hyX hc).2 hcov
      have hneq : (⟨y, Or.inl hyX⟩ : {a : A // clonePred X x a}) ≠
          (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) := by
        intro hEq
        exact hyc (congrArg Subtype.val hEq)
      exact (hunc _ hneq hred).elim

set_option compiler.extract_closed false in
theorem uncoveredSet_independenceOfClones : IndependenceOfClones UncoveredSet := by
  intro V A _ _ _ P X x hX hx
  classical
  refine ⟨?_, ?_⟩
  · intro c hc
    simpa [UncoveredSet, uncoveredSet] using
      (uncovered_nonclone_iff_reduced (P := P) (X := X) (x := x) (hX := hX) (hx := hx)
        (c := c) hc)
  · constructor
    · rintro ⟨y, hyX, hyMem⟩
      have hyUnc : uncovered P y := by
        simpa [UncoveredSet, uncoveredSet] using hyMem
      have hrepUnc : uncovered (removeClonesExcept P X x) (repCand X x) := by
        intro t htrep hcov
        by_cases htX : (t : A) ∈ X
        · have tx : (t : A) = x := by
            rcases t.2 with htNot | hEq
            · exact (htNot htX).elim
            · exact hEq
          exact (htrep (by
            apply Subtype.ext
            exact tx)).elim
        · have hty : covers P (t : A) y := by
            have hcov' : covers (removeClonesExcept P X x)
                (⟨(t : A), Or.inl htX⟩ : {a : A // clonePred X x a}) (repCand X x) := by
              simpa using hcov
            have htx : covers P (t : A) x :=
              (covers_reduced_nonclone_rep_iff (P := P) (X := X) (x := x) (hX := hX) (hx := hx)
                (c := (t : A)) htX).1 hcov'
            exact (covers_nonclone_clone_iff_rep (P := P) (X := X) (x := x) (hX := hX) (hx := hx)
              (c := (t : A)) (y := y) htX hyX).2 htx
          have hneq : (t : A) ≠ y := by
            intro hEq
            exact htX (by simpa [hEq] using hyX)
          exact (hyUnc (t : A) hneq hty).elim
      simpa [UncoveredSet, uncoveredSet, repCand] using hrepUnc
    · intro hrepMem
      have hrepUnc : uncovered (removeClonesExcept P X x) (repCand X x) := by
        simpa [UncoveredSet, uncoveredSet, repCand] using hrepMem
      let Sx : Finset A := Finset.univ.filter (fun a => a ∈ X)
      have hSx_ne : Sx.Nonempty := by
        rcases hX.1 with ⟨a, haX⟩
        refine ⟨a, ?_⟩
        simp [Sx, haX]
      let _ : LE A := ⟨fun a b => a = b ∨ covers P b a⟩
      have _ : IsTrans A (· ≤ ·) := by
        refine ⟨?_⟩
        intro a b c hab hbc
        cases hab with
        | inl hab =>
            subst hab
            exact hbc
        | inr hab =>
            cases hbc with
            | inl hbc =>
                subst hbc
                exact Or.inr hab
            | inr hbc =>
                exact Or.inr (covers_trans (P := P) hbc hab)
      obtain ⟨y, hymax⟩ := Sx.exists_maximalFor (f := id) hSx_ne
      have hyX : y ∈ X := by
        exact (Finset.mem_filter.mp hymax.1).2
      have hyUnc : uncovered P y := by
        intro z hzy hcov
        by_cases hzX : z ∈ X
        · have hzSx : z ∈ Sx := by simp [Sx, hzX]
          have hyz : y ≤ z := Or.inr hcov
          have hzy' : z ≤ y := hymax.2 hzSx hyz
          cases hzy' with
          | inl hEq =>
              exact (hzy hEq).elim
          | inr hcov' =>
              exact (covers_asymm (P := P) hcov') hcov
        · have hzx : covers P z x :=
            (covers_nonclone_clone_iff_rep (P := P) (X := X) (x := x) (hX := hX) (hx := hx)
              (c := z) (y := y) hzX hyX).1 hcov
          have hred : covers (removeClonesExcept P X x)
              (⟨z, Or.inl hzX⟩ : {a : A // clonePred X x a}) (repCand X x) :=
            (covers_reduced_nonclone_rep_iff (P := P) (X := X) (x := x) (hX := hX) (hx := hx)
              (c := z) hzX).2 hzx
          have hneq : (⟨z, Or.inl hzX⟩ : {a : A // clonePred X x a}) ≠ (repCand X x) := by
            intro hEq
            have : z = x := congrArg Subtype.val hEq
            exact hzX (by simpa [this] using hx)
          exact (hrepUnc _ hneq hred).elim
      refine ⟨y, hyX, ?_⟩
      simpa [UncoveredSet, uncoveredSet] using hyUnc

end

end SocialChoice
