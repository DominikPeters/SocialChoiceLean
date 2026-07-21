import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import SocialChoice.Profile
import SocialChoice.Axioms.Participation
import SocialChoice.Axioms.Reversal

namespace SocialChoice

open Finset

noncomputable def margin {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) : Int := by
  classical
  exact
    Int.ofNat ((Finset.univ.filter (fun v => Prefers P v a b)).card) -
      Int.ofNat ((Finset.univ.filter (fun v => Prefers P v b a)).card)

def margin_pos {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) : Prop :=
  0 < margin P a b

@[simp] lemma prefers_permuteCandidates_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) (v : V) (a b : A) :
    Prefers (permuteCandidates P σ) v a b ↔ Prefers P v (σ.symm a) (σ.symm b) := by
  rfl

@[simp] lemma prefers_relabelProfile_iff {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
    (P : Profile V A) (e : A ≃ B) (v : V) (a b : B) :
    Prefers (relabelProfile P e) v a b ↔ Prefers P v (e.symm a) (e.symm b) := by
  rfl

@[simp] lemma margin_permuteCandidates {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) (a b : A) :
    margin (permuteCandidates P σ) a b = margin P (σ.symm a) (σ.symm b) := by
  classical
  simp [margin]

@[simp] lemma margin_permuteVoters {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm V) (a b : A) :
    margin (permuteVoters P σ) a b = margin P a b := by
  classical
  have hcard_ab :
      (Finset.univ.filter (fun v => Prefers (permuteVoters P σ) v a b)).card =
        (Finset.univ.filter (fun v => Prefers P v a b)).card := by
    refine Finset.card_bij
      (s := Finset.univ.filter (fun v => Prefers (permuteVoters P σ) v a b))
      (t := Finset.univ.filter (fun v => Prefers P v a b))
      (i := fun v _ => σ v) ?_ ?_ ?_
    · intro v hv
      have hv' : Prefers (permuteVoters P σ) v a b := (Finset.mem_filter.mp hv).2
      have hv'' : Prefers P (σ v) a b := by
        exact hv'
      exact Finset.mem_filter.mpr ⟨by simp, hv''⟩
    · intro v1 hv1 v2 hv2 h
      exact σ.injective h
    · intro v hv
      have hv' : Prefers P v a b := (Finset.mem_filter.mp hv).2
      refine ⟨σ.symm v, ?_, by simp⟩
      have : Prefers (permuteVoters P σ) (σ.symm v) a b := by
        unfold Prefers at hv' ⊢
        rw [show (permuteVoters P σ).pref (σ.symm v) = P.pref v by
          simp [permuteVoters]]
        exact hv'
      exact Finset.mem_filter.mpr ⟨by simp, this⟩
  have hcard_ba :
      (Finset.univ.filter (fun v => Prefers (permuteVoters P σ) v b a)).card =
        (Finset.univ.filter (fun v => Prefers P v b a)).card := by
    refine Finset.card_bij
      (s := Finset.univ.filter (fun v => Prefers (permuteVoters P σ) v b a))
      (t := Finset.univ.filter (fun v => Prefers P v b a))
      (i := fun v _ => σ v) ?_ ?_ ?_
    · intro v hv
      have hv' : Prefers (permuteVoters P σ) v b a := (Finset.mem_filter.mp hv).2
      have hv'' : Prefers P (σ v) b a := by
        exact hv'
      exact Finset.mem_filter.mpr ⟨by simp, hv''⟩
    · intro v1 hv1 v2 hv2 h
      exact σ.injective h
    · intro v hv
      have hv' : Prefers P v b a := (Finset.mem_filter.mp hv).2
      refine ⟨σ.symm v, ?_, by simp⟩
      have : Prefers (permuteVoters P σ) (σ.symm v) b a := by
        unfold Prefers at hv' ⊢
        rw [show (permuteVoters P σ).pref (σ.symm v) = P.pref v by
          simp [permuteVoters]]
        exact hv'
      exact Finset.mem_filter.mpr ⟨by simp, this⟩
  simp [margin, hcard_ab, hcard_ba]

@[simp] lemma margin_relabelProfile {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
    (P : Profile V A) (e : A ≃ B) (a b : B) :
    margin (relabelProfile P e) a b = margin P (e.symm a) (e.symm b) := by
  classical
  simp [margin]

@[simp] lemma margin_pos_permuteCandidates_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) (a b : A) :
    margin_pos (permuteCandidates P σ) a b ↔ margin_pos P (σ.symm a) (σ.symm b) := by
  simp [margin_pos]

@[simp] lemma margin_pos_relabelProfile_iff {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
    (P : Profile V A) (e : A ≃ B) (a b : B) :
    margin_pos (relabelProfile P e) a b ↔ margin_pos P (e.symm a) (e.symm b) := by
  simp [margin_pos]

def skew_symmetric {A : Type} (M : A -> A -> Int) : Prop :=
  forall a b, M a b = -(M b a)

theorem margin_antisymmetric {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) : skew_symmetric (margin P) := by
  classical
  intro a b
  dsimp [margin, skew_symmetric]
  ring

theorem self_margin_zero {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a : A) : margin P a a = 0 := by
  classical
  dsimp [margin]
  simp

theorem ne_of_margin_pos {V A : Type} [Fintype V] [Fintype A]
    {P : Profile V A} {a b : A} (h : margin_pos P a b) : a ≠ b := by
  intro hEq
  subst hEq
  have h0 : (0 : Int) < 0 := by
    simp [margin_pos, self_margin_zero] at h
  exact (lt_irrefl 0 h0)

lemma unanimous_margin {V A : Type} [Fintype V] [Fintype A] [Nonempty V]
    (P : Profile V A) (x y : A) :
    (∀ v : V, Prefers P v x y) → margin_pos P x y := by
  classical
  intro hxy
  have hxy_card :
      (Finset.univ.filter (fun v => Prefers P v x y)).card = Fintype.card V := by
    have hxy_set :
        (Finset.univ.filter (fun v => Prefers P v x y)) = (Finset.univ : Finset V) := by
      ext v
      simp [hxy v]
    simp [hxy_set]
  have hyx_card : (Finset.univ.filter (fun v => Prefers P v y x)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hxyv : Prefers P v x y := hxy v
    have hcontra : ¬ Prefers P v y x := by
      let _ := P.pref v
      exact lt_asymm hxyv
    exact hcontra (by simpa using (Finset.mem_filter.mp hv).2)
  have hpos : (0 : Int) < (Fintype.card V : Int) := by
    exact Int.natCast_pos.mpr Fintype.card_pos
  dsimp [margin_pos, margin]
  simpa [hxy_card, hyx_card] using hpos

lemma unanimous_margin_eq_card {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x y : A) :
    (∀ v : V, Prefers P v x y) → margin P x y = (Fintype.card V : Int) := by
  classical
  intro hxy
  have hxy_card :
      (Finset.univ.filter (fun v => Prefers P v x y)).card = Fintype.card V := by
    have hxy_set :
        (Finset.univ.filter (fun v => Prefers P v x y)) = (Finset.univ : Finset V) := by
      ext v
      simp [hxy v]
    simp [hxy_set]
  have hyx_card : (Finset.univ.filter (fun v => Prefers P v y x)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hxyv : Prefers P v x y := hxy v
    have hcontra : ¬ Prefers P v y x := by
      let _ := P.pref v
      exact lt_asymm hxyv
    exact hcontra (by simpa using (Finset.mem_filter.mp hv).2)
  dsimp [margin]
  simp [hxy_card, hyx_card]

lemma margin_reverse_eq {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) :
    margin (reverse_profile P) b a = margin P a b := by
  classical
  simp [margin, prefers_reverse_profile]

lemma margin_le_card {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) :
    margin P a b ≤ (Fintype.card V : Int) := by
  classical
  have h1 :
      (Finset.univ.filter (fun v => Prefers P v a b)).card ≤ Fintype.card V := by
    simpa using (Finset.card_le_univ (s := Finset.univ.filter (fun v => Prefers P v a b)))
  have h1' :
      (Int.ofNat (Finset.univ.filter (fun v => Prefers P v a b)).card) ≤
        (Fintype.card V : Int) := by
    exact Int.ofNat_le_ofNat_of_le h1
  have h2' :
      (Int.ofNat (Finset.univ.filter (fun v => Prefers P v b a)).card) ≥ 0 := by
    exact Int.natCast_nonneg _
  have hsub :
      Int.ofNat (Finset.univ.filter (fun v => Prefers P v a b)).card -
          Int.ofNat (Finset.univ.filter (fun v => Prefers P v b a)).card ≤
        Int.ofNat (Finset.univ.filter (fun v => Prefers P v a b)).card := by
    exact sub_le_self _ h2'
  have hmargin :
      margin P a b ≤ Int.ofNat (Finset.univ.filter (fun v => Prefers P v a b)).card := by
    simp [margin]
  exact hmargin.trans h1'

lemma unanimous_of_margin_ge_card {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) :
    (Fintype.card V : Int) ≤ margin P a b → ∀ v : V, Prefers P v a b := by
  classical
  intro hle v
  by_contra hnot
  have hne : (Finset.univ.filter (fun v => Prefers P v a b)) ≠ (Finset.univ : Finset V) := by
    intro hEq
    have : v ∈ (Finset.univ.filter (fun v => Prefers P v a b)) := by
      simp [hEq]
    exact hnot (Finset.mem_filter.mp this).2
  have hcard_lt :
      (Finset.univ.filter (fun v => Prefers P v a b)).card < Fintype.card V := by
    exact (Finset.card_lt_iff_ne_univ _).2 hne
  have hcard_lt' :
      (Int.ofNat (Finset.univ.filter (fun v => Prefers P v a b)).card) <
        (Fintype.card V : Int) := by
    exact Int.ofNat_lt_ofNat_of_lt hcard_lt
  have hmargin_le :
      margin P a b ≤ Int.ofNat (Finset.univ.filter (fun v => Prefers P v a b)).card := by
    have h2' :
        (Int.ofNat (Finset.univ.filter (fun v => Prefers P v b a)).card) ≥ 0 := by
      exact Int.natCast_nonneg _
    have hsub :
        Int.ofNat (Finset.univ.filter (fun v => Prefers P v a b)).card -
            Int.ofNat (Finset.univ.filter (fun v => Prefers P v b a)).card ≤
          Int.ofNat (Finset.univ.filter (fun v => Prefers P v a b)).card := by
      exact sub_le_self _ h2'
    simp [margin]
  have hlt : margin P a b < (Fintype.card V : Int) :=
    lt_of_le_of_lt hmargin_le hcard_lt'
  exact (not_lt_of_ge hle hlt)

lemma margin_pos_irrefl {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) : ∀ x, ¬ margin_pos P x x := by
  intro x
  simp [margin_pos, self_margin_zero]

lemma margin_pos_asymm {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) : ∀ x y, margin_pos P x y → ¬ margin_pos P y x := by
  intro x y hxy hyx
  have hskew : margin P y x = - margin P x y := by
    simpa [skew_symmetric] using (margin_antisymmetric (P := P)) y x
  have hpos : 0 < margin P x y := by
    simpa [margin_pos] using hxy
  have hneg : margin P y x < 0 := by
    simpa [hskew] using (neg_neg_of_pos hpos)
  have hyx' : 0 < margin P y x := by
    simpa [margin_pos] using hyx
  exact (lt_asymm hyx' hneg)

lemma margin_addVoter_eq_of_prefers {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (ballot : LinearOrder A) (a b : A) (h : ballot.lt a b) :
    margin (addVoter P ballot) a b = margin P a b + 1 := by
  classical
  have hcard_ab :
      (Finset.univ.filter (fun v : V ⊕ Unit => Prefers (addVoter P ballot) v a b)).card =
        (Finset.univ.filter (fun v : V => Prefers P v a b)).card + 1 := by
    let S0 : Finset V := Finset.univ.filter (fun v => Prefers P v a b)
    let S : Finset (V ⊕ Unit) :=
      Finset.univ.filter (fun v => Prefers (addVoter P ballot) v a b)
    have hS : S = insert (Sum.inr ()) (S0.image (Sum.inl : V → V ⊕ Unit)) := by
      ext v
      cases v with
      | inl v =>
          simp [S, S0, Prefers, Finset.mem_image]
          rfl
      | inr u =>
          cases u
          simp [S, S0, Prefers, Finset.mem_image]
          exact h
    have hnotmem : Sum.inr () ∉ S0.image (Sum.inl : V → V ⊕ Unit) := by
      simp [Finset.mem_image]
    have hinj : Function.Injective (Sum.inl : V → V ⊕ Unit) := by
      intro a b hEq
      cases hEq
      rfl
    have hcard : S.card = (S0.image (Sum.inl : V → V ⊕ Unit)).card + 1 := by
      have hcard' :
          (insert (Sum.inr ()) (S0.image (Sum.inl : V → V ⊕ Unit))).card =
            (S0.image (Sum.inl : V → V ⊕ Unit)).card + 1 :=
        Finset.card_insert_of_notMem hnotmem
      simp [hS]
    calc
      S.card = (S0.image (Sum.inl : V → V ⊕ Unit)).card + 1 := hcard
      _ = S0.card + 1 := by
        simpa using (Finset.card_image_of_injective S0 hinj)
  let _ := ballot
  have hba : ¬ ballot.lt b a := by
    intro hba
    exact lt_asymm (by simpa using h) (by simpa using hba)
  have hcard_ba :
      (Finset.univ.filter (fun v : V ⊕ Unit => Prefers (addVoter P ballot) v b a)).card =
        (Finset.univ.filter (fun v : V => Prefers P v b a)).card := by
    let S0 : Finset V := Finset.univ.filter (fun v => Prefers P v b a)
    let S : Finset (V ⊕ Unit) :=
      Finset.univ.filter (fun v => Prefers (addVoter P ballot) v b a)
    have hS : S = S0.image Sum.inl := by
      ext v
      cases v with
      | inl v =>
          simp [S, S0, Prefers, Finset.mem_image]
          rfl
      | inr u =>
          cases u
          simp [S, S0, Prefers, Finset.mem_image]
          exact hba
    have hinj : Function.Injective (Sum.inl : V → V ⊕ Unit) := by
      intro a b hEq
      cases hEq
      rfl
    calc
      S.card = (S0.image Sum.inl).card := by
        simp [hS]
        rfl
      _ = S0.card := by
        simpa using (Finset.card_image_of_injective S0 hinj)
  dsimp [margin]
  simp [hcard_ab, hcard_ba]
  ring

lemma margin_add_newVoter_eq_of_prefers {U A : Type} [DecidableEq U] [Fintype A]
    {V : Finset U} {u : U} (hu : u ∉ V)
    (P : Profile (Electorate U V) A)
    (Q : Profile (Electorate U (insert u V)) A)
    (hagree : ∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v)
    (a b : A) (h : (Q.pref (newVoter (u := u) (V := V) hu)).lt a b) :
    margin Q a b = margin P a b + 1 := by
  classical
  let S0 : Finset (Electorate U V) := Finset.univ.filter (fun v => Prefers P v a b)
  let S : Finset (Electorate U (insert u V)) :=
    Finset.univ.filter (fun v => Prefers Q v a b)
  have hS : S =
      insert (newVoter (u := u) (V := V) hu) (S0.image (liftVoter (u := u))) := by
    ext v
    by_cases hv : v = newVoter (u := u) (V := V) hu
    · subst hv
      have hpref : Prefers Q (newVoter (u := u) (V := V) hu) a b := by
        simpa [Prefers] using h
      constructor
      · intro _hmem
        simp
      · intro _hmem
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpref⟩
    · have hv' : v.1 ∈ V := by
        have hmem : v.1 ∈ insert u V := v.2
        have hmem' : v.1 = u ∨ v.1 ∈ V := by
          simpa using (Finset.mem_insert.mp hmem)
        cases hmem' with
        | inl h =>
            exact (hv (Subtype.ext h)).elim
        | inr h => exact h
      let v' : Electorate U V := ⟨v.1, hv'⟩
      have hv_eq : v = liftVoter (u := u) v' := by
        apply Subtype.ext
        rfl
      have hpref : Prefers Q v a b ↔ Prefers P v' a b := by
        unfold Prefers
        rw [hv_eq, hagree]
      have himage : v ∈ S0.image (liftVoter (u := u)) ↔ v' ∈ S0 := by
        constructor
        · intro hvimg
          rcases Finset.mem_image.mp hvimg with ⟨w, hw, hweq⟩
          have hw' : w = v' := by
            apply (liftVoter_injective (u := u))
            simpa [hv_eq] using hweq
          simpa [hw'] using hw
        · intro hvS0
          exact Finset.mem_image.mpr ⟨v', hvS0, hv_eq.symm⟩
      have hvS : v ∈ S ↔ v' ∈ S0 := by
        constructor
        · intro hvS
          have hprefQ : Prefers Q v a b := (Finset.mem_filter.mp hvS).2
          have hprefP : Prefers P v' a b := (hpref.mp hprefQ)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprefP⟩
        · intro hvS0
          have hprefP : Prefers P v' a b := (Finset.mem_filter.mp hvS0).2
          have hprefQ : Prefers Q v a b := (hpref.mpr hprefP)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprefQ⟩
      have hinsert :
          v ∈ insert (newVoter (u := u) (V := V) hu) (S0.image (liftVoter (u := u))) ↔
            v ∈ S0.image (liftVoter (u := u)) := by
        simp [hv]
      calc
        v ∈ S ↔ v' ∈ S0 := hvS
        _ ↔ v ∈ S0.image (liftVoter (u := u)) := himage.symm
        _ ↔ v ∈ insert (newVoter (u := u) (V := V) hu) (S0.image (liftVoter (u := u))) :=
          hinsert.symm
  have hnotmem :
      newVoter (u := u) (V := V) hu ∉ S0.image (liftVoter (u := u)) := by
    intro hmem
    rcases Finset.mem_image.mp hmem with ⟨v, _hv, hveq⟩
    exact (liftVoter_ne_newVoter (u := u) (V := V) hu v) hveq
  have hinj : Function.Injective (liftVoter (u := u) : Electorate U V → Electorate U (insert u V)) :=
    liftVoter_injective (u := u)
  have hcard_ab :
      S.card = S0.card + 1 := by
    have hcard' :
        (insert (newVoter (u := u) (V := V) hu) (S0.image (liftVoter (u := u)))).card =
          (S0.image (liftVoter (u := u))).card + 1 :=
      Finset.card_insert_of_notMem hnotmem
    calc
      S.card = (S0.image (liftVoter (u := u))).card + 1 := by
        simpa [hS] using hcard'
      _ = S0.card + 1 := by
        simpa using (Finset.card_image_of_injective S0 hinj)
  let ballot := Q.pref (newVoter (u := u) (V := V) hu)
  have hba : ¬ ballot.lt b a := by
    let _ : Preorder A := ballot.toPreorder
    intro hba
    exact (lt_asymm (a := a) (b := b) (by simpa using h) (by simpa using hba))
  let T0 : Finset (Electorate U V) := Finset.univ.filter (fun v => Prefers P v b a)
  let T : Finset (Electorate U (insert u V)) :=
    Finset.univ.filter (fun v => Prefers Q v b a)
  have hT : T = T0.image (liftVoter (u := u)) := by
    ext v
    by_cases hv : v = newVoter (u := u) (V := V) hu
    · subst hv
      have hpref : ¬ Prefers Q (newVoter (u := u) (V := V) hu) b a := by
        simpa [Prefers, ballot] using hba
      constructor
      · intro hmem
        have hpref' : Prefers Q (newVoter (u := u) (V := V) hu) b a :=
          (Finset.mem_filter.mp hmem).2
        exact (hpref hpref').elim
      · intro hmem
        rcases Finset.mem_image.mp hmem with ⟨w, _hw, hweq⟩
        exact (False.elim ((liftVoter_ne_newVoter (u := u) (V := V) hu w) hweq))
    · have hv' : v.1 ∈ V := by
        have hmem : v.1 ∈ insert u V := v.2
        have hmem' : v.1 = u ∨ v.1 ∈ V := by
          simpa using (Finset.mem_insert.mp hmem)
        cases hmem' with
        | inl h =>
            exact (hv (Subtype.ext h)).elim
        | inr h => exact h
      let v' : Electorate U V := ⟨v.1, hv'⟩
      have hv_eq : v = liftVoter (u := u) v' := by
        apply Subtype.ext
        rfl
      have hpref : Prefers Q v b a ↔ Prefers P v' b a := by
        unfold Prefers
        rw [hv_eq, hagree]
      have himage : v ∈ T0.image (liftVoter (u := u)) ↔ v' ∈ T0 := by
        constructor
        · intro hvimg
          rcases Finset.mem_image.mp hvimg with ⟨w, hw, hweq⟩
          have hw' : w = v' := by
            apply (liftVoter_injective (u := u))
            simpa [hv_eq] using hweq
          simpa [hw'] using hw
        · intro hvT0
          exact Finset.mem_image.mpr ⟨v', hvT0, hv_eq.symm⟩
      have hvT : v ∈ T ↔ v' ∈ T0 := by
        constructor
        · intro hvT
          have hprefQ : Prefers Q v b a := (Finset.mem_filter.mp hvT).2
          have hprefP : Prefers P v' b a := (hpref.mp hprefQ)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprefP⟩
        · intro hvT0
          have hprefP : Prefers P v' b a := (Finset.mem_filter.mp hvT0).2
          have hprefQ : Prefers Q v b a := (hpref.mpr hprefP)
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hprefQ⟩
      calc
        v ∈ T ↔ v' ∈ T0 := hvT
        _ ↔ v ∈ T0.image (liftVoter (u := u)) := himage.symm
  have hcard_ba :
      T.card = T0.card := by
    calc
      T.card = (T0.image (liftVoter (u := u))).card := by
        simp [hT]
      _ = T0.card := by
        simpa using (Finset.card_image_of_injective T0 hinj)
  have hcard_ab' :
      (Finset.univ.filter (fun v : Electorate U (insert u V) => Prefers Q v a b)).card =
        (Finset.univ.filter (fun v : Electorate U V => Prefers P v a b)).card + 1 := by
    simpa [S, S0] using hcard_ab
  have hcard_ba' :
      (Finset.univ.filter (fun v : Electorate U (insert u V) => Prefers Q v b a)).card =
        (Finset.univ.filter (fun v : Electorate U V => Prefers P v b a)).card := by
    simpa [T, T0] using hcard_ba
  dsimp [margin]
  change
      (Int.ofNat
            (Finset.univ.filter
                  (fun v : Electorate U (insert u V) => Prefers Q v a b)).card) -
          Int.ofNat
            (Finset.univ.filter
                  (fun v : Electorate U (insert u V) => Prefers Q v b a)).card =
        Int.ofNat
            (Finset.univ.filter
                  (fun v : Electorate U V => Prefers P v a b)).card -
          Int.ofNat
            (Finset.univ.filter
                  (fun v : Electorate U V => Prefers P v b a)).card +
            1
  rw [hcard_ab', hcard_ba']
  simp [sub_eq_add_neg, add_assoc, add_comm]

lemma margin_add_newVoter_eq_of_prefers_rev {U A : Type} [DecidableEq U] [Fintype A]
    {V : Finset U} {u : U} (hu : u ∉ V)
    (P : Profile (Electorate U V) A)
    (Q : Profile (Electorate U (insert u V)) A)
    (hagree : ∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v)
    (a b : A) (h : (Q.pref (newVoter (u := u) (V := V) hu)).lt b a) :
    margin Q a b = margin P a b - 1 := by
  have hswap :
      margin Q b a = margin P b a + 1 :=
    margin_add_newVoter_eq_of_prefers (u := u) (V := V) hu P Q hagree b a h
  have hskewP : margin P a b = - margin P b a := by
    simpa [skew_symmetric] using (margin_antisymmetric (P := P)) a b
  have hskewQ : margin Q a b = - margin Q b a := by
    simpa [skew_symmetric] using (margin_antisymmetric (P := Q)) a b
  calc
    margin Q a b = - margin Q b a := hskewQ
    _ = - (margin P b a + 1) := by simp [hswap]
    _ = (- margin P b a) - 1 := by ring
    _ = margin P a b - 1 := by simp [hskewP]

lemma margin_le_add_newVoter {U A : Type} [DecidableEq U] [Fintype A]
    {V : Finset U} {u : U} (hu : u ∉ V)
    (P : Profile (Electorate U V) A)
    (Q : Profile (Electorate U (insert u V)) A)
    (hagree : ∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v)
    (a b : A) :
    margin P a b ≤ margin Q a b + 1 := by
  classical
  by_cases hEq : a = b
  · subst hEq
    simp [self_margin_zero]
  · let ballot := Q.pref (newVoter (u := u) (V := V) hu)
    let _ : Preorder A := ballot.toPreorder
    have htr : ballot.lt a b ∨ ballot.lt b a := lt_or_gt_of_ne hEq
    cases htr with
    | inl hlt =>
        have hmargin :
            margin Q a b = margin P a b + 1 :=
          margin_add_newVoter_eq_of_prefers (u := u) (V := V) hu P Q hagree a b hlt
        linarith [hmargin]
    | inr hgt =>
        have hmargin :
            margin Q a b = margin P a b - 1 :=
          margin_add_newVoter_eq_of_prefers_rev (u := u) (V := V) hu P Q hagree a b hgt
        linarith [hmargin]

lemma margin_add_newVoter_le {U A : Type} [DecidableEq U] [Fintype A]
    {V : Finset U} {u : U} (hu : u ∉ V)
    (P : Profile (Electorate U V) A)
    (Q : Profile (Electorate U (insert u V)) A)
    (hagree : ∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v)
    (a b : A) :
    margin Q a b ≤ margin P a b + 1 := by
  classical
  by_cases hEq : a = b
  · subst hEq
    simp [self_margin_zero]
  · let ballot := Q.pref (newVoter (u := u) (V := V) hu)
    let _ : Preorder A := ballot.toPreorder
    have htr : ballot.lt a b ∨ ballot.lt b a := lt_or_gt_of_ne hEq
    cases htr with
    | inl hlt =>
        have hmargin :
            margin Q a b = margin P a b + 1 :=
          margin_add_newVoter_eq_of_prefers (u := u) (V := V) hu P Q hagree a b hlt
        linarith [hmargin]
    | inr hgt =>
        have hmargin :
            margin Q a b = margin P a b - 1 :=
          margin_add_newVoter_eq_of_prefers_rev (u := u) (V := V) hu P Q hagree a b hgt
        linarith [hmargin]

lemma margin_addVoter_eq_of_prefers_rev {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (ballot : LinearOrder A) (a b : A) (h : ballot.lt b a) :
    margin (addVoter P ballot) a b = margin P a b - 1 := by
  have hswap : margin (addVoter P ballot) b a = margin P b a + 1 :=
    margin_addVoter_eq_of_prefers P ballot b a h
  have hskewP : margin P a b = - margin P b a := by
    simpa [skew_symmetric] using (margin_antisymmetric (P := P)) a b
  have hskewP' : margin (addVoter P ballot) a b = - margin (addVoter P ballot) b a := by
    simpa [skew_symmetric] using (margin_antisymmetric (P := addVoter P ballot)) a b
  calc
    margin (addVoter P ballot) a b = - margin (addVoter P ballot) b a := hskewP'
    _ = - (margin P b a + 1) := by simp [hswap]
    _ = (- margin P b a) - 1 := by ring
    _ = margin P a b - 1 := by simp [hskewP]

lemma margin_le_addVoter {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (ballot : LinearOrder A) (a b : A) :
    margin P a b ≤ margin (addVoter P ballot) a b + 1 := by
  classical
  by_cases hEq : a = b
  · subst hEq
    simp [self_margin_zero]
  · let _ := ballot
    have htr : a < b ∨ b < a := lt_or_gt_of_ne hEq
    cases htr with
    | inl hlt =>
        have hlt' : ballot.lt a b := by simpa using hlt
        have hmargin : margin (addVoter P ballot) a b = margin P a b + 1 :=
          margin_addVoter_eq_of_prefers P ballot a b hlt'
        linarith [hmargin]
    | inr hgt =>
        have hgt' : ballot.lt b a := by simpa using hgt
        have hmargin : margin (addVoter P ballot) a b = margin P a b - 1 :=
          margin_addVoter_eq_of_prefers_rev P ballot a b hgt'
        linarith [hmargin]

lemma margin_addVoter_le {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (ballot : LinearOrder A) (a b : A) :
    margin (addVoter P ballot) a b ≤ margin P a b + 1 := by
  classical
  by_cases hEq : a = b
  · subst hEq
    simp [self_margin_zero]
  · let _ := ballot
    have htr : a < b ∨ b < a := lt_or_gt_of_ne hEq
    cases htr with
    | inl hlt =>
        have hlt' : ballot.lt a b := by simpa using hlt
        have hmargin : margin (addVoter P ballot) a b = margin P a b + 1 :=
          margin_addVoter_eq_of_prefers P ballot a b hlt'
        linarith [hmargin]
    | inr hgt =>
        have hgt' : ballot.lt b a := by simpa using hgt
        have hmargin : margin (addVoter P ballot) a b = margin P a b - 1 :=
          margin_addVoter_eq_of_prefers_rev P ballot a b hgt'
        linarith [hmargin]

lemma margin_lemma {V A : Type} [Fintype V] [Fintype A]
    (P P' : Profile V A) (a b : A) (_ : a ≠ b) :
    (∀ v : V, (Prefers P v a b → Prefers P' v a b) ∧
      (Prefers P' v b a → Prefers P v b a)) →
    margin P a b ≤ margin P' a b := by
  classical
  intro lift
  have h1 :
      (Finset.univ.filter (fun v => Prefers P v a b)).card ≤
        (Finset.univ.filter (fun v => Prefers P' v a b)).card := by
    refine cardinality_lemma (p := fun v => Prefers P v a b)
      (q := fun v => Prefers P' v a b) ?_
    intro v hv
    exact (lift v).1 hv
  have h2 :
      (Finset.univ.filter (fun v => Prefers P' v b a)).card ≤
        (Finset.univ.filter (fun v => Prefers P v b a)).card := by
    refine cardinality_lemma (p := fun v => Prefers P' v b a)
      (q := fun v => Prefers P v b a) ?_
    intro v hv
    exact (lift v).2 hv
  have h1' :
      (Int.ofNat (Finset.univ.filter (fun v => Prefers P v a b)).card) ≤
        Int.ofNat (Finset.univ.filter (fun v => Prefers P' v a b)).card := by
    exact Int.ofNat_le_ofNat_of_le h1
  have h2' :
      (Int.ofNat (Finset.univ.filter (fun v => Prefers P' v b a)).card) ≤
        Int.ofNat (Finset.univ.filter (fun v => Prefers P v b a)).card := by
    exact Int.ofNat_le_ofNat_of_le h2
  have hsub := sub_le_sub h1' h2'
  simpa [margin] using hsub

lemma margin_eq_margin_restrictProfile {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    {P : Profile V A} {c : A} {a b : {x : A // x ≠ c}} :
    margin P a b = margin (restrictProfile P c) a b := by
  classical
  have h1 :
      (Finset.univ.filter (fun v => Prefers P v a b)).card =
        (Finset.univ.filter (fun v => Prefers (restrictProfile P c) v a b)).card := by
    refine cardinality_lemma2 (p := fun v => Prefers P v a b)
      (q := fun v => Prefers (restrictProfile P c) v a b) ?_
    intro v
    simp
  have h2 :
      (Finset.univ.filter (fun v => Prefers P v b a)).card =
        (Finset.univ.filter (fun v => Prefers (restrictProfile P c) v b a)).card := by
    refine cardinality_lemma2 (p := fun v => Prefers P v b a)
      (q := fun v => Prefers (restrictProfile P c) v b a) ?_
    intro v
    simp
  dsimp [margin]
  simp [h1, h2]

lemma margin_eq_margin_restrictCandidates {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (p : A → Prop) [DecidablePred p]
    {a b : {x : A // p x}} :
    margin P a b = margin (restrictCandidates P p) a b := by
  classical
  have h1 :
      (Finset.univ.filter (fun v => Prefers P v a b)).card =
        (Finset.univ.filter (fun v => Prefers (restrictCandidates P p) v a b)).card := by
    refine cardinality_lemma2 (p := fun v => Prefers P v a b)
      (q := fun v => Prefers (restrictCandidates P p) v a b) ?_
    intro v
    simp
  have h2 :
      (Finset.univ.filter (fun v => Prefers P v b a)).card =
        (Finset.univ.filter (fun v => Prefers (restrictCandidates P p) v b a)).card := by
    refine cardinality_lemma2 (p := fun v => Prefers P v b a)
      (q := fun v => Prefers (restrictCandidates P p) v b a) ?_
    intro v
    simp
  dsimp [margin]
  simp [h1, h2]

/-! ### Constant profiles and unions -/

lemma margin_constantProfile_of_lt {V A : Type} [Fintype V] [Fintype A]
    (r : LinearOrder A) {a b : A} (h : r.lt a b) :
    margin (constantProfile (V := V) (A := A) r) a b = (Fintype.card V : Int) := by
  classical
  apply unanimous_margin_eq_card
  intro v
  simp [Prefers]
  exact h

lemma margin_constantProfile_of_gt {V A : Type} [Fintype V] [Fintype A]
    (r : LinearOrder A) {a b : A} (h : r.lt b a) :
    margin (constantProfile (V := V) (A := A) r) a b = -(Fintype.card V : Int) := by
  classical
  have hba :
      margin (constantProfile (V := V) (A := A) r) b a = (Fintype.card V : Int) :=
    margin_constantProfile_of_lt (V := V) (A := A) r h
  have hskew :
      margin (constantProfile (V := V) (A := A) r) a b =
        - margin (constantProfile (V := V) (A := A) r) b a := by
    simpa [skew_symmetric] using
      (margin_antisymmetric (P := constantProfile (V := V) (A := A) r)) a b
  calc
    margin (constantProfile (V := V) (A := A) r) a b =
        - margin (constantProfile (V := V) (A := A) r) b a := hskew
    _ = -(Fintype.card V : Int) := by simp [hba]

lemma card_votersPreferring_unionProfiles {V W A : Type} [Fintype V] [Fintype W] [Fintype A]
    (P : Profile V A) (Q : Profile W A) (a b : A) :
    (votersPreferring (unionProfiles P Q) a b).card =
      (votersPreferring P a b).card + (votersPreferring Q a b).card := by
  classical
  let SV : Finset V := votersPreferring P a b
  let SW : Finset W := votersPreferring Q a b
  let S : Finset (V ⊕ W) := votersPreferring (unionProfiles P Q) a b
  have hS :
      S = SV.image Sum.inl ∪ SW.image Sum.inr := by
    ext v
    cases v with
    | inl v =>
        simp [S, SV, SW, votersPreferring, Prefers, Finset.mem_image]
        rfl
    | inr w =>
        simp [S, SV, SW, votersPreferring, Prefers, Finset.mem_image]
        rfl
  have hdisj : Disjoint (SV.image Sum.inl) (SW.image Sum.inr) := by
    refine Finset.disjoint_left.2 ?_
    intro v hvL hvR
    rcases Finset.mem_image.mp hvL with ⟨v1, _hv1, rfl⟩
    rcases Finset.mem_image.mp hvR with ⟨v2, _hv2, hEq⟩
    cases hEq
  have hinjL : Function.Injective (Sum.inl : V → V ⊕ W) := by
    intro v1 v2 hEq
    cases hEq
    rfl
  have hinjR : Function.Injective (Sum.inr : W → V ⊕ W) := by
    intro w1 w2 hEq
    cases hEq
    rfl
  calc
    S.card = (SV.image Sum.inl ∪ SW.image Sum.inr).card := by simp [hS]
    _ = (SV.image Sum.inl).card + (SW.image Sum.inr).card :=
      Finset.card_union_of_disjoint hdisj
    _ = SV.card + SW.card := by
      have hL : (SV.image Sum.inl).card = SV.card :=
        Finset.card_image_of_injective (s := SV) (f := Sum.inl) hinjL
      have hR : (SW.image Sum.inr).card = SW.card :=
        Finset.card_image_of_injective (s := SW) (f := Sum.inr) hinjR
      simp [hL, hR, SV, SW]

lemma margin_unionProfiles {V W A : Type} [Fintype V] [Fintype W] [Fintype A]
    (P : Profile V A) (Q : Profile W A) (a b : A) :
    margin (unionProfiles P Q) a b = margin P a b + margin Q a b := by
  classical
  have h1 := card_votersPreferring_unionProfiles (P := P) (Q := Q) (a := a) (b := b)
  have h2 := card_votersPreferring_unionProfiles (P := P) (Q := Q) (a := b) (b := a)
  dsimp [margin]
  have hUP :
      (#{v | Prefers (unionProfiles P Q) v a b}) =
        (votersPreferring (unionProfiles P Q) a b).card := by rfl
  have hUP' :
      (#{v | Prefers (unionProfiles P Q) v b a}) =
        (votersPreferring (unionProfiles P Q) b a).card := by rfl
  have hP :
      (#{v | Prefers P v a b}) = (votersPreferring P a b).card := by rfl
  have hP' :
      (#{v | Prefers P v b a}) = (votersPreferring P b a).card := by rfl
  have hQ :
      (#{v | Prefers Q v a b}) = (votersPreferring Q a b).card := by rfl
  have hQ' :
      (#{v | Prefers Q v b a}) = (votersPreferring Q b a).card := by rfl
  simp [hUP, hUP', hP, hP', hQ, hQ', h1, h2]
  ring

end SocialChoice
