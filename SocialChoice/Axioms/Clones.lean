import Mathlib.Data.Set.Basic
import SocialChoice.Profile
import SocialChoice.Meta

namespace SocialChoice

noncomputable instance instDecidablePredClone {A : Type} (X : Set A) (x : A) :
    DecidablePred (fun a : A => a ∉ X ∨ a = x) := by
  classical
  infer_instance

def clonePred {A : Type} (X : Set A) (x : A) : A → Prop := fun a => a ∉ X ∨ a = x

noncomputable instance instDecidablePredClonePred {A : Type} (X : Set A) (x : A) :
    DecidablePred (clonePred X x) := by
  classical
  exact instDecidablePredClone X x

noncomputable instance instFintypeClonePred {A : Type} [Fintype A] (X : Set A) (x : A) :
    Fintype {a : A // clonePred X x a} := by
  classical
  infer_instance

noncomputable instance instDecidableEqCloneSubtype {A : Type} (X : Set A) (x : A) :
    DecidableEq {a : A // clonePred X x a} := by
  classical
  exact Classical.decEq _

/-! ## Clone sets and restriction helpers -/

/-- A clone set `X` (subset of candidates). -/
def CloneSet {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) : Prop :=
  X.Nonempty ∧
    ∀ v c, c ∉ X →
      (∀ x ∈ X, Prefers P v x c) ∨ (∀ x ∈ X, Prefers P v c x)

/-- Remove all clones in `X` except for the representative `x`. -/
noncomputable def removeClonesExcept {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A) :
    Profile V {a : A // clonePred X x a} :=
  restrictCandidates P (clonePred X x)

lemma clonePred_swap {A : Type} [DecidableEq A] (X : Set A) (x x' a : A)
    (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    clonePred X x a ↔ clonePred X x' ((Equiv.swap x x') a) := by
  classical
  by_cases hax : a = x
  · subst hax
    simp [clonePred, Equiv.swap_apply_left]
  · by_cases hax' : a = x'
    · subst hax'
      simp [clonePred, Equiv.swap_apply_right, hxx', hx, hx', hax]
    · have hswap : (Equiv.swap x x') a = a := by
        simp [Equiv.swap_apply_def, hax, hax']
      simp [clonePred, hswap, hax, hax']

noncomputable def cloneSwapEquiv {A : Type} [DecidableEq A]
    (X : Set A) (x x' : A) (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    {a : A // clonePred X x a} ≃ {a : A // clonePred X x' a} :=
  (Equiv.swap x x').subtypeEquiv (clonePred_swap (X := X) (x := x) (x' := x')
    (hx := hx) (hx' := hx') (hxx' := hxx'))

lemma cloneSwapEquiv_apply_nonclone {A : Type} [DecidableEq A]
    {X : Set A} {x x' c : A} (hc : c ∉ X)
    (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    cloneSwapEquiv X x x' hx hx' hxx' ⟨c, Or.inl hc⟩ = ⟨c, Or.inl hc⟩ := by
  classical
  have hcx : c ≠ x := by
    intro h
    apply hc
    simpa [h] using hx
  have hcx' : c ≠ x' := by
    intro h
    apply hc
    simpa [h] using hx'
  have hswap : (Equiv.swap x x') c = c := by
    simp [Equiv.swap_apply_def, hcx, hcx']
  ext
  simp [cloneSwapEquiv, hswap]

lemma cloneSwapEquiv_symm_apply_nonclone {A : Type} [DecidableEq A]
    {X : Set A} {x x' c : A} (hc : c ∉ X)
    (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    (cloneSwapEquiv X x x' hx hx' hxx').symm ⟨c, Or.inl hc⟩ = ⟨c, Or.inl hc⟩ := by
  classical
  have hcx : c ≠ x := by
    intro h
    apply hc
    simpa [h] using hx
  have hcx' : c ≠ x' := by
    intro h
    apply hc
    simpa [h] using hx'
  apply Subtype.ext
  simp [cloneSwapEquiv, Equiv.swap_apply_def, hcx, hcx']

lemma cloneSwapEquiv_apply_rep {A : Type} [DecidableEq A]
    {X : Set A} {x x' : A} (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    cloneSwapEquiv X x x' hx hx' hxx' ⟨x, Or.inr rfl⟩ = ⟨x', Or.inr rfl⟩ := by
  classical
  ext
  simp [cloneSwapEquiv, Equiv.swap_apply_left]

lemma cloneSwapEquiv_symm_apply_rep {A : Type} [DecidableEq A]
    {X : Set A} {x x' : A} (hx : x ∈ X) (hx' : x' ∈ X) (hxx' : x ≠ x') :
    (cloneSwapEquiv X x x' hx hx' hxx').symm ⟨x', Or.inr rfl⟩ = ⟨x, Or.inr rfl⟩ := by
  classical
  apply Subtype.ext
  simp [cloneSwapEquiv, Equiv.swap_apply_right]

/-- Clone set on a restricted candidate type. -/
def restrictCloneSet {A : Type} (X : Set A) (ℓ : A) : Set {a : A // a ≠ ℓ} :=
  {a | (a : A) ∈ X}

@[simp] lemma mem_restrictCloneSet {A : Type} {X : Set A} {ℓ : A} {a : {a : A // a ≠ ℓ}} :
    a ∈ restrictCloneSet X ℓ ↔ (a : A) ∈ X := by
  rfl

lemma restrictCloneSet_nonempty {A : Type} {X : Set A} {ℓ : A}
    (h : ∃ x ∈ X, x ≠ ℓ) : (restrictCloneSet X ℓ).Nonempty := by
  rcases h with ⟨x, hx, hxne⟩
  refine ⟨⟨x, hxne⟩, ?_⟩
  simpa [restrictCloneSet] using hx

lemma cloneSet_restrictProfile
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (ℓ : A) (hX : CloneSet P X)
    (hXne : ∃ x ∈ X, x ≠ ℓ) :
    CloneSet (restrictCandidates P (fun x => x ≠ ℓ)) (restrictCloneSet X ℓ) := by
  classical
  rcases hX with ⟨_hXnonempty, hclone⟩
  refine ⟨restrictCloneSet_nonempty (X := X) (ℓ := ℓ) hXne, ?_⟩
  intro v c hc
  have hc' : (c : A) ∉ X := by
    intro hmem
    apply hc
    simpa [restrictCloneSet] using hmem
  have hcase := hclone v (c : A) hc'
  cases hcase with
  | inl hall =>
    left
    intro x hx
    have hx' : (x : A) ∈ X := by
      simpa [restrictCloneSet] using hx
    simpa using (hall x hx')
  | inr hall =>
    right
    intro x hx
    have hx' : (x : A) ∈ X := by
      simpa [restrictCloneSet] using hx
    simpa using (hall x hx')

lemma relabelProfile_restrictCandidates_subtypeSubtypeEquivSubtypeInter
  {V A : Type} [Fintype V] [Fintype A]
  (P : Profile V A)
  (p q : A → Prop) [DecidablePred p] [DecidablePred q] :
  relabelProfile (restrictCandidates (restrictCandidates P p) (fun x : {a : A // p a} => q x.1))
    (Equiv.subtypeSubtypeEquivSubtypeInter p q) =
    restrictCandidates P (fun a : A => p a ∧ q a) := by
  ext v
  rfl

@[simp] lemma prefers_removeClonesExcept_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A) (v : V)
    (a b : {a : A // clonePred X x a}) :
    Prefers (removeClonesExcept P X x) v a b ↔ Prefers P v a b := by
  rfl

lemma cloneSet_prefers_equiv
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (hX : CloneSet P X)
    {x x' y : A} (hx : x ∈ X) (hx' : x' ∈ X) (hy : y ∉ X) (v : V) :
    (Prefers P v x y ↔ Prefers P v x' y) ∧
      (Prefers P v y x ↔ Prefers P v y x') := by
  classical
  rcases hX with ⟨_, hclone⟩
  let _ := P.pref v
  have hcase := hclone v y hy
  cases hcase with
  | inl hall =>
      have hxpref : Prefers P v x y := hall x hx
      have hx'pref : Prefers P v x' y := hall x' hx'
      have hxfalse : ¬ Prefers P v y x := by
        intro h
        exact lt_asymm (hall x hx) h
      have hx'false : ¬ Prefers P v y x' := by
        intro h
        exact lt_asymm (hall x' hx') h
      refine ⟨?_, ?_⟩
      · exact ⟨(fun _ => hx'pref), (fun _ => hxpref)⟩
      · exact ⟨(fun h => (hxfalse h).elim), (fun h => (hx'false h).elim)⟩
  | inr hall =>
      have hxpref : Prefers P v y x := hall x hx
      have hx'pref : Prefers P v y x' := hall x' hx'
      have hxfalse : ¬ Prefers P v x y := by
        intro h
        exact lt_asymm h (hall x hx)
      have hx'false : ¬ Prefers P v x' y := by
        intro h
        exact lt_asymm h (hall x' hx')
      refine ⟨?_, ?_⟩
      · exact ⟨(fun h => (hxfalse h).elim), (fun h => (hx'false h).elim)⟩
      · exact ⟨(fun _ => hx'pref), (fun _ => hxpref)⟩

@[simp] lemma clonePred_restrictCloneSet_eq
  {A : Type} (X : Set A) (x ℓ : A) (hxℓ : x ≠ ℓ) :
  clonePred (restrictCloneSet (A := A) X ℓ) (⟨x, hxℓ⟩ : {a : A // a ≠ ℓ}) =
    (fun a : {a : A // a ≠ ℓ} => clonePred X x a.1) := by
  funext a
  apply propext
  constructor
  · intro h
    rcases h with h | h
    · left
      intro haX
      apply h
      simpa [restrictCloneSet] using haX
    · right
      exact congrArg Subtype.val h
  · intro h
    rcases h with h | h
    · left
      intro haX
      apply h
      simpa [restrictCloneSet] using haX
    · right
      ext
      simpa using h

/-- If `ℓ` is a clone different from the representative `x`, then deleting `ℓ` before
removing clones is redundant (up to relabeling). -/
lemma relabelProfile_removeClonesExcept_restrictProfile_of_clone
  {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
  (P : Profile V A) (X : Set A) (x ℓ : A)
  (hℓ : ℓ ∈ X) (hxℓ : x ≠ ℓ) :
  ∃ e : {a : A // clonePred X x a} ≃
      {a : {a : A // a ≠ ℓ} // clonePred (restrictCloneSet X ℓ)
        (⟨x, hxℓ⟩ : {a : A // a ≠ ℓ}) a},
    (∀ t,
      (((e t).1 : {a : A // a ≠ ℓ}).1) = t.1) ∧
    (∀ b,
      (e.symm b).1 = b.1.1) ∧
    relabelProfile (removeClonesExcept P X x) e =
      removeClonesExcept (restrictProfile P ℓ) (restrictCloneSet X ℓ)
        (⟨x, hxℓ⟩ : {a : A // a ≠ ℓ}) := by
  classical
  -- Build an explicit equivalence between the two restricted candidate types.
  let xℓ' : {a : A // a ≠ ℓ} := ⟨x, hxℓ⟩
  let e : {a : A // clonePred X x a} ≃
    {a : {a : A // a ≠ ℓ} // clonePred (restrictCloneSet X ℓ) xℓ' a} :=
    { toFun := fun t =>
        -- `t.1` cannot be `ℓ`, since `ℓ ∈ X` and `x ≠ ℓ`.
        let hne : (t.1 : A) ≠ ℓ := by
          intro hEq
          have htX : clonePred X x ℓ := by
            simpa [hEq] using t.2
          -- But `clonePred X x ℓ` would imply `ℓ ∉ X` or `ℓ = x`.
          rcases htX with htX | htX
          · exact htX hℓ
          · exact hxℓ (htX.symm)
        have hp' : clonePred (restrictCloneSet X ℓ) xℓ' (⟨t.1, hne⟩ : {a : A // a ≠ ℓ}) := by
          -- Convert the predicate using the simp lemma.
          have hpred :
              clonePred (restrictCloneSet X ℓ) xℓ' (⟨t.1, hne⟩ : {a : A // a ≠ ℓ}) ↔
                clonePred X x (t.1 : A) := by
            have := congrArg (fun f => f (⟨t.1, hne⟩ : {a : A // a ≠ ℓ}))
              (clonePred_restrictCloneSet_eq (X := X) (x := x) (ℓ := ℓ) (hxℓ := hxℓ))
            exact Iff.of_eq this
          exact (hpred.mpr t.2)
        ⟨⟨t.1, hne⟩, hp'⟩
      invFun := fun s =>
        ⟨s.1.1, by
          have hpred :
              clonePred (restrictCloneSet X ℓ) xℓ' s.1 ↔ clonePred X x (s.1 : A) := by
            have := congrArg (fun f => f s.1)
              (clonePred_restrictCloneSet_eq (X := X) (x := x) (ℓ := ℓ) (hxℓ := hxℓ))
            exact Iff.of_eq this
          exact (hpred.mp s.2)⟩
      left_inv := by
        intro t
        rfl
      right_inv := by
        intro s
        cases s with
        | mk s hs =>
            cases s with
            | mk s hs' =>
                rfl }
  refine ⟨e, ?_, ?_, ?_⟩
  · intro t
    rfl
  · intro b
    rfl
  -- Unfold both sides; the induced restricted orders coincide definitionally.
  ext v
  rfl

@[scAxiom]
def IndependenceOfClones (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
      (P : Profile V A) (X : Set A) (x : A),
    CloneSet P X → x ∈ X →
      (∀ c (hc : c ∉ X),
        (c ∈ f P ↔
          (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) ∈ f (removeClonesExcept P X x))) ∧
      ((∃ y, y ∈ X ∧ y ∈ f P) ↔
        (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈ f (removeClonesExcept P X x))

end SocialChoice
