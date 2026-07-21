import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import SocialChoice.Profile
import SocialChoice.Margin
import SocialChoice.Cycles
import SocialChoice.Rules.SplitCycle.Defs
import SocialChoice.Rules.SplitCycle.Neutrality
import SocialChoice.Rules.SplitCycle.Reversal
import SocialChoice.Axioms.Clones

namespace SocialChoice

open Finset

/--
  This file proves that Split Cycle satisfies independence of clones.
  The proof follows the paper "Split Cycle: A New Condorcet Consistent Voting Method Independent of Clones and Immune to Spoilers" by Holliday and Pacuit.
  Its formalization is based on a translation from the lean3 package `Formalized-Voting`.
  The proof reasons about deleting just one clone from the clone set.
  This is then later translated to the official definition where all but one clone are removed at once.
-/

noncomputable local instance instDecidableEq {A : Type} : DecidableEq A := Classical.decEq _

/-- Remove a single candidate (Holliday–Pacuit). -/
noncomputable def minusCandidate {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (c : A) : Profile V {x : A // x ≠ c} := by
  classical
  exact restrictCandidates P (fun x => x ≠ c)

def clones {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c}) : Prop :=
  D.Nonempty ∧
    ∀ (c' : {x : A // x ≠ c}), c' ∈ D →
      ∀ (x : {x : A // x ≠ c}) (v : V), x ∉ D →
        (Prefers P v c x ↔ Prefers P v c' x) ∧
          (Prefers P v x c ↔ Prefers P v x c')

lemma clones_of_cloneSet
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A)
    (hX : CloneSet P X) (hx : x ∈ X) (hXne : ∃ y ∈ X, y ≠ x) :
    clones P x (restrictCloneSet X x) := by
  classical
  rcases hX with ⟨_, hclone⟩
  refine ⟨restrictCloneSet_nonempty (X := X) (ℓ := x) hXne, ?_⟩
  intro c' hc' y v hy
  have hc'X : (c' : A) ∈ X := by
    simpa [restrictCloneSet] using hc'
  have hyX : (y : A) ∉ X := by
    intro hyX
    apply hy
    simpa [restrictCloneSet] using hyX
  let _ := P.pref v
  have hcase := hclone v (y : A) hyX
  cases hcase with
  | inl hall =>
      have hxpref : Prefers P v x y := hall x hx
      have hc'pref : Prefers P v c' y := hall c' hc'X
      have hxfalse : ¬ Prefers P v y x := by
        intro h
        exact lt_asymm hxpref h
      have hc'false : ¬ Prefers P v y c' := by
        intro h
        exact lt_asymm hc'pref h
      refine ⟨?_, ?_⟩
      · exact ⟨(fun _ => hc'pref), (fun _ => hxpref)⟩
      · exact ⟨(fun h => (hxfalse h).elim), (fun h => (hc'false h).elim)⟩
  | inr hall =>
      have hxpref : Prefers P v y x := hall x hx
      have hc'pref : Prefers P v y c' := hall c' hc'X
      have hxfalse : ¬ Prefers P v x y := by
        intro h
        exact lt_asymm h hxpref
      have hc'false : ¬ Prefers P v c' y := by
        intro h
        exact lt_asymm h hc'pref
      refine ⟨?_, ?_⟩
      · exact ⟨(fun h => (hxfalse h).elim), (fun h => (hc'false h).elim)⟩
      · exact ⟨(fun _ => hc'pref), (fun _ => hxpref)⟩

def NonCloneChoiceIndependenceOfClones (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
      (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c}),
    clones P c D →
      ∀ a : {x : A // x ≠ c},
        a ∉ D → (a.1 ∈ f P ↔ a ∈ f (minusCandidate P c))

def CloneChoiceIndependenceOfClones (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
      (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c}),
    clones P c D →
      ((c ∉ f P ∧ ∀ c' : {x : A // x ≠ c}, c' ∈ D → (c' : A) ∉ f P) ↔
        ∀ c' : {x : A // x ≠ c}, c' ∈ D → c' ∉ f (minusCandidate P c))

@[simp] lemma prefers_minusCandidate_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) (v : V) (a b : {x : A // x ≠ c}) :
    Prefers (minusCandidate P c) v a b ↔ Prefers P v a b := by
  rfl

lemma margin_eq_margin_minusCandidate {V A : Type} [Fintype V] [Fintype A]
    {P : Profile V A} {c : A} {a b : {x : A // x ≠ c}} :
    margin P a b = margin (minusCandidate P c) a b := by
  classical
  have h1 :
      (Finset.univ.filter (fun v => Prefers P v a b)).card =
        (Finset.univ.filter (fun v => Prefers (minusCandidate P c) v a b)).card := by
    refine cardinality_lemma2 (p := fun v => Prefers P v a b)
      (q := fun v => Prefers (minusCandidate P c) v a b) ?_
    intro v
    simp
  have h2 :
      (Finset.univ.filter (fun v => Prefers P v b a)).card =
        (Finset.univ.filter (fun v => Prefers (minusCandidate P c) v b a)).card := by
    refine cardinality_lemma2 (p := fun v => Prefers P v b a)
      (q := fun v => Prefers (minusCandidate P c) v b a) ?_
    intro v
    simp
  dsimp [margin]
  simp [h1, h2]

lemma margin_eq_clone_non_clone {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c})
    (b e : {x : A // x ≠ c}) (H : e ∈ D) (Hb : b ∉ D) :
    clones P c D → margin P c b = margin (minusCandidate P c) e b := by
  classical
  intro clone
  rcases clone with ⟨_, hclone⟩
  have h1 :
      (Finset.univ.filter (fun v => Prefers P v c b)).card =
        (Finset.univ.filter (fun v => Prefers (minusCandidate P c) v e b)).card := by
    refine cardinality_lemma2 (p := fun v => Prefers P v c b)
      (q := fun v => Prefers (minusCandidate P c) v e b) ?_
    intro v
    have hrel := (hclone e H b v Hb).1
    exact hrel
  have h2 :
      (Finset.univ.filter (fun v => Prefers P v b c)).card =
        (Finset.univ.filter (fun v => Prefers (minusCandidate P c) v b e)).card := by
    refine cardinality_lemma2 (p := fun v => Prefers P v b c)
      (q := fun v => Prefers (minusCandidate P c) v b e) ?_
    intro v
    have hrel := (hclone e H b v Hb).2
    exact hrel
  dsimp [margin]
  simp [h1, h2]

lemma margin_eq_clone_non_clone' {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c})
    {b e : {x : A // x ≠ c}} (H : e ∈ D) (Hb : b ∉ D) :
    clones P c D → margin P b c = margin (minusCandidate P c) b e := by
  classical
  intro clone
  have h := margin_eq_clone_non_clone P c D b e H Hb clone
  have hskewP : margin P b c = - margin P c b :=
    margin_antisymmetric P b c
  have hskewP' : margin (minusCandidate P c) b e =
      - margin (minusCandidate P c) e b :=
    margin_antisymmetric (minusCandidate P c) b e
  calc
    margin P b c = - margin P c b := hskewP
    _ = - margin (minusCandidate P c) e b := by simp [h]
    _ = margin (minusCandidate P c) b e := by
      symm
      exact hskewP'

lemma clone_mem_iff {A : Type} [Fintype A] (c : A) (D : Set {x : A // x ≠ c})
    {a : A} (ha : a ≠ c) :
    (∀ p : a ≠ c, (⟨a, p⟩ : {x : A // x ≠ c}) ∈ D) ↔
      (⟨a, ha⟩ : {x : A // x ≠ c}) ∈ D := by
  constructor
  · intro h
    exact h ha
  · intro h p
    exact h

lemma margin_eq_clone_left {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c})
    {a : A} (ha : a ≠ c) (haD : (⟨a, ha⟩ : {x : A // x ≠ c}) ∈ D)
    {b : {x : A // x ≠ c}} (hb : b ∉ D) (clone : clones P c D) :
    margin P a b = margin P c b := by
  have h1 := margin_eq_clone_non_clone P c D b ⟨a, ha⟩ haD hb clone
  have h2 := margin_eq_margin_minusCandidate (P := P) (c := c) (a := ⟨a, ha⟩) (b := b)
  have hcb : margin P c b = margin P a b :=
    h1.trans h2.symm
  exact hcb.symm

lemma margin_eq_clone_right {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c})
    {a : {x : A // x ≠ c}} (ha : a ∉ D)
    {e : {x : A // x ≠ c}} (he : e ∈ D) (clone : clones P c D) :
    margin P a e = margin P a c := by
  have h1 := margin_eq_clone_non_clone P c D a e he ha clone
  have h2 := margin_eq_margin_minusCandidate (P := P) (c := c) (a := e) (b := a)
  have hce : margin P c a = margin P e a :=
    h1.trans h2.symm
  have hskewP : margin P a e = - margin P e a :=
    margin_antisymmetric P a e
  have hskewP' : margin P a c = - margin P c a :=
    margin_antisymmetric P a c
  calc
    margin P a e = - margin P e a := hskewP
    _ = - margin P c a := by simp [hce]
    _ = margin P a c := by
      symm
      exact hskewP'

noncomputable def removeClones {A : Type} [Fintype A]
    (c : A) (D : Set {x : A // x ≠ c}) : List A → List A := by
  classical
  intro l
  exact
    to_path
      (l.map (fun x =>
        if (∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D) then c else x))

lemma replaceClonesHelper {A : Type} [Fintype A]
    (c : A) (D : Set {x : A // x ≠ c}) {x : A}
    (h : ¬∀ (p : x ≠ c), (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D) : x ≠ c := by
  intro hx
  subst hx
  apply h
  intro p
  exact (False.elim (p rfl))

noncomputable def replaceClones {A : Type} [Fintype A]
    (c : A) (D : Set {x : A // x ≠ c}) (d : {x : A // x ≠ c}) (_hd : d ∈ D) :
    List A → List {x : A // x ≠ c} := by
  classical
  intro l
  exact
    to_path
      (l.map (fun x =>
        dite (∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D)
          (fun _ => d)
          (fun h => ⟨x, replaceClonesHelper c D h⟩)))

noncomputable def removeClones' {A : Type} [Fintype A]
    (c : A) (D : Set {x : A // x ≠ c}) : List {x : A // x ≠ c} → List A := by
  classical
  intro l
  exact to_path (l.map (fun x => if x ∈ D then c else (x : A)))

lemma removeClones_nil_iff {A : Type} [Fintype A]
    (c : A) (D : Set {x : A // x ≠ c}) (l : List A) :
    l = [] ↔ removeClones c D l = [] := by
  classical
  constructor
  · intro h
    subst h
    simp [removeClones, to_path]
  · intro h
    have h' : l.map (fun x =>
        if (∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D) then c else x) = [] := by
      have : to_path (l.map (fun x =>
          if (∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D) then c else x)) = [] :=
        h
      exact (to_path_eq_nil_iff _).1 this
    exact (List.map_eq_nil_iff.mp h')

lemma removeClones_ne_nil_iff {A : Type} [Fintype A]
    (c : A) (D : Set {x : A // x ≠ c}) (l : List A) :
    l ≠ [] ↔ removeClones c D l ≠ [] :=
  not_iff_not.mpr (removeClones_nil_iff c D l)

lemma removeClones_nodup {A : Type} [Fintype A]
    (c : A) (D : Set {x : A // x ≠ c}) (l : List A) :
    (removeClones c D l).Nodup := by
  classical
  simp [removeClones, to_path_nodup]

lemma removeClones_first_elem {A : Type} [Fintype A]
    (c : A) (D : Set {x : A // x ≠ c}) (l : List A) (a : A)
    (hnot : ∀ p : a ≠ c, (⟨a, p⟩ : {x : A // x ≠ c}) ∉ D)
    (hne : l ≠ []) :
    l[0]'(List.length_pos_of_ne_nil hne) = a →
      (removeClones c D l)[0]'(List.length_pos_of_ne_nil
        ((removeClones_ne_nil_iff c D l).mp hne)) = a := by
  classical
  intro h0
  set f : A → A := fun x =>
    if (∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D) then c else x
  have hmap_ne : l.map f ≠ [] := by
    intro hmap
    exact hne (List.map_eq_nil_iff.mp hmap)
  have hfirst :=
    to_path_first_elem (l := l.map f) (h := hmap_ne)
  have hfirst' :
      (removeClones c D l)[0]'(List.length_pos_of_ne_nil
        ((removeClones_ne_nil_iff c D l).mp hne)) =
        (l.map f)[0]'(List.length_pos_of_ne_nil hmap_ne) :=
    hfirst
  have hmap0 :
      (l.map f)[0]'(List.length_pos_of_ne_nil hmap_ne) =
        f (l[0]'(List.length_pos_of_ne_nil hne)) :=
    List.getElem_map (f := f) (l := l) (i := 0)
        (h := List.length_pos_of_ne_nil hmap_ne)
  have hf : f a = a := by
    by_cases hac : a = c
    · subst hac
      simp [f]
    · have hclone :
        ¬∀ p : a ≠ c, (⟨a, p⟩ : {x : A // x ≠ c}) ∈ D := by
          intro hall
          exact (hnot hac) (hall hac)
      simp [f, hclone]
  calc
    (removeClones c D l)[0]'(List.length_pos_of_ne_nil
        ((removeClones_ne_nil_iff c D l).mp hne)) =
        (l.map f)[0]'(List.length_pos_of_ne_nil hmap_ne) := hfirst'
    _ = f (l[0]'(List.length_pos_of_ne_nil hne)) := hmap0
    _ = f a := by simp [h0]
    _ = a := hf

lemma removeClones_last_elem {A : Type} [Fintype A]
    (c : A) (D : Set {x : A // x ≠ c}) (l : List A) (a : A)
    (hnot : ∀ p : a ≠ c, (⟨a, p⟩ : {x : A // x ≠ c}) ∉ D)
    (hne : l ≠ []) :
    l.getLast hne = a →
      (removeClones c D l).getLast ((removeClones_ne_nil_iff c D l).mp hne) = a := by
  classical
  intro hlast
  set f : A → A := fun x =>
    if (∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D) then c else x
  have hmap_ne : l.map f ≠ [] := by
    intro hmap
    exact hne (List.map_eq_nil_iff.mp hmap)
  have hlast' :=
    to_path_last_elem (l := l.map f) (h := hmap_ne)
  have hlast'' :
      (removeClones c D l).getLast ((removeClones_ne_nil_iff c D l).mp hne) =
        (l.map f).getLast hmap_ne :=
    hlast'
  have hmap_last :
      (l.map f).getLast hmap_ne = f (l.getLast hne) :=
    List.getLast_map (f := f) (l := l) (h := hmap_ne)
  have hf : f a = a := by
    by_cases hac : a = c
    · subst hac
      simp [f]
    · have hclone :
        ¬∀ p : a ≠ c, (⟨a, p⟩ : {x : A // x ≠ c}) ∈ D := by
          intro hall
          exact (hnot hac) (hall hac)
      simp [f, hclone]
  calc
    (removeClones c D l).getLast ((removeClones_ne_nil_iff c D l).mp hne) =
        (l.map f).getLast hmap_ne := hlast''
    _ = f (l.getLast hne) := hmap_last
    _ = f a := by simp [hlast]
    _ = a := hf

lemma removeClones_last_c {A : Type} [Fintype A]
    (c : A) (D : Set {x : A // x ≠ c}) (l : List A) (d : {x : A // x ≠ c})
    (hd : d ∈ D) (hne : l ≠ []) :
    l.getLast hne = (d : A) →
      (removeClones c D l).getLast ((removeClones_ne_nil_iff c D l).mp hne) = c := by
  classical
  intro hlast
  set f : A → A := fun x =>
    if (∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D) then c else x
  have hmap_ne : l.map f ≠ [] := by
    intro hmap
    exact hne (List.map_eq_nil_iff.mp hmap)
  have hlast' :=
    to_path_last_elem (l := l.map f) (h := hmap_ne)
  have hlast'' :
      (removeClones c D l).getLast ((removeClones_ne_nil_iff c D l).mp hne) =
        (l.map f).getLast hmap_ne :=
    hlast'
  have hmap_last :
      (l.map f).getLast hmap_ne = f (l.getLast hne) :=
    List.getLast_map (f := f) (l := l) (h := hmap_ne)
  have hall :
      ∀ p : (d : A) ≠ c, (⟨(d : A), p⟩ : {x : A // x ≠ c}) ∈ D :=
    (clone_mem_iff (c := c) (D := D) (a := (d : A)) (ha := d.property)).2 hd
  have hf : f d = c := by
    simp [f, hall]
  calc
    (removeClones c D l).getLast ((removeClones_ne_nil_iff c D l).mp hne) =
        (l.map f).getLast hmap_ne := hlast''
    _ = f (l.getLast hne) := hmap_last
    _ = f d := by simp [hlast]
    _ = c := hf

lemma removeClones'_nil_iff {A : Type} [Fintype A]
    (c : A) (D : Set {x : A // x ≠ c}) (l : List {x : A // x ≠ c}) :
    l = [] ↔ removeClones' c D l = [] := by
  classical
  constructor
  · intro h
    subst h
    simp [removeClones', to_path]
  · intro h
    have h' : l.map (fun x => if x ∈ D then c else (x : A)) = [] := by
      have : to_path (l.map (fun x => if x ∈ D then c else (x : A))) = [] :=
        h
      exact (to_path_eq_nil_iff _).1 this
    exact (List.map_eq_nil_iff.mp h')

lemma removeClones'_ne_nil_iff {A : Type} [Fintype A]
    (c : A) (D : Set {x : A // x ≠ c}) (l : List {x : A // x ≠ c}) :
    l ≠ [] ↔ removeClones' c D l ≠ [] :=
  not_iff_not.mpr (removeClones'_nil_iff c D l)

lemma removeClones'_nodup {A : Type} [Fintype A]
    (c : A) (D : Set {x : A // x ≠ c}) (l : List {x : A // x ≠ c}) :
    (removeClones' c D l).Nodup := by
  classical
  simp [removeClones', to_path_nodup]

lemma removeClones'_first_elem {A : Type} [Fintype A]
    (c : A) (D : Set {x : A // x ≠ c}) (l : List {x : A // x ≠ c})
    (a : {x : A // x ≠ c}) (hnot : a ∉ D) (hne : l ≠ []) :
    l[0]'(List.length_pos_of_ne_nil hne) = a →
      (removeClones' c D l)[0]'(List.length_pos_of_ne_nil
        ((removeClones'_ne_nil_iff c D l).mp hne)) = a := by
  classical
  intro h0
  set f : {x : A // x ≠ c} → A := fun x => if x ∈ D then c else (x : A)
  have hmap_ne : l.map f ≠ [] := by
    intro hmap
    exact hne (List.map_eq_nil_iff.mp hmap)
  have hfirst :=
    to_path_first_elem (l := l.map f) (h := hmap_ne)
  have hfirst' :
      (removeClones' c D l)[0]'(List.length_pos_of_ne_nil
        ((removeClones'_ne_nil_iff c D l).mp hne)) =
        (l.map f)[0]'(List.length_pos_of_ne_nil hmap_ne) :=
    hfirst
  have hmap0 :
      (l.map f)[0]'(List.length_pos_of_ne_nil hmap_ne) =
        f (l[0]'(List.length_pos_of_ne_nil hne)) :=
    List.getElem_map (f := f) (l := l) (i := 0)
        (h := List.length_pos_of_ne_nil hmap_ne)
  have hf : f a = a := by
    have hnot' : ¬a ∈ D := hnot
    simp [f, hnot']
  calc
    (removeClones' c D l)[0]'(List.length_pos_of_ne_nil
        ((removeClones'_ne_nil_iff c D l).mp hne)) =
        (l.map f)[0]'(List.length_pos_of_ne_nil hmap_ne) := hfirst'
    _ = f (l[0]'(List.length_pos_of_ne_nil hne)) := hmap0
    _ = f a := by simp [h0]
    _ = a := hf

lemma removeClones'_last_elem {A : Type} [Fintype A]
    (c : A) (D : Set {x : A // x ≠ c}) (l : List {x : A // x ≠ c})
    (a : {x : A // x ≠ c}) (hnot : a ∉ D) (hne : l ≠ []) :
    l.getLast hne = a →
      (removeClones' c D l).getLast ((removeClones'_ne_nil_iff c D l).mp hne) = a := by
  classical
  intro hlast
  set f : {x : A // x ≠ c} → A := fun x => if x ∈ D then c else (x : A)
  have hmap_ne : l.map f ≠ [] := by
    intro hmap
    exact hne (List.map_eq_nil_iff.mp hmap)
  have hlast' :=
    to_path_last_elem (l := l.map f) (h := hmap_ne)
  have hlast'' :
      (removeClones' c D l).getLast ((removeClones'_ne_nil_iff c D l).mp hne) =
        (l.map f).getLast hmap_ne :=
    hlast'
  have hmap_last :
      (l.map f).getLast hmap_ne = f (l.getLast hne) :=
    List.getLast_map (f := f) (l := l) (h := hmap_ne)
  have hf : f a = a := by
    have hnot' : ¬a ∈ D := hnot
    simp [f, hnot']
  calc
    (removeClones' c D l).getLast ((removeClones'_ne_nil_iff c D l).mp hne) =
        (l.map f).getLast hmap_ne := hlast''
    _ = f (l.getLast hne) := hmap_last
    _ = f a := by simp [hlast]
    _ = a := hf

lemma replaceClones_nil_iff {A : Type} [Fintype A]
    (c : A) (D : Set {x : A // x ≠ c}) (d : {x : A // x ≠ c}) (hd : d ∈ D) (l : List A) :
    l = [] ↔ replaceClones c D d hd l = [] := by
  classical
  constructor
  · intro h
    subst h
    simp [replaceClones, to_path]
  · intro h
    have h' : l.map (fun x =>
        dite (∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D)
          (fun _ => d)
          (fun h => ⟨x, replaceClonesHelper c D h⟩)) = [] := by
      have : to_path (l.map (fun x =>
          dite (∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D)
            (fun _ => d)
            (fun h => ⟨x, replaceClonesHelper c D h⟩))) = [] :=
        h
      exact (to_path_eq_nil_iff _).1 this
    exact (List.map_eq_nil_iff.mp h')

lemma replaceClones_ne_nil_iff {A : Type} [Fintype A]
    (c : A) (D : Set {x : A // x ≠ c}) (d : {x : A // x ≠ c}) (hd : d ∈ D) (l : List A) :
    l ≠ [] ↔ replaceClones c D d hd l ≠ [] :=
  not_iff_not.mpr (replaceClones_nil_iff c D d hd l)

lemma replaceClones_nodup {A : Type} [Fintype A]
    (c : A) (D : Set {x : A // x ≠ c}) (d : {x : A // x ≠ c}) (hd : d ∈ D) (l : List A) :
    (replaceClones c D d hd l).Nodup := by
  classical
  simp [replaceClones, to_path_nodup]

lemma replaceClones_first_elem {A : Type} [Fintype A]
    (c : A) (D : Set {x : A // x ≠ c}) (d : {x : A // x ≠ c}) (hd : d ∈ D)
    (l : List A) (a : A)
    (hnot : ¬∀ p : a ≠ c, (⟨a, p⟩ : {x : A // x ≠ c}) ∈ D)
    (hne : l ≠ []) :
    l[0]'(List.length_pos_of_ne_nil hne) = a →
      (replaceClones c D d hd l)[0]'(List.length_pos_of_ne_nil
        ((replaceClones_ne_nil_iff c D d hd l).mp hne)) = ⟨a, replaceClonesHelper c D hnot⟩ := by
  classical
  intro h0
  set f : A → {x : A // x ≠ c} := fun x =>
    dite (∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D)
      (fun _ => d)
      (fun h => ⟨x, replaceClonesHelper c D h⟩)
  have hmap_ne : l.map f ≠ [] := by
    intro hmap
    exact hne (List.map_eq_nil_iff.mp hmap)
  have hfirst :=
    to_path_first_elem (l := l.map f) (h := hmap_ne)
  have hfirst' :
      (replaceClones c D d hd l)[0]'(List.length_pos_of_ne_nil
        ((replaceClones_ne_nil_iff c D d hd l).mp hne)) =
        (l.map f)[0]'(List.length_pos_of_ne_nil hmap_ne) :=
    hfirst
  have hmap0 :
      (l.map f)[0]'(List.length_pos_of_ne_nil hmap_ne) =
        f (l[0]'(List.length_pos_of_ne_nil hne)) :=
    List.getElem_map (f := f) (l := l) (i := 0)
        (h := List.length_pos_of_ne_nil hmap_ne)
  have hf : f a = ⟨a, replaceClonesHelper c D hnot⟩ := by
    simp [f, hnot]
  calc
    (replaceClones c D d hd l)[0]'(List.length_pos_of_ne_nil
        ((replaceClones_ne_nil_iff c D d hd l).mp hne)) =
        (l.map f)[0]'(List.length_pos_of_ne_nil hmap_ne) := hfirst'
    _ = f (l[0]'(List.length_pos_of_ne_nil hne)) := hmap0
    _ = f a := by simp [h0]
    _ = ⟨a, replaceClonesHelper c D hnot⟩ := hf

lemma replaceClones_last_elem {A : Type} [Fintype A]
    (c : A) (D : Set {x : A // x ≠ c}) (d : {x : A // x ≠ c}) (hd : d ∈ D)
    (l : List A) (a : A)
    (hnot : ¬∀ p : a ≠ c, (⟨a, p⟩ : {x : A // x ≠ c}) ∈ D)
    (hne : l ≠ []) :
    l.getLast hne = a →
      (replaceClones c D d hd l).getLast ((replaceClones_ne_nil_iff c D d hd l).mp hne) =
        ⟨a, replaceClonesHelper c D hnot⟩ := by
  classical
  intro hlast
  set f : A → {x : A // x ≠ c} := fun x =>
    dite (∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D)
      (fun _ => d)
      (fun h => ⟨x, replaceClonesHelper c D h⟩)
  have hmap_ne : l.map f ≠ [] := by
    intro hmap
    exact hne (List.map_eq_nil_iff.mp hmap)
  have hlast' :=
    to_path_last_elem (l := l.map f) (h := hmap_ne)
  have hlast'' :
      (replaceClones c D d hd l).getLast ((replaceClones_ne_nil_iff c D d hd l).mp hne) =
        (l.map f).getLast hmap_ne :=
    hlast'
  have hmap_last :
      (l.map f).getLast hmap_ne = f (l.getLast hne) :=
    List.getLast_map (f := f) (l := l) (h := hmap_ne)
  have hf : f a = ⟨a, replaceClonesHelper c D hnot⟩ := by
    simp [f, hnot]
  calc
    (replaceClones c D d hd l).getLast ((replaceClones_ne_nil_iff c D d hd l).mp hne) =
        (l.map f).getLast hmap_ne := hlast''
    _ = f (l.getLast hne) := hmap_last
    _ = f a := by simp [hlast]
    _ = ⟨a, replaceClonesHelper c D hnot⟩ := hf

lemma replaceClones_last_c {A : Type} [Fintype A]
    (c : A) (D : Set {x : A // x ≠ c}) (d : {x : A // x ≠ c}) (hd : d ∈ D)
    (l : List A) (hne : l ≠ []) :
    l.getLast hne = c →
      (replaceClones c D d hd l).getLast ((replaceClones_ne_nil_iff c D d hd l).mp hne) = d := by
  classical
  intro hlast
  set f : A → {x : A // x ≠ c} := fun x =>
    dite (∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D)
      (fun _ => d)
      (fun h => ⟨x, replaceClonesHelper c D h⟩)
  have hmap_ne : l.map f ≠ [] := by
    intro hmap
    exact hne (List.map_eq_nil_iff.mp hmap)
  have hlast' :=
    to_path_last_elem (l := l.map f) (h := hmap_ne)
  have hlast'' :
      (replaceClones c D d hd l).getLast ((replaceClones_ne_nil_iff c D d hd l).mp hne) =
        (l.map f).getLast hmap_ne :=
    hlast'
  have hmap_last :
      (l.map f).getLast hmap_ne = f (l.getLast hne) :=
    List.getLast_map (f := f) (l := l) (h := hmap_ne)
  have hf : f c = d := by
    have hclone : ∀ p : c ≠ c, (⟨c, p⟩ : {x : A // x ≠ c}) ∈ D := by
      intro p
      exact (False.elim (p rfl))
    simp [f, hclone]
  calc
    (replaceClones c D d hd l).getLast ((replaceClones_ne_nil_iff c D d hd l).mp hne) =
        (l.map f).getLast hmap_ne := hlast''
    _ = f (l.getLast hne) := hmap_last
    _ = f c := by simp [hlast]
    _ = d := hf

section ChainTransport

variable {V A : Type} [Fintype V] [Fintype A]

lemma not_clone_mem {A : Type} [Fintype A] (c : A) (D : Set {x : A // x ≠ c})
    {x : A} (h : ¬∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D) :
    (⟨x, replaceClonesHelper c D h⟩ : {x : A // x ≠ c}) ∉ D := by
  intro hx
  have hall : ∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D := by
    have hiff :=
      (clone_mem_iff (c := c) (D := D) (a := x) (ha := replaceClonesHelper c D h))
    exact (hiff.mpr hx)
  exact h hall

lemma chain_of_chain_eq_or {X : Type} {R : X → X → Prop} {l : List X}
    (hchain : List.IsChain (fun a b => a = b ∨ R a b) l) (hnodup : l.Nodup) :
    List.IsChain R l := by
  refine (List.isChain_iff_getElem (R := R) (l := l)).2 ?_
  intro i hi
  have hchain' :=
    (List.isChain_iff_getElem (R := fun a b => a = b ∨ R a b) (l := l)).1 hchain
  have hrel := hchain' i hi
  cases hrel with
  | inl hEq =>
      have hi' : i < l.length := lt_trans (Nat.lt_succ_self i) hi
      have hEqIdx :
          i = i + 1 :=
        (List.Nodup.getElem_inj_iff (l := l) hnodup (i := i) (hi := hi')
          (j := i + 1) (hj := hi)).1 hEq
      exact (False.elim ((Nat.ne_of_lt (Nat.lt_succ_self i)) hEqIdx))
  | inr hR =>
      exact hR

lemma removeClones_chain_of_chain (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c})
    (l : List A) (b d : {x : A // x ≠ c}) (hb : b ∉ D) (hd : d ∈ D) (clone : clones P c D) :
    List.IsChain (fun a b_1 : A => margin P d b ≤ margin P a b_1) l →
      List.IsChain (fun a b_1 : A => margin P c b ≤ margin P a b_1) (removeClones c D l) := by
  classical
  intro hchain
  set f : A → A := fun x =>
    if (∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D) then c else x
  have hchain' :
      List.IsChain (fun a b_1 => f a = f b_1 ∨ margin P c b ≤ margin P (f a) (f b_1)) l := by
    refine hchain.imp ?_
    intro x y hxy
    by_cases hEq : f x = f y
    · exact Or.inl hEq
    · have hcb : margin P c b = margin P d b := by
        have h :=
          margin_eq_clone_left (P := P) (c := c) (D := D) (a := d.1) (ha := d.2)
            (haD := by simpa using hd) (b := b) (hb := hb) (clone := clone)
        simpa using h.symm
      have hxy' : margin P c b ≤ margin P x y := by
        simpa [hcb] using hxy
      have hxy'' : margin P x y = margin P (f x) (f y) := by
        by_cases hxClone : ∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D
        · have hfx : f x = c := by simp [f, hxClone]
          have hyClone : ¬∀ p : y ≠ c, (⟨y, p⟩ : {x : A // x ≠ c}) ∈ D := by
            intro hy
            have : f y = c := by simp [f, hy]
            exact hEq (by simpa [hfx] using this.symm)
          have hfy : f y = y := by simp [f, hyClone]
          by_cases hxEq : x = c
          · simp [hxEq, hfy, f]
          · have hxD :
              (⟨x, hxEq⟩ : {x : A // x ≠ c}) ∈ D :=
              (clone_mem_iff (c := c) (D := D) (a := x) hxEq).1 hxClone
            have hyNot :
              (⟨y, replaceClonesHelper c D hyClone⟩ : {x : A // x ≠ c}) ∉ D :=
              not_clone_mem c D hyClone
            have hcl :=
              margin_eq_clone_left (P := P) (c := c) (D := D) (a := x) (ha := hxEq)
                (haD := hxD) (b := ⟨y, replaceClonesHelper c D hyClone⟩)
                (hb := hyNot) (clone := clone)
            simpa [hfx, hfy] using hcl
        · have hfx : f x = x := by simp [f, hxClone]
          by_cases hyClone : ∀ p : y ≠ c, (⟨y, p⟩ : {x : A // x ≠ c}) ∈ D
          · have hfy : f y = c := by simp [f, hyClone]
            by_cases hyEq : y = c
            · simp [hyEq, hfx, f]
            · have hxNot :
                (⟨x, replaceClonesHelper c D hxClone⟩ : {x : A // x ≠ c}) ∉ D :=
                not_clone_mem c D hxClone
              have hyD :
                (⟨y, hyEq⟩ : {x : A // x ≠ c}) ∈ D :=
                (clone_mem_iff (c := c) (D := D) (a := y) hyEq).1 hyClone
              have hcl :=
                margin_eq_clone_right (P := P) (c := c) (D := D)
                  (a := ⟨x, replaceClonesHelper c D hxClone⟩) (ha := hxNot)
                  (e := ⟨y, hyEq⟩) (he := hyD) (clone := clone)
              simpa [hfx, hfy] using hcl
          · have hfy : f y = y := by simp [f, hyClone]
            simp [hfx, hfy]
      exact Or.inr (by simpa [hxy''] using hxy')
  have hchain_map :
      List.IsChain (fun a b_1 => a = b_1 ∨ margin P c b ≤ margin P a b_1) (l.map f) := by
    exact (List.isChain_map (R := fun a b_1 => a = b_1 ∨ margin P c b ≤ margin P a b_1)
      (f := f) (l := l)).2 hchain'
  have hchain_path :
      List.IsChain (fun a b_1 => a = b_1 ∨ margin P c b ≤ margin P a b_1)
        (removeClones c D l) := by
    have hpath :=
      to_path_chain'_of_chain' (P := fun a b_1 => a = b_1 ∨ margin P c b ≤ margin P a b_1)
        (l := l.map f) hchain_map
    simpa [removeClones, f] using hpath
  exact chain_of_chain_eq_or (R := fun a b_1 : A => margin P c b ≤ margin P a b_1)
    hchain_path (removeClones_nodup c D l)

lemma A6_chain (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c})
    (l : List A) (b d d' : {x : A // x ≠ c}) (hd : d ∈ D) (clone : clones P c D) :
    List.IsChain (fun a b_1 : A => margin P b d' ≤ margin P a b_1) l →
      List.IsChain (fun a b_1 : {x : A // x ≠ c} =>
        margin (minusCandidate P c) b d' ≤ margin (minusCandidate P c) a b_1)
        (replaceClones c D d hd l) := by
  classical
  intro hchain
  set f : A → {x : A // x ≠ c} := fun x =>
    dite (∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D)
      (fun _ => d)
      (fun h => ⟨x, replaceClonesHelper c D h⟩)
  have hchain' :
      List.IsChain
          (fun a b_1 =>
            f a = f b_1 ∨
              margin (minusCandidate P c) b d' ≤
                margin (minusCandidate P c) (f a) (f b_1)) l := by
    refine hchain.imp ?_
    intro x y hxy
    by_cases hEq : f x = f y
    · exact Or.inl hEq
    · have hxy' :
        margin (minusCandidate P c) b d' ≤ margin (minusCandidate P c) (f x) (f y) := by
        have hbd : margin (minusCandidate P c) b d' = margin P b d' := by
          have h := margin_eq_margin_minusCandidate (P := P) (c := c) (a := b) (b := d')
          simpa using h.symm
        have hxy0 : margin P b d' ≤ margin P x y := hxy
        have hxy1 : margin (minusCandidate P c) b d' ≤ margin P x y := by
          simpa [hbd] using hxy0
        have hxy2 : margin P x y = margin (minusCandidate P c) (f x) (f y) := by
          by_cases hxClone : ∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D
          · have hfx : f x = d := by simp [f, hxClone]
            have hyClone : ¬∀ p : y ≠ c, (⟨y, p⟩ : {x : A // x ≠ c}) ∈ D := by
              intro hy
              have : f y = d := by simp [f, hy]
              exact hEq (by simpa [hfx] using this.symm)
            have hfy : f y = ⟨y, replaceClonesHelper c D hyClone⟩ := by
              simp [f, hyClone]
            by_cases hxEq : x = c
            · simp [hxEq]
              have hyNot :
                  (⟨y, replaceClonesHelper c D hyClone⟩ : {x : A // x ≠ c}) ∉ D :=
                not_clone_mem c D hyClone
              have hcd :=
                margin_eq_clone_non_clone (P := P) (c := c) (D := D)
                  (b := ⟨y, replaceClonesHelper c D hyClone⟩) (e := d)
                  (H := hd) (Hb := hyNot) clone
              have hfc : f c = d := by
                simpa [hxEq] using hfx
              simpa [hfc, hfy] using hcd
            · have hxD :
                (⟨x, hxEq⟩ : {x : A // x ≠ c}) ∈ D :=
                (clone_mem_iff (c := c) (D := D) (a := x) hxEq).1 hxClone
              have hyNot :
                (⟨y, replaceClonesHelper c D hyClone⟩ : {x : A // x ≠ c}) ∉ D :=
                not_clone_mem c D hyClone
              have hcl :=
                margin_eq_clone_left (P := P) (c := c) (D := D) (a := x) (ha := hxEq)
                  (haD := hxD) (b := ⟨y, replaceClonesHelper c D hyClone⟩)
                  (hb := hyNot) (clone := clone)
              have hcl' :
                  margin P x y =
                    margin (minusCandidate P c) d
                      (⟨y, replaceClonesHelper c D hyClone⟩ : {x : A // x ≠ c}) := by
                have hcd := margin_eq_clone_non_clone P c D
                  (b := ⟨y, replaceClonesHelper c D hyClone⟩) (e := d)
                  (H := hd) (Hb := hyNot) clone
                simpa using (hcl.trans hcd)
              simpa [hfx, hfy] using hcl'
          · have hfx : f x = ⟨x, replaceClonesHelper c D hxClone⟩ := by
              simp [f, hxClone]
            by_cases hyClone : ∀ p : y ≠ c, (⟨y, p⟩ : {x : A // x ≠ c}) ∈ D
            · have hfy : f y = d := by simp [f, hyClone]
              by_cases hyEq : y = c
              · simp [hyEq]
                have hxNot :
                    (⟨x, replaceClonesHelper c D hxClone⟩ : {x : A // x ≠ c}) ∉ D :=
                  not_clone_mem c D hxClone
                have hcd :=
                  margin_eq_clone_non_clone' (P := P) (c := c) (D := D)
                    (H := hd) (Hb := hxNot) (b := ⟨x, replaceClonesHelper c D hxClone⟩) clone
                have hfc : f c = d := by
                  simpa [hyEq] using hfy
                simpa [hfx, hfc] using hcd
              · have hxNot :
                  (⟨x, replaceClonesHelper c D hxClone⟩ : {x : A // x ≠ c}) ∉ D :=
                  not_clone_mem c D hxClone
                have hyD :
                  (⟨y, hyEq⟩ : {x : A // x ≠ c}) ∈ D :=
                  (clone_mem_iff (c := c) (D := D) (a := y) hyEq).1 hyClone
                have hcl :=
                  margin_eq_clone_right (P := P) (c := c) (D := D)
                    (a := ⟨x, replaceClonesHelper c D hxClone⟩) (ha := hxNot)
                    (e := ⟨y, hyEq⟩) (he := hyD) (clone := clone)
                have hcl' :
                    margin P x y =
                      margin (minusCandidate P c)
                        (⟨x, replaceClonesHelper c D hxClone⟩ : {x : A // x ≠ c}) d := by
                  have hcd := margin_eq_clone_non_clone' (P := P) (c := c) (D := D)
                    (H := hd) (Hb := hxNot) (b := ⟨x, replaceClonesHelper c D hxClone⟩) clone
                  simpa using (hcl.trans hcd)
                simpa [hfx, hfy] using hcl'
            · have hfy : f y = ⟨y, replaceClonesHelper c D hyClone⟩ := by
                simp [f, hyClone]
              have hxy3 :
                  margin P x y =
                    margin (minusCandidate P c)
                      ⟨x, replaceClonesHelper c D hxClone⟩
                      ⟨y, replaceClonesHelper c D hyClone⟩ := by
                simpa using (margin_eq_margin_minusCandidate
                  (P := P) (c := c)
                  (a := ⟨x, replaceClonesHelper c D hxClone⟩)
                  (b := ⟨y, replaceClonesHelper c D hyClone⟩))
              simpa [hfx, hfy] using hxy3
        simpa [hxy2] using hxy1
      exact Or.inr hxy'
  have hchain_map :
      List.IsChain
          (fun a b_1 : {x : A // x ≠ c} =>
            a = b_1 ∨
              margin (minusCandidate P c) b d' ≤ margin (minusCandidate P c) a b_1)
          (l.map f) := by
    exact (List.isChain_map
      (R := fun a b_1 : {x : A // x ≠ c} =>
        a = b_1 ∨ margin (minusCandidate P c) b d' ≤ margin (minusCandidate P c) a b_1)
      (f := f) (l := l)).2 hchain'
  have hchain_path :
      List.IsChain
          (fun a b_1 : {x : A // x ≠ c} =>
            a = b_1 ∨
              margin (minusCandidate P c) b d' ≤ margin (minusCandidate P c) a b_1)
          (replaceClones c D d hd l) := by
    have hpath :=
      to_path_chain'_of_chain'
        (P := fun a b_1 : {x : A // x ≠ c} =>
          a = b_1 ∨ margin (minusCandidate P c) b d' ≤ margin (minusCandidate P c) a b_1)
        (l := l.map f) hchain_map
    simpa [replaceClones, f] using hpath
  exact chain_of_chain_eq_or
    (R := fun a b_1 : {x : A // x ≠ c} =>
      margin (minusCandidate P c) b d' ≤ margin (minusCandidate P c) a b_1)
    hchain_path (replaceClones_nodup c D d hd l)

lemma A5_chain (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c})
    (l : List A) (d b : {x : A // x ≠ c}) (hd : d ∈ D) (hb : b ∉ D)
    (clone : clones P c D) :
    List.IsChain (fun a b_1 : A => margin P c b ≤ margin P a b_1) l →
      List.IsChain (fun a b_1 : {x : A // x ≠ c} =>
        margin P d b ≤ margin P a b_1) (replaceClones c D d hd l) := by
  classical
  intro hchain
  set f : A → {x : A // x ≠ c} := fun x =>
    dite (∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D)
      (fun _ => d)
      (fun h => ⟨x, replaceClonesHelper c D h⟩)
  have hchain' :
      List.IsChain
          (fun a b_1 =>
            f a = f b_1 ∨ margin P d b ≤ margin P (f a) (f b_1)) l := by
    refine hchain.imp ?_
    intro x y hxy
    by_cases hEq : f x = f y
    · exact Or.inl hEq
    · have hdb : margin P d b = margin P c b := by
        have h :=
          margin_eq_clone_left (P := P) (c := c) (D := D) (a := d.1) (ha := d.2)
            (haD := by simpa using hd) (b := b) (hb := hb) (clone := clone)
        simpa using h
      have hxy' : margin P d b ≤ margin P x y := by
        simpa [hdb] using hxy
      have hxy'' : margin P x y = margin P (f x) (f y) := by
        by_cases hxClone : ∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D
        · have hfx : f x = d := by simp [f, hxClone]
          have hyClone : ¬∀ p : y ≠ c, (⟨y, p⟩ : {x : A // x ≠ c}) ∈ D := by
            intro hy
            have : f y = d := by simp [f, hy]
            exact hEq (by simpa [hfx] using this.symm)
          have hfy : f y = ⟨y, replaceClonesHelper c D hyClone⟩ := by
            simp [f, hyClone]
          by_cases hxEq : x = c
          · simp [hxEq]
            have hyNot :
                (⟨y, replaceClonesHelper c D hyClone⟩ : {x : A // x ≠ c}) ∉ D :=
              not_clone_mem c D hyClone
            have hcd :=
              margin_eq_clone_non_clone (P := P) (c := c) (D := D)
                (b := ⟨y, replaceClonesHelper c D hyClone⟩) (e := d)
                (H := hd) (Hb := hyNot) clone
            have hfc : f c = d := by
              simpa [hxEq] using hfx
            have htrans := hcd.trans
              (margin_eq_margin_minusCandidate (P := P) (c := c) (a := d)
                (b := (⟨y, replaceClonesHelper c D hyClone⟩ : {x : A // x ≠ c}))).symm
            simpa [hfc, hfy] using htrans
          · have hxD :
              (⟨x, hxEq⟩ : {x : A // x ≠ c}) ∈ D :=
              (clone_mem_iff (c := c) (D := D) (a := x) hxEq).1 hxClone
            have hyNot :
              (⟨y, replaceClonesHelper c D hyClone⟩ : {x : A // x ≠ c}) ∉ D :=
              not_clone_mem c D hyClone
            have hcl :=
              margin_eq_clone_left (P := P) (c := c) (D := D) (a := x) (ha := hxEq)
                (haD := hxD) (b := ⟨y, replaceClonesHelper c D hyClone⟩)
                (hb := hyNot) (clone := clone)
            have hcl' :
                margin P x y =
                  margin P d (⟨y, replaceClonesHelper c D hyClone⟩ : {x : A // x ≠ c}) := by
              have hcd :=
                margin_eq_clone_left (P := P) (c := c) (D := D) (a := d.1) (ha := d.2)
                  (haD := by simpa using hd) (b := ⟨y, replaceClonesHelper c D hyClone⟩)
                  (hb := hyNot) (clone := clone)
              simpa using (hcl.trans hcd.symm)
            simpa [hfx, hfy] using hcl'
        · have hfx : f x = ⟨x, replaceClonesHelper c D hxClone⟩ := by
            simp [f, hxClone]
          by_cases hyClone : ∀ p : y ≠ c, (⟨y, p⟩ : {x : A // x ≠ c}) ∈ D
          · have hfy : f y = d := by simp [f, hyClone]
            by_cases hyEq : y = c
            · simp [hyEq]
              have hxNot :
                  (⟨x, replaceClonesHelper c D hxClone⟩ : {x : A // x ≠ c}) ∉ D :=
                not_clone_mem c D hxClone
              have hcd :=
                margin_eq_clone_right (P := P) (c := c) (D := D)
                  (a := ⟨x, replaceClonesHelper c D hxClone⟩) (ha := hxNot)
                  (e := d) (he := hd) (clone := clone)
              have hfc : f c = d := by
                simpa [hyEq] using hfy
              simpa [hfx, hfc] using hcd.symm
            · have hxNot :
                (⟨x, replaceClonesHelper c D hxClone⟩ : {x : A // x ≠ c}) ∉ D :=
                not_clone_mem c D hxClone
              have hyD :
                (⟨y, hyEq⟩ : {x : A // x ≠ c}) ∈ D :=
                (clone_mem_iff (c := c) (D := D) (a := y) hyEq).1 hyClone
              have hcl :=
                margin_eq_clone_right (P := P) (c := c) (D := D)
                  (a := ⟨x, replaceClonesHelper c D hxClone⟩) (ha := hxNot)
                  (e := ⟨y, hyEq⟩) (he := hyD) (clone := clone)
              have hcl' :
                  margin P x y =
                    margin P (⟨x, replaceClonesHelper c D hxClone⟩ : {x : A // x ≠ c}) d := by
                have hcd :=
                  margin_eq_clone_right (P := P) (c := c) (D := D)
                    (a := ⟨x, replaceClonesHelper c D hxClone⟩) (ha := hxNot)
                    (e := d) (he := hd) (clone := clone)
                simpa using (hcl.trans hcd.symm)
              simpa [hfx, hfy] using hcl'
          · have hfy : f y = ⟨y, replaceClonesHelper c D hyClone⟩ := by
              simp [f, hyClone]
            have hxy3 :
                margin P x y =
                  margin P (⟨x, replaceClonesHelper c D hxClone⟩ : {x : A // x ≠ c})
                    (⟨y, replaceClonesHelper c D hyClone⟩ : {x : A // x ≠ c}) :=
              rfl
            simp [hfx, hfy, hxy3]
      exact Or.inr (by simpa [hxy''] using hxy')
  have hchain_map :
      List.IsChain
          (fun a b_1 : {x : A // x ≠ c} =>
            a = b_1 ∨ margin P d b ≤ margin P a b_1) (l.map f) := by
    exact (List.isChain_map
      (R := fun a b_1 : {x : A // x ≠ c} =>
        a = b_1 ∨ margin P d b ≤ margin P a b_1)
      (f := f) (l := l)).2 hchain'
  have hchain_path :
      List.IsChain
          (fun a b_1 : {x : A // x ≠ c} =>
            a = b_1 ∨ margin P d b ≤ margin P a b_1)
          (replaceClones c D d hd l) := by
    have hpath :=
      to_path_chain'_of_chain'
        (P := fun a b_1 : {x : A // x ≠ c} =>
          a = b_1 ∨ margin P d b ≤ margin P a b_1)
        (l := l.map f) hchain_map
    simpa [replaceClones, f] using hpath
  exact chain_of_chain_eq_or
    (R := fun a b_1 : {x : A // x ≠ c} => margin P d b ≤ margin P a b_1)
    hchain_path (replaceClones_nodup c D d hd l)

lemma removeClones'_cycle1 (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c})
    {l : List {x : A // x ≠ c}} {a' : {x : A // x ≠ c}} (ha : a' ∉ D)
    {d : {x : A // x ≠ c}} (hd : d ∈ D) (clone : clones P c D) :
    List.IsChain (fun a b : {x : A // x ≠ c} =>
      margin (minusCandidate P c) a' d ≤ margin (minusCandidate P c) a b) l →
      List.IsChain (fun a b : A => margin P a' c ≤ margin P a b) (removeClones' c D l) := by
  classical
  intro hchain
  set f : {x : A // x ≠ c} → A := fun x => if x ∈ D then c else (x : A)
  have hchain' :
      List.IsChain
          (fun a b =>
            f a = f b ∨ margin P a' c ≤ margin P (f a) (f b)) l := by
    refine hchain.imp ?_
    intro x y hxy
    by_cases hEq : f x = f y
    · exact Or.inl hEq
    · have hleft : margin P a' c = margin (minusCandidate P c) a' d := by
        have h :=
          margin_eq_clone_non_clone' (P := P) (c := c) (D := D)
            (H := hd) (Hb := ha) (b := a') clone
        simpa using h
      have hxy0 : margin P a' c ≤ margin (minusCandidate P c) x y := by
        simpa [hleft] using hxy
      have hxy1 : margin (minusCandidate P c) x y = margin P (f x) (f y) := by
        by_cases hxClone : x ∈ D
        · have hfx : f x = c := by simp [f, hxClone]
          have hyClone : y ∉ D := by
            intro hy
            have : f y = c := by simp [f, hy]
            exact hEq (by simpa [hfx] using this.symm)
          have hfy : f y = (y : A) := by simp [f, hyClone]
          have hcl :=
            margin_eq_clone_non_clone (P := P) (c := c) (D := D)
              (b := y) (e := x) (H := hxClone) (Hb := hyClone) clone
          simpa [hfx, hfy] using hcl.symm
        · have hfx : f x = (x : A) := by simp [f, hxClone]
          by_cases hyClone : y ∈ D
          · have hfy : f y = c := by simp [f, hyClone]
            have hcl :=
              margin_eq_clone_non_clone' (P := P) (c := c) (D := D)
                (H := hyClone) (Hb := hxClone) (b := x) clone
            simpa [hfx, hfy] using hcl.symm
          · have hfy : f y = (y : A) := by simp [f, hyClone]
            have hcl :=
              margin_eq_margin_minusCandidate (P := P) (c := c) (a := x) (b := y)
            simpa [hfx, hfy] using hcl.symm
      exact Or.inr (hxy1 ▸ hxy0)
  have hchain_map :
      List.IsChain
          (fun a b => a = b ∨ margin P a' c ≤ margin P a b) (l.map f) := by
    exact (List.isChain_map
      (R := fun a b => a = b ∨ margin P a' c ≤ margin P a b)
      (f := f) (l := l)).2 hchain'
  have hchain_path :
      List.IsChain
          (fun a b => a = b ∨ margin P a' c ≤ margin P a b)
          (removeClones' c D l) := by
    have hpath :=
      to_path_chain'_of_chain'
        (P := fun a b => a = b ∨ margin P a' c ≤ margin P a b)
        (l := l.map f) hchain_map
    simpa [removeClones', f] using hpath
  exact chain_of_chain_eq_or (R := fun a b : A => margin P a' c ≤ margin P a b)
    hchain_path (removeClones'_nodup c D l)

lemma removeClones'_cycle2 (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c})
    {l : List A} {a' : {x : A // x ≠ c}} (ha : a' ∉ D)
    {d : {x : A // x ≠ c}} (hd : d ∈ D) (clone : clones P c D) :
    List.IsChain (fun a b : A => margin P a' c ≤ margin P a b) l →
      List.IsChain (fun a b : {x : A // x ≠ c} =>
        margin (minusCandidate P c) a' d ≤ margin (minusCandidate P c) a b)
        (replaceClones c D d hd l) := by
  classical
  intro hchain
  set f : A → {x : A // x ≠ c} := fun x =>
    dite (∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D)
      (fun _ => d)
      (fun h => ⟨x, replaceClonesHelper c D h⟩)
  have hchain' :
      List.IsChain
          (fun a b_1 =>
            f a = f b_1 ∨
              margin (minusCandidate P c) a' d ≤ margin (minusCandidate P c) (f a) (f b_1)) l := by
    refine hchain.imp ?_
    intro x y hxy
    by_cases hEq : f x = f y
    · exact Or.inl hEq
    · have hleft : margin (minusCandidate P c) a' d = margin P a' c := by
        have h :=
          margin_eq_clone_non_clone' (P := P) (c := c) (D := D)
            (H := hd) (Hb := ha) (b := a') clone
        simpa using h.symm
      have hxy0 : margin (minusCandidate P c) a' d ≤ margin P x y := by
        simpa [hleft] using hxy
      have hxy1 : margin P x y = margin (minusCandidate P c) (f x) (f y) := by
        by_cases hxClone : ∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D
        · have hfx : f x = d := by simp [f, hxClone]
          have hyClone : ¬∀ p : y ≠ c, (⟨y, p⟩ : {x : A // x ≠ c}) ∈ D := by
            intro hy
            have : f y = d := by simp [f, hy]
            exact hEq (by simpa [hfx] using this.symm)
          have hfy : f y = ⟨y, replaceClonesHelper c D hyClone⟩ := by
            simp [f, hyClone]
          by_cases hxEq : x = c
          · simp [hxEq]
            have hyNot :
                (⟨y, replaceClonesHelper c D hyClone⟩ : {x : A // x ≠ c}) ∉ D :=
              not_clone_mem c D hyClone
            have hcd :=
              margin_eq_clone_non_clone (P := P) (c := c) (D := D)
                (b := ⟨y, replaceClonesHelper c D hyClone⟩) (e := d)
                (H := hd) (Hb := hyNot) clone
            have hfc : f c = d := by
              simpa [hxEq] using hfx
            simpa [hfc, hfy] using hcd
          · have hxD :
              (⟨x, hxEq⟩ : {x : A // x ≠ c}) ∈ D :=
              (clone_mem_iff (c := c) (D := D) (a := x) hxEq).1 hxClone
            have hyNot :
              (⟨y, replaceClonesHelper c D hyClone⟩ : {x : A // x ≠ c}) ∉ D :=
              not_clone_mem c D hyClone
            have hcl :=
              margin_eq_clone_left (P := P) (c := c) (D := D) (a := x) (ha := hxEq)
                (haD := hxD) (b := ⟨y, replaceClonesHelper c D hyClone⟩)
                (hb := hyNot) (clone := clone)
            have hcl' :
                margin P x y =
                  margin (minusCandidate P c) d
                    (⟨y, replaceClonesHelper c D hyClone⟩ : {x : A // x ≠ c}) := by
              have hcd :=
                margin_eq_clone_non_clone (P := P) (c := c) (D := D)
                  (b := ⟨y, replaceClonesHelper c D hyClone⟩) (e := d)
                  (H := hd) (Hb := hyNot) clone
              simpa using (hcl.trans hcd)
            simpa [hfx, hfy] using hcl'
        · have hfx : f x = ⟨x, replaceClonesHelper c D hxClone⟩ := by
            simp [f, hxClone]
          by_cases hyClone : ∀ p : y ≠ c, (⟨y, p⟩ : {x : A // x ≠ c}) ∈ D
          · have hfy : f y = d := by simp [f, hyClone]
            by_cases hyEq : y = c
            · simp [hyEq]
              have hxNot :
                  (⟨x, replaceClonesHelper c D hxClone⟩ : {x : A // x ≠ c}) ∉ D :=
                not_clone_mem c D hxClone
              have hcd :=
                margin_eq_clone_non_clone' (P := P) (c := c) (D := D)
                  (H := hd) (Hb := hxNot) (b := ⟨x, replaceClonesHelper c D hxClone⟩) clone
              have hfc : f c = d := by
                simpa [hyEq] using hfy
              simpa [hfx, hfc] using hcd
            · have hxNot :
                (⟨x, replaceClonesHelper c D hxClone⟩ : {x : A // x ≠ c}) ∉ D :=
                not_clone_mem c D hxClone
              have hyD :
                (⟨y, hyEq⟩ : {x : A // x ≠ c}) ∈ D :=
                (clone_mem_iff (c := c) (D := D) (a := y) hyEq).1 hyClone
              have hcl :=
                margin_eq_clone_right (P := P) (c := c) (D := D)
                  (a := ⟨x, replaceClonesHelper c D hxClone⟩) (ha := hxNot)
                  (e := ⟨y, hyEq⟩) (he := hyD) (clone := clone)
              have hcl' :
                  margin P x y =
                    margin (minusCandidate P c)
                      (⟨x, replaceClonesHelper c D hxClone⟩ : {x : A // x ≠ c}) d := by
                have hcd :=
                  margin_eq_clone_non_clone' (P := P) (c := c) (D := D)
                    (H := hd) (Hb := hxNot) (b := ⟨x, replaceClonesHelper c D hxClone⟩) clone
                simpa using (hcl.trans hcd)
              simpa [hfx, hfy] using hcl'
          · have hfy : f y = ⟨y, replaceClonesHelper c D hyClone⟩ := by
              simp [f, hyClone]
            have hxy3 :
                margin P x y =
                  margin (minusCandidate P c)
                    ⟨x, replaceClonesHelper c D hxClone⟩
                    ⟨y, replaceClonesHelper c D hyClone⟩ := by
              simpa using (margin_eq_margin_minusCandidate
                (P := P) (c := c)
                (a := ⟨x, replaceClonesHelper c D hxClone⟩)
                (b := ⟨y, replaceClonesHelper c D hyClone⟩))
            simpa [hfx, hfy] using hxy3
      exact Or.inr (hxy1 ▸ hxy0)
  have hchain_map :
      List.IsChain
          (fun a b_1 : {x : A // x ≠ c} =>
            a = b_1 ∨
              margin (minusCandidate P c) a' d ≤ margin (minusCandidate P c) a b_1)
          (l.map f) := by
    exact (List.isChain_map
      (R := fun a b_1 : {x : A // x ≠ c} =>
        a = b_1 ∨ margin (minusCandidate P c) a' d ≤ margin (minusCandidate P c) a b_1)
      (f := f) (l := l)).2 hchain'
  have hchain_path :
      List.IsChain
          (fun a b_1 : {x : A // x ≠ c} =>
            a = b_1 ∨
              margin (minusCandidate P c) a' d ≤ margin (minusCandidate P c) a b_1)
          (replaceClones c D d hd l) := by
    have hpath :=
      to_path_chain'_of_chain'
        (P := fun a b_1 : {x : A // x ≠ c} =>
          a = b_1 ∨ margin (minusCandidate P c) a' d ≤ margin (minusCandidate P c) a b_1)
        (l := l.map f) hchain_map
    simpa [replaceClones, f] using hpath
  exact chain_of_chain_eq_or
    (R := fun a b : {x : A // x ≠ c} =>
      margin (minusCandidate P c) a' d ≤ margin (minusCandidate P c) a b)
    hchain_path (replaceClones_nodup c D d hd l)

end ChainTransport

section DefeatEquivalence

variable {V A : Type} [Fintype V] [Fintype A]

def splitCycleDefeatsPath {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x y : A) : Prop :=
  margin_pos P x y ∧
    ¬ ∃ l : List A, ∃ h : l ≠ [],
      l.Nodup ∧
        l[0]'(List.length_pos_of_ne_nil h) = y ∧
          l.getLast h = x ∧
            List.IsChain (fun a b => margin P x y ≤ margin P a b) l

lemma cycle_of_path {X : Type} {R : X → X → Prop} {l : List X}
    {x y : X} (hne : l ≠ [])
    (hfirst : l[0]'(List.length_pos_of_ne_nil hne) = y)
    (hlast : l.getLast hne = x)
    (hchain : List.IsChain R l) (hrel : R x y) : cycle R l := by
  have hhead : l.head hne = y := by
    simpa [List.head_eq_getElem_zero] using hfirst
  have hrel' : R x (l.head hne) := by
    simpa [hhead] using hrel
  have hchain' : List.IsChain R (x :: l) :=
    List.IsChain.cons_of_ne_nil hne hchain hrel'
  refine ⟨hne, ?_⟩
  simpa [hlast] using hchain'

lemma path_of_cycle {X : Type} [DecidableEq X] {R : X → X → Prop}
    {c : List X} {x y : X} (hcycle : cycle R c) (hx : x ∈ c) (hy : y ∈ c) :
    ∃ l : List X, ∃ h : l ≠ [],
      l.Nodup ∧
        l[0]'(List.length_pos_of_ne_nil h) = y ∧
          l.getLast h = x ∧
            List.IsChain R l := by
  classical
  set crot : List X := c.rotate (List.idxOf y c)
  have hcycle_rot : cycle R crot := by
    have hrot := rotate'_cycle_of_cycle (c := c) (n := List.idxOf y c) hcycle
    simpa [crot, List.rotate_eq_rotate'] using hrot
  rcases hcycle_rot with ⟨hcrot_ne, hchain_rot⟩
  have hxcrot : x ∈ crot := by
    have hmem := (List.mem_rotate (l := c) (a := x) (n := List.idxOf y c))
    exact hmem.mpr hx
  have hidx_x : List.idxOf x crot < crot.length := List.idxOf_lt_length_iff.2 hxcrot
  set l3 : List X := crot.take (List.idxOf x crot + 1)
  have hchain_l3 : List.IsChain R l3 := by
    have hchain_take :=
      chain'_take_of_chain (l := crot) (a := hcrot_ne)
        (n := List.idxOf x crot + 1) hchain_rot
    simpa [l3] using hchain_take
  have hne_l3 : l3 ≠ [] := by
    have hle : List.idxOf x crot + 1 ≤ crot.length := Nat.succ_le_of_lt hidx_x
    have hlen :
        l3.length = List.idxOf x crot + 1 := by
      simpa [l3] using
        (List.length_take_of_le (l := crot) (i := List.idxOf x crot + 1) hle)
    have hpos : 0 < l3.length :=
      hlen.symm ▸ Nat.succ_pos (List.idxOf x crot)
    exact List.length_pos_iff_ne_nil.mp hpos
  set l : List X := to_path l3
  have hne_l : l ≠ [] := by
    simpa [l] using (to_path_ne_nil_iff l3 hne_l3)
  have hchain_l : List.IsChain R l := by
    simpa [l] using (to_path_chain'_of_chain' (l := l3) hchain_l3)
  have hnodup_l : l.Nodup := by
    simpa [l] using (to_path_nodup l3)
  have hhead_crot : crot.head hcrot_ne = y := by
    have h0c : 0 < crot.length := List.length_pos_of_ne_nil hcrot_ne
    have hidx_y : List.idxOf y c < c.length := List.idxOf_lt_length_iff.2 hy
    have hget0 :
        crot[0]'h0c = y := by
      have hget0' := List.getElem_rotate (l := c) (n := List.idxOf y c) (k := 0)
        (h := by
          simpa [crot, List.length_rotate] using (List.length_pos_of_mem hy))
      simpa [crot, Nat.zero_add, Nat.mod_eq_of_lt hidx_y] using hget0'
    calc
      crot.head hcrot_ne = crot[0]'h0c := List.head_eq_getElem_zero (l := crot) hcrot_ne
      _ = y := hget0
  have hhead_l3 : l3.head hne_l3 = y := by
    have hhead_take :=
      List.head_take (l := crot) (i := List.idxOf x crot + 1) (h := hne_l3)
    simpa [l3, hhead_crot] using hhead_take
  have h0_l3 : 0 < l3.length := List.length_pos_of_ne_nil hne_l3
  have hfirst_l3 : l3[0]'h0_l3 = y := by
    calc
      l3[0]'h0_l3 = l3.head hne_l3 := by
        symm
        exact List.head_eq_getElem_zero (l := l3) hne_l3
      _ = y := hhead_l3
  have hlast_l3 : l3.getLast hne_l3 = x := by
    have hlast :=
      getLast_take_idxOf (l := crot) (a := x) hxcrot
    simpa [l3] using hlast
  have h0_l : 0 < l.length := by
    simpa [l] using (to_path_length_pos l3 hne_l3)
  have hfirst_l :
      l[0]'h0_l = y := by
    have hfirst :=
      to_path_first_elem (l := l3) (h := hne_l3)
    have hfirst' :
        l[0]'h0_l = l3[0]'(List.length_pos_of_ne_nil hne_l3) := by
      simpa [l] using hfirst
    exact hfirst'.trans hfirst_l3
  have hlast_l : l.getLast hne_l = x := by
    have hlast :=
      to_path_last_elem (l := l3) (h := hne_l3)
    have hlast' : l.getLast hne_l = l3.getLast hne_l3 := by
      simpa [l] using hlast
    exact hlast'.trans hlast_l3
  exact ⟨l, hne_l, hnodup_l, hfirst_l, hlast_l, hchain_l⟩

lemma splitCycleDefeats_iff_path {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x y : A) :
    splitCycleDefeats P x y ↔ splitCycleDefeatsPath P x y := by
  classical
  constructor
  · intro hdef
    rcases hdef with ⟨hpos, hnocycle⟩
    refine ⟨hpos, ?_⟩
    intro hex
    rcases hex with ⟨l, hne, hnodup, hfirst, hlast, hchain⟩
    have hy : y ∈ l := by
      have hy' : l[0]'(List.length_pos_of_ne_nil hne) = y := hfirst
      exact List.mem_of_getElem (l := l) (i := 0) (a := y) (by simpa using hy')
    have hx : x ∈ l := by
      have hx' : l.getLast hne ∈ l := List.getLast_mem hne
      simpa [hlast] using hx'
    have hcycle : cycle (fun a b => margin P x y ≤ margin P a b) l := by
      have hrel : margin P x y ≤ margin P x y := le_rfl
      exact cycle_of_path (hne := hne) (hfirst := hfirst) (hlast := hlast)
        (hchain := hchain) hrel
    exact hnocycle ⟨l, hx, hy, hcycle⟩
  · intro hdef
    rcases hdef with ⟨hpos, hnoPath⟩
    refine ⟨hpos, ?_⟩
    intro hcycle
    rcases hcycle with ⟨c, hx, hy, hcycle⟩
    rcases path_of_cycle (hcycle := hcycle) (hx := hx) (hy := hy) with
      ⟨l, hne, hnodup, hfirst, hlast, hchain⟩
    exact hnoPath ⟨l, hne, hnodup, hfirst, hlast, hchain⟩

end DefeatEquivalence

section CloneDefeats

variable {V A : Type} [Fintype V] [Fintype A]

lemma clone_maintains_defeat (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c})
    (a b : {x : A // x ≠ c}) (Hb : b ∉ D) :
    clones P c D →
      (splitCycleDefeats (minusCandidate P c) a b ↔ splitCycleDefeats P a b) := by
  classical
  intro clone
  constructor
  · intro hdef
    rcases (splitCycleDefeats_iff_path (P := minusCandidate P c) (x := a) (y := b)).1 hdef with
      ⟨hpos, hno⟩
    refine (splitCycleDefeats_iff_path (P := P) (x := a) (y := b)).2 ?_
    refine ⟨?_, ?_⟩
    · change 0 < margin P (a : A) (b : A)
      rw [margin_eq_margin_minusCandidate (P := P) (c := c) (a := a) (b := b)]
      exact hpos
    · intro hex
      rcases hex with ⟨l, hne, hnodup, hfirst, hlast, hchain⟩
      have hDne : D.Nonempty := clone.1
      rcases hDne with ⟨d0, hd0⟩
      let d : {x : A // x ≠ c} := if a ∈ D then a else d0
      have hd : d ∈ D := by
        by_cases ha : a ∈ D
        · simp [d, ha]
        · simp [d, ha, hd0]
      have b_not : ¬∀ p : (b : A) ≠ c, (⟨(b : A), p⟩ : {x : A // x ≠ c}) ∈ D := by
        intro hall
        have hb' : (⟨(b : A), b.property⟩ : {x : A // x ≠ c}) ∈ D :=
          (clone_mem_iff (c := c) (D := D) (a := (b : A)) (ha := b.property)).1 hall
        exact Hb (by simpa using hb')
      have hne' : replaceClones c D d hd l ≠ [] :=
        (replaceClones_ne_nil_iff c D d hd l).1 hne
      have hnodup' : (replaceClones c D d hd l).Nodup :=
        replaceClones_nodup c D d hd l
      have hfirst' :
          (replaceClones c D d hd l)[0]'(List.length_pos_of_ne_nil hne') = b := by
        have hfirst'' :=
          replaceClones_first_elem (c := c) (D := D) (d := d) (hd := hd)
            (l := l) (a := b) (hnot := b_not) (hne := hne) hfirst
        have hb' : (⟨b, replaceClonesHelper c D b_not⟩ : {x : A // x ≠ c}) = b := by
          ext
          rfl
        simp [hb', hfirst'']
      have hlast' :
          (replaceClones c D d hd l).getLast hne' = a := by
        by_cases ha : a ∈ D
        · have hd' : d = a := by simp [d, ha]
          set f : A → {x : A // x ≠ c} := fun x =>
            dite (∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D)
              (fun _ => d)
              (fun h => ⟨x, replaceClonesHelper c D h⟩)
          have hmap_ne : l.map f ≠ [] := by
            intro hmap
            exact hne (List.map_eq_nil_iff.mp hmap)
          have hlast_map :
              (l.map f).getLast hmap_ne = f (l.getLast hne) :=
            List.getLast_map (f := f) (l := l) (h := hmap_ne)
          have hlast_path :
              (replaceClones c D d hd l).getLast hne' = f (l.getLast hne) := by
            have hlast :=
              to_path_last_elem (l := l.map f) (h := hmap_ne)
            simpa [replaceClones, f] using hlast
          have hfa : f a = d := by
            have hall :
                ∀ p : (a : A) ≠ c, (⟨(a : A), p⟩ : {x : A // x ≠ c}) ∈ D :=
              (clone_mem_iff (c := c) (D := D) (a := (a : A)) (ha := a.property)).2 ha
            simp [f, hall]
          have hlast_a : l.getLast hne = (a : A) := hlast
          simpa [hlast_a, hfa, hd'] using hlast_path
        · have hnota : ¬∀ p : (a : A) ≠ c, (⟨(a : A), p⟩ : {x : A // x ≠ c}) ∈ D := by
            intro hall
            have ha' : (⟨(a : A), a.property⟩ : {x : A // x ≠ c}) ∈ D :=
              (clone_mem_iff (c := c) (D := D) (a := (a : A)) (ha := a.property)).1 hall
            exact ha (by simpa using ha')
          have hlast'' :=
            replaceClones_last_elem (c := c) (D := D) (d := d) (hd := hd)
              (l := l) (a := a) (hnot := hnota) (hne := hne) hlast
          have ha' : (⟨a, replaceClonesHelper c D hnota⟩ : {x : A // x ≠ c}) = a := by
            ext
            rfl
          simpa [ha'] using hlast''
      have hchain' :
          List.IsChain (fun a_1 b_1 : {x : A // x ≠ c} =>
            margin (minusCandidate P c) a b ≤ margin (minusCandidate P c) a_1 b_1)
            (replaceClones c D d hd l) := by
        simpa using
          (A6_chain (P := P) (c := c) (D := D) (l := l)
            (b := a) (d := d) (d' := b) (hd := hd) (clone := clone) hchain)
      exact hno ⟨replaceClones c D d hd l, hne', hnodup', hfirst', hlast', hchain'⟩
  · intro hdef
    rcases (splitCycleDefeats_iff_path (P := P) (x := a) (y := b)).1 hdef with
      ⟨hpos, hno⟩
    refine (splitCycleDefeats_iff_path (P := minusCandidate P c) (x := a) (y := b)).2 ?_
    refine ⟨?_, ?_⟩
    · change 0 < margin (minusCandidate P c) a b
      rw [← margin_eq_margin_minusCandidate (P := P) (c := c) (a := a) (b := b)]
      exact hpos
    · intro hex
      rcases hex with ⟨l, hne, hnodup, hfirst, hlast, hchain⟩
      let l' : List A := l.map Subtype.val
      have hne' : l' ≠ [] := by
        intro hnil
        exact hne (List.map_eq_nil_iff.mp hnil)
      have hnodup' : l'.Nodup := by
        refine hnodup.map ?_
        intro x y hxy
        exact Subtype.ext (by simpa using hxy)
      have hfirst' : l'[0]'(List.length_pos_of_ne_nil hne') = (b : A) := by
        simpa [l', List.getElem_map] using congrArg Subtype.val hfirst
      have hlast' : l'.getLast hne' = (a : A) := by
        simpa [l', hlast] using (List.getLast_map (f := Subtype.val) (l := l) (h := hne'))
      have hchain' : List.IsChain (fun a_1 b_1 : A => margin P a b ≤ margin P a_1 b_1) l' := by
        refine (List.isChain_iff_getElem (R := fun a_1 b_1 : A => margin P a b ≤ margin P a_1 b_1)
          (l := l')).2 ?_
        intro i hi
        have hchain'' :=
          (List.isChain_iff_getElem (R := fun a_1 b_1 : {x : A // x ≠ c} =>
            margin (minusCandidate P c) a b ≤ margin (minusCandidate P c) a_1 b_1)
            (l := l)).1 hchain
        have hi_l : i + 1 < l.length := by
          simpa [l', List.length_map] using hi
        have hi_l0 : i < l.length :=
          Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_of_lt hi_l)
        have hrel := hchain'' i hi_l
        have hrel' :
            margin P a b ≤ margin P (l[i]'hi_l0) (l[i + 1]'hi_l) := by
          simpa [margin_eq_margin_minusCandidate (P := P) (c := c)] using hrel
        simpa [l', List.getElem_map] using hrel'
      exact hno ⟨l', hne', hnodup', hfirst', hlast', hchain'⟩

lemma clone_maintains_defeat' (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c})
    (a b : {x : A // x ≠ c}) (Ha : a ∉ D) (Hb : b ∈ D) :
    clones P c D →
      (splitCycleDefeats (minusCandidate P c) a b ↔ splitCycleDefeats P a b) := by
  classical
  intro clone
  constructor
  · intro hdef
    rcases (splitCycleDefeats_iff_path (P := minusCandidate P c) (x := a) (y := b)).1 hdef with
      ⟨hpos, hno⟩
    refine (splitCycleDefeats_iff_path (P := P) (x := a) (y := b)).2 ?_
    refine ⟨?_, ?_⟩
    · change 0 < margin P (a : A) (b : A)
      rw [margin_eq_margin_minusCandidate (P := P) (c := c) (a := a) (b := b)]
      exact hpos
    · intro hex
      rcases hex with ⟨l, hne, hnodup, hfirst, hlast, hchain⟩
      have hne' : replaceClones c D b Hb l ≠ [] :=
        (replaceClones_ne_nil_iff c D b Hb l).1 hne
      have hnodup' : (replaceClones c D b Hb l).Nodup :=
        replaceClones_nodup c D b Hb l
      have hfirst' :
          (replaceClones c D b Hb l)[0]'(List.length_pos_of_ne_nil hne') = b := by
        set f : A → {x : A // x ≠ c} := fun x =>
          dite (∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D)
            (fun _ => b)
            (fun h => ⟨x, replaceClonesHelper c D h⟩)
        have hmap_ne : l.map f ≠ [] := by
          intro hmap
          exact hne (List.map_eq_nil_iff.mp hmap)
        have hfirst_path :=
          to_path_first_elem (l := l.map f) (h := hmap_ne)
        have hfirst' :
            (replaceClones c D b Hb l)[0]'(List.length_pos_of_ne_nil hne') =
              (l.map f)[0]'(List.length_pos_of_ne_nil hmap_ne) :=
          hfirst_path
        have hmap0 :
            (l.map f)[0]'(List.length_pos_of_ne_nil hmap_ne) =
              f (l[0]'(List.length_pos_of_ne_nil hne)) :=
          List.getElem_map (f := f) (l := l) (i := 0)
            (h := List.length_pos_of_ne_nil hmap_ne)
        have hall :
            ∀ p : (b : A) ≠ c, (⟨(b : A), p⟩ : {x : A // x ≠ c}) ∈ D :=
          (clone_mem_iff (c := c) (D := D) (a := (b : A)) (ha := b.property)).2 Hb
        have hfb : f b = b := by
          simp [f, hall]
        calc
          (replaceClones c D b Hb l)[0]'(List.length_pos_of_ne_nil hne') =
              (l.map f)[0]'(List.length_pos_of_ne_nil hmap_ne) := hfirst'
          _ = f (l[0]'(List.length_pos_of_ne_nil hne)) := hmap0
          _ = f b := by simp [hfirst]
          _ = b := hfb
      have hnota :
          ¬∀ p : (a : A) ≠ c, (⟨(a : A), p⟩ : {x : A // x ≠ c}) ∈ D := by
        intro hall
        have ha' : (⟨(a : A), a.property⟩ : {x : A // x ≠ c}) ∈ D :=
          (clone_mem_iff (c := c) (D := D) (a := (a : A)) (ha := a.property)).1 hall
        exact Ha (by simpa using ha')
      have hlast'' :=
        replaceClones_last_elem (c := c) (D := D) (d := b) (hd := Hb)
          (l := l) (a := a) (hnot := hnota) (hne := hne) hlast
      have ha' : (⟨a, replaceClonesHelper c D hnota⟩ : {x : A // x ≠ c}) = a := by
        ext
        rfl
      have hlast' : (replaceClones c D b Hb l).getLast hne' = a := by
        simpa [ha'] using hlast''
      have hchain' :
          List.IsChain (fun a_1 b_1 : {x : A // x ≠ c} =>
            margin (minusCandidate P c) a b ≤ margin (minusCandidate P c) a_1 b_1)
            (replaceClones c D b Hb l) := by
        simpa using
          (A6_chain (P := P) (c := c) (D := D) (l := l)
            (b := a) (d := b) (d' := b) (hd := Hb) (clone := clone) hchain)
      exact hno ⟨replaceClones c D b Hb l, hne', hnodup', hfirst', hlast', hchain'⟩
  · intro hdef
    rcases (splitCycleDefeats_iff_path (P := P) (x := a) (y := b)).1 hdef with
      ⟨hpos, hno⟩
    refine (splitCycleDefeats_iff_path (P := minusCandidate P c) (x := a) (y := b)).2 ?_
    refine ⟨?_, ?_⟩
    · change 0 < margin (minusCandidate P c) a b
      rw [← margin_eq_margin_minusCandidate (P := P) (c := c) (a := a) (b := b)]
      exact hpos
    · intro hex
      rcases hex with ⟨l, hne, hnodup, hfirst, hlast, hchain⟩
      let l' : List A := l.map Subtype.val
      have hne' : l' ≠ [] := by
        intro hnil
        exact hne (List.map_eq_nil_iff.mp hnil)
      have hnodup' : l'.Nodup := by
        refine hnodup.map ?_
        intro x y hxy
        exact Subtype.ext (by simpa using hxy)
      have hfirst' : l'[0]'(List.length_pos_of_ne_nil hne') = (b : A) := by
        simpa [l', List.getElem_map] using congrArg Subtype.val hfirst
      have hlast' : l'.getLast hne' = (a : A) := by
        simpa [l', hlast] using (List.getLast_map (f := Subtype.val) (l := l) (h := hne'))
      have hchain' : List.IsChain (fun a_1 b_1 : A => margin P a b ≤ margin P a_1 b_1) l' := by
        refine (List.isChain_iff_getElem (R := fun a_1 b_1 : A => margin P a b ≤ margin P a_1 b_1)
          (l := l')).2 ?_
        intro i hi
        have hchain'' :=
          (List.isChain_iff_getElem (R := fun a_1 b_1 : {x : A // x ≠ c} =>
            margin (minusCandidate P c) a b ≤ margin (minusCandidate P c) a_1 b_1)
            (l := l)).1 hchain
        have hi_l : i + 1 < l.length := by
          simpa [l', List.length_map] using hi
        have hi_l0 : i < l.length :=
          Nat.lt_of_lt_of_le (Nat.lt_succ_self i) (Nat.le_of_lt hi_l)
        have hrel := hchain'' i hi_l
        have hrel' :
            margin P a b ≤ margin P (l[i]'hi_l0) (l[i + 1]'hi_l) := by
          simpa [margin_eq_margin_minusCandidate (P := P) (c := c)] using hrel
        simpa [l', List.getElem_map] using hrel'
      exact hno ⟨l', hne', hnodup', hfirst', hlast', hchain'⟩

lemma every_clone_defeats (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c})
    (b : {x : A // x ≠ c}) (Hb : b ∉ D) (d : {x : A // x ≠ c}) (Hd : d ∈ D) :
    clones P c D →
      (splitCycleDefeats P c b ↔ splitCycleDefeats P d b) := by
  classical
  intro clone
  constructor
  · intro hdef
    rcases (splitCycleDefeats_iff_path (P := P) (x := c) (y := b)).1 hdef with
      ⟨hpos, hno⟩
    refine (splitCycleDefeats_iff_path (P := P) (x := d) (y := b)).2 ?_
    refine ⟨?_, ?_⟩
    · have hdb : margin P d b = margin P c b := by
        have h :=
          margin_eq_clone_left (P := P) (c := c) (D := D) (a := d.1) (ha := d.2)
            (haD := by simpa using Hd) (b := b) (hb := Hb) (clone := clone)
        simpa using h
      simpa [margin_pos, hdb] using hpos
    · intro hex
      rcases hex with ⟨l, hne, hnodup, hfirst, hlast, hchain⟩
      have hne' : removeClones c D l ≠ [] :=
        (removeClones_ne_nil_iff c D l).1 hne
      have hnodup' : (removeClones c D l).Nodup :=
        removeClones_nodup c D l
      have hbnot :
          ∀ p : (b : A) ≠ c, (⟨(b : A), p⟩ : {x : A // x ≠ c}) ∉ D := by
        intro p hb'
        have hb'' : (⟨(b : A), p⟩ : {x : A // x ≠ c}) = b := by
          ext
          rfl
        exact Hb (by simpa [hb''] using hb')
      have hfirst' :
          (removeClones c D l)[0]'(List.length_pos_of_ne_nil hne') = (b : A) := by
        have hfirst'' :=
          removeClones_first_elem (c := c) (D := D) (l := l) (a := b)
            (hnot := hbnot) (hne := hne) hfirst
        simpa using hfirst''
      have hlast' :
          (removeClones c D l).getLast hne' = c := by
        simpa using
          (removeClones_last_c (c := c) (D := D) (l := l) (d := d)
            (hd := Hd) (hne := hne) hlast)
      have hchain' :
          List.IsChain (fun a_1 b_1 : A => margin P c b ≤ margin P a_1 b_1)
            (removeClones c D l) := by
        simpa using
          (removeClones_chain_of_chain (P := P) (c := c) (D := D) (l := l)
            (b := b) (d := d) (hb := Hb) (hd := Hd) (clone := clone) hchain)
      exact hno ⟨removeClones c D l, hne', hnodup', hfirst', hlast', hchain'⟩
  · intro hdef
    rcases (splitCycleDefeats_iff_path (P := P) (x := d) (y := b)).1 hdef with
      ⟨hpos, hno⟩
    refine (splitCycleDefeats_iff_path (P := P) (x := c) (y := b)).2 ?_
    refine ⟨?_, ?_⟩
    · have hdb : margin P d b = margin P c b := by
        have h :=
          margin_eq_clone_left (P := P) (c := c) (D := D) (a := d.1) (ha := d.2)
            (haD := by simpa using Hd) (b := b) (hb := Hb) (clone := clone)
        simpa using h
      simpa [margin_pos, hdb] using hpos
    · intro hex
      rcases hex with ⟨l, hne, hnodup, hfirst, hlast, hchain⟩
      have hne_rep : replaceClones c D d Hd l ≠ [] :=
        (replaceClones_ne_nil_iff c D d Hd l).1 hne
      let l' : List A := (replaceClones c D d Hd l).map Subtype.val
      have hne' : l' ≠ [] := by
        intro hnil
        exact hne_rep (List.map_eq_nil_iff.mp hnil)
      have hnodup' : l'.Nodup := by
        have hnodup_rep : (replaceClones c D d Hd l).Nodup :=
          replaceClones_nodup c D d Hd l
        refine hnodup_rep.map ?_
        intro x y hxy
        exact Subtype.ext (by simpa using hxy)
      have hbnot :
          ¬∀ p : (b : A) ≠ c, (⟨(b : A), p⟩ : {x : A // x ≠ c}) ∈ D := by
        intro hall
        have hb' : (⟨(b : A), b.property⟩ : {x : A // x ≠ c}) ∈ D :=
          (clone_mem_iff (c := c) (D := D) (a := (b : A)) (ha := b.property)).1 hall
        exact Hb (by simpa using hb')
      have hfirst_rep :
          (replaceClones c D d Hd l)[0]'(List.length_pos_of_ne_nil hne_rep) = b := by
        have hfirst'' :=
          replaceClones_first_elem (c := c) (D := D) (d := d) (hd := Hd)
            (l := l) (a := b) (hnot := hbnot) (hne := hne) hfirst
        have hb' : (⟨b, replaceClonesHelper c D hbnot⟩ : {x : A // x ≠ c}) = b := by
          ext
          rfl
        simpa [hb'] using hfirst''
      have hfirst' : l'[0]'(List.length_pos_of_ne_nil hne') = (b : A) := by
        simpa [l', List.getElem_map] using congrArg Subtype.val hfirst_rep
      have hlast_rep :
          (replaceClones c D d Hd l).getLast hne_rep = d := by
        simpa using
          (replaceClones_last_c (c := c) (D := D) (d := d) (hd := Hd) (l := l) (hne := hne) hlast)
      have hlast' : l'.getLast hne' = (d : A) := by
        simpa [l', hlast_rep] using
          (List.getLast_map (f := Subtype.val) (l := replaceClones c D d Hd l) (h := hne'))
      have hchain_rep :
          List.IsChain (fun a_1 b_1 : {x : A // x ≠ c} => margin P d b ≤ margin P a_1 b_1)
            (replaceClones c D d Hd l) := by
        simpa using
          (A5_chain (P := P) (c := c) (D := D) (l := l) (d := d) (b := b)
            (hd := Hd) (hb := Hb) (clone := clone) hchain)
      have hchain' :
          List.IsChain (fun a_1 b_1 : A => margin P d b ≤ margin P a_1 b_1) l' := by
        exact (List.isChain_map (R := fun a_1 b_1 : A => margin P d b ≤ margin P a_1 b_1)
          (f := Subtype.val) (l := replaceClones c D d Hd l)).2 (by
            simpa using hchain_rep)
      exact hno ⟨l', hne', hnodup', hfirst', hlast', hchain'⟩

lemma every_clone_defeated' (P : Profile V A) (c : A) (D : Set {x : A // x ≠ c})
    (a : {x : A // x ≠ c}) (Ha : a ∉ D) (d : {x : A // x ≠ c}) (Hd : d ∈ D) :
    clones P c D →
      (splitCycleDefeats P a c ↔ splitCycleDefeats (minusCandidate P c) a d) := by
  classical
  intro clone
  constructor
  · intro hdef
    rcases (splitCycleDefeats_iff_path (P := P) (x := a) (y := c)).1 hdef with
      ⟨hpos, hno⟩
    refine (splitCycleDefeats_iff_path (P := minusCandidate P c) (x := a) (y := d)).2 ?_
    refine ⟨?_, ?_⟩
    · have h :=
        margin_eq_clone_non_clone' (P := P) (c := c) (D := D) (H := Hd) (Hb := Ha) (b := a)
          clone
      simpa [margin_pos, h] using hpos
    · intro hex
      rcases hex with ⟨l, hne, hnodup, hfirst, hlast, hchain⟩
      have hne' : removeClones' c D l ≠ [] :=
        (removeClones'_ne_nil_iff c D l).1 hne
      have hnodup' : (removeClones' c D l).Nodup :=
        removeClones'_nodup c D l
      have hfirst' :
          (removeClones' c D l)[0]'(List.length_pos_of_ne_nil hne') = c := by
        set f : {x : A // x ≠ c} → A := fun x => if x ∈ D then c else (x : A)
        have hmap_ne : l.map f ≠ [] := by
          intro hmap
          exact hne (List.map_eq_nil_iff.mp hmap)
        have hfirst_path :=
          to_path_first_elem (l := l.map f) (h := hmap_ne)
        have hfirst' :
            (removeClones' c D l)[0]'(List.length_pos_of_ne_nil hne') =
              (l.map f)[0]'(List.length_pos_of_ne_nil hmap_ne) :=
          hfirst_path
        have hmap0 :
            (l.map f)[0]'(List.length_pos_of_ne_nil hmap_ne) =
              f (l[0]'(List.length_pos_of_ne_nil hne)) :=
          List.getElem_map (f := f) (l := l) (i := 0)
            (h := List.length_pos_of_ne_nil hmap_ne)
        have hf : f d = c := by
          simp [f, Hd]
        calc
          (removeClones' c D l)[0]'(List.length_pos_of_ne_nil hne') =
              (l.map f)[0]'(List.length_pos_of_ne_nil hmap_ne) := hfirst'
          _ = f (l[0]'(List.length_pos_of_ne_nil hne)) := hmap0
          _ = f d := by simp [hfirst]
          _ = c := hf
      have hlast' :
          (removeClones' c D l).getLast hne' = a := by
        simpa using
          (removeClones'_last_elem (c := c) (D := D) (l := l) (a := a) (hnot := Ha)
            (hne := hne) hlast)
      have hchain' :
          List.IsChain (fun a_1 b_1 : A => margin P a c ≤ margin P a_1 b_1)
            (removeClones' c D l) := by
        simpa using
          (removeClones'_cycle1 (P := P) (c := c) (D := D) (l := l) (a' := a)
            (ha := Ha) (d := d) (hd := Hd) (clone := clone) hchain)
      exact hno ⟨removeClones' c D l, hne', hnodup', hfirst', hlast', hchain'⟩
  · intro hdef
    rcases (splitCycleDefeats_iff_path (P := minusCandidate P c) (x := a) (y := d)).1 hdef with
      ⟨hpos, hno⟩
    refine (splitCycleDefeats_iff_path (P := P) (x := a) (y := c)).2 ?_
    refine ⟨?_, ?_⟩
    · have h :=
        margin_eq_clone_non_clone' (P := P) (c := c) (D := D) (H := Hd) (Hb := Ha) (b := a)
          clone
      simpa [margin_pos, h] using hpos
    · intro hex
      rcases hex with ⟨l, hne, hnodup, hfirst, hlast, hchain⟩
      have hne' : replaceClones c D d Hd l ≠ [] :=
        (replaceClones_ne_nil_iff c D d Hd l).1 hne
      have hnodup' : (replaceClones c D d Hd l).Nodup :=
        replaceClones_nodup c D d Hd l
      have hfirst' :
          (replaceClones c D d Hd l)[0]'(List.length_pos_of_ne_nil hne') = d := by
        set f : A → {x : A // x ≠ c} := fun x =>
          dite (∀ p : x ≠ c, (⟨x, p⟩ : {x : A // x ≠ c}) ∈ D)
            (fun _ => d)
            (fun h => ⟨x, replaceClonesHelper c D h⟩)
        have hmap_ne : l.map f ≠ [] := by
          intro hmap
          exact hne (List.map_eq_nil_iff.mp hmap)
        have hfirst_path :=
          to_path_first_elem (l := l.map f) (h := hmap_ne)
        have hfirst'' :
            (replaceClones c D d Hd l)[0]'(List.length_pos_of_ne_nil hne') =
              (l.map f)[0]'(List.length_pos_of_ne_nil hmap_ne) :=
          hfirst_path
        have hmap0 :
            (l.map f)[0]'(List.length_pos_of_ne_nil hmap_ne) =
              f (l[0]'(List.length_pos_of_ne_nil hne)) :=
          List.getElem_map (f := f) (l := l) (i := 0)
            (h := List.length_pos_of_ne_nil hmap_ne)
        have hfc : f c = d := by
          have hclone : ∀ p : c ≠ c, (⟨c, p⟩ : {x : A // x ≠ c}) ∈ D := by
            intro p
            exact (False.elim (p rfl))
          simp [f, hclone]
        calc
          (replaceClones c D d Hd l)[0]'(List.length_pos_of_ne_nil hne') =
              (l.map f)[0]'(List.length_pos_of_ne_nil hmap_ne) := hfirst''
          _ = f (l[0]'(List.length_pos_of_ne_nil hne)) := hmap0
          _ = f c := by simp [hfirst]
          _ = d := hfc
      have hlast' :
          (replaceClones c D d Hd l).getLast hne' = a := by
        have hnota :
            ¬∀ p : (a : A) ≠ c, (⟨(a : A), p⟩ : {x : A // x ≠ c}) ∈ D := by
          intro hall
          have ha' : (⟨(a : A), a.property⟩ : {x : A // x ≠ c}) ∈ D :=
            (clone_mem_iff (c := c) (D := D) (a := (a : A)) (ha := a.property)).1 hall
          exact Ha (by simpa using ha')
        have hlast'' :=
          replaceClones_last_elem (c := c) (D := D) (d := d) (hd := Hd)
            (l := l) (a := a) (hnot := hnota) (hne := hne) hlast
        have ha' : (⟨a, replaceClonesHelper c D hnota⟩ : {x : A // x ≠ c}) = a := by
          ext
          rfl
        simpa [ha'] using hlast''
      have hchain' :
          List.IsChain (fun a_1 b_1 : {x : A // x ≠ c} =>
            margin (minusCandidate P c) a d ≤ margin (minusCandidate P c) a_1 b_1)
            (replaceClones c D d Hd l) := by
        simpa using
          (removeClones'_cycle2 (P := P) (c := c) (D := D) (l := l) (a' := a)
            (ha := Ha) (d := d) (hd := Hd) (clone := clone) hchain)
      exact hno ⟨replaceClones c D d Hd l, hne', hnodup', hfirst', hlast', hchain'⟩

end CloneDefeats

section Final
variable {V A : Type} [Fintype V] [Fintype A]

theorem split_cycle_non_clone_choice_independence_of_clones : NonCloneChoiceIndependenceOfClones splitCycle := by
  intro V A _ _ _ P c D clone a ha
  classical
  constructor
  · intro haP
    have hcond : ∀ y, ¬ splitCycleDefeats P y a.1 := (Finset.mem_filter.mp haP).2
    have hcond' : ∀ y, ¬ splitCycleDefeats (minusCandidate P c) y a := by
      intro y hy
      have hy' : splitCycleDefeats P y a :=
        (clone_maintains_defeat (P := P) (c := c) (D := D) (a := y) (b := a) (Hb := ha) clone).1 hy
      exact (hcond y) (by simpa using hy')
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hcond'⟩
  · intro haP
    have hcond : ∀ y, ¬ splitCycleDefeats (minusCandidate P c) y a :=
      (Finset.mem_filter.mp haP).2
    rcases clone.1 with ⟨d, hd⟩
    have hcond' : ∀ y, ¬ splitCycleDefeats P y a.1 := by
      intro y hy
      by_cases hyc : y = c
      ·
        have hy' : splitCycleDefeats P c a.1 := by simpa [hyc] using hy
        have hdefd :
            splitCycleDefeats P d a :=
          (every_clone_defeats (P := P) (c := c) (D := D) (b := a) (Hb := ha)
            (d := d) (Hd := hd) clone).1 (by simpa using hy')
        have hdefm :
            splitCycleDefeats (minusCandidate P c) d a :=
          (clone_maintains_defeat (P := P) (c := c) (D := D) (a := d) (b := a) (Hb := ha)
            clone).2 hdefd
        exact (hcond d) hdefm
      ·
        let y' : {x : A // x ≠ c} := ⟨y, hyc⟩
        have hy' : splitCycleDefeats P y' a := by simpa using hy
        have hdefm :
            splitCycleDefeats (minusCandidate P c) y' a :=
          (clone_maintains_defeat (P := P) (c := c) (D := D) (a := y') (b := a) (Hb := ha)
            clone).2 hy'
        exact (hcond y') hdefm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ a.1, hcond'⟩

theorem split_cycle_clone_choice_independence_of_clones : CloneChoiceIndependenceOfClones splitCycle := by
  intro V A _ _ _ P c D clone
  classical
  constructor
  · intro hnone
    rcases hnone with ⟨hc_not, hD_not⟩
    let C := {x : A // ∀ h : x ≠ c, (⟨x, h⟩ : {x // x ≠ c}) ∈ D}
    haveI : Fintype C := by classical infer_instance
    have cC : C := ⟨c, by intro h; cases h rfl⟩
    have hnot_all : ¬ ∀ c' : C, ∃ d : C, splitCycleDefeats P d.1 c'.1 := by
      intro hdefC
      rcases cycle_of_forall_defeater (R := fun a b : C => splitCycleDefeats P a.1 b.1) cC hdefC with
        ⟨l, hcycle⟩
      have hcycleA : cycle (splitCycleDefeats P) (l.map Subtype.val) := by
        simpa using (cycle_map (f := Subtype.val) (P := splitCycleDefeats P) hcycle)
      exact (splitCycleDefeats_acyclic P) _ hcycleA
    rcases not_forall.mp hnot_all with ⟨d, hd⟩
    have hd_notmem : (d : A) ∉ splitCycle P := by
      by_cases hdc : (d : A) = c
      · simpa [hdc] using hc_not
      · have hdD : (⟨(d : A), hdc⟩ : {x : A // x ≠ c}) ∈ D :=
          d.property hdc
        exact hD_not _ hdD
    have hnotall : ¬ ∀ y, ¬ splitCycleDefeats P y d.1 := by
      intro hall
      exact hd_notmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩)
    obtain ⟨a, ha⟩ := not_forall.mp hnotall
    have hdefa : splitCycleDefeats P a d.1 := not_not.mp ha
    have hnot_clone :
        ¬∀ h : a ≠ c, (⟨a, h⟩ : {x : A // x ≠ c}) ∈ D := by
      intro hall
      let aC : C := ⟨a, hall⟩
      have hdefa' : splitCycleDefeats P (aC : A) d.1 := by
        simpa [aC] using hdefa
      exact hd ⟨aC, hdefa'⟩
    let a' : {x : A // x ≠ c} := ⟨a, replaceClonesHelper c D hnot_clone⟩
    have ha_notD : a' ∉ D := by
      simpa using (not_clone_mem c D hnot_clone)
    have hdefc : splitCycleDefeats P a' c := by
      by_cases hdc : (d : A) = c
      · simpa [hdc] using hdefa
      · have hdD : (⟨(d : A), hdc⟩ : {x : A // x ≠ c}) ∈ D :=
          d.property hdc
        let d' : {x : A // x ≠ c} := ⟨(d : A), hdc⟩
        have hdefa' : splitCycleDefeats P a' d' := by
          simpa using hdefa
        have hdefm :
            splitCycleDefeats (minusCandidate P c) a' d' :=
          (clone_maintains_defeat' (P := P) (c := c) (D := D) (a := a') (b := d')
            (Ha := ha_notD) (Hb := hdD) clone).2 hdefa'
        exact
          (every_clone_defeated' (P := P) (c := c) (D := D) (a := a') (Ha := ha_notD) (d := d')
            (Hd := hdD) clone).2 hdefm
    intro e heD he_mem
    have hdefm :
        splitCycleDefeats (minusCandidate P c) a' e :=
      (every_clone_defeated' (P := P) (c := c) (D := D) (a := a') (Ha := ha_notD) (d := e)
        (Hd := heD) clone).1 hdefc
    have hcond : ∀ y, ¬ splitCycleDefeats (minusCandidate P c) y e :=
      (Finset.mem_filter.mp he_mem).2
    exact (hcond a') hdefm
  · intro hnone
    have hDne : D.Nonempty := clone.1
    rcases hDne with ⟨d0, hd0⟩
    let S := {x : {x : A // x ≠ c} // x ∈ D}
    haveI : Fintype S := by classical infer_instance
    have s0 : S := ⟨d0, hd0⟩
    have hnot_all :
        ¬ ∀ c' : S, ∃ d : S, splitCycleDefeats (minusCandidate P c) d.1 c'.1 := by
      intro hdefS
      rcases cycle_of_forall_defeater
        (R := fun a b : S => splitCycleDefeats (minusCandidate P c) a.1 b.1) s0 hdefS with
        ⟨l, hcycle⟩
      have hcycleA : cycle (splitCycleDefeats (minusCandidate P c)) (l.map Subtype.val) := by
        simpa using (cycle_map (f := Subtype.val) (P := splitCycleDefeats (minusCandidate P c)) hcycle)
      exact (splitCycleDefeats_acyclic (P := minusCandidate P c)) _ hcycleA
    rcases not_forall.mp hnot_all with ⟨d, hd⟩
    have hd_notmem : d.1 ∉ splitCycle (minusCandidate P c) := by
      exact hnone _ d.2
    have hnotall : ¬ ∀ y, ¬ splitCycleDefeats (minusCandidate P c) y d.1 := by
      intro hall
      exact hd_notmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩)
    obtain ⟨a, ha⟩ := not_forall.mp hnotall
    have hdefm : splitCycleDefeats (minusCandidate P c) a d.1 := not_not.mp ha
    have ha_notD : a ∉ D := by
      intro haD
      let aS : S := ⟨a, haD⟩
      have hdefm' : splitCycleDefeats (minusCandidate P c) (aS : {x : A // x ≠ c}) d.1 := by
        simpa [aS] using hdefm
      exact hd ⟨aS, hdefm'⟩
    have hdefc : splitCycleDefeats P a c :=
      (every_clone_defeated' (P := P) (c := c) (D := D) (a := a) (Ha := ha_notD) (d := d.1)
        (Hd := d.2) clone).2 hdefm
    have hc_not : c ∉ splitCycle P := by
      intro hc_mem
      have hcond : ∀ y, ¬ splitCycleDefeats P y c := (Finset.mem_filter.mp hc_mem).2
      exact (hcond a) hdefc
    have hD_not : ∀ e : {x : A // x ≠ c}, e ∈ D → (e : A) ∉ splitCycle P := by
      intro e heD he_mem
      have hdefm_e :
          splitCycleDefeats (minusCandidate P c) a e :=
        (every_clone_defeated' (P := P) (c := c) (D := D) (a := a) (Ha := ha_notD) (d := e)
          (Hd := heD) clone).1 hdefc
      have hdefP_e :
          splitCycleDefeats P a e :=
        (clone_maintains_defeat' (P := P) (c := c) (D := D) (a := a) (b := e)
            (Ha := ha_notD) (Hb := heD) clone).1 hdefm_e
      have hcond : ∀ y, ¬ splitCycleDefeats P y e := (Finset.mem_filter.mp he_mem).2
      exact (hcond a) hdefP_e
    exact ⟨hc_not, hD_not⟩

/-! ## Independence of Clones -/

/-- Combined clone properties for induction. -/
def split_cycle_clone_independence_props
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x : A) : Prop :=
  (∀ c (hc : c ∉ X),
      (c ∈ splitCycle P ↔
        (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) ∈
          splitCycle (removeClonesExcept P X x))) ∧
  ((∃ y, y ∈ X ∧ y ∈ splitCycle P) ↔
    (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈
      splitCycle (removeClonesExcept P X x))

theorem split_cycle_independence_of_clones : IndependenceOfClones splitCycle := by
  unfold IndependenceOfClones
  intro V A instV instA instDecEq P X x hX hx
  classical
  -- Strong induction on the number of candidates.
  set n := Fintype.card A with hn
  let Motive : Nat → Prop := fun k =>
    ∀ {A' : Type} [Fintype A'] [DecidableEq A'],
      Fintype.card A' = k →
        ∀ {V' : Type} [Fintype V'] (P' : Profile V' A') (X' : Set A') (x' : A'),
          CloneSet P' X' → x' ∈ X' → split_cycle_clone_independence_props P' X' x'
  have hStrong : Motive n := by
    classical
    refine Nat.strongRecOn (motive := Motive) n ?_
    intro k ih A' _ _ hcard V' _ P' X' x' hX' hx'
    by_cases hX_singleton : ∀ y ∈ X', y = x'
    · -- X' = {x'}: removeClonesExcept is just a relabeling of P'
      have hpred : ∀ a : A', clonePred X' x' a := by
        intro a
        by_cases hax : a = x'
        · subst hax
          exact Or.inr rfl
        · left
          intro haX
          exact hax (hX_singleton a haX)
      let e : A' ≃ {a : A' // clonePred X' x' a} :=
        { toFun := fun a => ⟨a, hpred a⟩
          invFun := fun s => (s : A')
          left_inv := by intro a; rfl
          right_inv := by intro s; ext; rfl }
      have hrelabel : relabelProfile P' e = removeClonesExcept P' X' x' := by
        ext v
        rfl
      refine ⟨?_, ?_⟩
      · intro c hc
        have hmem :
            (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' x' a}) ∈
                splitCycle (removeClonesExcept P' X' x') ↔
              c ∈ splitCycle P' := by
          have hec : e.symm (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' x' a}) = c := rfl
          simpa only [hrelabel, hec] using
            (mem_splitCycle_relabelProfile_iff (P := P') (e := e)
              (b := (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' x' a})))
        exact hmem.symm
      · have hxmem :
            (⟨x', Or.inr rfl⟩ : {a : A' // clonePred X' x' a}) ∈
                splitCycle (removeClonesExcept P' X' x') ↔
              x' ∈ splitCycle P' := by
          have hex : e.symm (⟨x', Or.inr rfl⟩ : {a : A' // clonePred X' x' a}) = x' := rfl
          simpa only [hrelabel, hex] using
            (mem_splitCycle_relabelProfile_iff (P := P') (e := e)
              (b := (⟨x', Or.inr rfl⟩ : {a : A' // clonePred X' x' a})))
        constructor
        · intro h
          rcases h with ⟨y, hyX, hywin⟩
          have hy : y = x' := hX_singleton y hyX
          subst hy
          exact hxmem.mpr hywin
        · intro hxwin
          exact ⟨x', hx', hxmem.mp hxwin⟩
    · -- Pick a distinct clone ℓ in X'
      have hXne : ∃ y ∈ X', y ≠ x' := by
        by_contra h
        push_neg at h
        exact hX_singleton h
      rcases hXne with ⟨ℓ, hℓX, hxℓ⟩
      have hxℓ' : x' ≠ ℓ := hxℓ.symm
      let xℓ : {a : A' // a ≠ ℓ} := ⟨x', hxℓ'⟩
      have hcloneℓ :
          clones P' ℓ (restrictCloneSet X' ℓ) :=
        clones_of_cloneSet (P := P') (X := X') (x := ℓ) hX' hℓX ⟨x', hx', hxℓ'⟩
      have hklt : Fintype.card {a : A' // a ≠ ℓ} < k := by
        simpa [hcard] using (card_subtype_ne_lt (x := ℓ))
      have hM : Motive (Fintype.card {a : A' // a ≠ ℓ}) := ih _ hklt
      have hX_restr :
          CloneSet (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) :=
        cloneSet_restrictProfile (P := P') (X := X') (ℓ := ℓ) (hX := hX')
          ⟨x', hx', hxℓ'⟩
      have hxℓ_mem : xℓ ∈ restrictCloneSet X' ℓ := by
        simpa [restrictCloneSet, xℓ] using hx'
      have hrec :
          split_cycle_clone_independence_props
            (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ :=
        hM (A' := {a : A' // a ≠ ℓ}) rfl
          (P' := restrictProfile P' ℓ)
          (X' := restrictCloneSet X' ℓ) (x' := xℓ) hX_restr hxℓ_mem
      rcases relabelProfile_removeClonesExcept_restrictProfile_of_clone
        (P := P') (X := X') (x := x') (ℓ := ℓ) hℓX hxℓ' with
        ⟨e, he1, he2, hrelabel⟩
      refine ⟨?_, ?_⟩
      · intro c hc
        have hcℓ : c ≠ ℓ := by
          intro h
          apply hc
          simpa [h] using hℓX
        have hnot : (⟨c, hcℓ⟩ : {a : A' // a ≠ ℓ}) ∉ restrictCloneSet X' ℓ := by
          intro hmem
          apply hc
          simpa [restrictCloneSet] using hmem
        have hnon :
            c ∈ splitCycle P' ↔
              (⟨c, hcℓ⟩ : {a : A' // a ≠ ℓ}) ∈ splitCycle (restrictProfile P' ℓ) := by
          have hnon' :=
            split_cycle_non_clone_choice_independence_of_clones
              (P := P') (c := ℓ) (D := restrictCloneSet X' ℓ) hcloneℓ
              (a := (⟨c, hcℓ⟩ : {a : A' // a ≠ ℓ})) hnot
          change c ∈ splitCycle P' ↔
            (⟨c, hcℓ⟩ : {a : A' // a ≠ ℓ}) ∈ splitCycle (minusCandidate P' ℓ)
          exact hnon'
        have hrec_non :
            (⟨c, hcℓ⟩ : {a : A' // a ≠ ℓ}) ∈ splitCycle (restrictProfile P' ℓ) ↔
              (⟨⟨c, hcℓ⟩, Or.inl hnot⟩ :
                  {a : {a : A' // a ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) ∈
                splitCycle (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) :=
          (hrec.1 (c := (⟨c, hcℓ⟩ : {a : A' // a ≠ ℓ})) hnot)
        let b :
            {a : {a : A' // a ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a} :=
          ⟨⟨c, hcℓ⟩, Or.inl hnot⟩
        have hmem :
            b ∈ splitCycle (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) ↔
              (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' x' a}) ∈
                splitCycle (removeClonesExcept P' X' x') := by
          have hmem' :
              b ∈ splitCycle (relabelProfile (removeClonesExcept P' X' x') e) ↔
                e.symm b ∈ splitCycle (removeClonesExcept P' X' x') := by
            simpa using
              (mem_splitCycle_relabelProfile_iff (P := removeClonesExcept P' X' x') (e := e) (b := b))
          have hsymm :
              e.symm b = (⟨c, Or.inl hc⟩ : {a : A' // clonePred X' x' a}) := by
            apply Subtype.ext
            have hval : (e.symm b).1 = b.1.1 := he2 b
            simpa [b] using hval
          simpa [hrelabel, hsymm] using hmem'
        exact hnon.trans (hrec_non.trans hmem)
      · have hnone_left :
            (∀ y ∈ X', y ∉ splitCycle P') ↔
              (ℓ ∉ splitCycle P' ∧
                ∀ c' : {x : A' // x ≠ ℓ},
                  c' ∈ restrictCloneSet X' ℓ → (c' : A') ∉ splitCycle P') := by
          constructor
          · intro hnone
            refine ⟨?_, ?_⟩
            · exact hnone ℓ hℓX
            · intro c' hc'
              exact hnone c' (by simpa [restrictCloneSet] using hc')
          · intro hnone
            rcases hnone with ⟨hℓ, hall⟩
            intro y hyX hywin
            by_cases hyℓ : y = ℓ
            · subst hyℓ
              exact hℓ hywin
            · have hy' : (⟨y, hyℓ⟩ : {x : A' // x ≠ ℓ}) ∈ restrictCloneSet X' ℓ := by
                simpa [restrictCloneSet] using hyX
              exact hall _ hy' hywin
        have hclone_choice :=
          split_cycle_clone_choice_independence_of_clones
            (P := P') (c := ℓ) (D := restrictCloneSet X' ℓ) hcloneℓ
        have hnone :
            (∀ y ∈ X', y ∉ splitCycle P') ↔
              ∀ c' : {x : A' // x ≠ ℓ},
                c' ∈ restrictCloneSet X' ℓ →
                  c' ∉ splitCycle (restrictProfile P' ℓ) := by
          have hnone' :
              (ℓ ∉ splitCycle P' ∧
                ∀ c' : {x : A' // x ≠ ℓ},
                  c' ∈ restrictCloneSet X' ℓ → (c' : A') ∉ splitCycle P') ↔
                ∀ c' : {x : A' // x ≠ ℓ},
                  c' ∈ restrictCloneSet X' ℓ →
                    c' ∉ splitCycle (minusCandidate P' ℓ) := by
            simpa [minusCandidate] using hclone_choice
          exact hnone_left.trans hnone'
        have hexists :
            (∃ y, y ∈ X' ∧ y ∈ splitCycle P') ↔
              ∃ c' : {x : A' // x ≠ ℓ},
                c' ∈ restrictCloneSet X' ℓ ∧ c' ∈ splitCycle (restrictProfile P' ℓ) := by
          constructor
          · intro h
            by_contra hnot
            have hnone_restr :
                ∀ c' : {x : A' // x ≠ ℓ},
                  c' ∈ restrictCloneSet X' ℓ →
                    c' ∉ splitCycle (restrictProfile P' ℓ) := by
              intro c' hc' hwin
              exact hnot ⟨c', hc', hwin⟩
            have hnone_orig : ∀ y ∈ X', y ∉ splitCycle P' := hnone.mpr hnone_restr
            rcases h with ⟨y, hyX, hywin⟩
            exact (hnone_orig y hyX) hywin
          · intro h
            by_contra hnot
            have hnone_orig : ∀ y ∈ X', y ∉ splitCycle P' := by
              intro y hyX hywin
              exact hnot ⟨y, hyX, hywin⟩
            have hnone_restr :
                ∀ c' : {x : A' // x ≠ ℓ},
                  c' ∈ restrictCloneSet X' ℓ →
                    c' ∉ splitCycle (restrictProfile P' ℓ) := hnone.mp hnone_orig
            rcases h with ⟨c', hc'X, hc'win⟩
            exact (hnone_restr c' hc'X) hc'win
        have hrec_clone :
            (∃ y, y ∈ restrictCloneSet X' ℓ ∧ y ∈ splitCycle (restrictProfile P' ℓ)) ↔
              (⟨xℓ, Or.inr rfl⟩ :
                {a : {a : A' // a ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) ∈
                splitCycle (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) :=
          hrec.2
        have hrep :
            (⟨xℓ, Or.inr rfl⟩ :
                {a : {a : A' // a ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) ∈
              splitCycle (removeClonesExcept (restrictProfile P' ℓ) (restrictCloneSet X' ℓ) xℓ) ↔
                (⟨x', Or.inr rfl⟩ : {a : A' // clonePred X' x' a}) ∈
                  splitCycle (removeClonesExcept P' X' x') := by
          have hmem' :
              (⟨xℓ, Or.inr rfl⟩ :
                  {a : {a : A' // a ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) ∈
                splitCycle (relabelProfile (removeClonesExcept P' X' x') e) ↔
                  e.symm (⟨xℓ, Or.inr rfl⟩ :
                    {a : {a : A' // a ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) ∈
                      splitCycle (removeClonesExcept P' X' x') := by
            simpa using
              (mem_splitCycle_relabelProfile_iff (P := removeClonesExcept P' X' x') (e := e)
                (b := (⟨xℓ, Or.inr rfl⟩ :
                  {a : {a : A' // a ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})))
          have hsymm :
              e.symm (⟨xℓ, Or.inr rfl⟩ :
                  {a : {a : A' // a ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}) =
                (⟨x', Or.inr rfl⟩ : {a : A' // clonePred X' x' a}) := by
            apply Subtype.ext
            have hval :
                (e.symm (⟨xℓ, Or.inr rfl⟩ :
                  {a : {a : A' // a ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a})).1 =
                  (⟨xℓ, Or.inr rfl⟩ :
                    {a : {a : A' // a ≠ ℓ} // clonePred (restrictCloneSet X' ℓ) xℓ a}).1.1 := by
              exact he2 _
            simpa [xℓ] using hval
          simpa [hrelabel, hsymm] using hmem'
        exact (hexists.trans (hrec_clone.trans hrep))
  have hFinal := hStrong (A' := A) rfl (P' := P) (X' := X) (x' := x) hX hx
  simpa [split_cycle_clone_independence_props] using hFinal

end Final

end SocialChoice
