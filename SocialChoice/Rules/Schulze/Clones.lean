import Mathlib.Data.Set.Basic
import Mathlib.Tactic
import SocialChoice.Profile
import SocialChoice.Margin
import SocialChoice.Cycles
import SocialChoice.Axioms.Clones
import SocialChoice.Rules.Schulze.Defs
import SocialChoice.Rules.Schulze.Path
import SocialChoice.Rules.Schulze.Transitivity

namespace SocialChoice

noncomputable local instance instDecidableEqSchulze {A : Type} : DecidableEq A := Classical.decEq _

@[simp] lemma margin_removeClonesExcept
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A)
    (a b : {a : A // clonePred X x a}) :
    margin (removeClonesExcept P X x) a b = margin P a b := by
  classical
  simp [margin]

lemma pathStrengthAux_removeClonesExcept
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A) :
    ∀ (a : {a : A // clonePred X x a}) (l : List {a : A // clonePred X x a}) (m : Int),
      pathStrengthAux (removeClonesExcept P X x) a l m =
        pathStrengthAux P a.1 (l.map Subtype.val) m
  | a, [], m => by
      simp [pathStrengthAux]
  | a, b :: t, m => by
      simp [pathStrengthAux, margin_removeClonesExcept, pathStrengthAux_removeClonesExcept]

lemma pathStrength_removeClonesExcept
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A) :
    ∀ l : List {a : A // clonePred X x a},
      pathStrength (removeClonesExcept P X x) l =
        pathStrength P (l.map Subtype.val)
  | [] => by
      simp [pathStrength]
  | [a] => by
      simp [pathStrength]
  | a :: b :: t => by
      simp [pathStrength, pathStrengthAux_removeClonesExcept, margin_removeClonesExcept]

lemma margin_clone_eq_of_cloneSet
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (hX : CloneSet P X)
    {x x' y : A} (hx : x ∈ X) (hx' : x' ∈ X) (hy : y ∉ X) :
    margin P x y = margin P x' y ∧ margin P y x = margin P y x' := by
  classical
  have hpref := cloneSet_prefers_equiv (P := P) (X := X) hX
    (hx := hx) (hx' := hx') (hy := hy)
  have h1 :
      (Finset.univ.filter (fun v => Prefers P v x y)).card =
        (Finset.univ.filter (fun v => Prefers P v x' y)).card := by
    refine cardinality_lemma2 (p := fun v => Prefers P v x y)
      (q := fun v => Prefers P v x' y) ?_
    intro v
    exact (hpref v).1
  have h2 :
      (Finset.univ.filter (fun v => Prefers P v y x)).card =
        (Finset.univ.filter (fun v => Prefers P v y x')).card := by
    refine cardinality_lemma2 (p := fun v => Prefers P v y x)
      (q := fun v => Prefers P v y x') ?_
    intro v
    exact (hpref v).2
  refine ⟨?_, ?_⟩
  · dsimp [margin]
    rw [h1, h2]
  · dsimp [margin]
    rw [h1, h2]

/-! ## Path transport for clone collapse -/

noncomputable def collapseToRep {A : Type} (X : Set A) (x : A) (_hx : x ∈ X) :
    A → {a : A // clonePred X x a} := by
  classical
  exact fun a =>
    if hax : a ∈ X then
      ⟨x, Or.inr rfl⟩
    else
      ⟨a, Or.inl hax⟩

noncomputable def expandFromRep {A : Type} (X : Set A) (x y : A) :
    {a : A // clonePred X x a} → A := by
  classical
  exact fun a =>
    if hax : (a : A) ∈ X then y else a.1

lemma collapseToRep_val_of_not_mem {A : Type} (X : Set A) (x : A) (hx : x ∈ X)
    {a : A} (ha : a ∉ X) :
    (collapseToRep X x hx a).1 = a := by
  simp [collapseToRep, ha]

lemma collapseToRep_val_of_mem {A : Type} (X : Set A) (x : A) (hx : x ∈ X)
    {a : A} (ha : a ∈ X) :
    (collapseToRep X x hx a).1 = x := by
  simp [collapseToRep, ha]

lemma expandFromRep_val_of_not_mem {A : Type} (X : Set A) (x y : A)
    {a : {a : A // clonePred X x a}} (ha : (a : A) ∉ X) :
    expandFromRep X x y a = a := by
  simp [expandFromRep, ha]

lemma expandFromRep_val_of_mem {A : Type} (X : Set A) (x y : A)
    {a : {a : A // clonePred X x a}} (ha : (a : A) ∈ X) :
    expandFromRep X x y a = y := by
  simp [expandFromRep, ha]

lemma subtype_val_eq_rep_of_mem {A : Type} (X : Set A) (x : A)
    {a : {a : A // clonePred X x a}} (ha : (a : A) ∈ X) :
    (a : A) = x := by
  cases a with
  | mk a ha' =>
      cases ha' with
      | inl hnot => exact (False.elim (hnot ha))
      | inr hEq => exact hEq

lemma expandFromRep_injective {A : Type} (X : Set A) (x y : A) (hy : y ∈ X) :
    Function.Injective (expandFromRep X x y) := by
  classical
  intro a b h
  by_cases ha : (a : A) ∈ X
  · have hya : expandFromRep X x y a = y := by simp [expandFromRep, ha]
    by_cases hb : (b : A) ∈ X
    · have ha' : (a : A) = x := subtype_val_eq_rep_of_mem (X := X) (x := x) ha
      have hb' : (b : A) = x := subtype_val_eq_rep_of_mem (X := X) (x := x) hb
      apply Subtype.ext
      simp [ha', hb']
    · have hyb : expandFromRep X x y b = b := by simp [expandFromRep, hb]
      have : y = b := by simpa [hya, hyb] using h
      exact (hb (by simpa [this] using hy)).elim
  · have hya : expandFromRep X x y a = a := by simp [expandFromRep, ha]
    by_cases hb : (b : A) ∈ X
    · have hyb : expandFromRep X x y b = y := by simp [expandFromRep, hb]
      have : a = y := by simpa [hya, hyb] using h
      exact (ha (by simpa [this] using hy)).elim
    · have hyb : expandFromRep X x y b = b := by simp [expandFromRep, hb]
      have : (a : A) = (b : A) := by simpa [hya, hyb] using h
      exact Subtype.ext this

lemma collapseToRep_subtype_eq {A : Type} (X : Set A) (x : A) (hx : x ∈ X)
    (b : {a : A // clonePred X x a}) :
    collapseToRep X x hx b.1 = b := by
  classical
  by_cases hb : (b : A) ∈ X
  · have hb' : (b : A) = x := subtype_val_eq_rep_of_mem (X := X) (x := x) hb
    apply Subtype.ext
    simp [collapseToRep, hb', hx]
  · apply Subtype.ext
    simp [collapseToRep, hb]

lemma collapseToRep_ne_of_not_both_mem {A : Type} (X : Set A) (x : A) (hx : x ∈ X)
    {a b : A} (hne : a ≠ b) (hnot : a ∉ X ∨ b ∉ X) :
    collapseToRep X x hx a ≠ collapseToRep X x hx b := by
  classical
  intro hEq
  cases hnot with
  | inl ha =>
      by_cases hb : b ∈ X
      · have hval : a = x := by
          have hval' := congrArg Subtype.val hEq
          simp [collapseToRep, ha, hb] at hval'
          exact hval'
        exact ha (by simpa [hval] using hx)
      · have hval := congrArg Subtype.val hEq
        simp [collapseToRep, ha, hb] at hval
        exact hne hval
  | inr hb =>
      by_cases ha : a ∈ X
      · have hval : x = b := by
          have hval' := congrArg Subtype.val hEq
          simp [collapseToRep, ha, hb] at hval'
          exact hval'
        exact hb (by simpa [hval] using hx)
      · have hval := congrArg Subtype.val hEq
        simp [collapseToRep, ha, hb] at hval
        exact hne hval

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

lemma isChain_of_le_pathStrength {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (m : Int) :
    ∀ l, m ≤ pathStrength P l →
      List.IsChain (fun a b => m ≤ margin P a b) l
  | [], _ => by
      simp
  | [a], _ => by
      simp
  | a :: b :: t, h => by
      cases t with
      | nil =>
          have hrel : m ≤ margin P a b := by
            simpa [pathStrength_two] using h
          exact (List.isChain_cons_cons).2 ⟨hrel, by simp⟩
      | cons c t' =>
          have hstrength :
              pathStrength P (a :: b :: c :: t') =
                min (margin P a b) (pathStrength P (b :: c :: t')) :=
            pathStrength_cons_cons_cons (P := P) a b c t'
          have h' : m ≤ min (margin P a b) (pathStrength P (b :: c :: t')) := by
            simpa [hstrength] using h
          have hrel : m ≤ margin P a b := (le_min_iff.mp h').1
          have htail : m ≤ pathStrength P (b :: c :: t') := (le_min_iff.mp h').2
          have hchain_tail :=
            isChain_of_le_pathStrength (P := P) (m := m) (l := b :: c :: t') htail
          exact (List.isChain_cons_cons).2 ⟨hrel, hchain_tail⟩

lemma pathStrength_ge_of_chain
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (m : Int) :
    ∀ l, List.IsChain (fun a b => m ≤ margin P a b) l →
      2 ≤ l.length → m ≤ pathStrength P l
  | [], _hchain, hlen => by
      simp at hlen
  | [_], _hchain, hlen => by
      simp at hlen
  | a :: b :: t, hchain, _hlen => by
      have hab : m ≤ margin P a b :=
        List.IsChain.rel_head (R := fun a b => m ≤ margin P a b) hchain
      cases t with
      | nil =>
          exact hab
      | cons c t' =>
          have htail : List.IsChain (fun a b => m ≤ margin P a b) (b :: c :: t') :=
            hchain.tail
          have htail_len : 2 ≤ (b :: c :: t').length := by simp
          have htail_ge :=
            pathStrength_ge_of_chain (P := P) (m := m) (l := b :: c :: t') htail htail_len
          have hmin : m ≤ min (margin P a b) (pathStrength P (b :: c :: t')) := by
            exact le_min hab htail_ge
          simpa [pathStrength_cons_cons_cons] using hmin

noncomputable def collapsePath {A : Type} (X : Set A) (x : A) (hx : x ∈ X) :
    List A → List {a : A // clonePred X x a} :=
  fun l => to_path (l.map (collapseToRep X x hx))

lemma collapse_rel_of_rel
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A) (hx : x ∈ X) (hX : CloneSet P X)
    (m : Int) {a b : A} (hrel : m ≤ margin P a b) :
    collapseToRep X x hx a = collapseToRep X x hx b ∨
      m ≤ margin (removeClonesExcept P X x)
        (collapseToRep X x hx a) (collapseToRep X x hx b) := by
  classical
  by_cases ha : a ∈ X
  · by_cases hb : b ∈ X
    · left
      simp [collapseToRep, ha, hb]
    · right
      have hmargin :
          margin P a b = margin P x b := by
        have h := margin_clone_eq_of_cloneSet (P := P) (X := X) hX
          (hx := hx) (hx' := ha) (hy := hb)
        exact h.1.symm
      have hmargin' :
          margin (removeClonesExcept P X x)
            (collapseToRep X x hx a) (collapseToRep X x hx b) = margin P x b := by
        simp [collapseToRep, ha, hb, margin_removeClonesExcept]
      simpa [hmargin, hmargin'] using hrel
  · by_cases hb : b ∈ X
    · right
      have hmargin :
          margin P a b = margin P a x := by
        have h := margin_clone_eq_of_cloneSet (P := P) (X := X) hX
          (hx := hx) (hx' := hb) (hy := ha)
        exact h.2.symm
      have hmargin' :
          margin (removeClonesExcept P X x)
            (collapseToRep X x hx a) (collapseToRep X x hx b) = margin P a x := by
        simp [collapseToRep, ha, hb, margin_removeClonesExcept]
      simpa [hmargin, hmargin'] using hrel
    · right
      have hmargin' :
          margin (removeClonesExcept P X x)
            (collapseToRep X x hx a) (collapseToRep X x hx b) = margin P a b := by
        simp [collapseToRep, ha, hb, margin_removeClonesExcept]
      simpa [hmargin'] using hrel

lemma collapse_chain_of_chain
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x : A) (hx : x ∈ X) (hX : CloneSet P X)
    (m : Int) (l : List A) :
    List.IsChain (fun a b => m ≤ margin P a b) l →
      List.IsChain (fun a b => m ≤ margin (removeClonesExcept P X x) a b)
        (collapsePath X x hx l) := by
  classical
  intro hchain
  let f := collapseToRep X x hx
  have hchain_map :
      List.IsChain (fun a b => a = b ∨
        m ≤ margin (removeClonesExcept P X x) a b) (l.map f) := by
    refine (List.isChain_map_of_isChain (R := fun a b => m ≤ margin P a b)
      (S := fun a b => a = b ∨ m ≤ margin (removeClonesExcept P X x) a b)
      (f := f) ?_ hchain)
    intro a b hrel
    exact collapse_rel_of_rel (P := P) (X := X) (x := x) (hx := hx) (hX := hX)
      (m := m) hrel
  have hchain_path :
      List.IsChain (fun a b => a = b ∨
        m ≤ margin (removeClonesExcept P X x) a b) (to_path (l.map f)) := by
    exact to_path_chain'_of_chain' (l := l.map f) hchain_map
  have hnodup : (to_path (l.map f)).Nodup := by
    exact to_path_nodup (l := l.map f)
  exact chain_of_chain_eq_or hchain_path hnodup

lemma collapsePath_head?
    {A : Type} [DecidableEq A] (X : Set A) (x : A) (hx : x ∈ X)
    {l : List A} {a : A} (hhead : l.head? = some a) :
    (collapsePath X x hx l).head? = some (collapseToRep X x hx a) := by
  classical
  cases l with
  | nil =>
      simp at hhead
  | cons a' t =>
      simp [List.head?] at hhead
      subst hhead
      have hmap_ne : (List.map (collapseToRep X x hx) (a' :: t)) ≠ [] := by
        simp
      have htp_ne : (collapsePath X x hx (a' :: t)) ≠ [] := by
        simp [collapsePath]
        exact to_path_ne_nil_iff (l := (a' :: t).map (collapseToRep X x hx))
          hmap_ne
      have hfirst :=
        to_path_first_elem (l := (a' :: t).map (collapseToRep X x hx)) (h := by simp)
      have h0 :
          (collapsePath X x hx (a' :: t))[0]'(List.length_pos_of_ne_nil htp_ne) =
            (collapseToRep X x hx a') := by
        have hmap0 :
            ((a' :: t).map (collapseToRep X x hx))[0]'(by simp) =
              collapseToRep X x hx a' := by
          simp
        simp [collapsePath]
        exact hfirst.trans hmap0
      have hhead' :
          (collapsePath X x hx (a' :: t)).head? =
            some ((collapsePath X x hx (a' :: t)).head htp_ne) := by
        exact List.head?_eq_some_head htp_ne
      have hhead'' :
          (collapsePath X x hx (a' :: t)).head htp_ne =
            collapseToRep X x hx a' := by
        simp [List.head_eq_getElem_zero]
        exact h0
      simp [hhead'', hhead']

lemma collapsePath_last?
    {A : Type} [DecidableEq A] (X : Set A) (x : A) (hx : x ∈ X)
    {l : List A} {a : A} (hlast : l.getLast? = some a) :
    (collapsePath X x hx l).getLast? = some (collapseToRep X x hx a) := by
  classical
  have hne : l ≠ [] := by
    intro hnil
    subst hnil
    simp at hlast
  have hlast_eq : l.getLast hne = a := by
    have hlast' := List.getLast?_eq_getLast_of_ne_nil (l := l) hne
    have : some (l.getLast hne) = some a := by simpa [hlast'] using hlast
    exact Option.some.inj this
  have hmap_ne : (l.map (collapseToRep X x hx)) ≠ [] := by
    intro hmap
    exact hne (List.map_eq_nil_iff.mp hmap)
  have htp_ne : collapsePath X x hx l ≠ [] := by
    simp [collapsePath]
    exact to_path_ne_nil_iff (l := l.map (collapseToRep X x hx)) hmap_ne
  have hlast_path :=
    to_path_last_elem (l := l.map (collapseToRep X x hx)) (h := by
      simpa using hmap_ne)
  have hlast_map :
      (l.map (collapseToRep X x hx)).getLast hmap_ne =
        collapseToRep X x hx a := by
    have hmap_last := List.getLast_map (f := collapseToRep X x hx) (l := l) (h := hmap_ne)
    have hmap_last' := hmap_last
    rw [hlast_eq] at hmap_last'
    exact hmap_last'
  have hlast0 :
      (collapsePath X x hx l).getLast htp_ne = collapseToRep X x hx a := by
    simp [collapsePath]
    exact hlast_path.trans hlast_map
  have hlast? :
      (collapsePath X x hx l).getLast? =
        some ((collapsePath X x hx l).getLast htp_ne) := by
    exact List.getLast?_eq_getLast_of_ne_nil (l := collapsePath X x hx l) htp_ne
  simp [hlast0, hlast?]

lemma strongestPath_le_collapse
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x : A) (hx : x ∈ X) (hX : CloneSet P X)
    {a b : A} (hne : a ≠ b) (hnot : a ∉ X ∨ b ∉ X) :
    strongestPath P a b ≤
      strongestPath (removeClonesExcept P X x)
        (collapseToRep X x hx a) (collapseToRep X x hx b) := by
  classical
  have hne_paths :
      (pathsUpTo (A := A) (Fintype.card A) a b).Nonempty :=
    pathsUpTo_nonempty_of_ne (A := A) a b hne
  rcases exists_max_path_props (P := P) (a := a) (b := b) hne_paths with
    ⟨l, _hl, hhead, hlast, _hnodup, hlen, hstrength⟩
  set m := strongestPath P a b with hm
  have hchain :
      List.IsChain (fun u v => m ≤ margin P u v) l := by
    have hmle : m ≤ pathStrength P l := by
      simp [hm, hstrength]
    exact isChain_of_le_pathStrength (P := P) (m := m) (l := l) hmle
  let l' := collapsePath X x hx l
  have hchain' :
      List.IsChain (fun u v => m ≤ margin (removeClonesExcept P X x) u v) l' := by
    exact collapse_chain_of_chain (P := P) (X := X) (x := x) (hx := hx) (hX := hX)
      (m := m) (l := l) hchain
  have hhead' :
      l'.head? = some (collapseToRep X x hx a) := by
    simpa [l'] using collapsePath_head? (X := X) (x := x) (hx := hx) (l := l) (a := a) hhead
  have hlast' :
      l'.getLast? = some (collapseToRep X x hx b) := by
    simpa [l'] using collapsePath_last? (X := X) (x := x) (hx := hx) (l := l) (a := b) hlast
  have hnodup' : l'.Nodup := by
    simp [l', collapsePath, to_path_nodup]
  have hne' :
      collapseToRep X x hx a ≠ collapseToRep X x hx b :=
    collapseToRep_ne_of_not_both_mem (X := X) (x := x) (hx := hx) (a := a) (b := b)
      hne hnot
  have hlen' : 2 ≤ l'.length := by
    exact length_ge_two_of_head_last_ne (l := l') (a := collapseToRep X x hx a)
      (b := collapseToRep X x hx b) hhead' hlast' hne'
  have hmem :
      l' ∈ pathsUpTo (A := {a : A // clonePred X x a})
        (Fintype.card {a : A // clonePred X x a})
        (collapseToRep X x hx a) (collapseToRep X x hx b) :=
    mem_pathsUpTo_of_props (l := l') (a := collapseToRep X x hx a)
      (b := collapseToRep X x hx b) hhead' hlast' hnodup' hlen'
  have hstrength' : m ≤ pathStrength (removeClonesExcept P X x) l' :=
    pathStrength_ge_of_chain (P := removeClonesExcept P X x) (m := m) (l := l') hchain' hlen'
  have hle :
      m ≤ strongestPath (removeClonesExcept P X x)
        (collapseToRep X x hx a) (collapseToRep X x hx b) := by
    exact le_trans hstrength'
      (pathStrength_of_mem_pathsUpTo_le_strongestPath (P := removeClonesExcept P X x)
        (a := collapseToRep X x hx a) (b := collapseToRep X x hx b) (l := l') hmem)
  simpa [hm] using hle

lemma expand_rel_of_rel
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (X : Set A) (x y : A) (hx : x ∈ X) (hy : y ∈ X) (hX : CloneSet P X)
    (m : Int) {a b : {a : A // clonePred X x a}}
    (hrel : m ≤ margin (removeClonesExcept P X x) a b) :
    expandFromRep X x y a = expandFromRep X x y b ∨
      m ≤ margin P (expandFromRep X x y a) (expandFromRep X x y b) := by
  classical
  by_cases ha : (a : A) ∈ X
  · by_cases hb : (b : A) ∈ X
    · left
      simp [expandFromRep, ha, hb]
    · right
      have ha' : (a : A) = x := subtype_val_eq_rep_of_mem (X := X) (x := x) ha
      have hrel' : m ≤ margin P x b := by
        simpa [margin_removeClonesExcept, ha'] using hrel
      have hxy :
          margin P x b = margin P y b := by
        have h := margin_clone_eq_of_cloneSet (P := P) (X := X) hX
          (hx := hx) (hx' := hy) (hy := hb)
        exact h.1
      simpa [expandFromRep, ha, hb, hxy] using hrel'
  · by_cases hb : (b : A) ∈ X
    · right
      have hb' : (b : A) = x := subtype_val_eq_rep_of_mem (X := X) (x := x) hb
      have hrel' : m ≤ margin P a x := by
        simpa [margin_removeClonesExcept, hb'] using hrel
      have hxy :
          margin P a x = margin P a y := by
        have h := margin_clone_eq_of_cloneSet (P := P) (X := X) hX
          (hx := hx) (hx' := hy) (hy := ha)
        exact h.2
      simpa [expandFromRep, ha, hb, hxy] using hrel'
    · right
      have hrel' : m ≤ margin P a b := by
        simpa [margin_removeClonesExcept, ha, hb] using hrel
      simpa [expandFromRep, ha, hb] using hrel'

lemma strongestPath_le_expand
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x y : A) (hx : x ∈ X) (hy : y ∈ X) (hX : CloneSet P X)
    {a b : {a : A // clonePred X x a}} (hne : a ≠ b) :
    strongestPath (removeClonesExcept P X x) a b ≤
      strongestPath P (expandFromRep X x y a) (expandFromRep X x y b) := by
  classical
  have hne_paths :
      (pathsUpTo (A := {a : A // clonePred X x a}) (Fintype.card {a : A // clonePred X x a})
        a b).Nonempty :=
    pathsUpTo_nonempty_of_ne (A := {a : A // clonePred X x a}) a b hne
  rcases exists_max_path_props (P := removeClonesExcept P X x) (a := a) (b := b) hne_paths with
    ⟨l, _hl, hhead, hlast, hnodup, hlen, hstrength⟩
  set m := strongestPath (removeClonesExcept P X x) a b with hm
  have hchain :
      List.IsChain (fun u v => m ≤ margin (removeClonesExcept P X x) u v) l := by
    have hmle : m ≤ pathStrength (removeClonesExcept P X x) l := by
      simp [hm, hstrength]
    exact isChain_of_le_pathStrength (P := removeClonesExcept P X x) (m := m) (l := l) hmle
  have hchain_map :
      List.IsChain (fun u v =>
        u = v ∨ m ≤ margin P u v) (l.map (expandFromRep X x y)) := by
    refine (List.isChain_map_of_isChain
      (R := fun u v => m ≤ margin (removeClonesExcept P X x) u v)
      (S := fun u v => u = v ∨ m ≤ margin P u v)
      (f := expandFromRep X x y) ?_ hchain)
    intro u v hrel
    exact expand_rel_of_rel (P := P) (X := X) (x := x) (y := y) (hx := hx) (hy := hy)
      (hX := hX) (m := m) hrel
  have hnodup_map :
      (l.map (expandFromRep X x y)).Nodup := by
    exact (List.Nodup.map (expandFromRep_injective (X := X) (x := x) (y := y) hy) hnodup)
  have hchain' :
      List.IsChain (fun u v => m ≤ margin P u v) (l.map (expandFromRep X x y)) := by
    exact chain_of_chain_eq_or hchain_map hnodup_map
  have hhead' :
      (l.map (expandFromRep X x y)).head? = some (expandFromRep X x y a) := by
    cases l with
    | nil =>
        simp at hhead
    | cons a' t =>
        simp [List.head?] at hhead
        subst hhead
        simp [List.head?]
  have hlast' :
      (l.map (expandFromRep X x y)).getLast? = some (expandFromRep X x y b) := by
    have hne_l : l ≠ [] := by
      intro hnil
      subst hnil
      simp at hhead
    have hlast_eq : l.getLast hne_l = b := by
      have hlast' := List.getLast?_eq_getLast_of_ne_nil (l := l) hne_l
      have : some (l.getLast hne_l) = some b := by simpa [hlast'] using hlast
      exact Option.some.inj this
    have hmap_ne : (l.map (expandFromRep X x y)) ≠ [] := by
      intro hmap
      exact hne_l (List.map_eq_nil_iff.mp hmap)
    have hmap_last := List.getLast_map (f := expandFromRep X x y) (l := l) (h := hmap_ne)
    have hlast0 :
        (l.map (expandFromRep X x y)).getLast hmap_ne =
          expandFromRep X x y b := by
      have hmap_last' := hmap_last
      rw [hlast_eq] at hmap_last'
      exact hmap_last'
    have hlast? :
        (l.map (expandFromRep X x y)).getLast? =
          some ((l.map (expandFromRep X x y)).getLast hmap_ne) := by
      exact List.getLast?_eq_getLast_of_ne_nil (l := l.map (expandFromRep X x y)) hmap_ne
    simp [hlast0, hlast?]
  have hlen' : 2 ≤ (l.map (expandFromRep X x y)).length := by
    simpa using hlen
  have hmem :
      l.map (expandFromRep X x y) ∈ pathsUpTo (A := A) (Fintype.card A)
        (expandFromRep X x y a) (expandFromRep X x y b) :=
    mem_pathsUpTo_of_props (l := l.map (expandFromRep X x y))
      (a := expandFromRep X x y a) (b := expandFromRep X x y b)
      hhead' hlast' hnodup_map hlen'
  have hstrength' : m ≤ pathStrength P (l.map (expandFromRep X x y)) :=
    pathStrength_ge_of_chain (P := P) (m := m) (l := l.map (expandFromRep X x y))
      hchain' hlen'
  have hle :
      m ≤ strongestPath P (expandFromRep X x y a) (expandFromRep X x y b) := by
    exact le_trans hstrength'
      (pathStrength_of_mem_pathsUpTo_le_strongestPath (P := P)
        (a := expandFromRep X x y a) (b := expandFromRep X x y b)
        (l := l.map (expandFromRep X x y)) hmem)
  simpa [hm] using hle

lemma expandFromRep_self {A : Type} (X : Set A) (x : A) (b : {a : A // clonePred X x a}) :
    expandFromRep X x x b = b.1 := by
  classical
  by_cases hb : (b : A) ∈ X
  · have hb' : (b : A) = x := subtype_val_eq_rep_of_mem (X := X) (x := x) hb
    have hx : x ∈ X := by
      simpa [hb'] using hb
    simp [expandFromRep, hb', hx]
  · simp [expandFromRep, hb]

lemma strongestPath_nonclone_clone_eq
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x y : A) (hx : x ∈ X) (hy : y ∈ X) (hX : CloneSet P X)
    {c : A} (hc : c ∉ X) :
    strongestPath P c y =
      strongestPath (removeClonesExcept P X x)
        (collapseToRep X x hx c) (collapseToRep X x hx y) := by
  classical
  have hne : c ≠ y := by
    intro h
    apply hc
    simpa [h] using hy
  have hle1 :=
    strongestPath_le_collapse (P := P) (X := X) (x := x) (hx := hx) (hX := hX)
      (a := c) (b := y) (hne := hne) (hnot := Or.inl hc)
  have hle2 :=
    strongestPath_le_expand (P := P) (X := X) (x := x) (y := y) (hx := hx) (hy := hy) (hX := hX)
      (a := collapseToRep X x hx c) (b := collapseToRep X x hx y)
      (hne :=
        collapseToRep_ne_of_not_both_mem (X := X) (x := x) (hx := hx)
          (a := c) (b := y) (hne := hne) (hnot := Or.inl hc))
  have hle2' :
      strongestPath (removeClonesExcept P X x)
        (collapseToRep X x hx c) (collapseToRep X x hx y) ≤
        strongestPath P c y := by
    simpa [expandFromRep, collapseToRep, hc, hy, hx] using hle2
  exact le_antisymm hle1 hle2'

lemma strongestPath_clone_nonclone_eq
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x y : A) (hx : x ∈ X) (hy : y ∈ X) (hX : CloneSet P X)
    {c : A} (hc : c ∉ X) :
    strongestPath P y c =
      strongestPath (removeClonesExcept P X x)
        (collapseToRep X x hx y) (collapseToRep X x hx c) := by
  classical
  have hne : y ≠ c := by
    intro h
    apply hc
    simpa [h] using hy
  have hle1 :=
    strongestPath_le_collapse (P := P) (X := X) (x := x) (hx := hx) (hX := hX)
      (a := y) (b := c) (hne := hne) (hnot := Or.inr hc)
  have hle2 :=
    strongestPath_le_expand (P := P) (X := X) (x := x) (y := y) (hx := hx) (hy := hy) (hX := hX)
      (a := collapseToRep X x hx y) (b := collapseToRep X x hx c)
      (hne :=
        collapseToRep_ne_of_not_both_mem (X := X) (x := x) (hx := hx)
          (a := y) (b := c) (hne := hne) (hnot := Or.inr hc))
  have hle2' :
      strongestPath (removeClonesExcept P X x)
        (collapseToRep X x hx y) (collapseToRep X x hx c) ≤
        strongestPath P y c := by
    simpa [expandFromRep, collapseToRep, hc, hy, hx] using hle2
  exact le_antisymm hle1 hle2'

lemma schulzeDefeats_nonclone_clone_iff
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x y : A) (hx : x ∈ X) (hy : y ∈ X) (hX : CloneSet P X)
    {c : A} (hc : c ∉ X) :
    schulzeDefeats P c y ↔
      schulzeDefeats (removeClonesExcept P X x)
        (collapseToRep X x hx c) (collapseToRep X x hx y) := by
  have h1 :=
    strongestPath_nonclone_clone_eq (P := P) (X := X) (x := x) (y := y)
      (hx := hx) (hy := hy) (hX := hX) (c := c) hc
  have h2 :=
    strongestPath_clone_nonclone_eq (P := P) (X := X) (x := x) (y := y)
      (hx := hx) (hy := hy) (hX := hX) (c := c) hc
  dsimp [schulzeDefeats]
  simp [h1, h2]

lemma schulzeDefeats_clone_nonclone_iff
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x y : A) (hx : x ∈ X) (hy : y ∈ X) (hX : CloneSet P X)
    {c : A} (hc : c ∉ X) :
    schulzeDefeats P y c ↔
      schulzeDefeats (removeClonesExcept P X x)
        (collapseToRep X x hx y) (collapseToRep X x hx c) := by
  have h1 :=
    strongestPath_clone_nonclone_eq (P := P) (X := X) (x := x) (y := y)
      (hx := hx) (hy := hy) (hX := hX) (c := c) hc
  have h2 :=
    strongestPath_nonclone_clone_eq (P := P) (X := X) (x := x) (y := y)
      (hx := hx) (hy := hy) (hX := hX) (c := c) hc
  dsimp [schulzeDefeats]
  simp [h1, h2]

lemma schulzeDefeats_nonclone_iff
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x : A) (hx : x ∈ X) (hX : CloneSet P X)
    {c : A} (hc : c ∉ X) (b : {a : A // clonePred X x a}) :
    schulzeDefeats (removeClonesExcept P X x) b ⟨c, Or.inl hc⟩ ↔
      schulzeDefeats P b.1 c := by
  classical
  by_cases hbc : b = (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a})
  · subst hbc
    constructor
    · intro hdef
      exact (schulzeDefeats_ne (P := removeClonesExcept P X x) hdef rfl).elim
    · intro hdef
      exact (schulzeDefeats_ne (P := P) hdef rfl).elim
  · have hbne : b.1 ≠ c := by
      intro h
      apply hbc
      apply Subtype.ext
      simp [h]
    have hle1 :=
      strongestPath_le_collapse (P := P) (X := X) (x := x) (hx := hx) (hX := hX)
        (a := b.1) (b := c) (hne := hbne) (hnot := Or.inr hc)
    have hle1' :
        strongestPath P b.1 c ≤
          strongestPath (removeClonesExcept P X x) b ⟨c, Or.inl hc⟩ := by
      have hb' : collapseToRep X x hx b.1 = b :=
        collapseToRep_subtype_eq (X := X) (x := x) (hx := hx) b
      have hc' :
          collapseToRep X x hx c =
            (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) := by
        simp [collapseToRep, hc]
      simpa [hb', hc'] using hle1
    have hle2 :=
      strongestPath_le_expand (P := P) (X := X) (x := x) (y := x) (hx := hx) (hy := hx) (hX := hX)
        (a := b) (b := (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a})) (hne := hbc)
    have hle2' :
        strongestPath (removeClonesExcept P X x) b ⟨c, Or.inl hc⟩ ≤
          strongestPath P b.1 c := by
      simpa [expandFromRep_self, hc] using hle2
    have h1 : strongestPath P b.1 c =
        strongestPath (removeClonesExcept P X x) b ⟨c, Or.inl hc⟩ :=
      le_antisymm hle1' hle2'
    have hle3 :=
      strongestPath_le_collapse (P := P) (X := X) (x := x) (hx := hx) (hX := hX)
        (a := c) (b := b.1) (hne := hbne.symm) (hnot := Or.inl hc)
    have hle3' :
        strongestPath P c b.1 ≤
          strongestPath (removeClonesExcept P X x) ⟨c, Or.inl hc⟩ b := by
      have hb' : collapseToRep X x hx b.1 = b :=
        collapseToRep_subtype_eq (X := X) (x := x) (hx := hx) b
      have hc' :
          collapseToRep X x hx c =
            (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) := by
        simp [collapseToRep, hc]
      simpa [hb', hc'] using hle3
    have hle4 :=
      strongestPath_le_expand (P := P) (X := X) (x := x) (y := x) (hx := hx) (hy := hx) (hX := hX)
        (a := (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a})) (b := b)
        (hne := by
          intro h
          exact hbc h.symm)
    have hle4' :
        strongestPath (removeClonesExcept P X x) ⟨c, Or.inl hc⟩ b ≤
          strongestPath P c b.1 := by
      simpa [expandFromRep_self, hc] using hle4
    have h2 : strongestPath P c b.1 =
        strongestPath (removeClonesExcept P X x) ⟨c, Or.inl hc⟩ b :=
      le_antisymm hle3' hle4'
    dsimp [schulzeDefeats]
    simp [h1, h2]

/-! ## Independence of clones for Schulze -/

def schulze_clone_independence_props
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (X : Set A) (x : A) : Prop :=
  (∀ c (hc : c ∉ X),
      (c ∈ schulze P ↔
        (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) ∈
          schulze (removeClonesExcept P X x))) ∧
  ((∃ y, y ∈ X ∧ y ∈ schulze P) ↔
    (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) ∈
      schulze (removeClonesExcept P X x))

theorem schulze_independence_of_clones : IndependenceOfClones schulze := by
  unfold IndependenceOfClones
  intro V A instV instA instDecEq P X x hX hx
  classical
  constructor
  · intro c hc
    constructor
    · intro hcwin
      have hcond : ∀ b, ¬ schulzeDefeats P b c := (Finset.mem_filter.mp hcwin).2
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_univ _, ?_⟩
      intro b hdef
      have hdef' : schulzeDefeats P b.1 c :=
        (schulzeDefeats_nonclone_iff (P := P) (X := X) (x := x) (hx := hx)
            (hX := hX) (hc := hc) b).1 hdef
      exact (hcond b.1) hdef'
    · intro hcwin
      have hcond :
          ∀ b : {a : A // clonePred X x a},
            ¬ schulzeDefeats (removeClonesExcept P X x) b ⟨c, Or.inl hc⟩ :=
        (Finset.mem_filter.mp hcwin).2
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_univ _, ?_⟩
      intro a hdef
      by_cases ha : a ∈ X
      · have hdef' :
            schulzeDefeats (removeClonesExcept P X x)
              (collapseToRep X x hx a) (collapseToRep X x hx c) :=
          (schulzeDefeats_clone_nonclone_iff (P := P) (X := X) (x := x) (y := a)
              (hx := hx) (hy := ha) (hX := hX) (c := c) hc).1 hdef
        have hdef'' :
            schulzeDefeats (removeClonesExcept P X x)
              (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a})
              (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) := by
          simpa [collapseToRep, ha, hc] using hdef'
        exact (hcond _ ) hdef''
      · have hdef' :
            schulzeDefeats (removeClonesExcept P X x)
              (⟨a, Or.inl ha⟩ : {a : A // clonePred X x a})
              (⟨c, Or.inl hc⟩ : {a : A // clonePred X x a}) :=
          (schulzeDefeats_nonclone_iff (P := P) (X := X) (x := x) (hx := hx)
              (hX := hX) (hc := hc)
              (b := (⟨a, Or.inl ha⟩ : {a : A // clonePred X x a}))).2 hdef
        exact (hcond _ ) hdef'
  · constructor
    · intro hwin
      rcases hwin with ⟨y, hy, hywin⟩
      have hycond : ∀ b, ¬ schulzeDefeats P b y := (Finset.mem_filter.mp hywin).2
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_univ _, ?_⟩
      intro b hdef
      by_cases hb : (b : A) ∈ X
      · have hb' : (b : A) = x := subtype_val_eq_rep_of_mem (X := X) (x := x) hb
        have hb'' : b = (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := by
          apply Subtype.ext
          exact hb'
        exact (schulzeDefeats_ne (P := removeClonesExcept P X x) hdef) hb''
      · have hdef' : schulzeDefeats P b.1 y :=
          (schulzeDefeats_nonclone_clone_iff (P := P) (X := X) (x := x) (y := y)
              (hx := hx) (hy := hy) (hX := hX) (c := b.1) hb).2
            (by
              simpa [collapseToRep, hb, hy] using hdef)
        exact (hycond b.1) hdef'
    · intro hrep
      have hcond :
          ∀ b : {a : A // clonePred X x a},
            ¬ schulzeDefeats (removeClonesExcept P X x) b ⟨x, Or.inr rfl⟩ :=
        (Finset.mem_filter.mp hrep).2
      have hXne : X.Nonempty := hX.1
      let s : Finset A := Finset.univ.filter (fun a => a ∈ X)
      have hs : s.Nonempty := by
        rcases hXne with ⟨y, hy⟩
        refine ⟨y, ?_⟩
        simp [s, hy]
      rcases exists_schulze_maximal (P := P) (s := s) hs with ⟨y, hy_s, hy_max⟩
      have hy : y ∈ X := by
        simpa [s] using (Finset.mem_filter.mp hy_s).2
      refine ⟨y, hy, ?_⟩
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_univ _, ?_⟩
      intro b hdef
      by_cases hb : b ∈ X
      · have hb_s : b ∈ s := by
          simp [s, hb]
        exact (hy_max b hb_s) hdef
      · have hdef' :
            schulzeDefeats (removeClonesExcept P X x)
              (collapseToRep X x hx b) (collapseToRep X x hx y) :=
          (schulzeDefeats_nonclone_clone_iff (P := P) (X := X) (x := x) (y := y)
              (hx := hx) (hy := hy) (hX := hX) (c := b) hb).1 hdef
        have hb' :
            collapseToRep X x hx b =
              (⟨b, Or.inl hb⟩ : {a : A // clonePred X x a}) := by
          simp [collapseToRep, hb]
        have hy' :
            collapseToRep X x hx y =
              (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := by
          simp [collapseToRep, hy]
        have hdef'' :
            schulzeDefeats (removeClonesExcept P X x)
              (⟨b, Or.inl hb⟩ : {a : A // clonePred X x a})
              (⟨x, Or.inr rfl⟩ : {a : A // clonePred X x a}) := by
          simpa [hb', hy'] using hdef'
        exact (hcond _ ) hdef''

end SocialChoice
