import Mathlib.Data.List.Basic
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Rotate
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Fintype.EquivFin

namespace SocialChoice

def cycle {X : Type} (P : X -> X -> Prop) (c : List X) : Prop :=
  ∃ h : c ≠ [], List.IsChain P (List.getLast c h :: c)

def acyclic {X : Type} (P : X -> X -> Prop) : Prop :=
  ∀ c : List X, ¬ cycle P c

def reverse_rel {X : Type} (P : X -> X -> Prop) : X -> X -> Prop :=
  fun x y => P y x

theorem length_cycle_pos {X : Type} {P : X -> X -> Prop} {c : List X}
    (hc : cycle P c) : 0 < c.length := by
  rcases hc with ⟨h, _⟩
  exact List.length_pos_of_ne_nil h

theorem rotate'_ne_nil_of_ne_nil {X : Type} {l : List X} {n : Nat} :
    l ≠ [] -> l.rotate' n ≠ [] := by
  intro h hrot
  have hlen : l.length = 0 := by
    have hlenRot : (l.rotate' n).length = 0 := by simp [hrot]
    simpa [List.length_rotate'] using hlenRot
  exact h (List.length_eq_zero_iff.mp hlen)

theorem rotate1_cycle_of_cycle {X : Type} {a : X} {l : List X} {P : X -> X -> Prop} :
    cycle P (a :: l) -> cycle P (l ++ [a]) := by
  intro hc
  rcases hc with ⟨hne, hchain⟩
  have hne' : l ++ [a] ≠ [] :=
    List.append_ne_nil_of_right_ne_nil l (List.cons_ne_nil a [])
  have hchain_tail : List.IsChain P (a :: l) :=
    hchain.tail
  have hchain_singleton : List.IsChain P ([a] : List X) := by
    exact (List.isChain_singleton (R := P) a)
  have hrel :
      ∀ x ∈ (a :: l).getLast?, ∀ y ∈ ([a] : List X).head?, P x y := by
    intro x hx y hy
    obtain ⟨hxl, hxEq⟩ := List.mem_getLast?_eq_getLast (l := a :: l) (x := x) hx
    have hyEq : y = a := by
      have hyEq' : a = y := by simpa using hy
      exact hyEq'.symm
    cases hyEq
    have hrel' : P (List.getLast (a :: l) hne) a :=
      List.IsChain.rel_head hchain
    have hxEq' : x = List.getLast (a :: l) hne := by
      calc
        x = List.getLast (a :: l) hxl := hxEq
        _ = List.getLast (a :: l) hne := by
          exact List.getLast_congr hxl hne rfl
    subst hxEq'
    exact hrel'
  have hchain_append : List.IsChain P (a :: l ++ [a]) := by
    have hchain' : List.IsChain P ((a :: l) ++ [a]) :=
      List.IsChain.append hchain_tail hchain_singleton hrel
    simpa using hchain'
  refine ⟨hne', ?_⟩
  have h0 : l ++ [a] ≠ [] :=
    List.append_ne_nil_of_right_ne_nil l (List.cons_ne_nil a [])
  have hlast0 : List.getLast (l ++ [a]) h0 = a := by
    simp
  have hlast : List.getLast (l ++ [a]) hne' = a :=
    (List.getLast_congr hne' h0 rfl).trans hlast0
  simpa [hlast] using hchain_append

theorem rotate'_cycle_of_cycle {X : Type} {c : List X} {P : X -> X -> Prop} {n : Nat} :
    cycle P c -> cycle P (List.rotate' c n) := by
  intro cy
  induction n with
  | zero =>
      simpa using cy
  | succ n ih =>
      rcases ih with ⟨hne, hchain⟩
      have ih' : cycle P (List.rotate' c n) := ⟨hne, hchain⟩
      obtain ⟨a, l, hcons⟩ := List.exists_cons_of_ne_nil hne
      have ih'' : cycle P (a :: l) := by
        simpa [hcons] using ih'
      have hrot : List.rotate' c (Nat.succ n) = l ++ [a] := by
        calc
          List.rotate' c (Nat.succ n) = (List.rotate' c n).rotate' 1 := by
            symm
            simpa using (List.rotate'_rotate' c n 1)
          _ = (a :: l).rotate' 1 := by
            simp [hcons]
          _ = l ++ [a] := by
            simp
      have hcycle : cycle P (l ++ [a]) :=
        rotate1_cycle_of_cycle ih''
      simpa [hrot] using hcycle

lemma getLast_reverse_eq_head {X : Type} {c : List X} (hne : c ≠ []) :
    List.getLast c.reverse (by
        intro hnil
        exact hne (List.reverse_eq_nil_iff.mp hnil)) = c.head hne := by
  cases c with
  | nil => cases hne rfl
  | cons a t =>
      simp [List.reverse_cons]

lemma getLast_map {α β : Type} (f : α → β) {l : List α} (hne : l ≠ []) :
    List.getLast (l.map f) (by
        intro hnil
        cases l with
        | nil => cases hne rfl
        | cons a t => cases hnil) = f (List.getLast l hne) := by
  induction l with
  | nil => cases hne rfl
  | cons a t ih =>
      cases t with
      | nil => simp
      | cons b t =>
          have htne : b :: t ≠ [] := by simp
          have hmap_ne : List.map f (b :: t) ≠ [] := by simp
          calc
            List.getLast (List.map f (a :: b :: t)) (by
                intro hnil
                cases hnil) =
                List.getLast (List.map f (b :: t)) hmap_ne := by
                  simp [List.getLast_cons]
            _ = f (List.getLast (b :: t) htne) := by
                  simpa using (ih htne)
            _ = f (List.getLast (a :: b :: t) (by simp)) := by
                  simp [List.getLast_cons]

lemma cycle_map {α β : Type} {P : β → β → Prop} {f : α → β} {c : List α} :
    cycle (fun a b => P (f a) (f b)) c → cycle P (c.map f) := by
  intro hcyc
  rcases hcyc with ⟨hne, hchain⟩
  have hne' : c.map f ≠ [] := by
    intro hnil
    cases c with
    | nil => exact hne rfl
    | cons a t => cases hnil
  have hchain' :
      List.IsChain P (List.getLast (c.map f) hne' :: c.map f) := by
    have hchain_map : List.IsChain P ((List.getLast c hne :: c).map f) := by
      exact (List.isChain_map (R := P) (f := f) (l := List.getLast c hne :: c)).2 hchain
    simpa [getLast_map (f := f) (l := c) (hne := hne)] using hchain_map
  exact ⟨hne', hchain'⟩

lemma cycle_reverse_rel {X : Type} {P : X → X → Prop} {c : List X} :
    cycle P c → cycle (reverse_rel P) c.reverse := by
  intro hcyc
  rcases hcyc with ⟨hne, hchain⟩
  have hne' : c.reverse ≠ [] := by
    intro hnil
    have : c = [] := by
      simpa using (List.reverse_eq_nil_iff.mp hnil)
    exact hne this
  refine ⟨hne', ?_⟩
  have hchain_tail : c.IsChain P := hchain.tail
  have hchain_singleton : ([c.head hne] : List X).IsChain P := by
    exact (List.isChain_singleton (R := P) (c.head hne))
  have hrel : ∀ x ∈ c.getLast?, ∀ y ∈ ([c.head hne] : List X).head?, P x y := by
    intro x hx y hy
    obtain ⟨hx', hxEq⟩ := List.mem_getLast?_eq_getLast (l := c) (x := x) hx
    have hyEq : y = c.head hne := by
      simpa [eq_comm] using hy
    subst hxEq
    subst hyEq
    have hy' : c.head hne ∈ c.head? := by
      cases c with
      | nil => cases hne rfl
      | cons a t => simp
    exact (List.IsChain.rel_head? (R := P) (x := List.getLast c hne) (l := c) hchain hy')
  have hchain_app : (c ++ [c.head hne]).IsChain P :=
    List.IsChain.append hchain_tail hchain_singleton hrel
  have hchain_rev : (List.getLast c.reverse hne' :: c.reverse).reverse.IsChain P := by
    simpa [getLast_reverse_eq_head (c := c) hne] using hchain_app
  have hchain_final : (List.getLast c.reverse hne' :: c.reverse).IsChain (reverse_rel P) := by
    change List.IsChain (fun a b => P b a) (List.getLast c.reverse hne' :: c.reverse)
    exact (List.isChain_reverse (l := List.getLast c.reverse hne' :: c.reverse) (R := P)).1
      hchain_rev
  simpa using hchain_final

lemma getLast_iterate_succ {α : Type} (f : α → α) (a : α) (n : Nat) :
    List.getLast (List.iterate f a (n + 1)) (by simp) = Nat.iterate f n a := by
  induction n generalizing a with
  | zero =>
      simp [List.iterate]
  | succ n ih =>
      have htail : List.iterate f (f a) (n + 1) ≠ [] := by simp
      calc
        List.getLast (List.iterate f a (n + 2)) (by simp) =
            List.getLast (List.iterate f (f a) (n + 1)) htail := by
              simp [List.iterate, List.getLast_cons]
        _ = Nat.iterate f n (f a) := by
              simpa using (ih (a := f a))
        _ = Nat.iterate f (n + 1) a := by
              simp [Function.iterate_succ_apply]

lemma isChain_iterate_reverse_rel {α : Type} (R : α → α → Prop) (f : α → α)
    (h : ∀ a, R (f a) a) :
    ∀ n a, List.IsChain (reverse_rel R) (List.iterate f a n)
  | 0, a => by
      simp [List.iterate]
  | n + 1, a => by
      cases n with
      | zero =>
          simp [List.iterate]
      | succ n =>
          have htail :
              List.IsChain (reverse_rel R) (f a :: List.iterate f (f (f a)) n) := by
            simpa [List.iterate] using
              (isChain_iterate_reverse_rel (R := R) (f := f) (h := h)
                (n := Nat.succ n) (a := f a))
          exact (List.isChain_cons_cons).2 ⟨by simpa [reverse_rel] using h a, htail⟩

theorem dominates_of_cycle_index {X : Type} (l : List X) (P : X -> X -> Prop)
    (c : cycle P l) (i : Nat) (hi : i < l.length)
    (hmod : (i + 1) % l.length < l.length) :
    P (l[i]'hi) (l[(i + 1) % l.length]'hmod) := by
  rcases c with ⟨hne, hchain⟩
  have hlen : 0 < l.length := List.length_pos_of_ne_nil hne
  by_cases hlast : i = l.length - 1
  · have hsucc : l.length - 1 + 1 = l.length := by
      have hpred := Nat.succ_pred_eq_of_pos hlen
      simpa [Nat.succ_eq_add_one, Nat.pred_eq_sub_one] using hpred
    have hpred : l.length - 1 < l.length := by
      have : l.length - 1 < l.length - 1 + 1 := Nat.lt_succ_self _
      simpa [hsucc] using this
    have hfin : (⟨i, hi⟩ : Fin l.length) = ⟨l.length - 1, hpred⟩ := by
      apply Fin.ext
      exact hlast
    have hleft : l[i]'hi = List.getLast l hne := by
      change l.get ⟨i, hi⟩ = List.getLast l hne
      calc
        l.get ⟨i, hi⟩ = l.get ⟨l.length - 1, hpred⟩ := by
          simp [hfin]
        _ = List.getLast l (by
              intro hnil
              simp [hnil] at hpred) := by
          simpa using (List.get_length_sub_one (l := l) hpred)
        _ = List.getLast l hne := by
          exact List.getLast_congr _ _ rfl
    have hmod0 : (i + 1) % l.length = 0 := by
      subst hlast
      simp [hsucc]
    have hright : l[(i + 1) % l.length]'hmod = l[0]'hlen := by
      change l.get ⟨(i + 1) % l.length, hmod⟩ = l.get ⟨0, hlen⟩
      apply congrArg (fun j => l.get j)
      apply Fin.ext
      simp [hmod0]
    have hrel : P (List.getLast l hne) (l.get ⟨0, hlen⟩) := by
      obtain ⟨b, l', rfl⟩ := List.exists_cons_of_ne_nil hne
      have hrel' : P (List.getLast (b :: l') (by simp)) b := by
        simpa using (List.IsChain.rel_head hchain)
      simpa using hrel'
    simpa [hleft, hright] using hrel
  · have hle : i + 1 ≤ l.length := Nat.succ_le_of_lt hi
    have hne : i + 1 ≠ l.length := by
      intro hEq
      have hsucc : l.length - 1 + 1 = l.length := by
        have hpred := Nat.succ_pred_eq_of_pos hlen
        simpa [Nat.succ_eq_add_one, Nat.pred_eq_sub_one] using hpred
      have hEq' : i + 1 = l.length - 1 + 1 := by simpa [hsucc] using hEq
      have : i = l.length - 1 := Nat.add_right_cancel hEq'
      exact hlast this
    have hlt : i + 1 < l.length := lt_of_le_of_ne hle hne
    have hmodEq : (i + 1) % l.length = i + 1 := Nat.mod_eq_of_lt hlt
    have hchain_tail : List.IsChain P l := hchain.tail
    have hrel : P l[i] l[i + 1] := by
      exact (List.isChain_iff_getElem).1 hchain_tail i hlt
    convert hrel

theorem dominate_of_cycle {X : Type} (l : List X) (P : X -> X -> Prop) (c : cycle P l) :
    ∀ x ∈ l, ∃ y ∈ l, P y x := by
  intro x hx
  have hx' : ∃ (i : Fin l.length), l.get i = x := by
    have hx'' : ∃ z ∈ l, z = x := ⟨x, hx, rfl⟩
    simpa using (List.exists_mem_iff_get (l := l) (p := fun z => z = x)).1 hx''
  rcases hx' with ⟨i, rfl⟩
  have hlen : 0 < l.length := length_cycle_pos c
  by_cases hzero : i.val = 0
  · rcases c with ⟨hne, hchain⟩
    have hrel : P (List.getLast l hne) (l.get ⟨0, hlen⟩) := by
      obtain ⟨b, l', rfl⟩ := List.exists_cons_of_ne_nil hne
      have hrel' : P (List.getLast (b :: l') (by simp)) b := by
        exact (List.IsChain.rel_head hchain)
      simp [hrel']
    refine ⟨List.getLast l hne, ?_, ?_⟩
    · exact List.getLast_mem hne
    · have hi : i = ⟨0, hlen⟩ := by
        apply Fin.ext
        simpa using hzero
      simpa [hi] using hrel
  · have hlt : i.val - 1 + 1 < l.length := by
      have hlt' : i.val < l.length := i.isLt
      have hpos : 0 < i.val := Nat.pos_of_ne_zero hzero
      have : i.val - 1 + 1 = i.val := by
        simpa [Nat.succ_eq_add_one, Nat.pred_eq_sub_one] using
          (Nat.succ_pred_eq_of_pos hpos)
      simp [this, hlt']
    have hmod : (i.val - 1 + 1) % l.length < l.length :=
      Nat.mod_lt _ hlen
    have hrel :=
      dominates_of_cycle_index l P c (i.val - 1) (by
        have hpos : 0 < i.val := Nat.pos_of_ne_zero hzero
        have : i.val - 1 < i.val := Nat.sub_lt (Nat.succ_le_of_lt hpos) (by simp)
        exact lt_of_lt_of_le this (Nat.le_of_lt i.isLt)) hmod
    refine ⟨l.get ⟨i.val - 1, ?_⟩, ?_, ?_⟩
    · have hpos : 0 < i.val := Nat.pos_of_ne_zero hzero
      have : i.val - 1 < i.val := Nat.sub_lt (Nat.succ_le_of_lt hpos) (by simp)
      exact lt_of_lt_of_le this (Nat.le_of_lt i.isLt)
    · exact List.get_mem _ _
    · have hmodEq : (i.val - 1 + 1) % l.length = i.val := by
        have hpos : 0 < i.val := Nat.pos_of_ne_zero hzero
        have hlt' : i.val < l.length := i.isLt
        have hstep : i.val - 1 + 1 = i.val := by
          simpa [Nat.succ_eq_add_one, Nat.pred_eq_sub_one] using
            (Nat.succ_pred_eq_of_pos hpos)
        have hlt'' : i.val - 1 + 1 < l.length := by
          simp [hstep, hlt']
        calc
          (i.val - 1 + 1) % l.length = i.val - 1 + 1 := Nat.mod_eq_of_lt hlt''
          _ = i.val := hstep
      have hrel' := hrel
      simp [hmodEq] at hrel'
      exact hrel'

section ToPath

variable {X : Type} [DecidableEq X]

def to_path : List X → List X
  | [] => []
  | u :: p =>
      if List.idxOf u (to_path p) < (to_path p).length then
        (to_path p).drop (List.idxOf u (to_path p))
      else
        u :: to_path p

omit [DecidableEq X] in
theorem nodup_drop_of_nodup {l : List X} {n : ℕ} : l.Nodup → (l.drop n).Nodup := by
  intro h
  exact List.Nodup.sublist (List.drop_sublist n l) h

theorem to_path_nodup (l : List X) : (to_path l).Nodup := by
  induction l with
  | nil =>
      simp [to_path]
  | cons a l ih =>
      by_cases h : List.idxOf a (to_path l) < (to_path l).length
      · simpa [to_path, h] using (nodup_drop_of_nodup (l := to_path l)
          (n := List.idxOf a (to_path l)) ih)
      · have hnot : a ∉ to_path l := by
          intro hmem
          exact h (List.idxOf_lt_length_iff.2 hmem)
        simp [to_path, List.nodup_cons, hnot, ih]

theorem to_path_eq_nil_iff (l : List X) : to_path l = [] ↔ l = [] := by
  cases l with
  | nil =>
      simp [to_path]
  | cons a l =>
      constructor
      · intro h
        have hpos : 0 < (to_path (a :: l)).length := by
          by_cases h' : List.idxOf a (to_path l) < (to_path l).length
          · have hpos' : 0 < (to_path l).length - List.idxOf a (to_path l) :=
              Nat.sub_pos_of_lt h'
            simpa [to_path, h', List.length_drop] using hpos'
          · simp [to_path, h']
        have hne : to_path (a :: l) ≠ [] :=
          List.length_pos_iff_ne_nil.mp hpos
        exact (hne h).elim
      · intro h
        cases h

theorem to_path_ne_nil_iff (l : List X) (h : l ≠ []) : to_path l ≠ [] := by
  intro htp
  have : l = [] := (to_path_eq_nil_iff l).1 htp
  exact h this

theorem to_path_length_pos (l : List X) (h : l ≠ []) : 0 < (to_path l).length := by
  exact List.length_pos_of_ne_nil (to_path_ne_nil_iff l h)

omit [DecidableEq X] in
theorem getElem_drop_zero {l : List X} {n : Nat} (h : n < l.length) :
    (l.drop n)[0]'(by
      have : 0 < l.length - n := Nat.sub_pos_of_lt h
      simpa [List.length_drop] using this) = l[n]'h := by
  induction l generalizing n with
  | nil =>
      cases h
  | cons a l ih =>
      cases n with
      | zero =>
          simp
      | succ n =>
          have h' : n < l.length := by
            simpa using h
          simp [ih (n := n) h']

theorem to_path_first_elem (l : List X) (h : l ≠ []) :
    (to_path l)[0]'(to_path_length_pos l h) = l[0]'(List.length_pos_of_ne_nil h) := by
  cases l with
  | nil =>
      cases h rfl
  | cons a l =>
      by_cases h' : List.idxOf a (to_path l) < (to_path l).length
      · have hlen : 0 < (to_path l).length - List.idxOf a (to_path l) :=
          Nat.sub_pos_of_lt h'
        have hhead :
            ((to_path l).drop (List.idxOf a (to_path l)))[0]'
              (by simpa [List.length_drop] using hlen) = a := by
          calc
            ((to_path l).drop (List.idxOf a (to_path l)))[0]'
                (by simpa [List.length_drop] using hlen)
                = (to_path l)[List.idxOf a (to_path l)]'h' := by
                    exact (getElem_drop_zero (l := to_path l)
                      (n := List.idxOf a (to_path l)) h')
            _ = a := by
              exact (List.getElem_idxOf (xs := to_path l) (x := a) h')
        simp [to_path, h', hhead]
      · simp [to_path, h']

omit [DecidableEq X] in
theorem getLast_drop {l : List X} {n : Nat} (h : n < l.length) :
    List.getLast (l.drop n) (by
      have : 0 < l.length - n := Nat.sub_pos_of_lt h
      exact List.length_pos_iff_ne_nil.mp (by simpa [List.length_drop] using this)) =
      List.getLast l (by
        exact List.length_pos_iff_ne_nil.mp (lt_of_le_of_lt (Nat.zero_le _) h)) := by
  have hdrop : l.drop n ≠ [] := by
    apply List.length_pos_iff_ne_nil.mp
    have : 0 < l.length - n := Nat.sub_pos_of_lt h
    simpa [List.length_drop] using this
  have hne : l ≠ [] := by
    apply List.length_pos_iff_ne_nil.mp
    exact lt_of_le_of_lt (Nat.zero_le _) h
  have hlast :
      List.getLast (l.take n ++ l.drop n)
        (List.append_ne_nil_of_right_ne_nil _ hdrop) = List.getLast (l.drop n) hdrop :=
    List.getLast_append_of_right_ne_nil (l₁ := l.take n) (l₂ := l.drop n) hdrop
  simp

theorem to_path_last_elem (l : List X) (h : l ≠ []) :
    (to_path l).getLast (to_path_ne_nil_iff l h) = l.getLast h := by
  induction l with
  | nil =>
      cases h rfl
  | cons a l ih =>
      cases l with
      | nil =>
          simp [to_path]
      | cons b t =>
          have hpath :
              to_path (a :: b :: t) =
                if List.idxOf a (to_path (b :: t)) < (to_path (b :: t)).length then
                  (to_path (b :: t)).drop (List.idxOf a (to_path (b :: t)))
                else
                  a :: to_path (b :: t) := by
            rfl
          have hl : b :: t ≠ [] := by simp
          have htp : to_path (b :: t) ≠ [] :=
            to_path_ne_nil_iff (b :: t) hl
          by_cases h' : List.idxOf a (to_path (b :: t)) < (to_path (b :: t)).length
          · have hdrop :
              List.getLast ((to_path (b :: t)).drop (List.idxOf a (to_path (b :: t))))
                (by
                  have : 0 < (to_path (b :: t)).length - List.idxOf a (to_path (b :: t)) :=
                    Nat.sub_pos_of_lt h'
                  exact List.length_pos_iff_ne_nil.mp (by simpa [List.length_drop] using this)) =
                List.getLast (to_path (b :: t)) htp := by
              exact (getLast_drop (l := to_path (b :: t))
                (n := List.idxOf a (to_path (b :: t))) h')
            have ih' : List.getLast (to_path (b :: t)) htp = List.getLast (b :: t) hl := by
              exact (ih (h := hl))
            have hpath' :
                to_path (a :: b :: t) =
                  (to_path (b :: t)).drop (List.idxOf a (to_path (b :: t))) := by
              simp [hpath, h']
            calc
              (to_path (a :: b :: t)).getLast
                    (to_path_ne_nil_iff (a :: b :: t) (by simp)) =
                  List.getLast (to_path (b :: t)) htp := by
                    simp [hpath', hdrop]
              _ = List.getLast (b :: t) hl := ih'
              _ = List.getLast (a :: b :: t) (by simp) := by
                    simp [List.getLast_cons]
          · have ih' : List.getLast (to_path (b :: t)) htp = List.getLast (b :: t) hl := by
              exact (ih (h := hl))
            have hpath' : to_path (a :: b :: t) = a :: to_path (b :: t) := by
              simp [hpath, h']
            calc
              (to_path (a :: b :: t)).getLast
                    (to_path_ne_nil_iff (a :: b :: t) (by simp)) =
                  List.getLast (to_path (b :: t)) htp := by
                    simp [hpath', htp]
              _ = List.getLast (b :: t) hl := ih'
              _ = List.getLast (a :: b :: t) (by simp) := by
                    simp [List.getLast_cons]

omit [DecidableEq X] in
theorem drop_chain'_of_chain' {P : X → X → Prop} {l : List X} {n : ℕ} :
    List.IsChain P l → List.IsChain P (l.drop n) := by
  intro h
  exact (List.IsChain.drop (l := l) (n := n) h)

theorem to_path_chain'_of_chain' {P : X → X → Prop} {l : List X} :
    List.IsChain P l → List.IsChain P (to_path l) := by
  intro hchain
  induction l with
  | nil =>
      simp [to_path]
  | cons a l ih =>
      by_cases h' : List.idxOf a (to_path l) < (to_path l).length
      · have htail : List.IsChain P l := hchain.tail
        have hpath : List.IsChain P (to_path l) := ih htail
        have hdrop := drop_chain'_of_chain' (l := to_path l)
          (n := List.idxOf a (to_path l)) hpath
        simp [to_path, h', hdrop]
      · cases l with
        | nil =>
            simp [to_path]
        | cons b t =>
            have hpath_eq :
                to_path (a :: b :: t) =
                  if List.idxOf a (to_path (b :: t)) < (to_path (b :: t)).length then
                    (to_path (b :: t)).drop (List.idxOf a (to_path (b :: t)))
                  else
                    a :: to_path (b :: t) := by
              rfl
            have htail : List.IsChain P (b :: t) := hchain.tail
            have hpath : List.IsChain P (to_path (b :: t)) := ih htail
            have htp : to_path (b :: t) ≠ [] := by
              exact to_path_ne_nil_iff (b :: t) (by simp)
            have hhead : (to_path (b :: t)).head htp = b := by
              have hfirst := to_path_first_elem (l := b :: t) (h := by simp)
              simp [List.head_eq_getElem_zero, hfirst]
            have hab : P a b := by
              exact (List.IsChain.rel_head hchain)
            have hrel : P a ((to_path (b :: t)).head htp) := by
              simp [hhead, hab]
            have hpath' : to_path (a :: b :: t) = a :: to_path (b :: t) := by
              simp [hpath_eq, h']
            have hcons := List.IsChain.cons_of_ne_nil htp hpath hrel
            simp [hpath', hcons]

theorem rotate'_eq_nil_iff (X : Type) (l : List X) (n : ℕ) : l.rotate' n = [] ↔ l = [] := by
  constructor
  · intro h
    have hlen : (l.rotate' n).length = 0 := by simp [h]
    have : l.length = 0 := by
      simpa [List.length_rotate'] using hlen
    exact List.length_eq_zero_iff.mp this
  · intro h
    cases h
    simp

theorem cycle_of_cycle_imp {X : Type} {l : List X} {p₁ p₂ : X → X → Prop}
    (e : ∀ x y, p₁ x y → p₂ x y) : cycle p₁ l → cycle p₂ l := by
  intro c
  rcases c with ⟨hne, hchain⟩
  refine ⟨hne, ?_⟩
  exact hchain.imp (by intro x y h; exact e x y h)

theorem chain'_take_of_chain {X : Type} {l : List X} {P : X → X → Prop}
    (a : l ≠ []) {n : ℕ} (c : List.IsChain P (l.getLast a :: l)) :
    List.IsChain P (l.take n) := by
  simpa using (List.IsChain.take (l := l) (n := n) c.tail)

lemma getLast_take_idxOf {X : Type} [DecidableEq X] {l : List X} {a : X} (ha : a ∈ l) :
    List.getLast (l.take (List.idxOf a l + 1))
      (by
        have hidx : List.idxOf a l < l.length := List.idxOf_lt_length_iff.2 ha
        have hle : List.idxOf a l + 1 ≤ l.length := Nat.succ_le_of_lt hidx
        have hlen : (l.take (List.idxOf a l + 1)).length = List.idxOf a l + 1 := by
          exact (List.length_take_of_le (l := l) (i := List.idxOf a l + 1) hle)
        have hpos : 0 < (l.take (List.idxOf a l + 1)).length := by
          simp [hlen]
        exact List.length_pos_iff_ne_nil.mp hpos) = a := by
  classical
  have hidx : List.idxOf a l < l.length := List.idxOf_lt_length_iff.2 ha
  have htake :
      l.take (List.idxOf a l + 1) =
        l.take (List.idxOf a l) ++ [l[List.idxOf a l]] := by
    symm
    exact List.take_concat_get' (l := l) (i := List.idxOf a l) hidx
  have hne' :
      l.take (List.idxOf a l) ++ [l[List.idxOf a l]] ≠ [] :=
    List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
  have hne :
      l.take (List.idxOf a l + 1) ≠ [] := by
    simp [htake]
  have hlast' :
      List.getLast (l.take (List.idxOf a l) ++ [l[List.idxOf a l]]) hne' =
        l[List.idxOf a l] := by
    simp
  have hlast :
      List.getLast (l.take (List.idxOf a l + 1)) hne = l[List.idxOf a l] := by
    simp [htake]
  have hx : l[List.idxOf a l]'hidx = a := by
    exact (List.getElem_idxOf (xs := l) (x := a) hidx)
  have hx' : l[List.idxOf a l] = a := by
    simp [hx]
  simp [hx', hlast]

end ToPath

lemma cycle_of_forall_defeater {X : Type} [Fintype X]
    {R : X → X → Prop} (x0 : X) (hdef : ∀ x, ∃ y, R y x) :
    ∃ c : List X, cycle R c := by
  classical
  choose s hs using hdef
  let seq : ℕ → X := fun n => Nat.iterate s n x0
  have hni : ¬ Function.Injective seq := not_injective_infinite_finite seq
  rcases (Function.not_injective_iff.1 hni) with ⟨i, j, hEq, hij⟩
  cases lt_or_gt_of_ne hij with
  | inl hlt =>
      have hmpos : 0 < j - i := Nat.sub_pos_of_lt hlt
      let m := j - i
      let a0 : X := seq i
      have hperiod : Nat.iterate s m a0 = a0 := by
        have hsum : i + m = j := Nat.add_sub_of_le (Nat.le_of_lt hlt)
        have hEq' : Nat.iterate s i x0 = Nat.iterate s j x0 := by
          simpa [seq] using hEq
        have hiter : Nat.iterate s (i + m) x0 = Nat.iterate s i x0 := by
          simpa [hsum] using hEq'.symm
        have hiter' : Nat.iterate s m a0 = Nat.iterate s (m + i) x0 := by
          simpa [a0, seq] using (Function.iterate_add_apply s m i x0).symm
        calc
          Nat.iterate s m a0 = Nat.iterate s (m + i) x0 := hiter'
          _ = Nat.iterate s (i + m) x0 := by simp [Nat.add_comm]
          _ = Nat.iterate s i x0 := hiter
          _ = a0 := by simp [a0, seq]
      have hmne : m ≠ 0 := Nat.ne_of_gt hmpos
      obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hmne
      let l : List X := List.iterate s a0 (Nat.succ m')
      have hlne : l ≠ [] := by
        simp [l]
      have hchain_l :
          l.IsChain (reverse_rel R) := by
        simpa [l] using
          (isChain_iterate_reverse_rel (R := R) (f := s) (h := hs)
            (n := Nat.succ m') (a := a0))
      have hrel :
          ∀ x ∈ l.getLast?, ∀ y ∈ ([a0] : List X).head?,
            reverse_rel R x y := by
        intro x hx y hy
        obtain ⟨hx', hxEq⟩ := List.mem_getLast?_eq_getLast (l := l) (x := x) hx
        have hyEq : y = a0 := by
          simpa [eq_comm] using hy
        subst hxEq
        subst hyEq
        have hlast : List.getLast l hlne = Nat.iterate s m' a0 := by
          simpa [l] using (getLast_iterate_succ s a0 m')
        have hperiod' : s (Nat.iterate s m' a0) = a0 := by
          simpa [Function.iterate_succ_apply', hm'] using hperiod
        have hdef : R a0 (Nat.iterate s m' a0) := by
          have hdef' : R (s (Nat.iterate s m' a0)) (Nat.iterate s m' a0) :=
            hs (Nat.iterate s m' a0)
          simpa [hperiod'] using hdef'
        simpa [reverse_rel, hlast] using hdef
      have hchain_append :
          (l ++ [a0]).IsChain (reverse_rel R) := by
        refine List.IsChain.append hchain_l ?_ hrel
        exact List.isChain_singleton a0
      have hchain_cycle :
          (a0 :: l.reverse).IsChain R := by
        have hchain_rev :
            (l ++ [a0]).reverse.IsChain R := by
          exact (List.isChain_reverse (R := R) (l := l ++ [a0])).2 hchain_append
        simpa using hchain_rev
      let cS : List X := l.reverse
      have hne : cS ≠ [] := by
        intro hnil
        exact hlne (List.reverse_eq_nil_iff.mp hnil)
      have hlast : List.getLast cS hne = a0 := by
        have hlast' := getLast_reverse_eq_head (c := l) (hne := hlne)
        have hhead : l.head hlne = a0 := by
          simp [l]
        simp [cS, hhead, hlast']
      have hcycleS : cycle R cS := by
        refine ⟨hne, ?_⟩
        simpa [cS, hlast] using hchain_cycle
      exact ⟨cS, hcycleS⟩
  | inr hgt =>
      have hEq' : seq j = seq i := hEq.symm
      have hlt : j < i := hgt
      have hmpos : 0 < i - j := Nat.sub_pos_of_lt hlt
      let m := i - j
      let a0 : X := seq j
      have hperiod : Nat.iterate s m a0 = a0 := by
        have hsum : j + m = i := Nat.add_sub_of_le (Nat.le_of_lt hlt)
        have hEq'' : Nat.iterate s j x0 = Nat.iterate s i x0 := by
          simpa [seq] using hEq'
        have hiter : Nat.iterate s (j + m) x0 = Nat.iterate s j x0 := by
          simpa [hsum] using hEq''.symm
        have hiter' : Nat.iterate s m a0 = Nat.iterate s (m + j) x0 := by
          simpa [a0, seq] using (Function.iterate_add_apply s m j x0).symm
        calc
          Nat.iterate s m a0 = Nat.iterate s (m + j) x0 := hiter'
          _ = Nat.iterate s (j + m) x0 := by simp [Nat.add_comm]
          _ = Nat.iterate s j x0 := hiter
          _ = a0 := by simp [a0, seq]
      have hmne : m ≠ 0 := Nat.ne_of_gt hmpos
      obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hmne
      let l : List X := List.iterate s a0 (Nat.succ m')
      have hlne : l ≠ [] := by
        simp [l]
      have hchain_l :
          l.IsChain (reverse_rel R) := by
        simpa [l] using
          (isChain_iterate_reverse_rel (R := R) (f := s) (h := hs)
            (n := Nat.succ m') (a := a0))
      have hrel :
          ∀ x ∈ l.getLast?, ∀ y ∈ ([a0] : List X).head?,
            reverse_rel R x y := by
        intro x hx y hy
        obtain ⟨hx', hxEq⟩ := List.mem_getLast?_eq_getLast (l := l) (x := x) hx
        have hyEq : y = a0 := by
          simpa [eq_comm] using hy
        subst hxEq
        subst hyEq
        have hlast : List.getLast l hlne = Nat.iterate s m' a0 := by
          simpa [l] using (getLast_iterate_succ s a0 m')
        have hperiod' : s (Nat.iterate s m' a0) = a0 := by
          simpa [Function.iterate_succ_apply', hm'] using hperiod
        have hdef : R a0 (Nat.iterate s m' a0) := by
          have hdef' : R (s (Nat.iterate s m' a0)) (Nat.iterate s m' a0) :=
            hs (Nat.iterate s m' a0)
          simpa [hperiod'] using hdef'
        simpa [reverse_rel, hlast] using hdef
      have hchain_append :
          (l ++ [a0]).IsChain (reverse_rel R) := by
        refine List.IsChain.append hchain_l ?_ hrel
        exact List.isChain_singleton a0
      have hchain_cycle :
          (a0 :: l.reverse).IsChain R := by
        have hchain_rev :
            (l ++ [a0]).reverse.IsChain R := by
          exact (List.isChain_reverse (R := R) (l := l ++ [a0])).2 hchain_append
        simpa using hchain_rev
      let cS : List X := l.reverse
      have hne : cS ≠ [] := by
        intro hnil
        exact hlne (List.reverse_eq_nil_iff.mp hnil)
      have hlast : List.getLast cS hne = a0 := by
        have hlast' := getLast_reverse_eq_head (c := l) (hne := hlne)
        have hhead : l.head hlne = a0 := by
          simp [l]
        simp [cS, hhead, hlast']
      have hcycleS : cycle R cS := by
        refine ⟨hne, ?_⟩
        simpa [cS, hlast] using hchain_cycle
      exact ⟨cS, hcycleS⟩

end SocialChoice
