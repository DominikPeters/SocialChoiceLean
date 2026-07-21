import SocialChoice.Axioms.Strategyproofness
import Mathlib.Data.Finset.Insert
import SocialChoice.Rank
import SocialChoice.ListBallot

namespace SocialChoice

/-!
# Down-Monotonicity for Singleton Winners

This file defines down-monotonicity for singleton winners and proves that
optimist and pessimist strategyproofness together imply this property.

This is Lemma 2.4 from Taylor's "The Manipulability of Voting Systems" (2002).
-/

open Finset

variable {A : Type}

/-! ## Ballot Manipulation: Swapping Alternatives -/

/-- Swap two alternatives in a linear order. -/
@[reducible] noncomputable def swapInBallot [DecidableEq A]
    (r : LinearOrder A) (x y : A) : LinearOrder A := by
  exact relabelBallot r (Equiv.swap x y)


/-! ## Properties of Ballot Swapping -/

/-- The fundamental property of swapInBallot. -/
lemma swapInBallot_lt [DecidableEq A] (r : LinearOrder A) (x y a b : A) :
    (swapInBallot r x y).lt a b ↔ r.lt (Equiv.swap x y a) (Equiv.swap x y b) := by
  rfl

/-- Swapping x and y reverses their relative order. -/
lemma swapInBallot_swap [DecidableEq A] (r : LinearOrder A) (x y : A) :
    (swapInBallot r x y).lt x y ↔ r.lt y x := by
  simp [swapInBallot_lt]

/-- Swapping x and y reverses their relative order (symmetric version). -/
lemma swapInBallot_swap' [DecidableEq A] (r : LinearOrder A) (x y : A) :
    (swapInBallot r x y).lt y x ↔ r.lt x y := by
  simp [swapInBallot_lt]

/-- Swapping preserves relative order of alternatives not in {x, y}. -/
lemma swapInBallot_preserves [DecidableEq A] (r : LinearOrder A) (x y a b : A)
    (ha : a ≠ x) (ha' : a ≠ y) (hb : b ≠ x) (hb' : b ≠ y) :
    (swapInBallot r x y).lt a b ↔ r.lt a b := by
  rw [swapInBallot_lt]
  simp [Equiv.swap_apply_of_ne_of_ne ha ha', Equiv.swap_apply_of_ne_of_ne hb hb']


/-! ## Adjacency -/

/-- Two alternatives x and y are adjacent in a linear order if x is immediately
    above y (i.e., x < y and there's no z with x < z < y). -/
def Adjacent (r : LinearOrder A) (x y : A) : Prop :=
  r.lt x y ∧ ∀ z : A, ¬(r.lt x z ∧ r.lt z y)

lemma adjacent_iff_adjacentInOrder {A : Type} (r : LinearOrder A) (x y : A) :
    Adjacent r x y ↔ AdjacentInOrder r x y := by
  rfl

lemma adjacent_iff_adjacentInList {A : Type} [Fintype A] [DecidableEq A]
    (r : LinearOrder A) (x y : A) :
    Adjacent r x y ↔ AdjacentInList (listOfLinearOrder r) x y := by
  simpa [adjacent_iff_adjacentInOrder] using
    (adjacentInOrder_iff_adjacentInList (r := r) x y)

lemma adjacent_lt_iff_lt_right (r : LinearOrder A) {x y z : A} (hadj : Adjacent r x y)
    (hzy : z ≠ y) :
    r.lt x z ↔ r.lt y z := by
  classical
  let _ := r
  constructor
  · intro hxz
    by_cases hzy_lt : z < y
    · exact (hadj.2 z ⟨hxz, hzy_lt⟩).elim
    · have hyz_le : y ≤ z := le_of_not_gt hzy_lt
      exact lt_of_le_of_ne hyz_le (Ne.symm hzy)
  · intro hyz
    exact lt_trans hadj.1 hyz

lemma adjacent_lt_iff_lt_left (r : LinearOrder A) {x y z : A} (hadj : Adjacent r x y)
    (hzx : z ≠ x) :
    r.lt z x ↔ r.lt z y := by
  classical
  let _ := r
  constructor
  · intro hzx_lt
    exact lt_trans hzx_lt hadj.1
  · intro hzy_lt
    by_cases hxz_lt : x < z
    · exact (hadj.2 z ⟨hxz_lt, hzy_lt⟩).elim
    · have hzx_le : z ≤ x := le_of_not_gt hxz_lt
      exact lt_of_le_of_ne hzx_le hzx

/-- If x and y are adjacent, the only pair whose relative order changes is {x, y}. -/
lemma swap_adjacent_only_changes_xy [DecidableEq A]
    (r : LinearOrder A) (x y : A) (hadj : Adjacent r x y)
    (a b : A) (hab : a ≠ b) :
    ((swapInBallot r x y).lt a b ↔ r.lt a b) ∨ ({a, b} = ({x, y} : Set A)) := by
  classical
  by_cases hax : a = x
  · subst a
    by_cases hby : b = y
    · subst b
      right
      rfl
    · have hbx : b ≠ x := by
        intro hb
        exact hab (hb ▸ rfl)
      left
      have h1 : (swapInBallot r x y).lt x b ↔ r.lt y b := by
        simp [swapInBallot_lt, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hbx hby]
      have h2 : r.lt y b ↔ r.lt x b :=
        (adjacent_lt_iff_lt_right (r := r) (x := x) (y := y) (z := b) hadj hby).symm
      exact h1.trans h2
  · by_cases hay : a = y
    · subst a
      by_cases hbx : b = x
      · subst b
        right
        ext z
        simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm]
      · have hby : b ≠ y := by
          intro hb
          exact hab (hb ▸ rfl)
        left
        have h1 : (swapInBallot r x y).lt y b ↔ r.lt x b := by
          simp [swapInBallot_lt, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hbx hby]
        have h2 : r.lt x b ↔ r.lt y b :=
          adjacent_lt_iff_lt_right (r := r) (x := x) (y := y) (z := b) hadj hby
        exact h1.trans h2
    · by_cases hbx : b = x
      · subst b
        left
        have h1 : (swapInBallot r x y).lt a x ↔ r.lt a y := by
          simp [swapInBallot_lt, Equiv.swap_apply_of_ne_of_ne hax hay, Equiv.swap_apply_left]
        have h2 : r.lt a y ↔ r.lt a x :=
          (adjacent_lt_iff_lt_left (r := r) (x := x) (y := y) (z := a) hadj hax).symm
        exact h1.trans h2
      · by_cases hby : b = y
        · subst b
          left
          have h1 : (swapInBallot r x y).lt a y ↔ r.lt a x := by
            simp [swapInBallot_lt, Equiv.swap_apply_of_ne_of_ne hax hay, Equiv.swap_apply_right]
          have h2 : r.lt a x ↔ r.lt a y :=
            adjacent_lt_iff_lt_left (r := r) (x := x) (y := y) (z := a) hadj hax
          exact h1.trans h2
        · left
          exact swapInBallot_preserves r x y a b hax hay hbx hby

section ProfileSwap

variable {V : Type} [Fintype V] [Fintype A] [DecidableEq A]

/-! ## Profile Swapping -/

/-- A profile where one voter has two alternatives swapped on their ballot. -/
noncomputable def swapInProfile (P : Profile V A) (v : V) (x y : A) : Profile V A :=
  updateProfile P v (swapInBallot (P.pref v) x y)

/-- The original profile P equals an update of the swapped profile. -/
lemma profile_eq_update_of_swap (P : Profile V A) (v : V) (x y : A) :
    P = updateProfile (swapInProfile P v x y) v (P.pref v) := by
  apply Profile.ext
  intro u
  unfold swapInProfile updateProfile
  by_cases huv : u = v
  · subst u
    simp only [if_true]
  · simp only [if_neg huv]

/-- swapInProfile relates to updateProfile. -/
lemma swapInProfile_eq (P : Profile V A) (v : V) (x y : A) :
    swapInProfile P v x y = updateProfile P v (swapInBallot (P.pref v) x y) := rfl

omit [DecidableEq A] in
lemma updateProfile_updateProfile_same (P : Profile V A) (v : V)
    (ballot1 ballot2 : LinearOrder A) :
    updateProfile (updateProfile P v ballot1) v ballot2 = updateProfile P v ballot2 := by
  classical
  apply Profile.ext
  intro u
  unfold updateProfile
  by_cases h : u = v
  · subst u
    simp only [if_true]
  · simp only [if_neg h]

end ProfileSwap

/-! ## Down-Monotonicity for Singleton Winners -/

/-- Down-monotonicity for singleton winners: if f(P) = {w} (a singleton),
    and P' is obtained from P by having one voter swap two adjacent alternatives
    x and y on their ballot where x is a loser (x ≠ w) and x is immediately above y,
    then f(P') = {w}. -/
def DownMonotonicitySingleton (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (v : V) (w x y : A),
    f P = {w} →
    x ≠ w →
    Adjacent (P.pref v) x y →
    f (swapInProfile P v x y) = {w}

/-! ## Expanded Down-Monotonicity -/

/-- `DownObtainable w P P'` means no voter ever moves `w` down relative to any alternative. -/
def DownObtainable {V A : Type} [Fintype V] [Fintype A]
    (w : A) (P P' : Profile V A) : Prop :=
  ∀ v : V, ∀ b : A, Prefers P v w b → Prefers P' v w b

def DownMonotonicity (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A]
    (P P' : Profile V A) (w : A),
    f P = {w} →
    DownObtainable (V := V) (A := A) w P P' →
    f P' = {w}

/-! ## List-Level Swap Sequences -/

section ListSwapSeq

variable [DecidableEq A]

inductive DownSwapSeq (w : A) : List A → List A → Prop
  | refl (l : List A) : DownSwapSeq w l l
  | cons (a : A) {l l' : List A} :
      DownSwapSeq w l l' → DownSwapSeq w (a :: l) (a :: l')
  | swap {a b : A} {l : List A} (ha : a ≠ w) :
      DownSwapSeq w (a :: b :: l) (b :: a :: l)
  | trans {l l' l'' : List A} :
      DownSwapSeq w l l' → DownSwapSeq w l' l'' → DownSwapSeq w l l''

omit [DecidableEq A] in
lemma downSwapSeq_perm {w : A} {l l' : List A} :
    DownSwapSeq w l l' → List.Perm l l' := by
  intro hseq
  induction hseq with
  | refl l =>
      exact List.Perm.refl l
  | cons a hseq ih =>
      exact List.Perm.cons a ih
  | swap ha =>
      rename_i a b l
      simpa using (List.Perm.swap' a b (List.Perm.refl l)).symm
  | trans h1 h2 ih1 ih2 =>
      exact ih1.trans ih2

lemma downSwapSeq_bubble_to_front (w y : A) :
    ∀ l : List A, y ∈ l → w ∉ l.take (l.idxOf y) →
      DownSwapSeq w l (y :: l.take (l.idxOf y) ++ l.drop (l.idxOf y + 1)) := by
  intro l hy hw
  induction l with
  | nil =>
      cases hy
  | cons a l ih =>
      by_cases hya : y = a
      · subst hya
        simp [DownSwapSeq.refl, List.drop]
      · have hy' : y ∈ l := by
          simpa [hya] using hy
        have htake :
            (a :: l).take ((a :: l).idxOf y) = a :: l.take (l.idxOf y) := by
          simp [List.idxOf_cons_ne _ (Ne.symm hya)]
        have hw' : w ∉ l.take (l.idxOf y) := by
          intro hw_mem
          apply hw
          have : w ∈ a :: l.take (l.idxOf y) := List.mem_cons_of_mem _ hw_mem
          simpa [htake] using this
        have hseq := ih hy' hw'
        have hne : a ≠ w := by
          intro hwa
          apply hw
          subst hwa
          have : a ∈ (a :: l).take ((a :: l).idxOf y) := by
            rw [htake]
            simp
          exact this
        refine DownSwapSeq.trans (DownSwapSeq.cons a hseq) ?_
        -- swap the new head `a` with `y`
        have hswap :
            DownSwapSeq w (a :: y :: l.take (l.idxOf y) ++ l.drop (l.idxOf y + 1))
              (y :: a :: l.take (l.idxOf y) ++ l.drop (l.idxOf y + 1)) :=
          DownSwapSeq.swap (w := w) (a := a) (b := y)
            (l := l.take (l.idxOf y) ++ l.drop (l.idxOf y + 1)) hne
        simpa [List.idxOf_cons_ne _ (Ne.symm hya), List.take, List.drop, Nat.add_assoc] using hswap

end ListSwapSeq

/-! ## List-Level Down-Obtainable -/

section ListDownObtainable

variable [DecidableEq A]

def DownObtainableList (w : A) (l l' : List A) : Prop :=
  ∀ b : A, l.idxOf w < l.idxOf b → l'.idxOf w < l'.idxOf b

lemma idxOf_map_swap {l : List A} (hnodup : l.Nodup) (hcomplete : ∀ a, a ∈ l) (x y a : A) :
    (l.map (Equiv.swap x y)).idxOf a = l.idxOf (Equiv.swap x y a) := by
  classical
  let l' := l.map (Equiv.swap x y)
  have hnodup' : l'.Nodup := List.Nodup.map (fun _ _ h => (Equiv.swap x y).injective h) hnodup
  have ha_mem : a ∈ l' := by
    refine List.mem_map.2 ?_
    exact ⟨Equiv.swap x y a, hcomplete _, by simp⟩
  have hi : l.idxOf (Equiv.swap x y a) < l.length := List.idxOf_lt_length_of_mem (hcomplete _)
  have hlen : l.idxOf (Equiv.swap x y a) < l'.length := by
    simpa [l', List.length_map] using hi
  have hget : l[l.idxOf (Equiv.swap x y a)] = Equiv.swap x y a :=
    List.getElem_idxOf (x := Equiv.swap x y a) (xs := l) (h := hi)
  have hget' : l'[l.idxOf (Equiv.swap x y a)] = a := by
    have hmap :=
      List.getElem_map (f := Equiv.swap x y) (l := l)
        (i := l.idxOf (Equiv.swap x y a)) (h := hlen)
    calc
      l'[l.idxOf (Equiv.swap x y a)] = Equiv.swap x y (l[l.idxOf (Equiv.swap x y a)]) := hmap
      _ = Equiv.swap x y (Equiv.swap x y a) := by simp [hget]
      _ = a := by simp
  have hidx' :
      l'.idxOf (l'[l.idxOf (Equiv.swap x y a)]) = l.idxOf (Equiv.swap x y a) := by
    simpa [l'] using
      (List.Nodup.idxOf_getElem (xs := l') hnodup' (l.idxOf (Equiv.swap x y a)) hlen)
  simpa [hget'] using hidx'

lemma idxOf_eraseIdx_eq_of_lt {l : List A} {y x : A}
    (hx : x ∈ l) (hxy : l.idxOf x < l.idxOf y) :
    (l.eraseIdx (l.idxOf y)).idxOf x = l.idxOf x := by
  let i := l.idxOf y
  have hx_take : x ∈ l.take i :=
    (List.mem_take_iff_idxOf_lt (ha := hx)).2 (by simpa [i] using hxy)
  have htail : l.eraseIdx i = l.take i ++ l.drop (i + 1) := by
    simpa [i] using (List.eraseIdx_eq_take_drop_succ (l := l) (i := i))
  have hidx_tail :
      (l.eraseIdx i).idxOf x = (l.take i).idxOf x := by
    have := List.idxOf_append_of_mem (l₁ := l.take i) (l₂ := l.drop (i + 1)) hx_take
    simpa [htail] using this
  have hidx_l :
      l.idxOf x = (l.take i).idxOf x := by
    have := List.idxOf_append_of_mem (l₁ := l.take i) (l₂ := l.drop i) hx_take
    simpa [i, List.take_append_drop] using this
  exact hidx_tail.trans hidx_l.symm

lemma idxOf_eraseIdx_eq_of_gt {l : List A} {y x : A}
    (hy : y ∈ l) (hx : x ∈ l) (hxy : l.idxOf y < l.idxOf x) (hxy_ne : x ≠ y) :
    (l.eraseIdx (l.idxOf y)).idxOf x = l.idxOf x - 1 := by
  let i := l.idxOf y
  have hx_notmem : x ∉ l.take i := by
    intro hx_take
    have hlt : l.idxOf x < i := (List.mem_take_iff_idxOf_lt (ha := hx)).1 hx_take
    exact (Nat.lt_asymm hxy (by simpa [i] using hlt))
  have htail : l.eraseIdx i = l.take i ++ l.drop (i + 1) := by
    simpa [i] using (List.eraseIdx_eq_take_drop_succ (l := l) (i := i))
  have hidx_tail :
      (l.eraseIdx i).idxOf x = (l.take i).length + (l.drop (i + 1)).idxOf x := by
    have := List.idxOf_append_of_notMem (l₁ := l.take i) (l₂ := l.drop (i + 1)) hx_notmem
    simpa [htail] using this
  have hi : i < l.length := List.idxOf_lt_length_of_mem hy
  have hget : l[i] = y := by
    have hi' : l.idxOf y < l.length := by simpa [i] using hi
    exact (List.getElem_idxOf (x := y) (xs := l) (h := hi'))
  have hdrop : l.drop i = y :: l.drop (i + 1) := by
    simpa [hget, i] using (List.drop_eq_getElem_cons (l := l) (i := i) hi)
  have hidx_drop : (l.drop i).idxOf x = (l.drop (i + 1)).idxOf x + 1 := by
    simp [hdrop, List.idxOf_cons_ne _ (Ne.symm hxy_ne)]
  have hidx_l' : l.idxOf x = (l.take i).length + (l.drop i).idxOf x := by
    have := List.idxOf_append_of_notMem (l₁ := l.take i) (l₂ := l.drop i) hx_notmem
    simpa [i, List.take_append_drop] using this
  have hidx_l :
      l.idxOf x = (l.take i).length + 1 + (l.drop (i + 1)).idxOf x := by
    simpa [hidx_drop, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hidx_l'
  calc
    (l.eraseIdx i).idxOf x = (l.take i).length + (l.drop (i + 1)).idxOf x := hidx_tail
    _ = ((l.take i).length + 1 + (l.drop (i + 1)).idxOf x) - 1 := by
      omega
    _ = l.idxOf x - 1 := by simp [hidx_l]

lemma idxOf_eraseIdx_lt_iff_of_ne {l : List A} {y w b : A}
    (hy : y ∈ l) (hw : w ∈ l) (hb : b ∈ l) (hw_ne : w ≠ y) (hb_ne : b ≠ y) :
    (l.eraseIdx (l.idxOf y)).idxOf w < (l.eraseIdx (l.idxOf y)).idxOf b ↔
      l.idxOf w < l.idxOf b := by
  let i := l.idxOf y
  have hwi_ne : l.idxOf w ≠ i := by
    have h := (List.idxOf_inj (l := l) (x := w) (y := y) hw)
    exact fun h' => hw_ne (h.mp (by simpa [i] using h'))
  have hbi_ne : l.idxOf b ≠ i := by
    have h := (List.idxOf_inj (l := l) (x := b) (y := y) hb)
    exact fun h' => hb_ne (h.mp (by simpa [i] using h'))
  have hwi : l.idxOf w < i ∨ i < l.idxOf w := lt_or_gt_of_ne hwi_ne
  have hbi : l.idxOf b < i ∨ i < l.idxOf b := lt_or_gt_of_ne hbi_ne
  cases hwi with
  | inl hwi_lt =>
      cases hbi with
      | inl hbi_lt =>
          have hw' := idxOf_eraseIdx_eq_of_lt (l := l) (y := y) (x := w) hw (by simpa [i] using hwi_lt)
          have hb' := idxOf_eraseIdx_eq_of_lt (l := l) (y := y) (x := b) hb (by simpa [i] using hbi_lt)
          constructor
          · intro h
            rw [hw', hb'] at h
            exact h
          · intro h
            rw [hw', hb']
            exact h
      | inr hbi_gt =>
          have hw' := idxOf_eraseIdx_eq_of_lt (l := l) (y := y) (x := w) hw (by simpa [i] using hwi_lt)
          have hb' :=
            idxOf_eraseIdx_eq_of_gt (l := l) (y := y) (x := b) hy hb (by simpa [i] using hbi_gt) hb_ne
          constructor
          · intro _
            exact lt_trans hwi_lt hbi_gt
          · intro _
            have : l.idxOf w < l.idxOf b - 1 := by
              omega
            rw [hw', hb']
            exact this
  | inr hwi_gt =>
      cases hbi with
      | inl hbi_lt =>
          have hw' :=
            idxOf_eraseIdx_eq_of_gt (l := l) (y := y) (x := w) hy hw (by simpa [i] using hwi_gt) hw_ne
          have hb' := idxOf_eraseIdx_eq_of_lt (l := l) (y := y) (x := b) hb (by simpa [i] using hbi_lt)
          constructor
          · intro htail
            have : ¬ l.idxOf w - 1 < l.idxOf b := by omega
            rw [hw', hb'] at htail
            exact (this htail).elim
          · intro hlt
            have : l.idxOf b < l.idxOf w := lt_trans hbi_lt hwi_gt
            exact (lt_asymm hlt this).elim
      | inr hbi_gt =>
          have hw' :=
            idxOf_eraseIdx_eq_of_gt (l := l) (y := y) (x := w) hy hw (by simpa [i] using hwi_gt) hw_ne
          have hb' :=
            idxOf_eraseIdx_eq_of_gt (l := l) (y := y) (x := b) hy hb (by simpa [i] using hbi_gt) hb_ne
          constructor
          · intro h
            rw [hw', hb'] at h
            have : l.idxOf w < l.idxOf b := by omega
            exact this
          · intro h
            have : l.idxOf w - 1 < l.idxOf b - 1 := by omega
            rw [hw', hb']
            exact this

lemma downSwapSeq_of_downObtainableList {w : A} :
    ∀ {l l' : List A},
      l.Nodup → l'.Nodup → List.Perm l l' →
      DownObtainableList w l l' → DownSwapSeq w l l' := by
  classical
  intro l l' hnodup hnodup' hperm hdown
  induction l' generalizing l with
  | nil =>
      have hl : l = [] := hperm.eq_nil
      subst hl
      exact DownSwapSeq.refl []
  | cons y ys ih =>
      have hcons := (List.cons_perm_iff_perm_erase).1 hperm.symm
      have hy : y ∈ l := hcons.1
      have hperm_tail : List.Perm (l.erase y) ys := hcons.2.symm
      have hw_prefix : w ∉ l.take (l.idxOf y) := by
        intro hw_mem
        by_cases hw : w ∈ l
        · have hw_lt : l.idxOf w < l.idxOf y :=
            (List.mem_take_iff_idxOf_lt (ha := hw)).1 hw_mem
          by_cases hwy : y = w
          · subst hwy
            exact (Nat.lt_irrefl _ hw_lt)
          · have hw_lt' : (y :: ys).idxOf w < (y :: ys).idxOf y :=
              hdown y hw_lt
            have : False := by
              simp at hw_lt'
            exact this
        · exact hw (List.mem_of_mem_take hw_mem)
      have hfront :
          DownSwapSeq w l (y :: l.take (l.idxOf y) ++ l.drop (l.idxOf y + 1)) :=
        downSwapSeq_bubble_to_front w y l hy hw_prefix
      let l_tail := l.eraseIdx (l.idxOf y)
      have htail : l_tail = l.take (l.idxOf y) ++ l.drop (l.idxOf y + 1) := by
        simp [l_tail, List.eraseIdx_eq_take_drop_succ]
      have hfront' : DownSwapSeq w l (y :: l_tail) := by
        simpa [htail] using hfront
      have hnodup_tail : l_tail.Nodup := by
        simpa [l_tail] using (List.Nodup.eraseIdx (l := l) (k := l.idxOf y) hnodup)
      have hi : l.idxOf y < l.length := List.idxOf_lt_length_of_mem hy
      have hget : l[l.idxOf y] = y :=
        List.getElem_idxOf (x := y) (xs := l) (h := hi)
      have herase : l.erase y = l_tail := by
        have h := List.Nodup.erase_getElem (l := l) hnodup (i := l.idxOf y) hi
        rw [hget] at h
        dsimp [l_tail]
        exact h
      have hperm_tail' : List.Perm l_tail ys := by
        simpa [herase] using hperm_tail
      have hdown_tail : DownObtainableList w l_tail ys := by
        intro b hlt
        by_cases hwy : y = w
        · have hw_not : w ∉ l_tail := by
            have : w ∉ l.erase w := by
              simpa using (List.Nodup.not_mem_erase (l := l) hnodup)
            have herase' : l.erase w = l_tail := by
              simpa [hwy] using herase
            simpa [herase'] using this
          have hw_idx : l_tail.idxOf w = l_tail.length := List.idxOf_of_notMem hw_not
          have hb_le : l_tail.idxOf b ≤ l_tail.length :=
            List.idxOf_le_length (l := l_tail) (a := b)
          have hlt' : l_tail.length < l_tail.idxOf b := by
            simpa [hw_idx] using hlt
          exact (False.elim ((Nat.not_lt_of_ge hb_le) hlt'))
        · have hw_tail : w ∈ l_tail := by
            by_contra hw_tail
            have hw_idx : l_tail.idxOf w = l_tail.length := List.idxOf_of_notMem hw_tail
            have hb_le : l_tail.idxOf b ≤ l_tail.length :=
              List.idxOf_le_length (l := l_tail) (a := b)
            have hlt' : l_tail.length < l_tail.idxOf b := by
              simpa [hw_idx] using hlt
            exact (Nat.not_lt_of_ge hb_le) hlt'
          have hw_tail' : w ∈ l.eraseIdx (l.idxOf y) := by
            have hw_tail' := hw_tail
            dsimp [l_tail] at hw_tail'
            exact hw_tail'
          have hw : w ∈ l := List.mem_of_mem_eraseIdx hw_tail'
          have hw_mem_l' : w ∈ (y :: ys) := hperm.subset hw
          have hwy' : w ≠ y := Ne.symm hwy
          have hw_mem_ys : w ∈ ys := by
            simpa [List.mem_cons, hwy'] using hw_mem_l'
          have hy_not : y ∉ ys := (List.nodup_cons.mp hnodup').1
          by_cases hby : b = y
          · have hw_lt : ys.idxOf w < ys.length := List.idxOf_lt_length_of_mem hw_mem_ys
            have hy_idx : ys.idxOf y = ys.length := List.idxOf_of_notMem hy_not
            simpa [hby, hy_idx] using hw_lt
          · by_cases hb : b ∈ l
            · have hlt' :
                  l.idxOf w < l.idxOf b := by
                have hiff :=
                  idxOf_eraseIdx_lt_iff_of_ne (l := l) (y := y) (w := w) (b := b)
                    hy hw hb hwy' hby
                exact hiff.1 (by simpa [l_tail] using hlt)
              have hdown' : (y :: ys).idxOf w < (y :: ys).idxOf b := hdown b hlt'
              have hdown'' : ys.idxOf w < ys.idxOf b := by
                simpa [List.idxOf_cons_ne _ hwy, List.idxOf_cons_ne _ (Ne.symm hby)] using hdown'
              exact hdown''
            · have hb_not : b ∉ (y :: ys) := by
                exact mt (hperm.mem_iff (a := b)).2 hb
              have hb_not_ys : b ∉ ys := by
                intro hb_ys
                have : b ∈ (y :: ys) := by
                  simpa [List.mem_cons, hby] using hb_ys
                exact hb_not this
              have hb_idx : ys.idxOf b = ys.length := List.idxOf_of_notMem hb_not_ys
              have hw_lt : ys.idxOf w < ys.length := List.idxOf_lt_length_of_mem hw_mem_ys
              simpa [hb_idx] using hw_lt
      have hseq_tail : DownSwapSeq w l_tail ys :=
        ih hnodup_tail (List.nodup_cons.mp hnodup').2 hperm_tail' hdown_tail
      have hseq_tail' : DownSwapSeq w (y :: l_tail) (y :: ys) :=
        DownSwapSeq.cons y hseq_tail
      exact DownSwapSeq.trans hfront' hseq_tail'

lemma downObtainableList_of_downObtainable [Fintype A]
    {V : Type} [Fintype V] (P P' : Profile V A) (v : V) (w : A)
    (hdown : DownObtainable (V := V) (A := A) w P P') :
    DownObtainableList w (listOfLinearOrder (P.pref v)) (listOfLinearOrder (P'.pref v)) := by
  intro b hlt
  have hlt' : Prefers P v w b := by
    have h := (listOfLinearOrder_lt_iff_idxOf (r := P.pref v) w b).2 hlt
    simpa [Prefers] using h
  have hlt'' : Prefers P' v w b := hdown v b hlt'
  have h := (listOfLinearOrder_lt_iff_idxOf (r := P'.pref v) w b).1 hlt''
  simpa using h

end ListDownObtainable

section LinearOrderOfListHelpers

variable {A : Type} [DecidableEq A]

lemma linearOrderOfList_congr {l : List A}
    (hnodup1 hnodup2 : l.Nodup) (hcomplete1 hcomplete2 : ∀ a, a ∈ l) :
    linearOrderOfList l hnodup1 hcomplete1 = linearOrderOfList l hnodup2 hcomplete2 := by
  classical
  apply LinearOrder.ext_lt
  intro a b
  simp [linearOrderOfList_lt_iff_idxOf]

lemma adjacent_linearOrderOfList_of_adjacentInList {l : List A}
    (hnodup : l.Nodup) (hcomplete : ∀ a, a ∈ l) {a b : A}
    (hadj : AdjacentInList l a b) :
    Adjacent (linearOrderOfList l hnodup hcomplete) a b := by
  classical
  have hlt : (linearOrderOfList l hnodup hcomplete).lt a b := by
    have hidx : l.idxOf a < l.idxOf b := by
      have h : l.idxOf a < l.idxOf a + 1 := Nat.lt_succ_self _
      exact lt_of_lt_of_eq h hadj
    exact (linearOrderOfList_lt_iff_idxOf (l := l) (hnodup := hnodup) (hcomplete := hcomplete) a b).2 hidx
  refine ⟨hlt, ?_⟩
  intro z hz
  have hidx_az : l.idxOf a < l.idxOf z :=
    (linearOrderOfList_lt_iff_idxOf (l := l) (hnodup := hnodup) (hcomplete := hcomplete) a z).1 hz.1
  have hidx_zb : l.idxOf z < l.idxOf b :=
    (linearOrderOfList_lt_iff_idxOf (l := l) (hnodup := hnodup) (hcomplete := hcomplete) z b).1 hz.2
  have hle : l.idxOf a + 1 ≤ l.idxOf z := Nat.succ_le_of_lt hidx_az
  have hlt' : l.idxOf z < l.idxOf a + 1 := by
    exact lt_of_lt_of_eq hidx_zb hadj.symm
  exact (lt_irrefl _ (lt_of_lt_of_le hlt' hle))

lemma map_swap_eq_self_of_not_mem (l : List A) (a b : A)
    (ha : a ∉ l) (hb : b ∉ l) :
    l.map (Equiv.swap a b) = l := by
  classical
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hxa : x ≠ a := by
        intro h
        apply ha
        simp [h]
      have hxb : x ≠ b := by
        intro h
        apply hb
        simp [h]
      have ha' : a ∉ xs := by
        intro h
        apply ha
        simp [h]
      have hb' : b ∉ xs := by
        intro h
        apply hb
        simp [h]
      simp [Equiv.swap_apply_of_ne_of_ne hxa hxb, ih ha' hb']

lemma idxOf_append_of_not_mem {l₁ l₂ : List A} {a : A} (h : a ∉ l₁) :
    (l₁ ++ l₂).idxOf a = l₁.length + l₂.idxOf a := by
  classical
  induction l₁ with
  | nil => simp
  | cons d t ih =>
      have hda : d ≠ a := by
        intro hda
        apply h
        simp [hda]
      have h' : a ∉ t := by
        intro hmem
        apply h
        simp [hmem]
      simp [List.cons_append, List.idxOf_cons_ne _ hda, ih h', List.length, Nat.succ_add]

lemma map_swap_pre_cons_cons (pre tail : List A) (a b : A)
    (ha_pre : a ∉ pre) (hb_pre : b ∉ pre)
    (ha_tail : a ∉ tail) (hb_tail : b ∉ tail) :
    (pre ++ a :: b :: tail).map (Equiv.swap a b) = pre ++ b :: a :: tail := by
  classical
  have hpre : pre.map (Equiv.swap a b) = pre :=
    map_swap_eq_self_of_not_mem pre a b ha_pre hb_pre
  have htail : tail.map (Equiv.swap a b) = tail :=
    map_swap_eq_self_of_not_mem tail a b ha_tail hb_tail
  simp [List.map_append, hpre, htail, Equiv.swap_apply_left, Equiv.swap_apply_right]

lemma swapInBallot_linearOrderOfList_map_swap (l : List A)
    (hnodup : l.Nodup) (hcomplete : ∀ a, a ∈ l) (x y : A) :
    swapInBallot (linearOrderOfList l hnodup hcomplete) x y =
      linearOrderOfList (l.map (Equiv.swap x y))
        (List.Nodup.map (fun _ _ h => (Equiv.swap x y).injective h) hnodup)
        (by
          intro a
          refine List.mem_map.2 ?_
          exact ⟨Equiv.swap x y a, hcomplete _, by simp⟩) := by
  classical
  apply LinearOrder.ext_lt
  intro a b
  have hswap :
      (swapInBallot (linearOrderOfList l hnodup hcomplete) x y).lt a b ↔
        (linearOrderOfList l hnodup hcomplete).lt (Equiv.swap x y a) (Equiv.swap x y b) := by
    simpa using
      (swapInBallot_lt (r := linearOrderOfList l hnodup hcomplete) x y a b)
  have hidx :
      (linearOrderOfList l hnodup hcomplete).lt (Equiv.swap x y a) (Equiv.swap x y b) ↔
        l.idxOf (Equiv.swap x y a) < l.idxOf (Equiv.swap x y b) :=
    (linearOrderOfList_lt_iff_idxOf (l := l) (hnodup := hnodup) (hcomplete := hcomplete) _ _)
  have hlin :
      (linearOrderOfList (l.map (Equiv.swap x y))
          (List.Nodup.map (fun _ _ h => (Equiv.swap x y).injective h) hnodup)
          (by
            intro a
            refine List.mem_map.2 ?_
            exact ⟨Equiv.swap x y a, hcomplete _, by simp⟩)).lt a b ↔
        (l.map (Equiv.swap x y)).idxOf a < (l.map (Equiv.swap x y)).idxOf b :=
    (linearOrderOfList_lt_iff_idxOf
      (l := l.map (Equiv.swap x y))
      (hnodup := List.Nodup.map (fun _ _ h => (Equiv.swap x y).injective h) hnodup)
      (hcomplete := by
        intro a
        refine List.mem_map.2 ?_
        exact ⟨Equiv.swap x y a, hcomplete _, by simp⟩) a b)
  have hidx' :
      (l.map (Equiv.swap x y)).idxOf a =
        l.idxOf (Equiv.swap x y a) := by
    simpa using
      (idxOf_map_swap (l := l) (hnodup := hnodup) (hcomplete := hcomplete) (x := x) (y := y) (a := a))
  have hidx'' :
      (l.map (Equiv.swap x y)).idxOf b =
        l.idxOf (Equiv.swap x y b) := by
    simpa using
      (idxOf_map_swap (l := l) (hnodup := hnodup) (hcomplete := hcomplete) (x := x) (y := y) (a := b))
  constructor
  · intro h
    have h' : l.idxOf (Equiv.swap x y a) < l.idxOf (Equiv.swap x y b) := (hswap.mp h |> hidx.mp)
    have h'' : (l.map (Equiv.swap x y)).idxOf a < (l.map (Equiv.swap x y)).idxOf b := by
      simpa [hidx', hidx''] using h'
    exact (hlin.mpr h'')
  · intro h
    have h' : (l.map (Equiv.swap x y)).idxOf a < (l.map (Equiv.swap x y)).idxOf b := hlin.mp h
    have h'' : l.idxOf (Equiv.swap x y a) < l.idxOf (Equiv.swap x y b) := by
      simpa [hidx', hidx''] using h'
    exact hswap.mpr (hidx.mpr h'')

end LinearOrderOfListHelpers

section ListOfLinearOrderSwap

noncomputable def listOfLinearOrderSwap [Fintype A]
    (r : LinearOrder A) (x y : A) : List A :=
  (listOfLinearOrder r).map (Equiv.swap x y)

lemma listOfLinearOrderSwap_nodup [Fintype A] (r : LinearOrder A) (x y : A) :
    (listOfLinearOrderSwap r x y).Nodup := by
  classical
  unfold listOfLinearOrderSwap
  exact
    List.Nodup.map (fun _ _ h => (Equiv.swap x y).injective h)
      (listOfLinearOrder_nodup (r := r))

lemma listOfLinearOrderSwap_complete [Fintype A] (r : LinearOrder A) (x y : A) (a : A) :
    a ∈ listOfLinearOrderSwap r x y := by
  classical
  unfold listOfLinearOrderSwap
  refine List.mem_map.2 ?_
  exact ⟨Equiv.swap x y a, listOfLinearOrder_complete (r := r) _, by simp⟩

lemma swapInBallot_eq_linearOrderOfList_map_swap [Fintype A] (r : LinearOrder A) (x y : A) :
    swapInBallot r x y =
      linearOrderOfList (listOfLinearOrderSwap r x y)
        (listOfLinearOrderSwap_nodup (r := r) x y)
        (listOfLinearOrderSwap_complete (r := r) x y) := by
  classical
  let _ : LinearOrder A := r
  let _ : DecidableEq A := inferInstance
  apply LinearOrder.ext_lt
  intro a b
  have hswap : (swapInBallot r x y).lt a b ↔ r.lt (Equiv.swap x y a) (Equiv.swap x y b) :=
    swapInBallot_lt r x y a b
  have hidx :
      r.lt (Equiv.swap x y a) (Equiv.swap x y b) ↔
        (listOfLinearOrder r).idxOf (Equiv.swap x y a) <
          (listOfLinearOrder r).idxOf (Equiv.swap x y b) :=
    (listOfLinearOrder_lt_iff_idxOf (r := r) _ _)
  have hlin :
      (linearOrderOfList (listOfLinearOrderSwap r x y)
        (listOfLinearOrderSwap_nodup (r := r) x y)
        (listOfLinearOrderSwap_complete (r := r) x y)).lt a b ↔
        (listOfLinearOrderSwap r x y).idxOf a <
          (listOfLinearOrderSwap r x y).idxOf b :=
    (linearOrderOfList_lt_iff_idxOf
      (l := listOfLinearOrderSwap r x y)
      (hnodup := listOfLinearOrderSwap_nodup (r := r) x y)
      (hcomplete := listOfLinearOrderSwap_complete (r := r) x y) a b)
  have hidx' :
      (listOfLinearOrderSwap r x y).idxOf a =
        (listOfLinearOrder r).idxOf (Equiv.swap x y a) := by
    simpa [listOfLinearOrderSwap] using
      (idxOf_map_swap (l := listOfLinearOrder r)
        (hnodup := listOfLinearOrder_nodup (r := r))
        (hcomplete := listOfLinearOrder_complete (r := r)) (x := x) (y := y) (a := a))
  have hidx'' :
      (listOfLinearOrderSwap r x y).idxOf b =
        (listOfLinearOrder r).idxOf (Equiv.swap x y b) := by
    simpa [listOfLinearOrderSwap] using
      (idxOf_map_swap (l := listOfLinearOrder r)
        (hnodup := listOfLinearOrder_nodup (r := r))
        (hcomplete := listOfLinearOrder_complete (r := r)) (x := x) (y := y) (a := b))
  constructor
  · intro h
    have h' : (listOfLinearOrder r).idxOf (Equiv.swap x y a) <
        (listOfLinearOrder r).idxOf (Equiv.swap x y b) := (hswap.mp h |> hidx.mp)
    have h'' : (listOfLinearOrderSwap r x y).idxOf a <
        (listOfLinearOrderSwap r x y).idxOf b := by simpa [hidx', hidx''] using h'
    exact (hlin.mpr h'')
  · intro h
    have h' : (listOfLinearOrderSwap r x y).idxOf a <
        (listOfLinearOrderSwap r x y).idxOf b := hlin.mp h
    have h'' : (listOfLinearOrder r).idxOf (Equiv.swap x y a) <
        (listOfLinearOrder r).idxOf (Equiv.swap x y b) := by
      simpa [hidx', hidx''] using h'
    exact hswap.mpr (hidx.mpr h'')

end ListOfLinearOrderSwap

section ListOfLinearOrderPerm

lemma listOfLinearOrder_perm_univ [Fintype A] (r : LinearOrder A) :
    List.Perm (listOfLinearOrder r) (Finset.univ : Finset A).toList := by
  classical
  let _ := r
  simpa [listOfLinearOrder] using
    (Finset.sort_perm_toList (s := (Finset.univ : Finset A)) (r := fun a b => a ≤ b))

lemma listOfLinearOrder_perm [Fintype A] (r r' : LinearOrder A) :
    List.Perm (listOfLinearOrder r) (listOfLinearOrder r') := by
  classical
  exact (listOfLinearOrder_perm_univ (r := r)).trans
    (listOfLinearOrder_perm_univ (r := r')).symm

end ListOfLinearOrderPerm

section DownSwapSeqOfDownObtainable

lemma downSwapSeq_of_downObtainable [Fintype A] [DecidableEq A] {V : Type} [Fintype V]
    (P P' : Profile V A) (v : V) (w : A)
    (hdown : DownObtainable (V := V) (A := A) w P P') :
    DownSwapSeq w (listOfLinearOrder (P.pref v)) (listOfLinearOrder (P'.pref v)) := by
  have hdown_list :
      DownObtainableList w (listOfLinearOrder (P.pref v)) (listOfLinearOrder (P'.pref v)) :=
    downObtainableList_of_downObtainable (P := P) (P' := P') (v := v) (w := w) hdown
  have hperm :
      List.Perm (listOfLinearOrder (P.pref v)) (listOfLinearOrder (P'.pref v)) :=
    listOfLinearOrder_perm (r := P.pref v) (r' := P'.pref v)
  exact downSwapSeq_of_downObtainableList
    (l := listOfLinearOrder (P.pref v))
    (l' := listOfLinearOrder (P'.pref v))
    (w := w)
    (listOfLinearOrder_nodup (r := P.pref v))
    (listOfLinearOrder_nodup (r := P'.pref v))
    hperm
    hdown_list

end DownSwapSeqOfDownObtainable

section ProfileLevel

variable {V : Type} [Fintype V] [Fintype A] [DecidableEq A]

/-- `DownObtainableSeq w P P'` means `P'` is obtained from `P` by a sequence of
    adjacent swaps where a loser is moved down one position. -/
inductive DownObtainableSeq (w : A) : Profile V A → Profile V A → Prop
  | refl (P : Profile V A) : DownObtainableSeq w P P
  | step (P Q : Profile V A) (v : V) (x y : A) :
      x ≠ w →
      Adjacent (P.pref v) x y →
      DownObtainableSeq w (swapInProfile P v x y) Q →
      DownObtainableSeq w P Q

lemma prefers_w_preserved_swap (P : Profile V A) (v : V) (w x y b : A)
    (hxw : x ≠ w) (hadj : Adjacent (P.pref v) x y)
    (hwb : Prefers P v w b) :
    Prefers (swapInProfile P v x y) v w b := by
  classical
  let r := P.pref v
  have hwb_ne : w ≠ b := ne_of_lt hwb
  have h :=
    swap_adjacent_only_changes_xy (r := r) (x := x) (y := y) hadj w b hwb_ne
  cases h with
  | inl hpres =>
      have hwb' : (swapInBallot r x y).lt w b := hpres.mpr hwb
      change ((swapInProfile P v x y).pref v).lt w b
      rw [show (swapInProfile P v x y).pref v = swapInBallot r x y by
        simp only [swapInProfile, updateProfile, if_pos, r]]
      exact hwb'
  | inr hset =>
      exfalso
      have hw_mem : w ∈ ({x, y} : Set A) := by
        have : w ∈ ({w, b} : Set A) := by simp
        simpa [hset] using this
      have hw_mem' : w = x ∨ w = y := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hw_mem
      rcases hw_mem' with hwx | hwy
      · exact hxw hwx.symm
      · have hb_mem : b ∈ ({x, y} : Set A) := by
          have : b ∈ ({w, b} : Set A) := by simp
          simpa [hset] using this
        have hb_mem' : b = x ∨ b = y := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hb_mem
        rcases hb_mem' with hbx | hby
        · have hxy : r.lt x y := hadj.1
          have hwb' : r.lt y x := by
            simpa [hwy, hbx, Prefers, r] using hwb
          exact lt_asymm hxy hwb'
        · exact hwb_ne (by simp [hwy, hby])

lemma downObtainable_of_swap (P : Profile V A) (v : V) (w x y : A)
    (hxw : x ≠ w) (hadj : Adjacent (P.pref v) x y) :
    DownObtainable (V := V) (A := A) w P (swapInProfile P v x y) := by
  intro u b hwb
  by_cases huv : u = v
  · have hwb' : Prefers P v w b := by simpa [huv] using hwb
    have hres := prefers_w_preserved_swap P v w x y b hxw hadj hwb'
    simpa [huv] using hres
  · unfold Prefers
    rw [show (swapInProfile P v x y).pref u = P.pref u by
      simp only [swapInProfile, updateProfile, if_neg huv]]
    exact hwb

lemma downObtainable_of_seq (w : A) {P Q : Profile V A} :
    DownObtainableSeq (V := V) (A := A) w P Q → DownObtainable (V := V) (A := A) w P Q := by
  intro hseq
  induction hseq with
  | refl P =>
      intro v b hwb
      simpa using hwb
  | step P Q v x y hxw hadj hrest ih =>
      intro v' b hwb
      have hswap : DownObtainable (V := V) (A := A) w P (swapInProfile P v x y) :=
        downObtainable_of_swap (P := P) (v := v) (w := w) (x := x) (y := y) hxw hadj
      have hwb' : Prefers (swapInProfile P v x y) v' w b := hswap v' b hwb
      exact ih v' b hwb'

lemma downMonotonicity_of_seq (f : VotingRule) (hf : DownMonotonicitySingleton f)
    {P Q : Profile V A} {w : A} (hP : f P = {w})
    (hseq : DownObtainableSeq (V := V) (A := A) w P Q) :
    f Q = {w} := by
  induction hseq with
  | refl P =>
      simpa using hP
  | step P Q v x y hxw hadj hrest ih =>
      have hswap : f (swapInProfile P v x y) = {w} :=
        hf P v w x y hP hxw hadj
      exact ih hswap

lemma downObtainableSeq_trans {w : A} {P Q R : Profile V A} :
    DownObtainableSeq (V := V) (A := A) w P Q →
    DownObtainableSeq (V := V) (A := A) w Q R →
    DownObtainableSeq (V := V) (A := A) w P R := by
  intro hPQ hQR
  induction hPQ with
  | refl P =>
      simpa using hQR
  | step P Q v x y hxw hadj hrest ih =>
      exact DownObtainableSeq.step P R v x y hxw hadj (ih hQR)

lemma downObtainableSeq_of_downSwapSeq_prefix
    (P : Profile V A) (v : V) (w : A) :
    ∀ {pre l l'}
      (hnodup : (pre ++ l).Nodup) (hcomplete : ∀ a, a ∈ pre ++ l)
      (hnodup' : (pre ++ l').Nodup) (hcomplete' : ∀ a, a ∈ pre ++ l'),
      DownSwapSeq w l l' →
      DownObtainableSeq w
        (updateProfile P v (linearOrderOfList (pre ++ l) hnodup hcomplete))
        (updateProfile P v (linearOrderOfList (pre ++ l') hnodup' hcomplete')) := by
  classical
  intro pre l l' hnodup hcomplete hnodup' hcomplete' hseq
  induction hseq generalizing pre with
  | refl l =>
      exact DownObtainableSeq.refl _
  | cons a hseq ih =>
      rename_i l1 l2
      have hnodup1 : ((pre ++ [a]) ++ l1).Nodup := by
        simpa [List.append_assoc] using hnodup
      have hcomplete1 : ∀ x, x ∈ (pre ++ [a]) ++ l1 := by
        simpa [List.append_assoc] using hcomplete
      have hnodup2 : ((pre ++ [a]) ++ l2).Nodup := by
        simpa [List.append_assoc] using hnodup'
      have hcomplete2 : ∀ x, x ∈ (pre ++ [a]) ++ l2 := by
        simpa [List.append_assoc] using hcomplete'
      simpa [List.append_assoc] using
        (ih (pre := pre ++ [a]) (hnodup := hnodup1) (hcomplete := hcomplete1)
          (hnodup' := hnodup2) (hcomplete' := hcomplete2))
  | swap ha =>
      rename_i a b l
      set L := pre ++ a :: b :: l
      set L' := pre ++ b :: a :: l
      have hnodup_ab : (a :: b :: l).Nodup := (List.nodup_append.mp hnodup).2.1
      have hdisj := (List.nodup_append.mp hnodup).2.2
      have ha_pre : a ∉ pre := by
        intro ha_mem
        have h := hdisj a ha_mem a (by simp)
        exact (h rfl).elim
      have hb_pre : b ∉ pre := by
        intro hb_mem
        have h := hdisj b hb_mem b (by simp)
        exact (h rfl).elim
      have hab_not : a ∉ b :: l := (List.nodup_cons.mp hnodup_ab).1
      have hnodup_bl : (b :: l).Nodup := (List.nodup_cons.mp hnodup_ab).2
      have hab : a ≠ b := by
        intro h
        apply hab_not
        simp [h]
      have ha_tail : a ∉ l := by
        intro ha_mem
        apply hab_not
        simp [ha_mem]
      have hb_tail : b ∉ l := (List.nodup_cons.mp hnodup_bl).1
      have hidxa : L.idxOf a = pre.length := by
        have h := idxOf_append_of_not_mem (l₁ := pre) (l₂ := a :: b :: l) ha_pre
        simpa [L] using h
      have hidxb : L.idxOf b = pre.length + 1 := by
        have h := idxOf_append_of_not_mem (l₁ := pre) (l₂ := a :: b :: l) hb_pre
        have hb' : (a :: b :: l).idxOf b = 1 := by
          simp [List.idxOf_cons_ne _ hab, List.idxOf_cons_self]
        simpa [L, hb', Nat.add_assoc] using h
      have hadj_list : AdjacentInList L a b := by
        simp [AdjacentInList, hidxa, hidxb]
      have hadj :
          Adjacent (linearOrderOfList L hnodup hcomplete) a b :=
        adjacent_linearOrderOfList_of_adjacentInList (l := L)
          (hnodup := hnodup) (hcomplete := hcomplete) hadj_list
      let P0 := updateProfile P v (linearOrderOfList L hnodup hcomplete)
      have hmap : L.map (Equiv.swap a b) = L' := by
        simpa [L, L'] using
          (map_swap_pre_cons_cons (pre := pre) (tail := l) (a := a) (b := b)
            ha_pre hb_pre ha_tail hb_tail)
      have hcomplete_map : ∀ x, x ∈ L.map (Equiv.swap a b) := by
        intro x
        refine List.mem_map.2 ?_
        exact ⟨Equiv.swap a b x, hcomplete _, by simp⟩
      have hswap_order :
          swapInBallot (linearOrderOfList L hnodup hcomplete) a b =
            linearOrderOfList L' hnodup' hcomplete' := by
        have hnodup_map : (L.map (Equiv.swap a b)).Nodup :=
          List.Nodup.map (fun _ _ h => (Equiv.swap a b).injective h) hnodup
        have hnodup_map' : L'.Nodup := by
          simpa [hmap] using hnodup_map
        have hcomplete_map' : ∀ x, x ∈ L' := by
          simpa [hmap] using hcomplete_map
        have hswap' :
            swapInBallot (linearOrderOfList L hnodup hcomplete) a b =
              linearOrderOfList L' hnodup_map' hcomplete_map' := by
          simpa [hmap] using
            (swapInBallot_linearOrderOfList_map_swap (l := L) (hnodup := hnodup)
              (hcomplete := hcomplete) (x := a) (y := b))
        have hcongr :
            linearOrderOfList L' hnodup_map' hcomplete_map' =
              linearOrderOfList L' hnodup' hcomplete' :=
          linearOrderOfList_congr
            (hnodup1 := hnodup_map')
            (hnodup2 := hnodup')
            (hcomplete1 := hcomplete_map')
            (hcomplete2 := hcomplete')
        exact hswap'.trans hcongr
      have hswap_profile :
          swapInProfile P0 v a b =
            updateProfile P v (linearOrderOfList L' hnodup' hcomplete') := by
        have hupdate :
            updateProfile P0 v (swapInBallot (linearOrderOfList L hnodup hcomplete) a b) =
              updateProfile P v (swapInBallot (linearOrderOfList L hnodup hcomplete) a b) := by
          simpa [P0] using
            (updateProfile_updateProfile_same (P := P) (v := v)
              (ballot1 := linearOrderOfList L hnodup hcomplete)
              (ballot2 := swapInBallot (linearOrderOfList L hnodup hcomplete) a b))
        calc
          swapInProfile P0 v a b
              = updateProfile P0 v (swapInBallot (linearOrderOfList L hnodup hcomplete) a b) := by
                  simp [swapInProfile_eq, P0, updateProfile]
          _ = updateProfile P v (swapInBallot (linearOrderOfList L hnodup hcomplete) a b) := hupdate
          _ = updateProfile P v (linearOrderOfList L' hnodup' hcomplete') := by
                simp [hswap_order]
      have hadj' : Adjacent (P0.pref v) a b := by
        simpa [P0, updateProfile] using hadj
      refine DownObtainableSeq.step
        (P := P0) (Q := updateProfile P v (linearOrderOfList L' hnodup' hcomplete'))
        v a b ha hadj' ?_
      simpa [hswap_profile] using (DownObtainableSeq.refl _)
  | trans h1 h2 ih1 ih2 =>
      rename_i l0 l1 l2
      have hperm1 : List.Perm l0 l1 := downSwapSeq_perm (w := w) h1
      have hperm_pre1 : List.Perm (pre ++ l0) (pre ++ l1) :=
        List.Perm.append_left _ hperm1
      have hnodup_mid : (pre ++ l1).Nodup :=
        (List.Perm.nodup_iff hperm_pre1).1 hnodup
      have hcomplete_mid : ∀ a, a ∈ pre ++ l1 := by
        intro a
        exact (hperm_pre1.mem_iff).1 (hcomplete a)
      have hseq1 :=
        ih1 (pre := pre) (hnodup := hnodup) (hcomplete := hcomplete)
          (hnodup' := hnodup_mid) (hcomplete' := hcomplete_mid)
      have hseq2 :=
        ih2 (pre := pre) (hnodup := hnodup_mid) (hcomplete := hcomplete_mid)
          (hnodup' := hnodup') (hcomplete' := hcomplete')
      exact downObtainableSeq_trans (w := w) hseq1 hseq2

lemma downObtainableSeq_of_downSwapSeq
    (P : Profile V A) (v : V) (w : A)
    {l l' : List A} (hnodup : l.Nodup) (hcomplete : ∀ a, a ∈ l)
    (hnodup' : l'.Nodup) (hcomplete' : ∀ a, a ∈ l')
    (hseq : DownSwapSeq w l l') :
    DownObtainableSeq w
      (updateProfile P v (linearOrderOfList l hnodup hcomplete))
      (updateProfile P v (linearOrderOfList l' hnodup' hcomplete')) := by
  simpa using
    (downObtainableSeq_of_downSwapSeq_prefix (P := P) (v := v) (w := w)
      (pre := []) (l := l) (l' := l')
      (hnodup := hnodup) (hcomplete := hcomplete)
      (hnodup' := hnodup') (hcomplete' := hcomplete') hseq)

lemma downObtainableSeq_updateProfile
    (P : Profile V A) (v : V) (w : A) (r' : LinearOrder A)
    (hdown : DownObtainable (V := V) (A := A) w P (updateProfile P v r')) :
    DownObtainableSeq w P (updateProfile P v r') := by
  have hseq_list :=
    downSwapSeq_of_downObtainable (P := P) (P' := updateProfile P v r') (v := v) (w := w) hdown
  have hseq_list' :
      DownSwapSeq w (listOfLinearOrder (P.pref v)) (listOfLinearOrder r') := by
    simpa [updateProfile] using hseq_list
  have hseq_profile :=
    downObtainableSeq_of_downSwapSeq (P := P) (v := v) (w := w)
      (l := listOfLinearOrder (P.pref v)) (l' := listOfLinearOrder r')
      (hnodup := listOfLinearOrder_nodup (r := P.pref v))
      (hcomplete := listOfLinearOrder_complete (r := P.pref v))
      (hnodup' := listOfLinearOrder_nodup (r := r'))
      (hcomplete' := listOfLinearOrder_complete (r := r')) hseq_list'
  have hself : updateProfile P v (P.pref v) = P := by
    classical
    apply Profile.ext
    intro u
    unfold updateProfile
    by_cases h : u = v
    · subst u
      simp only [if_true]
    · simp only [if_neg h]
  simpa [linearOrderOfList_listOfLinearOrder, hself] using hseq_profile

noncomputable def profileUpdateSet (P P' : Profile V A) (S : Finset V) : Profile V A := by
  classical
  exact { pref := fun v => if v ∈ S then P'.pref v else P.pref v }

omit [DecidableEq A] in
lemma profileUpdateSet_empty (P P' : Profile V A) :
    profileUpdateSet P P' (∅ : Finset V) = P := by
  classical
  apply Profile.ext
  intro v
  change (if v ∈ (∅ : Finset V) then P'.pref v else P.pref v) = P.pref v
  simp

omit [DecidableEq A] in
lemma profileUpdateSet_insert [DecidableEq V]
    (P P' : Profile V A) (S : Finset V) (v : V) (hv : v ∉ S) :
    profileUpdateSet P P' (insert v S) =
      updateProfile (profileUpdateSet P P' S) v (P'.pref v) := by
  classical
  apply Profile.ext
  intro u
  unfold profileUpdateSet updateProfile
  by_cases h : u = v
  · subst u
    simp only [Finset.mem_insert, true_or, if_true]
  · by_cases huS : u ∈ S
    · simp only [Finset.mem_insert, h, huS, false_or, if_true, if_false]
    · simp only [Finset.mem_insert, h, huS, or_false, if_false]

omit [DecidableEq A] in
lemma profileUpdateSet_univ (P P' : Profile V A) :
    profileUpdateSet P P' (Finset.univ : Finset V) = P' := by
  classical
  apply Profile.ext
  intro v
  change (if v ∈ (Finset.univ : Finset V) then P'.pref v else P.pref v) = P'.pref v
  simp only [Finset.mem_univ, if_true]

lemma downObtainableSeq_of_downObtainable
    {P P' : Profile V A} {w : A}
    (hdown : DownObtainable (V := V) (A := A) w P P') :
    DownObtainableSeq w P P' := by
  classical
  have hseq : ∀ S : Finset V, DownObtainableSeq w P (profileUpdateSet P P' S) := by
    intro S
    refine Finset.induction ?base ?step S
    · simpa [profileUpdateSet_empty] using (DownObtainableSeq.refl P)
    · intro v S hv hS
      have hdown_v :
          DownObtainable w (profileUpdateSet P P' S)
            (updateProfile (profileUpdateSet P P' S) v (P'.pref v)) := by
        intro u b hwb
        by_cases huv : u = v
        · cases huv
          have hwb' : Prefers P v w b := by
            unfold Prefers at hwb ⊢
            rw [show (profileUpdateSet P P' S).pref v = P.pref v by
              simp only [profileUpdateSet, if_neg hv]] at hwb
            exact hwb
          have hwb'' : Prefers P' v w b := hdown v b hwb'
          unfold Prefers at hwb'' ⊢
          rw [show (updateProfile (profileUpdateSet P P' S) v (P'.pref v)).pref v =
              P'.pref v by simp only [updateProfile, if_pos]]
          exact hwb''
        · unfold Prefers at hwb ⊢
          rw [show (updateProfile (profileUpdateSet P P' S) v (P'.pref v)).pref u =
              (profileUpdateSet P P' S).pref u by simp only [updateProfile, if_neg huv]]
          exact hwb
      have hstep :=
        downObtainableSeq_updateProfile (P := profileUpdateSet P P' S) (v := v)
          (w := w) (r' := P'.pref v) hdown_v
      have htrans := downObtainableSeq_trans (w := w) hS hstep
      simpa [profileUpdateSet_insert, hv] using htrans
  simpa [profileUpdateSet_univ] using hseq (Finset.univ : Finset V)

lemma downMonotonicity_of_singleton (f : VotingRule) (hf : DownMonotonicitySingleton f) :
    DownMonotonicity f := by
  classical
  intro V A _ _ P P' w hP hdown
  have hseq : DownObtainableSeq (V := V) (A := A) w P P' :=
    downObtainableSeq_of_downObtainable (V := V) (A := A) (w := w) hdown
  exact downMonotonicity_of_seq (f := f) (hf := hf) (P := P) (Q := P') (w := w) hP hseq

lemma downObtainableSeq_step_of_adjacentInList
    (P : Profile V A) (v : V) (w x y : A)
    (hxw : x ≠ w) (hadj : AdjacentInList (listOfLinearOrder (P.pref v)) x y) :
    DownObtainableSeq (V := V) (A := A) w P (swapInProfile P v x y) := by
  classical
  have hadj' : AdjacentInOrder (P.pref v) x y :=
    (adjacentInOrder_iff_adjacentInList (r := P.pref v) x y).2 hadj
  have hadj'' : Adjacent (P.pref v) x y := by
    simpa [Adjacent, AdjacentInOrder] using hadj'
  exact DownObtainableSeq.step P (swapInProfile P v x y) v x y hxw hadj''
    (DownObtainableSeq.refl _)

noncomputable def swapDownOnceProfile [DecidableEq A]
    (P : Profile V A) (v : V) (x : A) : Profile V A := by
  classical
  let l := listOfLinearOrder (P.pref v)
  by_cases h : l.idxOf x + 1 < l.length
  · exact swapInProfile P v x (l[l.idxOf x + 1]'h)
  · exact P

noncomputable def swapDownNProfile [DecidableEq A]
    (P : Profile V A) (v : V) (x : A) : Nat → Profile V A
  | 0 => P
  | n + 1 => swapDownNProfile (swapDownOnceProfile P v x) v x n

lemma downObtainableSeq_swapDownOnce
    (P : Profile V A) (v : V) (w x : A) (hxw : x ≠ w) :
    DownObtainableSeq (V := V) (A := A) w P (swapDownOnceProfile P v x) := by
  classical
  let l := listOfLinearOrder (P.pref v)
  by_cases h : l.idxOf x + 1 < l.length
  · have hadj : AdjacentInList l x (l[l.idxOf x + 1]'h) :=
      adjacentInList_idxOf_succ (l := l) (x := x)
        (hnodup := listOfLinearOrder_nodup (r := P.pref v)) h
    have hseq :=
      downObtainableSeq_step_of_adjacentInList (P := P) (v := v) (w := w) (x := x)
        (y := l[l.idxOf x + 1]'h) hxw hadj
    simpa [swapDownOnceProfile, l, h] using hseq
  · simp [swapDownOnceProfile, l, h, DownObtainableSeq.refl]

lemma downObtainableSeq_swapDownN
    (P : Profile V A) (v : V) (w x : A) (n : Nat) (hxw : x ≠ w) :
    DownObtainableSeq (V := V) (A := A) w P (swapDownNProfile P v x n) := by
  classical
  induction n generalizing P with
  | zero =>
      simp [swapDownNProfile, DownObtainableSeq.refl]
  | succ n ih =>
      simp [swapDownNProfile]
      have hstep := downObtainableSeq_swapDownOnce (P := P) (v := v) (w := w) (x := x) hxw
      have hrest := ih (P := swapDownOnceProfile P v x)
      exact downObtainableSeq_trans (w := w) hstep hrest

lemma downObtainable_swapDownN
    (P : Profile V A) (v : V) (w x : A) (n : Nat) (hxw : x ≠ w) :
    DownObtainable (V := V) (A := A) w P (swapDownNProfile P v x n) := by
  exact downObtainable_of_seq (w := w)
    (downObtainableSeq_swapDownN (P := P) (v := v) (w := w) (x := x) (n := n) hxw)

lemma downMonotonicity_swapDownN (f : VotingRule) (hf : DownMonotonicitySingleton f)
    (P : Profile V A) (v : V) (w x : A) (n : Nat) (hxw : x ≠ w)
    (hP : f P = {w}) :
    f (swapDownNProfile P v x n) = {w} := by
  refine downMonotonicity_of_seq (f := f) (hf := hf) (P := P) (Q := swapDownNProfile P v x n)
    (w := w) hP ?_
  exact downObtainableSeq_swapDownN (P := P) (v := v) (w := w) (x := x) (n := n) hxw

omit [DecidableEq A] in
lemma downMonotonicity_of_downObtainable (f : VotingRule) (hf : DownMonotonicity f)
    {P P' : Profile V A} {w : A} (hP : f P = {w})
    (hdown : DownObtainable (V := V) (A := A) w P P') :
    f P' = {w} := by
  exact hf P P' w hP hdown

/-! ## Main Theorem -/

/-- Lemma 2.4 from Taylor (2002). -/
theorem downMonotonicity_of_opt_pess_sp (f : VotingRule)
    (hf_total : IsVotingRule f)
    (hf_opt : OptimistStrategyproof f)
    (hf_pess : PessimistStrategyproof f) :
    DownMonotonicitySingleton f := by
  intro V A _ _ _ P v w x y hfP hxw hadj
  classical
  by_contra hne
  let P' := swapInProfile P v x y
  have hP' : updateProfile P v (P'.pref v) = P' := by
    apply Profile.ext
    intro u
    unfold P' swapInProfile updateProfile
    by_cases h : u = v
    · subst u
      simp only [if_true]
    · simp only [if_neg h]
  have hP : updateProfile P' v (P.pref v) = P := by
    simpa [P'] using (profile_eq_update_of_swap P v x y).symm
  let _ : Nonempty A := ⟨w⟩
  have hnonempty : (f P').Nonempty := hf_total P'
  have hex_ne : ∃ v' ∈ f P', v' ≠ w := by
    by_cases hw : w ∈ f P'
    · by_contra hno
      have hall : ∀ z ∈ f P', z = w := by
        intro z hz
        by_contra hne'
        exact hno ⟨z, hz, hne'⟩
      have hset : f P' = {w} := by
        ext z
        constructor
        · intro hz
          have hz' : z = w := hall z hz
          simp [hz']
        · intro hz
          have hz' : z = w := by simpa using hz
          subst hz'
          exact hw
      exact hne hset
    · obtain ⟨v', hv'⟩ := hnonempty
      refine ⟨v', hv', ?_⟩
      intro h
      exact hw (h ▸ hv')
  obtain ⟨v', hv'mem, hv'w⟩ := hex_ne

  let r := P.pref v
  have hxy : r.lt x y := hadj.1
  have hvw : r.lt v' w ∨ r.lt w v' := by
    let _ := r
    simpa using (lt_or_gt_of_ne hv'w)

  cases hvw with
  | inl hv'lt =>
      -- Optimist manipulation using true preferences P.
      have hmanip : ∃ y' ∈ f P', ∀ x' ∈ f P, Prefers P v y' x' := by
        refine ⟨v', hv'mem, ?_⟩
        intro x' hx'
        have hxw' : x' = w := by simpa [hfP] using hx'
        subst hxw'
        simpa [Prefers, r] using hv'lt
      have hmanip' :
          ∃ y' ∈ f (updateProfile P v (P'.pref v)),
            ∀ x' ∈ f P, Prefers P v y' x' := by
        simpa [hP'] using hmanip
      exact hf_opt P v (P'.pref v) hmanip'
  | inr hwlt =>
      -- Pessimist manipulation using true preferences P'.
      have hset_ne : ({w, v'} : Set A) ≠ ({x, y} : Set A) := by
        intro hset
        have hw_mem : w ∈ ({x, y} : Set A) := by
          have : w ∈ ({w, v'} : Set A) := by simp
          simpa [hset] using this
        have hw_mem' : w = x ∨ w = y := by
          simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hw_mem
        rcases hw_mem' with hwx | hwy
        · exact hxw hwx.symm
        · have hv_mem : v' ∈ ({x, y} : Set A) := by
            have : v' ∈ ({w, v'} : Set A) := by simp
            simpa [hset] using this
          have hv_mem' : v' = x ∨ v' = y := by
            simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hv_mem
          rcases hv_mem' with hvx | hvy
          · subst hwy hvx
            let _ := r
            exact (lt_asymm hxy hwlt)
          · exact hv'w (by simp [hwy, hvy])
      have horder :
          (swapInBallot r x y).lt w v' ↔ r.lt w v' := by
        have h :=
          swap_adjacent_only_changes_xy (r := r) (x := x) (y := y) hadj w v' (Ne.symm hv'w)
        cases h with
        | inl hpres => exact hpres
        | inr hset => exact (hset_ne hset).elim
      have hr' : P'.pref v = swapInBallot r x y := by
        simp [P', swapInProfile, updateProfile, r]
      have hwlt' : P'.pref v |>.lt w v' := by
        have : (swapInBallot r x y).lt w v' := horder.mpr hwlt
        rw [hr']
        exact this
      have hmanip :
          ∃ x' ∈ f P', ∀ y' ∈ f (updateProfile P' v (P.pref v)), Prefers P' v y' x' := by
        refine ⟨v', hv'mem, ?_⟩
        intro y' hy'
        have hy'P : y' ∈ f P := by simpa [hP] using hy'
        have hyw : y' = w := by simpa [hfP] using hy'P
        subst hyw
        simpa [Prefers, hr'] using hwlt'
      exact hf_pess P' v (P.pref v) hmanip

end ProfileLevel

end SocialChoice
