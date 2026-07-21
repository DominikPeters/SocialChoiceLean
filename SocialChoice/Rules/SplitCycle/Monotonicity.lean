import SocialChoice.Axioms.Monotonicity
import SocialChoice.Margin
import SocialChoice.Rules.SplitCycle.Defs

namespace SocialChoice

open Finset

lemma margin_lemma' {V A : Type} [Fintype V] [Fintype A]
    (P P' : Profile V A) (a b : A) :
    (∀ v : V, (Prefers P v a b → Prefers P' v a b) ∧
      (Prefers P' v b a → Prefers P v b a)) →
    margin P a b ≤ margin P' a b := by
  intro lift
  by_cases h : a = b
  · subst h
    simp [self_margin_zero]
  · exact margin_lemma P P' a b h lift

lemma margin_lt_margin_of_lift {V A : Type} [Fintype V] [Fintype A]
    (P P' : Profile V A) (y x : A) :
    simpleLift P' P x → margin P' y x ≤ margin P y x := by
  intro lift
  rcases lift with ⟨_, lift2⟩
  by_cases hxy : x = y
  · subst hxy
    simp [self_margin_zero]
  · have h1 : margin P x y ≤ margin P' x y :=
      margin_lemma P P' x y hxy (fun v => lift2 y v)
    have h2 : - margin P' x y ≤ - margin P x y := neg_le_neg h1
    have hskewP : margin P y x = - margin P x y := by
      simpa [skew_symmetric] using (margin_antisymmetric (P := P)) y x
    have hskewP' : margin P' y x = - margin P' x y := by
      simpa [skew_symmetric] using (margin_antisymmetric (P := P')) y x
    simpa [hskewP, hskewP'] using h2

theorem split_cycle_monotonicity : Monotonicity splitCycle := by
  intro V A _ _ P P' x hx hLift
  classical
  refine Finset.mem_filter.mpr ?_
  refine ⟨Finset.mem_univ x, ?_⟩
  intro y hy
  rcases hy with ⟨hpos', hnocycle'⟩
  have hle : margin P' y x ≤ margin P y x :=
    margin_lt_margin_of_lift P P' y x hLift
  have hpos : margin_pos P y x := by
    exact lt_of_lt_of_le hpos' hle
  have hxcond : ∀ y, ¬ splitCycleDefeats P y x := (Finset.mem_filter.mp hx).2
  have hcycleP :
      ∃ c : List A, y ∈ c ∧ x ∈ c ∧
        cycle (fun a b => margin P y x ≤ margin P a b) c := by
    by_contra hno
    exact hxcond y ⟨hpos, hno⟩
  rcases hcycleP with ⟨c, hymem, hxmem, hcycle⟩
  -- Following the Lean3 proof, rotate the cycle to start at `x`, take the prefix
  -- to the first `y`, and use `to_path` to remove repeats while preserving endpoints.
  -- This yields a chain from `x` to `y` whose edges do not point into `x`,
  -- so only the `y → x` edge can decrease.
  let R : A → A → Prop := fun a b => margin P y x ≤ margin P a b
  let R' : A → A → Prop := fun a b => margin P' y x ≤ margin P' a b
  set crot : List A := c.rotate (List.idxOf x c)
  have hcycle_rot : cycle R crot := by
    have hrot := rotate'_cycle_of_cycle (c := c) (n := List.idxOf x c) hcycle
    simpa [crot, List.rotate_eq_rotate'] using hrot
  rcases hcycle_rot with ⟨hcrot_ne, hchain_rot⟩
  have hycrot : y ∈ crot := by
    have hmem := (List.mem_rotate (l := c) (a := y) (n := List.idxOf x c))
    exact hmem.mpr hymem
  have hidx_y : List.idxOf y crot < crot.length := List.idxOf_lt_length_iff.2 hycrot
  set l3 : List A := crot.take (List.idxOf y crot + 1)
  have hchain_l3 : List.IsChain R l3 := by
    have hchain_take :=
      chain'_take_of_chain (l := crot) (a := hcrot_ne)
        (n := List.idxOf y crot + 1) hchain_rot
    simp [l3]
    exact hchain_take
  have hne_l3 : l3 ≠ [] := by
    have hle : List.idxOf y crot + 1 ≤ crot.length := Nat.succ_le_of_lt hidx_y
    have hlen :
        l3.length = List.idxOf y crot + 1 := by
      simpa [l3] using
        (List.length_take_of_le (l := crot) (i := List.idxOf y crot + 1) hle)
    have hpos : 0 < l3.length := by
      simp [hlen]
    exact List.length_pos_iff_ne_nil.mp hpos
  set l : List A := to_path l3
  have hne_l : l ≠ [] := by
    simp [l]
    exact to_path_ne_nil_iff l3 hne_l3
  have hchain_l : List.IsChain R l := by
    simp [l]
    exact to_path_chain'_of_chain' (l := l3) hchain_l3
  have hnodup_l : l.Nodup := by
    simp [l]
    exact to_path_nodup l3
  have hhead_crot : crot.head hcrot_ne = x := by
    have h0c : 0 < crot.length := List.length_pos_of_ne_nil hcrot_ne
    have hidx_x : List.idxOf x c < c.length := List.idxOf_lt_length_iff.2 hxmem
    have hget0 :
        crot[0]'h0c = x := by
      have hget0' := List.getElem_rotate (l := c) (n := List.idxOf x c) (k := 0)
        (h := by
          simpa [crot, List.length_rotate] using (List.length_pos_of_mem hxmem))
      simp [crot, Nat.mod_eq_of_lt hidx_x]
    calc
      crot.head hcrot_ne = crot[0]'h0c := List.head_eq_getElem_zero (l := crot) hcrot_ne
      _ = x := hget0
  have hhead_l3 : l3.head hne_l3 = x := by
    have hhead_take :=
      List.head_take (l := crot) (i := List.idxOf y crot + 1) (h := hne_l3)
    simpa [l3, hhead_crot] using hhead_take
  have h0_l3 : 0 < l3.length := List.length_pos_of_ne_nil hne_l3
  have hfirst_l3 : l3[0]'h0_l3 = x := by
    calc
      l3[0]'h0_l3 = l3.head hne_l3 := by
        symm
        exact List.head_eq_getElem_zero (l := l3) hne_l3
      _ = x := hhead_l3
  have hlast_l3 : l3.getLast hne_l3 = y := by
    have hlast :=
      getLast_take_idxOf (l := crot) (a := y) hycrot
    simpa [l3] using hlast
  have h0_l : 0 < l.length := by
    simpa [l] using (to_path_length_pos l3 hne_l3)
  have hfirst_l :
      l[0]'h0_l = x := by
    have hfirst :=
      to_path_first_elem (l := l3) (h := hne_l3)
    have hfirst' :
        l[0]'h0_l = l3[0]'(List.length_pos_of_ne_nil hne_l3) := by
      simpa [l] using hfirst
    exact hfirst'.trans hfirst_l3
  have hlast_l : l.getLast hne_l = y := by
    have hlast :=
      to_path_last_elem (l := l3) (h := hne_l3)
    have hlast' : l.getLast hne_l = l3.getLast hne_l3 := by
      simpa [l] using hlast
    exact hlast'.trans hlast_l3
  have hxmem_l : x ∈ l := by
    have hxmem' : l[0] = x := by
      simpa using hfirst_l
    exact List.mem_of_getElem (l := l) (i := 0) (a := x) hxmem'
  have hymem_l : y ∈ l := by
    have hymem' : l.getLast hne_l ∈ l := List.getLast_mem hne_l
    simpa [hlast_l] using hymem'
  have hchain_l' : List.IsChain R' l := by
    refine (List.isChain_iff_getElem (R := R') (l := l)).2 ?_
    intro i hi
    have hchain_l_get :=
      (List.isChain_iff_getElem (R := R) (l := l)).1 hchain_l
    have hrel := hchain_l_get i hi
    have hthresh : margin P' y x ≤ margin P y x :=
      margin_lt_margin_of_lift P P' y x hLift
    have hrel' : margin P' y x ≤ margin P (l[i]) (l[i + 1]) :=
      le_trans hthresh hrel
    by_cases h0 : i = 0
    · subst h0
      have hrel'' : margin P' y x ≤ margin P x (l[1]) := by
        simpa [hfirst_l] using hrel'
      have hmargin_x :
          margin P x (l[1]) ≤ margin P' x (l[1]) := by
        rcases hLift with ⟨_, lift2⟩
        exact margin_lemma' P P' x (l[1]) (fun v => lift2 (l[1]) v)
      have hmargin_x' :
          margin P x (l[1]) ≤ margin P' (l[0]) (l[1]) := by
        simpa [hfirst_l] using hmargin_x
      exact le_trans hrel'' hmargin_x'
    · have hpair : List.Pairwise (fun a b => a ≠ b) l := by
        simpa [List.Nodup] using hnodup_l
      have hpair' := (List.pairwise_iff_getElem (R := fun a b => a ≠ b) (l := l)).1 hpair
      have hlt : i < l.length := by
        exact Nat.lt_of_succ_lt hi
      have hne_i : l[i] ≠ x := by
        have hpair0i : l[0]'h0_l ≠ l[i]'hlt := by
          exact hpair' 0 i h0_l hlt (Nat.pos_of_ne_zero h0)
        intro hEq
        apply hpair0i
        simp [hfirst_l, hEq]
      have hne_i1 : l[i + 1] ≠ x := by
        have hpair01 : l[0]'h0_l ≠ l[i + 1]'hi := by
          exact hpair' 0 (i + 1) h0_l hi (Nat.succ_pos _)
        intro hEq
        apply hpair01
        simp [hfirst_l, hEq]
      have hmargin_eq :
          margin P (l[i]) (l[i + 1]) = margin P' (l[i]) (l[i + 1]) := by
        exact margin_eq_of_simpleLift P P' x (l[i]) (l[i + 1]) hne_i hne_i1 hLift
      have hmargin_le :
          margin P (l[i]) (l[i + 1]) ≤ margin P' (l[i]) (l[i + 1]) := by
        simp [hmargin_eq]
      exact le_trans hrel' hmargin_le
  have hcycle_l : cycle R' l := by
    refine ⟨hne_l, ?_⟩
    have hhead_l : l.head hne_l = x := by
      have hhead_eq := List.head_eq_getElem_zero (l := l) hne_l
      simpa [hfirst_l] using hhead_eq
    have hrel : R' (l.getLast hne_l) (l.head hne_l) := by
      dsimp [R']
      simp [hlast_l, hhead_l]
    exact List.IsChain.cons_of_ne_nil hne_l hchain_l' hrel
  exact hnocycle' ⟨l, hymem_l, hxmem_l, hcycle_l⟩

end SocialChoice
