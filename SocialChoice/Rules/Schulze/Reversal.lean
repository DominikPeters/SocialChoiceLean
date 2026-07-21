import SocialChoice.Axioms.Reversal
import SocialChoice.Margin
import SocialChoice.Cycles
import SocialChoice.Rules.Schulze.Defs
import SocialChoice.Rules.Schulze.Path
import SocialChoice.Rules.Schulze.Transitivity
import SocialChoice.Rules.SplitCycle.Reversal
import Mathlib.Tactic.FinCases

namespace SocialChoice

open Finset

lemma minList_reverse : ∀ l : List Int, minList l.reverse = minList l
  | [] => by
      simp [minList]
  | m :: ms => by
      cases ms with
      | nil =>
          simp [minList]
      | cons n ns =>
          have hs : (n :: ns).reverse ≠ [] := by simp
          have ht : ([m] : List Int) ≠ [] := by simp
          calc
            minList ((m :: n :: ns).reverse)
                = minList ((n :: ns).reverse ++ [m]) := by simp
            _ = min (minList (n :: ns).reverse) (minList [m]) := by
                simpa using (minList_append (s := (n :: ns).reverse) (t := [m]) hs ht)
            _ = min (minList (n :: ns)) m := by
                have hrev : minList (ns.reverse ++ [n]) = minList (n :: ns) := by
                  simpa [List.reverse_cons] using (minList_reverse (l := n :: ns))
                calc
                  min (minList (n :: ns).reverse) (minList [m]) =
                      min (minList (ns.reverse ++ [n])) (minList [m]) := by
                        simp [List.reverse_cons]
                  _ = min (minList (ns.reverse ++ [n])) m := by
                        simp [minList]
                  _ = min (minList (n :: ns)) m := by
                        simp [hrev]
            _ = min m (minList (n :: ns)) := by
                simp [min_comm]
            _ = minList (m :: n :: ns) := by
                have hne : (n :: ns) ≠ [] := by simp
                have hfold := foldl_min_eq_min (m := m) (t := n :: ns) hne
                simpa [minList] using hfold.symm

lemma pathMargins_reverse_profile {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) :
    ∀ l : List A, pathMargins (reverse_profile P) l = (pathMargins P l.reverse).reverse
  | [] => by
      simp [pathMargins]
  | [a] => by
      simp [pathMargins]
  | a :: b :: t => by
      cases t with
      | nil =>
          simp [pathMargins, margin_reverse_eq]
      | cons c t' =>
          have hsplit :
              pathMargins P (t'.reverse ++ [c, b, a]) =
                pathMargins P (t'.reverse ++ [c, b]) ++ [margin P b a] := by
            have h := pathMargins_append_cons
              (P := P) (l := t'.reverse ++ [c]) (b := b) (u := [a]) (by simp)
            simpa [pathMargins, List.append_assoc] using h
          have hstep :
              pathMargins (reverse_profile P) (b :: c :: t') =
                (pathMargins P (t'.reverse ++ [c, b])).reverse := by
            simpa [List.reverse_cons, List.append_assoc] using
              (pathMargins_reverse_profile (P := P) (l := b :: c :: t'))
          calc
            pathMargins (reverse_profile P) (a :: b :: c :: t') =
                margin (reverse_profile P) a b ::
                  pathMargins (reverse_profile P) (b :: c :: t') := by
                  simp [pathMargins]
            _ = margin P b a :: (pathMargins P (t'.reverse ++ [c, b])).reverse := by
                  simp [margin_reverse_eq, hstep]
            _ = (pathMargins P (t'.reverse ++ [c, b, a])).reverse := by
                  calc
                    margin P b a :: (pathMargins P (t'.reverse ++ [c, b])).reverse
                        = (pathMargins P (t'.reverse ++ [c, b]) ++ [margin P b a]).reverse := by
                            simp [List.reverse_append]
                    _ = (pathMargins P (t'.reverse ++ [c, b, a])).reverse := by
                            exact (congrArg List.reverse hsplit).symm
            _ = (pathMargins P (a :: b :: c :: t').reverse).reverse := by
                  simp [List.reverse_cons, List.append_assoc]

lemma pathStrength_reverse_profile {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (l : List A) :
    pathStrength (reverse_profile P) l = pathStrength P l.reverse := by
  calc
    pathStrength (reverse_profile P) l =
        minList (pathMargins (reverse_profile P) l) := by
          simp [pathStrength_eq_minList]
    _ = minList ((pathMargins P l.reverse).reverse) := by
          simp [pathMargins_reverse_profile]
    _ = minList (pathMargins P l.reverse) := by
          simp [minList_reverse]
    _ = pathStrength P l.reverse := by
          symm
          simp [pathStrength_eq_minList]

lemma mem_pathsUpTo_reverse {A : Type} [Fintype A]
    (l : List A) (a b : A) :
    l ∈ pathsUpTo (A := A) (Fintype.card A) a b →
      l.reverse ∈ pathsUpTo (A := A) (Fintype.card A) b a := by
  intro hl
  classical
  rcases path_props_of_mem_pathsUpTo (l := l) (a := a) (b := b) hl with
    ⟨hhead, hlast, hnodup, hlen⟩
  have hne : l ≠ [] := by
    intro hnil
    simp [hnil] at hlen
  have hne_rev : l.reverse ≠ [] := by
    intro hnil
    exact hne (List.reverse_eq_nil_iff.mp hnil)
  have hhead_val : l.head hne = a := by
    have hhead_eq : l.head? = some (l.head hne) := List.head?_eq_some_head (l := l) hne
    have : some (l.head hne) = some a := by simpa [hhead_eq] using hhead
    exact Option.some.inj this
  have hlast_val : List.getLast l hne = b := by
    have hlast_eq : l.getLast? = some (List.getLast l hne) :=
      List.getLast?_eq_some_getLast (l := l) hne
    have : some (List.getLast l hne) = some b := by simpa [hlast_eq] using hlast
    exact Option.some.inj this
  have hhead_rev_val : l.reverse.head hne_rev = List.getLast l hne := by
    have h := getLast_reverse_eq_head (c := l.reverse) (hne := hne_rev)
    simp [h.symm]
  have hhead_rev : l.reverse.head? = some b := by
    have hhead_eq : l.reverse.head? = some (l.reverse.head hne_rev) :=
      List.head?_eq_some_head (l := l.reverse) hne_rev
    have : l.reverse.head hne_rev = b := by
      calc
        l.reverse.head hne_rev = List.getLast l hne := hhead_rev_val
        _ = b := hlast_val
    simp [hhead_eq, this]
  have hlast_rev : l.reverse.getLast? = some a := by
    have hlast_eq : l.reverse.getLast? = some (List.getLast l.reverse hne_rev) :=
      List.getLast?_eq_some_getLast (l := l.reverse) hne_rev
    have hlast_rev_val : List.getLast l.reverse hne_rev = l.head hne := by
      simp [getLast_reverse_eq_head (c := l) (hne := hne)]
    have : List.getLast l.reverse hne_rev = a := by
      calc
        List.getLast l.reverse hne_rev = l.head hne := hlast_rev_val
        _ = a := hhead_val
    simp [hlast_eq, this]
  have hnodup_rev : l.reverse.Nodup := by
    exact (List.nodup_reverse).2 hnodup
  have hlen_rev : 2 ≤ l.reverse.length := by
    simpa using hlen
  exact mem_pathsUpTo_of_props (l := l.reverse) (a := b) (b := a)
    hhead_rev hlast_rev hnodup_rev hlen_rev

lemma strongestPath_reverse_profile {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) :
    strongestPath (reverse_profile P) a b = strongestPath P b a := by
  classical
  by_cases hne : (pathsUpTo (A := A) (Fintype.card A) a b).Nonempty
  · rcases exists_max_path_props (P := reverse_profile P) (a := a) (b := b) hne with
      ⟨l, hl, _hhead, _hlast, _hnodup, _hlen, hstrength_rev⟩
    have hl_rev :
        l.reverse ∈ pathsUpTo (A := A) (Fintype.card A) b a :=
      mem_pathsUpTo_reverse (l := l) (a := a) (b := b) hl
    have hle :
        pathStrength P l.reverse ≤ strongestPath P b a :=
      pathStrength_of_mem_pathsUpTo_le_strongestPath (P := P) (a := b) (b := a)
        (l := l.reverse) hl_rev
    have hstrength :
        pathStrength P l.reverse = strongestPath (reverse_profile P) a b := by
      simp [pathStrength_reverse_profile (P := P) (l := l)] at hstrength_rev
      exact hstrength_rev
    have hle1 : strongestPath (reverse_profile P) a b ≤ strongestPath P b a := by
      simpa [hstrength] using hle
    -- reverse the argument for the other direction
    have hne' : (pathsUpTo (A := A) (Fintype.card A) b a).Nonempty := by
      exact ⟨l.reverse, hl_rev⟩
    rcases exists_max_path_props (P := P) (a := b) (b := a) hne' with
      ⟨l', hl', _hhead', _hlast', _hnodup', _hlen', hstrength_p⟩
    have hl'_rev :
        l'.reverse ∈ pathsUpTo (A := A) (Fintype.card A) a b :=
      mem_pathsUpTo_reverse (l := l') (a := b) (b := a) hl'
    have hle' :
        pathStrength (reverse_profile P) l'.reverse ≤
          strongestPath (reverse_profile P) a b :=
      pathStrength_of_mem_pathsUpTo_le_strongestPath
        (P := reverse_profile P) (a := a) (b := b) (l := l'.reverse) hl'_rev
    have hstrength' :
        pathStrength (reverse_profile P) l'.reverse = strongestPath P b a := by
      have hrev := pathStrength_reverse_profile (P := P) (l := l'.reverse)
      have hrev' : pathStrength (reverse_profile P) l'.reverse = pathStrength P l' := by
        simpa [List.reverse_reverse] using hrev
      exact hrev'.trans hstrength_p
    have hle2 : strongestPath P b a ≤ strongestPath (reverse_profile P) a b := by
      simpa [hstrength'] using hle'
    exact le_antisymm hle1 hle2
  · -- empty paths: strongestPath falls back to margin
    have hne' : ¬ (pathsUpTo (A := A) (Fintype.card A) b a).Nonempty := by
      intro hne'
      rcases hne' with ⟨l, hl⟩
      have hl' := mem_pathsUpTo_reverse (l := l) (a := b) (b := a) hl
      exact hne ⟨l.reverse, hl'⟩
    simp [strongestPath, hne, hne', margin_reverse_eq]

lemma schulzeDefeats_reverse_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x y : A) :
    schulzeDefeats (reverse_profile P) y x ↔ schulzeDefeats P x y := by
  simp [schulzeDefeats, strongestPath_reverse_profile]

lemma schulzeDefeats_acyclic {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) : acyclic (schulzeDefeats P) := by
  classical
  intro c hcycle
  rcases hcycle with ⟨hne, hchain⟩
  have hmem : List.getLast c hne ∈ c := List.getLast_mem hne
  let _ : Trans (schulzeDefeats P) (schulzeDefeats P) (schulzeDefeats P) :=
    ⟨by
      intro a b c hab hbc
      exact schulzeDefeats_trans (P := P) hab hbc⟩
  have hrel : schulzeDefeats P (List.getLast c hne) (List.getLast c hne) := by
    exact (List.IsChain.rel_cons (R := schulzeDefeats P) (a := List.getLast c hne)
      (l := c) hchain hmem)
  exact (schulzeDefeats_asymm (P := P) hrel) hrel

theorem schulze_singleton_reversal_symmetry : SingletonReversalSymmetry schulze := by
  intro V A _ _ P x hnontriv hxwin
  classical
  have hxdef : ∃ y, schulzeDefeats P x y := by
    by_contra hnone
    have hnone' : ∀ y, ¬ schulzeDefeats P x y := by
      intro y hy
      exact hnone ⟨y, hy⟩
    rcases hnontriv with ⟨y0, hy0⟩
    let S := {y : A // y ≠ x}
    let y0S : S := ⟨y0, by simpa [eq_comm] using hy0⟩
    have hdefeater : ∀ a : S, ∃ b : S, schulzeDefeats P b.1 a.1 := by
      intro a
      have ha_notmem : a.1 ∉ schulze P := by
        intro ha_mem
        have : a.1 = x := by
          have : a.1 ∈ ({x} : Finset A) := by
            simpa [hxwin] using ha_mem
          simpa using (Finset.mem_singleton.mp this)
        exact a.property this
      have hnotall : ¬ ∀ y, ¬ schulzeDefeats P y a.1 := by
        intro hall
        exact ha_notmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hall⟩)
      obtain ⟨b, hb⟩ := not_forall.mp hnotall
      have hb' : schulzeDefeats P b a.1 := by
        exact not_not.mp hb
      have hbx : b ≠ x := by
        intro hEq
        subst hEq
        exact (hnone' a.1) hb'
      exact ⟨⟨b, hbx⟩, hb'⟩
    rcases cycle_of_forall_defeater (x0 := y0S)
        (R := fun a b : S => schulzeDefeats P a.1 b.1) hdefeater with
      ⟨cS, hcycleS⟩
    have hcycleA :
        cycle (schulzeDefeats P) (cS.map Subtype.val) := by
      simpa using (cycle_map (f := Subtype.val) (P := schulzeDefeats P) hcycleS)
    exact (schulzeDefeats_acyclic P) _ hcycleA
  rcases hxdef with ⟨y, hydef⟩
  have hydef' : schulzeDefeats (reverse_profile P) y x := by
    simpa [schulzeDefeats_reverse_iff] using hydef
  by_contra hxmem
  have hxcond : ∀ z, ¬ schulzeDefeats (reverse_profile P) z x :=
    (Finset.mem_filter.mp hxmem).2
  exact (hxcond y) hydef'

section SchulzeReversalCounterexample

open Finset

lemma reversalCounterexample_margin_from_0_le_zero (y : Fin 3) :
    margin reversalCounterexampleProfile (0 : Fin 3) y ≤ 0 := by
  fin_cases y
  · simp [reversalCounterexampleProfile,
      margin_eq_marginList (ballots := reversalCounterexampleBallots),
      reversalCounterexample_marginList_00]
  · simp [reversalCounterexampleProfile,
      margin_eq_marginList (ballots := reversalCounterexampleBallots),
      reversalCounterexample_marginList_01]
  · simp [reversalCounterexampleProfile,
      margin_eq_marginList (ballots := reversalCounterexampleBallots),
      reversalCounterexample_marginList_02]

lemma reversalCounterexample_margin_from_2_le_zero (y : Fin 3) :
    margin reversalCounterexampleProfile (2 : Fin 3) y ≤ 0 := by
  fin_cases y
  · simp [reversalCounterexampleProfile,
      margin_eq_marginList (ballots := reversalCounterexampleBallots),
      reversalCounterexample_marginList_20]
  · simp [reversalCounterexampleProfile,
      margin_eq_marginList (ballots := reversalCounterexampleBallots),
      reversalCounterexample_marginList_21]
  · simp [reversalCounterexampleProfile,
      margin_eq_marginList (ballots := reversalCounterexampleBallots),
      reversalCounterexample_marginList_22]

lemma reversalCounterexample_pathStrength_from_0_le_zero (t : List (Fin 3)) :
    pathStrength reversalCounterexampleProfile ((0 : Fin 3) :: t) ≤ 0 := by
  cases t with
  | nil =>
      simp [pathStrength]
  | cons y t' =>
      have hmargin : margin reversalCounterexampleProfile (0 : Fin 3) y ≤ 0 :=
        reversalCounterexample_margin_from_0_le_zero y
      have hpath :
          pathStrength reversalCounterexampleProfile (0 :: y :: t') ≤
            margin reversalCounterexampleProfile (0 : Fin 3) y := by
        simpa [pathStrength] using
          (pathStrengthAux_le_init (P := reversalCounterexampleProfile) (a := y) (l := t')
            (m := margin reversalCounterexampleProfile (0 : Fin 3) y))
      exact le_trans hpath hmargin

lemma reversalCounterexample_pathStrength_from_2_le_zero (t : List (Fin 3)) :
    pathStrength reversalCounterexampleProfile ((2 : Fin 3) :: t) ≤ 0 := by
  cases t with
  | nil =>
      simp [pathStrength]
  | cons y t' =>
      have hmargin : margin reversalCounterexampleProfile (2 : Fin 3) y ≤ 0 :=
        reversalCounterexample_margin_from_2_le_zero y
      have hpath :
          pathStrength reversalCounterexampleProfile (2 :: y :: t') ≤
            margin reversalCounterexampleProfile (2 : Fin 3) y := by
        simpa [pathStrength] using
          (pathStrengthAux_le_init (P := reversalCounterexampleProfile) (a := y) (l := t')
            (m := margin reversalCounterexampleProfile (2 : Fin 3) y))
      exact le_trans hpath hmargin

lemma reversalCounterexample_strongestPath_0_y_le_zero (y : Fin 3) (hy : y ≠ 0) :
    strongestPath reversalCounterexampleProfile (0 : Fin 3) y ≤ 0 := by
  classical
  have hne_paths :
      (pathsUpTo (A := Fin 3) (Fintype.card (Fin 3)) (0 : Fin 3) y).Nonempty :=
    pathsUpTo_nonempty_of_ne (A := Fin 3) (0 : Fin 3) y (by simpa [eq_comm] using hy)
  rcases exists_max_path_props (P := reversalCounterexampleProfile) (a := (0 : Fin 3)) (b := y)
      hne_paths with ⟨l, _hl, hhead, _hlast, _hnodup, hlen, hstrength⟩
  have hle : pathStrength reversalCounterexampleProfile l ≤ 0 := by
    cases l with
    | nil =>
        simp at hlen
    | cons x t =>
        have hx : x = (0 : Fin 3) := by
          apply Option.some.inj
          simpa using hhead
        subst hx
        simpa using (reversalCounterexample_pathStrength_from_0_le_zero (t := t))
  simpa [hstrength] using hle

lemma reversalCounterexample_strongestPath_2_y_le_zero (y : Fin 3) (hy : y ≠ 2) :
    strongestPath reversalCounterexampleProfile (2 : Fin 3) y ≤ 0 := by
  classical
  have hne_paths :
      (pathsUpTo (A := Fin 3) (Fintype.card (Fin 3)) (2 : Fin 3) y).Nonempty :=
    pathsUpTo_nonempty_of_ne (A := Fin 3) (2 : Fin 3) y (by simpa [eq_comm] using hy)
  rcases exists_max_path_props (P := reversalCounterexampleProfile) (a := (2 : Fin 3)) (b := y)
      hne_paths with ⟨l, _hl, hhead, _hlast, _hnodup, hlen, hstrength⟩
  have hle : pathStrength reversalCounterexampleProfile l ≤ 0 := by
    cases l with
    | nil =>
        simp at hlen
    | cons x t =>
        have hx : x = (2 : Fin 3) := by
          apply Option.some.inj
          simpa using hhead
        subst hx
        simpa using (reversalCounterexample_pathStrength_from_2_le_zero (t := t))
  simpa [hstrength] using hle

lemma reversalCounterexample_strongestPath_1_0_le_zero :
    strongestPath reversalCounterexampleProfile (1 : Fin 3) (0 : Fin 3) ≤ 0 := by
  classical
  have hne_paths :
      (pathsUpTo (A := Fin 3) (Fintype.card (Fin 3)) (1 : Fin 3) (0 : Fin 3)).Nonempty :=
    pathsUpTo_nonempty_of_ne (A := Fin 3) (1 : Fin 3) (0 : Fin 3) (by decide)
  rcases exists_max_path_props (P := reversalCounterexampleProfile) (a := (1 : Fin 3)) (b := (0 : Fin 3))
      hne_paths with ⟨l, _hl, hhead, hlast, hnodup, hlen, hstrength⟩
  have hle : pathStrength reversalCounterexampleProfile l ≤ 0 := by
    cases l with
    | nil =>
        simp at hlen
    | cons x t =>
        have hx : x = (1 : Fin 3) := by
          apply Option.some.inj
          simpa using hhead
        subst hx
        cases t with
        | nil =>
            simp at hlen
        | cons y t' =>
            have hy : y ≠ (1 : Fin 3) := by
              have hnot : (1 : Fin 3) ∉ (y :: t') := (List.nodup_cons.mp hnodup).1
              intro hyEq
              exact hnot (by simp [hyEq])
            fin_cases y
            ·
              have hpath :
                  pathStrength reversalCounterexampleProfile (1 :: (0 : Fin 3) :: t') ≤
                    margin reversalCounterexampleProfile (1 : Fin 3) (0 : Fin 3) := by
                simpa [pathStrength] using
                  (pathStrengthAux_le_init (P := reversalCounterexampleProfile) (a := (0 : Fin 3))
                    (l := t') (m := margin reversalCounterexampleProfile (1 : Fin 3) (0 : Fin 3)))
              have hmargin : margin reversalCounterexampleProfile (1 : Fin 3) (0 : Fin 3) ≤ 0 := by
                simp [reversalCounterexampleProfile,
                  margin_eq_marginList (ballots := reversalCounterexampleBallots),
                  reversalCounterexample_marginList_10]
              exact le_trans hpath hmargin
            · exact (hy rfl).elim
            ·
              cases t' with
              | nil =>
                  have hlast' : False := by
                    have hlast' := hlast
                    simp at hlast'
                  exact hlast'.elim
              | cons z t'' =>
                  have hpath :
                      pathStrength reversalCounterexampleProfile
                          (1 :: (2 : Fin 3) :: z :: t'') ≤
                        pathStrength reversalCounterexampleProfile ((2 : Fin 3) :: z :: t'') := by
                    have h :=
                      pathStrength_cons_cons_cons (P := reversalCounterexampleProfile) (a := (1 : Fin 3))
                        (b := (2 : Fin 3)) (c := z) (t := t'')
                    have hle :
                        pathStrength reversalCounterexampleProfile
                            (1 :: (2 : Fin 3) :: z :: t'') ≤
                          min (margin reversalCounterexampleProfile (1 : Fin 3) (2 : Fin 3))
                            (pathStrength reversalCounterexampleProfile ((2 : Fin 3) :: z :: t'')) := by
                      exact le_of_eq h
                    exact hle.trans (min_le_right _ _)
                  have hle2 :
                      pathStrength reversalCounterexampleProfile ((2 : Fin 3) :: z :: t'') ≤ 0 :=
                    reversalCounterexample_pathStrength_from_2_le_zero (t := z :: t'')
                  exact le_trans hpath hle2
  simpa [hstrength] using hle

lemma reversalCounterexample_strongestPath_0_y_ge_zero (y : Fin 3) (hy : y ≠ 0) :
    (0 : Int) ≤ strongestPath reversalCounterexampleProfile (0 : Fin 3) y := by
  fin_cases y
  · cases hy rfl
  ·
    have h :=
      margin_le_strongestPath_of_ne (P := reversalCounterexampleProfile) (a := (0 : Fin 3))
        (b := (1 : Fin 3)) (by decide)
    simpa [reversalCounterexampleProfile,
      margin_eq_marginList (ballots := reversalCounterexampleBallots),
      reversalCounterexample_marginList_01] using h
  ·
    have h :=
      margin_le_strongestPath_of_ne (P := reversalCounterexampleProfile) (a := (0 : Fin 3))
        (b := (2 : Fin 3)) (by decide)
    simpa [reversalCounterexampleProfile,
      margin_eq_marginList (ballots := reversalCounterexampleBallots),
      reversalCounterexample_marginList_02] using h

lemma reversalCounterexample_strongestPath_y_0_ge_zero (y : Fin 3) (hy : y ≠ 0) :
    (0 : Int) ≤ strongestPath reversalCounterexampleProfile y (0 : Fin 3) := by
  fin_cases y
  · cases hy rfl
  ·
    have h :=
      margin_le_strongestPath_of_ne (P := reversalCounterexampleProfile) (a := (1 : Fin 3))
        (b := (0 : Fin 3)) (by decide)
    simpa [reversalCounterexampleProfile,
      margin_eq_marginList (ballots := reversalCounterexampleBallots),
      reversalCounterexample_marginList_10] using h
  ·
    have h :=
      margin_le_strongestPath_of_ne (P := reversalCounterexampleProfile) (a := (2 : Fin 3))
        (b := (0 : Fin 3)) (by decide)
    simpa [reversalCounterexampleProfile,
      margin_eq_marginList (ballots := reversalCounterexampleBallots),
      reversalCounterexample_marginList_20] using h

lemma reversalCounterexample_strongestPath_1_2_ge_two :
    (2 : Int) ≤ strongestPath reversalCounterexampleProfile (1 : Fin 3) (2 : Fin 3) := by
  have hmem :
      [1, 2] ∈ pathsUpTo (A := Fin 3) (Fintype.card (Fin 3)) (1 : Fin 3) (2 : Fin 3) := by
    refine mem_pathsUpTo_of_props (l := [1, 2]) (a := (1 : Fin 3)) (b := (2 : Fin 3)) ?_ ?_ ?_ ?_
    · simp
    · simp
    · decide
    · simp
  have hle := pathStrength_of_mem_pathsUpTo_le_strongestPath
    (P := reversalCounterexampleProfile) (a := (1 : Fin 3)) (b := (2 : Fin 3)) (l := [1, 2]) hmem
  simpa [pathStrength_two, reversalCounterexampleProfile,
    margin_eq_marginList (ballots := reversalCounterexampleBallots),
    reversalCounterexample_marginList_12] using hle

lemma reversalCounterexample_schulzeDefeats_12 :
    schulzeDefeats reversalCounterexampleProfile (1 : Fin 3) (2 : Fin 3) := by
  have hge : (2 : Int) ≤ strongestPath reversalCounterexampleProfile (1 : Fin 3) (2 : Fin 3) :=
    reversalCounterexample_strongestPath_1_2_ge_two
  have hle : strongestPath reversalCounterexampleProfile (2 : Fin 3) (1 : Fin 3) ≤ 0 :=
    reversalCounterexample_strongestPath_2_y_le_zero (y := (1 : Fin 3)) (by decide)
  have hpos : (0 : Int) < strongestPath reversalCounterexampleProfile (1 : Fin 3) (2 : Fin 3) := by
    have h02 : (0 : Int) < 2 := by decide
    exact lt_of_lt_of_le h02 hge
  have hlt :
      strongestPath reversalCounterexampleProfile (2 : Fin 3) (1 : Fin 3) <
        strongestPath reversalCounterexampleProfile (1 : Fin 3) (2 : Fin 3) :=
    lt_of_le_of_lt hle hpos
  exact hlt

lemma reversalCounterexample_no_schulzeDefeats_to_zero :
    ∀ y : Fin 3, ¬ schulzeDefeats reversalCounterexampleProfile y (0 : Fin 3) := by
  intro y hydef
  fin_cases y
  · exact (lt_irrefl _ hydef)
  ·
    have hle : strongestPath reversalCounterexampleProfile (1 : Fin 3) (0 : Fin 3) ≤ 0 :=
      reversalCounterexample_strongestPath_1_0_le_zero
    have hge : (0 : Int) ≤ strongestPath reversalCounterexampleProfile (0 : Fin 3) (1 : Fin 3) :=
      reversalCounterexample_strongestPath_0_y_ge_zero (y := (1 : Fin 3)) (by decide)
    have hle' :
        strongestPath reversalCounterexampleProfile (1 : Fin 3) (0 : Fin 3) ≤
          strongestPath reversalCounterexampleProfile (0 : Fin 3) (1 : Fin 3) :=
      le_trans hle hge
    exact (not_lt_of_ge hle') hydef
  ·
    have hle : strongestPath reversalCounterexampleProfile (2 : Fin 3) (0 : Fin 3) ≤ 0 :=
      reversalCounterexample_strongestPath_2_y_le_zero (y := (0 : Fin 3)) (by decide)
    have hge : (0 : Int) ≤ strongestPath reversalCounterexampleProfile (0 : Fin 3) (2 : Fin 3) :=
      reversalCounterexample_strongestPath_0_y_ge_zero (y := (2 : Fin 3)) (by decide)
    have hle' :
        strongestPath reversalCounterexampleProfile (2 : Fin 3) (0 : Fin 3) ≤
          strongestPath reversalCounterexampleProfile (0 : Fin 3) (2 : Fin 3) :=
      le_trans hle hge
    exact (not_lt_of_ge hle') hydef

lemma reversalCounterexample_no_schulzeDefeats_from_zero :
    ∀ y : Fin 3, ¬ schulzeDefeats reversalCounterexampleProfile (0 : Fin 3) y := by
  intro y hydef
  fin_cases y
  · exact (lt_irrefl _ hydef)
  ·
    have hle : strongestPath reversalCounterexampleProfile (0 : Fin 3) (1 : Fin 3) ≤ 0 :=
      reversalCounterexample_strongestPath_0_y_le_zero (y := (1 : Fin 3)) (by decide)
    have hge : (0 : Int) ≤ strongestPath reversalCounterexampleProfile (1 : Fin 3) (0 : Fin 3) :=
      reversalCounterexample_strongestPath_y_0_ge_zero (y := (1 : Fin 3)) (by decide)
    have hle' :
        strongestPath reversalCounterexampleProfile (0 : Fin 3) (1 : Fin 3) ≤
          strongestPath reversalCounterexampleProfile (1 : Fin 3) (0 : Fin 3) :=
      le_trans hle hge
    exact (not_lt_of_ge hle') hydef
  ·
    have hle : strongestPath reversalCounterexampleProfile (0 : Fin 3) (2 : Fin 3) ≤ 0 :=
      reversalCounterexample_strongestPath_0_y_le_zero (y := (2 : Fin 3)) (by decide)
    have hge : (0 : Int) ≤ strongestPath reversalCounterexampleProfile (2 : Fin 3) (0 : Fin 3) :=
      reversalCounterexample_strongestPath_y_0_ge_zero (y := (2 : Fin 3)) (by decide)
    have hle' :
        strongestPath reversalCounterexampleProfile (0 : Fin 3) (2 : Fin 3) ≤
          strongestPath reversalCounterexampleProfile (2 : Fin 3) (0 : Fin 3) :=
      le_trans hle hge
    exact (not_lt_of_ge hle') hydef

lemma reversalCounterexample_zero_mem_schulze :
    (0 : Fin 3) ∈ schulze reversalCounterexampleProfile := by
  classical
  simp [schulze, reversalCounterexample_no_schulzeDefeats_to_zero]

lemma reversalCounterexample_zero_mem_schulze_reverse :
    (0 : Fin 3) ∈ schulze (reverse_profile reversalCounterexampleProfile) := by
  classical
  simp [schulze]
  intro y hydef
  have hydef' : schulzeDefeats reversalCounterexampleProfile (0 : Fin 3) y := by
    simpa [schulzeDefeats_reverse_iff] using hydef
  exact reversalCounterexample_no_schulzeDefeats_from_zero y hydef'

lemma reversalCounterexample_two_not_mem_schulze :
    (2 : Fin 3) ∉ schulze reversalCounterexampleProfile := by
  classical
  intro hmem
  have hcond : ∀ y, ¬ schulzeDefeats reversalCounterexampleProfile y (2 : Fin 3) := by
    simpa [schulze] using hmem
  exact (hcond 1) reversalCounterexample_schulzeDefeats_12

lemma reversalCounterexample_schulze_ne_univ :
    schulze reversalCounterexampleProfile ≠ Finset.univ := by
  intro hEq
  have hmem : (2 : Fin 3) ∈ schulze reversalCounterexampleProfile := by
    simp [hEq]
  exact reversalCounterexample_two_not_mem_schulze hmem

theorem schulze_not_reversal_symmetry : ¬ ReversalSymmetry schulze := by
  intro h
  have hne : schulze reversalCounterexampleProfile ≠ Finset.univ :=
    reversalCounterexample_schulze_ne_univ
  have hEq := h (P := reversalCounterexampleProfile) hne
  have hmem : (0 : Fin 3) ∈
      schulze reversalCounterexampleProfile ∩
        schulze (reverse_profile reversalCounterexampleProfile) := by
    exact Finset.mem_inter.mpr
      ⟨reversalCounterexample_zero_mem_schulze,
       reversalCounterexample_zero_mem_schulze_reverse⟩
  have hmem' := hmem
  simp [hEq] at hmem'

end SchulzeReversalCounterexample

end SocialChoice
