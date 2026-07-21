import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Participation
import SocialChoice.Axioms.Implications
import SocialChoice.ListBallot
import SocialChoice.Margin
import SocialChoice.Rules.Schulze.Defs
import SocialChoice.Rules.Schulze.Path
import SocialChoice.Rules.Schulze.InformationalBasis

namespace SocialChoice

open Finset
open Classical

attribute [instance] Classical.decEq

set_option maxHeartbeats 5000000

/-!
# Schulze fails negative involvement

Counterexample with 4 candidates and 9 voters:

Full profile (9 voters):
1 voter : 1 > 3 > 0 > 2
1 voter : 1 > 3 > 2 > 0
3 voters: 2 > 0 > 1 > 3
1 voter : 2 > 1 > 3 > 0
2 voters: 3 > 0 > 1 > 2
1 voter : 3 > 0 > 2 > 1
Schulze selects {0,1,2,3}.

Remove the voter with ballot 1 > 3 > 2 > 0:
Schulze selects {2}.

Read backwards, this violates Negative Involvement for candidate 0.
-/

namespace SchulzeNegativeInvolvementCounterexample

abbrev A4 := Fin 4

abbrev a0 : A4 := 0
abbrev a1 : A4 := 1
abbrev a2 : A4 := 2
abbrev a3 : A4 := 3

def ballot1302 : ListBallot 4 := ListBallot.mk' [a1, a3, a0, a2]
def ballot1320 : ListBallot 4 := ListBallot.mk' [a1, a3, a2, a0]
def ballot2013 : ListBallot 4 := ListBallot.mk' [a2, a0, a1, a3]
def ballot2130 : ListBallot 4 := ListBallot.mk' [a2, a1, a3, a0]
def ballot3012 : ListBallot 4 := ListBallot.mk' [a3, a0, a1, a2]
def ballot3021 : ListBallot 4 := ListBallot.mk' [a3, a0, a2, a1]

def ballots9 : Fin 9 → ListBallot 4
  | ⟨0, _⟩ => ballot1320
  | ⟨1, _⟩ => ballot1302
  | ⟨2, _⟩ => ballot2013
  | ⟨3, _⟩ => ballot2013
  | ⟨4, _⟩ => ballot2013
  | ⟨5, _⟩ => ballot2130
  | ⟨6, _⟩ => ballot3012
  | ⟨7, _⟩ => ballot3012
  | ⟨8, _⟩ => ballot3021

def ballots8 : Fin 8 → ListBallot 4
  | ⟨0, _⟩ => ballot1302
  | ⟨1, _⟩ => ballot2013
  | ⟨2, _⟩ => ballot2013
  | ⟨3, _⟩ => ballot2013
  | ⟨4, _⟩ => ballot2130
  | ⟨5, _⟩ => ballot3012
  | ⟨6, _⟩ => ballot3012
  | ⟨7, _⟩ => ballot3021

noncomputable def profile9_list : Profile (Fin 9) A4 :=
  profileOfListBallots ballots9

noncomputable def profile8_list : Profile (Fin 8) A4 :=
  profileOfListBallots ballots8

def voters8 : Finset (Fin 9) := Finset.univ.erase 0
def voters9 : Finset (Fin 9) := insert (0 : Fin 9) voters8

lemma voters8_not_mem : (0 : Fin 9) ∉ voters8 := by
  simp [voters8]

lemma voters9_eq_univ : (voters9 : Finset (Fin 9)) = Finset.univ := by
  ext x
  fin_cases x <;> simp [voters9, voters8]

noncomputable def fullProfile : Profile (Electorate (Fin 9) (Finset.univ)) A4 :=
  { pref := fun v => (ballots9 v.1).toLinearOrder }

noncomputable def profile8 : Profile (Electorate (Fin 9) voters8) A4 :=
  restrictElectorate fullProfile voters8 (by
    intro x hx; exact (Finset.mem_univ x))

noncomputable def profile9 : Profile (Electorate (Fin 9) voters9) A4 :=
  restrictElectorate fullProfile voters9 (by
    intro x hx; exact (Finset.mem_univ x))

noncomputable def e9 : Fin 9 ≃ Electorate (Fin 9) voters9 :=
  { toFun := fun x => ⟨x, by simp [voters9_eq_univ]⟩
    invFun := fun v => v.1
    left_inv := by intro x; rfl
    right_inv := by intro v; cases v; rfl }

noncomputable def e8_to : Fin 8 → Electorate (Fin 9) voters8
  | ⟨0, _⟩ => ⟨1, by simp [voters8]⟩
  | ⟨1, _⟩ => ⟨2, by simp [voters8]⟩
  | ⟨2, _⟩ => ⟨3, by simp [voters8]⟩
  | ⟨3, _⟩ => ⟨4, by simp [voters8]⟩
  | ⟨4, _⟩ => ⟨5, by simp [voters8]⟩
  | ⟨5, _⟩ => ⟨6, by simp [voters8]⟩
  | ⟨6, _⟩ => ⟨7, by simp [voters8]⟩
  | ⟨7, _⟩ => ⟨8, by simp [voters8]⟩

noncomputable def e8_inv : Electorate (Fin 9) voters8 → Fin 8
  | ⟨1, _⟩ => ⟨0, by decide⟩
  | ⟨2, _⟩ => ⟨1, by decide⟩
  | ⟨3, _⟩ => ⟨2, by decide⟩
  | ⟨4, _⟩ => ⟨3, by decide⟩
  | ⟨5, _⟩ => ⟨4, by decide⟩
  | ⟨6, _⟩ => ⟨5, by decide⟩
  | ⟨7, _⟩ => ⟨6, by decide⟩
  | ⟨8, _⟩ => ⟨7, by decide⟩
  | ⟨0, h⟩ => (False.elim (by simp [voters8] at h))

noncomputable def e8 : Fin 8 ≃ Electorate (Fin 9) voters8 :=
  { toFun := e8_to
    invFun := e8_inv
    left_inv := by
      intro v
      fin_cases v <;> rfl
    right_inv := by
      intro v
      cases v with
      | mk val hmem =>
          fin_cases val <;> simp [e8_to, e8_inv, voters8] at hmem ⊢ }

lemma relabel_profile9_eq_profile9_list :
    relabelProfileVoters e9 profile9 = profile9_list := by
  ext v
  rfl

lemma relabel_profile8_eq_profile8_list :
    relabelProfileVoters e8 profile8 = profile8_list := by
  ext v
  fin_cases v <;> rfl

lemma margin_profile9_eq_list (a b : A4) :
    margin profile9 a b = margin profile9_list a b := by
  have h :=
    margin_relabelProfileVoters (e := e9) (P := profile9) (a := a) (b := b)
  have h' : margin profile9_list a b = margin profile9 a b := by
    simpa [relabel_profile9_eq_profile9_list] using h
  simpa using h'.symm

lemma margin_profile8_eq_list (a b : A4) :
    margin profile8 a b = margin profile8_list a b := by
  have h :=
    margin_relabelProfileVoters (e := e8) (P := profile8) (a := a) (b := b)
  have h' : margin profile8_list a b = margin profile8 a b := by
    simpa [relabel_profile8_eq_profile8_list] using h
  simpa using h'.symm

lemma profiles_agree :
    ∀ v : Electorate (Fin 9) voters8,
      profile9.pref (liftVoter (u := (0 : Fin 9)) v) = profile8.pref v := by
  intro v
  simpa [profile8, profile9, voters9] using
    (restrictElectorate_agrees (Q := fullProfile) (S := voters8)
      (hS := by intro x hx; exact (Finset.mem_univ x))
      (u := (0 : Fin 9))
      (hSu := by intro x hx; exact (Finset.mem_univ x)) v)

private lemma ballot1320_bottom_0 : BallotBottom (ballot1320.toLinearOrder) a0 := by
  intro d hd
  fin_cases d
  · cases hd rfl
  ·
    have hlt :
        ballot1320.ranking.idxOf (1 : A4) < ballot1320.ranking.idxOf (0 : A4) := by
      decide
    simpa [ballot1320, ListBallot.lt_iff_idxOf] using hlt
  ·
    have hlt :
        ballot1320.ranking.idxOf (2 : A4) < ballot1320.ranking.idxOf (0 : A4) := by
      decide
    simpa [ballot1320, ListBallot.lt_iff_idxOf] using hlt
  ·
    have hlt :
        ballot1320.ranking.idxOf (3 : A4) < ballot1320.ranking.idxOf (0 : A4) := by
      decide
    simpa [ballot1320, ListBallot.lt_iff_idxOf] using hlt

lemma newVoter_bottom_0 :
    BallotBottom
      (profile9.pref (newVoter (u := (0 : Fin 9)) (V := voters8) voters8_not_mem))
      a0 := by
  change BallotBottom ballot1320.toLinearOrder a0
  exact ballot1320_bottom_0

/-! ## Margins for the full profile (9 voters) -/

private lemma marginList_profile9_0_1 :
    marginList (fun v => (ballots9 v).ranking) a0 a1 = 3 := by
  decide

private lemma marginList_profile9_0_2 :
    marginList (fun v => (ballots9 v).ranking) a0 a2 = -1 := by
  decide

private lemma marginList_profile9_0_3 :
    marginList (fun v => (ballots9 v).ranking) a0 a3 = -3 := by
  decide

private lemma marginList_profile9_1_2 :
    marginList (fun v => (ballots9 v).ranking) a1 a2 = -1 := by
  decide

private lemma marginList_profile9_1_3 :
    marginList (fun v => (ballots9 v).ranking) a1 a3 = 3 := by
  decide

private lemma marginList_profile9_2_3 :
    marginList (fun v => (ballots9 v).ranking) a2 a3 = -1 := by
  decide

lemma margin_profile9_0_1 : margin profile9_list a0 a1 = 3 := by
  have h := margin_eq_marginList (ballots := ballots9) (a := a0) (b := a1)
  simpa [profile9_list, marginList_profile9_0_1] using h

lemma margin_profile9_0_2 : margin profile9_list a0 a2 = -1 := by
  have h := margin_eq_marginList (ballots := ballots9) (a := a0) (b := a2)
  simpa [profile9_list, marginList_profile9_0_2] using h

lemma margin_profile9_0_3 : margin profile9_list a0 a3 = -3 := by
  have h := margin_eq_marginList (ballots := ballots9) (a := a0) (b := a3)
  simpa [profile9_list, marginList_profile9_0_3] using h

lemma margin_profile9_1_2 : margin profile9_list a1 a2 = -1 := by
  have h := margin_eq_marginList (ballots := ballots9) (a := a1) (b := a2)
  simpa [profile9_list, marginList_profile9_1_2] using h

lemma margin_profile9_1_3 : margin profile9_list a1 a3 = 3 := by
  have h := margin_eq_marginList (ballots := ballots9) (a := a1) (b := a3)
  simpa [profile9_list, marginList_profile9_1_3] using h

lemma margin_profile9_2_3 : margin profile9_list a2 a3 = -1 := by
  have h := margin_eq_marginList (ballots := ballots9) (a := a2) (b := a3)
  simpa [profile9_list, marginList_profile9_2_3] using h

lemma margin_profile9_1_0 : margin profile9_list a1 a0 = (-3 : Int) := by
  have h := margin_antisymmetric (P := profile9_list) a1 a0
  simpa [margin_profile9_0_1] using h

lemma margin_profile9_2_0 : margin profile9_list a2 a0 = (1 : Int) := by
  have h := margin_antisymmetric (P := profile9_list) a2 a0
  simpa [margin_profile9_0_2] using h

lemma margin_profile9_3_0 : margin profile9_list a3 a0 = (3 : Int) := by
  have h := margin_antisymmetric (P := profile9_list) a3 a0
  simpa [margin_profile9_0_3] using h

lemma margin_profile9_2_1 : margin profile9_list a2 a1 = (1 : Int) := by
  have h := margin_antisymmetric (P := profile9_list) a2 a1
  simpa [margin_profile9_1_2] using h

lemma margin_profile9_3_1 : margin profile9_list a3 a1 = (-3 : Int) := by
  have h := margin_antisymmetric (P := profile9_list) a3 a1
  simpa [margin_profile9_1_3] using h

lemma margin_profile9_3_2 : margin profile9_list a3 a2 = (1 : Int) := by
  have h := margin_antisymmetric (P := profile9_list) a3 a2
  simpa [margin_profile9_2_3] using h

lemma margin_profile9_1_le_three (y : A4) (hy : y ≠ a1) :
    margin profile9_list a1 y ≤ 3 := by
  fin_cases y
  ·
    have h : margin profile9_list a1 a0 = (-3 : Int) := margin_profile9_1_0
    simp [h]
  · cases hy rfl
  ·
    have h : margin profile9_list a1 a2 = (-1 : Int) := margin_profile9_1_2
    simp [h]
  ·
    have h : margin profile9_list a1 a3 = (3 : Int) := margin_profile9_1_3
    simp [h]

lemma margin_profile9_2_le_one (y : A4) (hy : y ≠ a2) :
    margin profile9_list a2 y ≤ 1 := by
  fin_cases y
  ·
    have h : margin profile9_list a2 a0 = (1 : Int) := margin_profile9_2_0
    simp [h]
  ·
    have h : margin profile9_list a2 a1 = (1 : Int) := margin_profile9_2_1
    simp [h]
  · cases hy rfl
  ·
    have h : margin profile9_list a2 a3 = (-1 : Int) := margin_profile9_2_3
    simp [h]

lemma margin_profile9_3_le_three (y : A4) (hy : y ≠ a3) :
    margin profile9_list a3 y ≤ 3 := by
  fin_cases y
  ·
    have h : margin profile9_list a3 a0 = (3 : Int) := margin_profile9_3_0
    simp [h]
  ·
    have h : margin profile9_list a3 a1 = (-3 : Int) := margin_profile9_3_1
    simp [h]
  ·
    have h : margin profile9_list a3 a2 = (1 : Int) := margin_profile9_3_2
    simp [h]
  · cases hy rfl

lemma pathStrength_le_first_margin {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) (t : List A) :
    pathStrength P (a :: b :: t) ≤ margin P a b := by
  simp [pathStrength, pathStrengthAux_le_init]

lemma strongestPath_profile9_1_0_le_three : strongestPath profile9_list a1 a0 ≤ 3 := by
  classical
  have hne : a1 ≠ a0 := by decide
  have hne_paths :
      (pathsUpTo (A := A4) (Fintype.card A4) a1 a0).Nonempty :=
    pathsUpTo_nonempty_of_ne (A := A4) a1 a0 hne
  rcases exists_max_path_props (P := profile9_list) (a := a1) (b := a0) hne_paths with
    ⟨l, _hl, hhead, _hlast, hnodup, hlen, hstrength⟩
  have hle : pathStrength profile9_list l ≤ 3 := by
    cases l with
    | nil =>
        simp at hlen
    | cons x t =>
        have hx : x = a1 := by
          apply Option.some.inj
          simpa using hhead
        subst hx
        cases t with
        | nil =>
            simp at hlen
        | cons y t' =>
            have hy : y ≠ a1 := by
              have hnot : a1 ∉ (y :: t') := (List.nodup_cons.mp hnodup).1
              intro hyEq
              exact hnot (by simp [hyEq])
            have hmargin : margin profile9_list a1 y ≤ 3 := margin_profile9_1_le_three y hy
            have hpath : pathStrength profile9_list (a1 :: y :: t') ≤ margin profile9_list a1 y :=
              pathStrength_le_first_margin profile9_list a1 y t'
            linarith
  simpa [hstrength] using hle

lemma strongestPath_profile9_2_0_le_one : strongestPath profile9_list a2 a0 ≤ 1 := by
  classical
  have hne : a2 ≠ a0 := by decide
  have hne_paths :
      (pathsUpTo (A := A4) (Fintype.card A4) a2 a0).Nonempty :=
    pathsUpTo_nonempty_of_ne (A := A4) a2 a0 hne
  rcases exists_max_path_props (P := profile9_list) (a := a2) (b := a0) hne_paths with
    ⟨l, _hl, hhead, _hlast, hnodup, hlen, hstrength⟩
  have hle : pathStrength profile9_list l ≤ 1 := by
    cases l with
    | nil =>
        simp at hlen
    | cons x t =>
        have hx : x = a2 := by
          apply Option.some.inj
          simpa using hhead
        subst hx
        cases t with
        | nil =>
            simp at hlen
        | cons y t' =>
            have hy : y ≠ a2 := by
              have hnot : a2 ∉ (y :: t') := (List.nodup_cons.mp hnodup).1
              intro hyEq
              exact hnot (by simp [hyEq])
            have hmargin : margin profile9_list a2 y ≤ 1 := margin_profile9_2_le_one y hy
            have hpath : pathStrength profile9_list (a2 :: y :: t') ≤ margin profile9_list a2 y :=
              pathStrength_le_first_margin profile9_list a2 y t'
            linarith
  simpa [hstrength] using hle

lemma strongestPath_profile9_3_0_le_three : strongestPath profile9_list a3 a0 ≤ 3 := by
  classical
  have hne : a3 ≠ a0 := by decide
  have hne_paths :
      (pathsUpTo (A := A4) (Fintype.card A4) a3 a0).Nonempty :=
    pathsUpTo_nonempty_of_ne (A := A4) a3 a0 hne
  rcases exists_max_path_props (P := profile9_list) (a := a3) (b := a0) hne_paths with
    ⟨l, _hl, hhead, _hlast, hnodup, hlen, hstrength⟩
  have hle : pathStrength profile9_list l ≤ 3 := by
    cases l with
    | nil =>
        simp at hlen
    | cons x t =>
        have hx : x = a3 := by
          apply Option.some.inj
          simpa using hhead
        subst hx
        cases t with
        | nil =>
            simp at hlen
        | cons y t' =>
            have hy : y ≠ a3 := by
              have hnot : a3 ∉ (y :: t') := (List.nodup_cons.mp hnodup).1
              intro hyEq
              exact hnot (by simp [hyEq])
            have hmargin : margin profile9_list a3 y ≤ 3 := margin_profile9_3_le_three y hy
            have hpath : pathStrength profile9_list (a3 :: y :: t') ≤ margin profile9_list a3 y :=
              pathStrength_le_first_margin profile9_list a3 y t'
            linarith
  simpa [hstrength] using hle

lemma strongestPath_profile9_0_1_ge_three : (3 : Int) ≤ strongestPath profile9_list a0 a1 := by
  have hne : a0 ≠ a1 := by decide
  have h := margin_le_strongestPath_of_ne (P := profile9_list) (a := a0) (b := a1) hne
  simpa [margin_profile9_0_1] using h

lemma pathStrength_profile9_0_1_3 : pathStrength profile9_list [a0, a1, a3] = 3 := by
  simp [pathStrength, pathStrengthAux, margin_profile9_0_1, margin_profile9_1_3]

lemma path_0_1_3_mem :
    [a0, a1, a3] ∈ pathsUpTo (A := A4) (Fintype.card A4) a0 a3 := by
  apply mem_pathsUpTo_of_props
  · simp
  · simp
  · decide
  · simp

lemma strongestPath_profile9_0_3_ge_three : (3 : Int) ≤ strongestPath profile9_list a0 a3 := by
  have h :=
    pathStrength_of_mem_pathsUpTo_le_strongestPath (P := profile9_list) (a := a0) (b := a3)
      (l := [a0, a1, a3]) path_0_1_3_mem
  simpa [pathStrength_profile9_0_1_3] using h

lemma pathStrength_profile9_0_1_3_2 : pathStrength profile9_list [a0, a1, a3, a2] = 1 := by
  simp [pathStrength_cons_cons_cons, margin_profile9_0_1, margin_profile9_1_3, margin_profile9_3_2]

lemma path_0_1_3_2_mem :
    [a0, a1, a3, a2] ∈ pathsUpTo (A := A4) (Fintype.card A4) a0 a2 := by
  apply mem_pathsUpTo_of_props
  · simp
  · simp
  · decide
  · simp

lemma strongestPath_profile9_0_2_ge_one : (1 : Int) ≤ strongestPath profile9_list a0 a2 := by
  have h :=
    pathStrength_of_mem_pathsUpTo_le_strongestPath (P := profile9_list) (a := a0) (b := a2)
      (l := [a0, a1, a3, a2]) path_0_1_3_2_mem
  simpa [pathStrength_profile9_0_1_3_2] using h

lemma a0_in_schulze_profile9_list : a0 ∈ schulze profile9_list := by
  classical
  simp [schulze]
  intro b
  fin_cases b
  ·
    intro hdef
    exact (schulzeDefeats_ne (P := profile9_list) hdef) rfl
  ·
    have hle : strongestPath profile9_list a1 a0 ≤ 3 := strongestPath_profile9_1_0_le_three
    have hge : (3 : Int) ≤ strongestPath profile9_list a0 a1 :=
      strongestPath_profile9_0_1_ge_three
    intro hdef
    exact (not_lt_of_ge (le_trans hle hge)) hdef
  ·
    have hle : strongestPath profile9_list a2 a0 ≤ 1 := strongestPath_profile9_2_0_le_one
    have hge : (1 : Int) ≤ strongestPath profile9_list a0 a2 :=
      strongestPath_profile9_0_2_ge_one
    intro hdef
    exact (not_lt_of_ge (le_trans hle hge)) hdef
  ·
    have hle : strongestPath profile9_list a3 a0 ≤ 3 := strongestPath_profile9_3_0_le_three
    have hge : (3 : Int) ≤ strongestPath profile9_list a0 a3 :=
      strongestPath_profile9_0_3_ge_three
    intro hdef
    exact (not_lt_of_ge (le_trans hle hge)) hdef

/-! ## Margins for the reduced profile (8 voters) -/

private lemma marginList_profile8_0_1 :
    marginList (fun v => (ballots8 v).ranking) a0 a1 = 4 := by
  decide

private lemma marginList_profile8_0_2 :
    marginList (fun v => (ballots8 v).ranking) a0 a2 = 0 := by
  decide

private lemma marginList_profile8_0_3 :
    marginList (fun v => (ballots8 v).ranking) a0 a3 = -2 := by
  decide

private lemma marginList_profile8_1_2 :
    marginList (fun v => (ballots8 v).ranking) a1 a2 = -2 := by
  decide

private lemma marginList_profile8_1_3 :
    marginList (fun v => (ballots8 v).ranking) a1 a3 = 2 := by
  decide

private lemma marginList_profile8_2_3 :
    marginList (fun v => (ballots8 v).ranking) a2 a3 = 0 := by
  decide

lemma margin_profile8_0_1 : margin profile8_list a0 a1 = 4 := by
  have h := margin_eq_marginList (ballots := ballots8) (a := a0) (b := a1)
  simpa [profile8_list, marginList_profile8_0_1] using h

lemma margin_profile8_0_2 : margin profile8_list a0 a2 = 0 := by
  have h := margin_eq_marginList (ballots := ballots8) (a := a0) (b := a2)
  simpa [profile8_list, marginList_profile8_0_2] using h

lemma margin_profile8_0_3 : margin profile8_list a0 a3 = -2 := by
  have h := margin_eq_marginList (ballots := ballots8) (a := a0) (b := a3)
  simpa [profile8_list, marginList_profile8_0_3] using h

lemma margin_profile8_1_2 : margin profile8_list a1 a2 = -2 := by
  have h := margin_eq_marginList (ballots := ballots8) (a := a1) (b := a2)
  simpa [profile8_list, marginList_profile8_1_2] using h

lemma margin_profile8_1_3 : margin profile8_list a1 a3 = 2 := by
  have h := margin_eq_marginList (ballots := ballots8) (a := a1) (b := a3)
  simpa [profile8_list, marginList_profile8_1_3] using h

lemma margin_profile8_2_3 : margin profile8_list a2 a3 = 0 := by
  have h := margin_eq_marginList (ballots := ballots8) (a := a2) (b := a3)
  simpa [profile8_list, marginList_profile8_2_3] using h

lemma margin_profile8_1_0 : margin profile8_list a1 a0 = (-4 : Int) := by
  have h := margin_antisymmetric (P := profile8_list) a1 a0
  simpa [margin_profile8_0_1] using h

lemma margin_profile8_2_0 : margin profile8_list a2 a0 = (0 : Int) := by
  have h := margin_antisymmetric (P := profile8_list) a2 a0
  simpa [margin_profile8_0_2] using h

lemma margin_profile8_3_0 : margin profile8_list a3 a0 = (2 : Int) := by
  have h := margin_antisymmetric (P := profile8_list) a3 a0
  simpa [margin_profile8_0_3] using h

lemma margin_profile8_2_1 : margin profile8_list a2 a1 = (2 : Int) := by
  have h := margin_antisymmetric (P := profile8_list) a2 a1
  simpa [margin_profile8_1_2] using h

lemma margin_profile8_3_1 : margin profile8_list a3 a1 = (-2 : Int) := by
  have h := margin_antisymmetric (P := profile8_list) a3 a1
  simpa [margin_profile8_1_3] using h

lemma margin_profile8_3_2 : margin profile8_list a3 a2 = (0 : Int) := by
  have h := margin_antisymmetric (P := profile8_list) a3 a2
  simpa [margin_profile8_2_3] using h

lemma margin_profile8_to_2_le_zero (x : A4) (hx : x ≠ a2) :
    margin profile8_list x a2 ≤ 0 := by
  fin_cases x
  ·
    have h : margin profile8_list a0 a2 = (0 : Int) := margin_profile8_0_2
    simp [h]
  ·
    have h : margin profile8_list a1 a2 = (-2 : Int) := margin_profile8_1_2
    simp [h]
  · cases hx rfl
  ·
    have h : margin profile8_list a3 a2 = (0 : Int) := margin_profile8_3_2
    simp [h]

lemma pathStrength_le_zero_of_last {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (cand : A)
    (hmargin : ∀ x, x ≠ cand → margin P x cand ≤ 0) :
    ∀ l, l.getLast? = some cand → pathStrength P l ≤ 0 := by
  intro l hlast
  induction l with
  | nil =>
      cases hlast
  | cons a t ih =>
      cases t with
      | nil =>
          have : a = cand := by
            apply Option.some.inj
            simpa using hlast
          subst this
          simp [pathStrength]
      | cons b t' =>
          cases t' with
          | nil =>
              have hb : b = cand := by
                apply Option.some.inj
                simpa using hlast
              subst hb
              by_cases h : a = b
              · subst h
                have hzero : margin P a a = 0 := self_margin_zero (P := P) a
                simp [pathStrength, pathStrengthAux, hzero]
              ·
                have hle := hmargin a h
                simpa [pathStrength, pathStrengthAux] using hle
          | cons d t'' =>
              have hlast' : (b :: d :: t'').getLast? = some cand := by
                simpa using hlast
              have hle' : pathStrength P (b :: d :: t'') ≤ 0 := ih hlast'
              have hstep :
                  pathStrength P (a :: b :: d :: t'') =
                    min (margin P a b) (pathStrength P (b :: d :: t'')) := by
                simpa using
                  (pathStrength_cons_cons_cons (P := P) (a := a) (b := b) (c := d) (t := t''))
              have hle :
                  pathStrength P (a :: b :: d :: t'') ≤ pathStrength P (b :: d :: t'') := by
                simp [hstep]
              linarith

lemma pathStrength_profile8_2_1_3_0 :
    pathStrength profile8_list [a2, a1, a3, a0] = 2 := by
  simp [pathStrength_cons_cons_cons, margin_profile8_2_1, margin_profile8_1_3, margin_profile8_3_0]

lemma path_2_1_3_0_mem :
    [a2, a1, a3, a0] ∈ pathsUpTo (A := A4) (Fintype.card A4) a2 a0 := by
  apply mem_pathsUpTo_of_props
  · simp
  · simp
  · decide
  · simp

lemma strongestPath_profile8_2_0_ge_two : (2 : Int) ≤ strongestPath profile8_list a2 a0 := by
  have h :=
    pathStrength_of_mem_pathsUpTo_le_strongestPath (P := profile8_list) (a := a2) (b := a0)
      (l := [a2, a1, a3, a0]) path_2_1_3_0_mem
  simpa [pathStrength_profile8_2_1_3_0] using h

lemma strongestPath_profile8_0_2_le_zero : strongestPath profile8_list a0 a2 ≤ 0 := by
  classical
  have hne : a0 ≠ a2 := by decide
  have hne_paths :
      (pathsUpTo (A := A4) (Fintype.card A4) a0 a2).Nonempty :=
    pathsUpTo_nonempty_of_ne (A := A4) a0 a2 hne
  rcases exists_max_path_props (P := profile8_list) (a := a0) (b := a2) hne_paths with
    ⟨l, _hl, _hhead, hlast, _hnodup, _hlen, hstrength⟩
  have hle : pathStrength profile8_list l ≤ 0 := by
    exact pathStrength_le_zero_of_last (P := profile8_list) (cand := a2)
      (hmargin := margin_profile8_to_2_le_zero) l hlast
  simpa [hstrength] using hle

lemma schulzeDefeats_profile8_2_0 : schulzeDefeats profile8_list a2 a0 := by
  have hge : (2 : Int) ≤ strongestPath profile8_list a2 a0 :=
    strongestPath_profile8_2_0_ge_two
  have hle : strongestPath profile8_list a0 a2 ≤ 0 :=
    strongestPath_profile8_0_2_le_zero
  have hlt : strongestPath profile8_list a0 a2 < strongestPath profile8_list a2 a0 := by
    linarith
  exact hlt

lemma a0_not_in_schulze_profile8_list : a0 ∉ schulze profile8_list := by
  classical
  intro hmem
  have hcond : ∀ b, ¬ schulzeDefeats profile8_list b a0 := by
    simpa [schulze] using hmem
  exact (hcond a2) schulzeDefeats_profile8_2_0

lemma a0_in_schulze_profile9 : a0 ∈ schulze profile9 := by
  have hmargin : ∀ x y : A4, margin profile9 x y = margin profile9_list x y := by
    intro x y
    exact margin_profile9_eq_list x y
  have hsch : schulze profile9 = schulze profile9_list :=
    schulze_marginBased (P₁ := profile9) (P₂ := profile9_list) hmargin
  simpa [hsch] using a0_in_schulze_profile9_list

lemma a0_not_in_schulze_profile8 : a0 ∉ schulze profile8 := by
  have hmargin : ∀ x y : A4, margin profile8 x y = margin profile8_list x y := by
    intro x y
    exact margin_profile8_eq_list x y
  have hsch : schulze profile8 = schulze profile8_list :=
    schulze_marginBased (P₁ := profile8) (P₂ := profile8_list) hmargin
  simpa [hsch] using a0_not_in_schulze_profile8_list

end SchulzeNegativeInvolvementCounterexample

open SchulzeNegativeInvolvementCounterexample

theorem schulze_not_negativeInvolvement : ¬ NegativeInvolvement schulze := by
  intro hneg
  have hnot : a0 ∉ schulze profile9 :=
    hneg (V := voters8) (u := (0 : Fin 9)) (hu := voters8_not_mem)
      (P := profile8) (Q := profile9) (c := a0)
      profiles_agree a0_not_in_schulze_profile8 newVoter_bottom_0
  exact hnot a0_in_schulze_profile9

end SocialChoice
