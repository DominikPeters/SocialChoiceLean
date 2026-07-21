import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Independence
import SocialChoice.ListBallot
import SocialChoice.Margin
import SocialChoice.Rules.Schulze.Defs
import SocialChoice.Rules.Schulze.Path

namespace SocialChoice

open Finset

namespace SchulzeIndependenceCounterexample

abbrev A5 := Fin 5

abbrev a0 : A5 := 0
abbrev a1 : A5 := 1
abbrev a2 : A5 := 2
abbrev a3 : A5 := 3
abbrev a4 : A5 := 4

def ballot24310 : ListBallot 5 := ListBallot.mk' [a2, a4, a3, a1, a0]
def ballot30214 : ListBallot 5 := ListBallot.mk' [a3, a0, a2, a1, a4]
def ballot41302 : ListBallot 5 := ListBallot.mk' [a4, a1, a3, a0, a2]

def blocks : List (Nat × ListBallot 5) :=
  [(1, ballot24310), (1, ballot30214), (1, ballot41302)]

@[reducible] noncomputable def profile : Profile (Fin (ballotList blocks).length) A5 :=
  profileOfBlocks blocks

lemma marginBlocks_1_0 : marginBlocks blocks a1 a0 = 1 := by decide
lemma marginBlocks_0_2 : marginBlocks blocks a0 a2 = 1 := by decide
lemma marginBlocks_2_1 : marginBlocks blocks a2 a1 = 1 := by decide
lemma marginBlocks_2_4 : marginBlocks blocks a2 a4 = 1 := by decide
lemma marginBlocks_3_0 : marginBlocks blocks a3 a0 = 3 := by decide
lemma marginBlocks_3_1 : marginBlocks blocks a3 a1 = 1 := by decide
lemma marginBlocks_3_2 : marginBlocks blocks a3 a2 = 1 := by decide
lemma marginBlocks_4_0 : marginBlocks blocks a4 a0 = 1 := by decide
lemma marginBlocks_4_1 : marginBlocks blocks a4 a1 = 1 := by decide
lemma marginBlocks_4_3 : marginBlocks blocks a4 a3 = 1 := by decide

lemma margin_profile_1_0 : margin profile a1 a0 = 1 := by
  simpa [marginBlocks_1_0] using
    (margin_profileOfBlocks (blocks := blocks) (a := a1) (b := a0) (hne := by decide))

lemma margin_profile_0_2 : margin profile a0 a2 = 1 := by
  simpa [marginBlocks_0_2] using
    (margin_profileOfBlocks (blocks := blocks) (a := a0) (b := a2) (hne := by decide))

lemma margin_profile_2_1 : margin profile a2 a1 = 1 := by
  simpa [marginBlocks_2_1] using
    (margin_profileOfBlocks (blocks := blocks) (a := a2) (b := a1) (hne := by decide))

lemma margin_profile_2_4 : margin profile a2 a4 = 1 := by
  simpa [marginBlocks_2_4] using
    (margin_profileOfBlocks (blocks := blocks) (a := a2) (b := a4) (hne := by decide))

lemma margin_profile_3_0 : margin profile a3 a0 = 3 := by
  simpa [marginBlocks_3_0] using
    (margin_profileOfBlocks (blocks := blocks) (a := a3) (b := a0) (hne := by decide))

lemma margin_profile_3_1 : margin profile a3 a1 = 1 := by
  simpa [marginBlocks_3_1] using
    (margin_profileOfBlocks (blocks := blocks) (a := a3) (b := a1) (hne := by decide))

lemma margin_profile_3_2 : margin profile a3 a2 = 1 := by
  simpa [marginBlocks_3_2] using
    (margin_profileOfBlocks (blocks := blocks) (a := a3) (b := a2) (hne := by decide))

lemma margin_profile_4_0 : margin profile a4 a0 = 1 := by
  simpa [marginBlocks_4_0] using
    (margin_profileOfBlocks (blocks := blocks) (a := a4) (b := a0) (hne := by decide))

lemma margin_profile_4_1 : margin profile a4 a1 = 1 := by
  simpa [marginBlocks_4_1] using
    (margin_profileOfBlocks (blocks := blocks) (a := a4) (b := a1) (hne := by decide))

lemma margin_profile_4_3 : margin profile a4 a3 = 1 := by
  simpa [marginBlocks_4_3] using
    (margin_profileOfBlocks (blocks := blocks) (a := a4) (b := a3) (hne := by decide))

lemma margin_profile_0_1 : margin profile a0 a1 = (-1 : Int) := by
  have h := margin_antisymmetric (P := profile) a0 a1
  simpa [margin_profile_1_0] using h

lemma margin_profile_1_2 : margin profile a1 a2 = (-1 : Int) := by
  have h := margin_antisymmetric (P := profile) a1 a2
  simpa [margin_profile_2_1] using h

lemma margin_profile_1_3 : margin profile a1 a3 = (-1 : Int) := by
  have h := margin_antisymmetric (P := profile) a1 a3
  simpa [margin_profile_3_1] using h

lemma margin_profile_1_4 : margin profile a1 a4 = (-1 : Int) := by
  have h := margin_antisymmetric (P := profile) a1 a4
  simpa [margin_profile_4_1] using h

lemma margin_profile_2_0 : margin profile a2 a0 = (-1 : Int) := by
  have h := margin_antisymmetric (P := profile) a2 a0
  simpa [margin_profile_0_2] using h

lemma margin_profile_2_3 : margin profile a2 a3 = (-1 : Int) := by
  have h := margin_antisymmetric (P := profile) a2 a3
  simpa [margin_profile_3_2] using h

lemma margin_profile_3_4 : margin profile a3 a4 = (-1 : Int) := by
  have h := margin_antisymmetric (P := profile) a3 a4
  simpa [margin_profile_4_3] using h

lemma margin_profile_4_2 : margin profile a4 a2 = (-1 : Int) := by
  have h := margin_antisymmetric (P := profile) a4 a2
  simpa [margin_profile_2_4] using h

lemma margin_profile_0_3 : margin profile a0 a3 = (-3 : Int) := by
  have h := margin_antisymmetric (P := profile) a0 a3
  simpa [margin_profile_3_0] using h

lemma margin_profile_0_4 : margin profile a0 a4 = (-1 : Int) := by
  have h := margin_antisymmetric (P := profile) a0 a4
  simpa [margin_profile_4_0] using h

lemma pathStrength_le_first_margin {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) (t : List A) :
    pathStrength P (a :: b :: t) ≤ margin P a b := by
  simp [pathStrength, pathStrengthAux_le_init]

lemma pathStrength_1_0_2 : pathStrength profile [a1, a0, a2] = 1 := by
  simp [pathStrength, pathStrengthAux, margin_profile_1_0, margin_profile_0_2]

lemma pathStrength_1_0_2_4 : pathStrength profile [a1, a0, a2, a4] = 1 := by
  simp [pathStrength_cons_cons_cons, margin_profile_1_0, margin_profile_0_2, margin_profile_2_4]

lemma pathStrength_1_0_2_4_3 : pathStrength profile [a1, a0, a2, a4, a3] = 1 := by
  simp [pathStrength_cons_cons_cons, margin_profile_1_0, margin_profile_0_2,
    margin_profile_2_4, margin_profile_4_3]

lemma path_1_0_2_mem :
    [a1, a0, a2] ∈ pathsUpTo (A := A5) (Fintype.card A5) a1 a2 := by
  refine mem_pathsUpTo_of_props (l := [a1, a0, a2]) (a := a1) (b := a2) ?_ ?_ ?_ ?_
  · simp
  · simp
  · decide
  · simp

lemma path_1_0_2_4_mem :
    [a1, a0, a2, a4] ∈ pathsUpTo (A := A5) (Fintype.card A5) a1 a4 := by
  refine mem_pathsUpTo_of_props (l := [a1, a0, a2, a4]) (a := a1) (b := a4) ?_ ?_ ?_ ?_
  · simp
  · simp
  · decide
  · simp

lemma path_1_0_2_4_3_mem :
    [a1, a0, a2, a4, a3] ∈ pathsUpTo (A := A5) (Fintype.card A5) a1 a3 := by
  refine mem_pathsUpTo_of_props (l := [a1, a0, a2, a4, a3]) (a := a1) (b := a3) ?_ ?_ ?_ ?_
  · simp
  · simp
  · decide
  · simp

lemma strongestPath_1_0_ge_one : (1 : Int) ≤ strongestPath profile a1 a0 := by
  have hne : a1 ≠ a0 := by decide
  have h := margin_le_strongestPath_of_ne (P := profile) (a := a1) (b := a0) hne
  simpa [margin_profile_1_0] using h

lemma strongestPath_1_2_ge_one : (1 : Int) ≤ strongestPath profile a1 a2 := by
  have hle := pathStrength_of_mem_pathsUpTo_le_strongestPath
    (P := profile) (a := a1) (b := a2) (l := [a1, a0, a2]) path_1_0_2_mem
  simpa [pathStrength_1_0_2] using hle

lemma strongestPath_1_4_ge_one : (1 : Int) ≤ strongestPath profile a1 a4 := by
  have hle := pathStrength_of_mem_pathsUpTo_le_strongestPath
    (P := profile) (a := a1) (b := a4) (l := [a1, a0, a2, a4]) path_1_0_2_4_mem
  simpa [pathStrength_1_0_2_4] using hle

lemma strongestPath_1_3_ge_one : (1 : Int) ≤ strongestPath profile a1 a3 := by
  have hle := pathStrength_of_mem_pathsUpTo_le_strongestPath
    (P := profile) (a := a1) (b := a3) (l := [a1, a0, a2, a4, a3]) path_1_0_2_4_3_mem
  simpa [pathStrength_1_0_2_4_3] using hle

lemma margin_profile_0_le_one (y : A5) (hy : y ≠ a0) : margin profile a0 y ≤ 1 := by
  fin_cases y
  · cases hy rfl
  ·
    have h : margin profile a0 a1 = (-1 : Int) := margin_profile_0_1
    simp [h]
  ·
    have h : margin profile a0 a2 = 1 := margin_profile_0_2
    simp [h]
  ·
    have h : margin profile a0 a3 = (-3 : Int) := margin_profile_0_3
    simp [h]
  ·
    have h : margin profile a0 a4 = (-1 : Int) := margin_profile_0_4
    simp [h]

lemma margin_profile_2_le_one (y : A5) (hy : y ≠ a2) : margin profile a2 y ≤ 1 := by
  fin_cases y
  ·
    have h : margin profile a2 a0 = (-1 : Int) := margin_profile_2_0
    simp [h]
  ·
    have h : margin profile a2 a1 = 1 := margin_profile_2_1
    simp [h]
  · cases hy rfl
  ·
    have h : margin profile a2 a3 = (-1 : Int) := margin_profile_2_3
    simp [h]
  ·
    have h : margin profile a2 a4 = 1 := margin_profile_2_4
    simp [h]

lemma margin_profile_4_le_one (y : A5) (hy : y ≠ a4) : margin profile a4 y ≤ 1 := by
  fin_cases y
  ·
    have h : margin profile a4 a0 = 1 := margin_profile_4_0
    simp [h]
  ·
    have h : margin profile a4 a1 = 1 := margin_profile_4_1
    simp [h]
  ·
    have h : margin profile a4 a2 = (-1 : Int) := margin_profile_4_2
    simp [h]
  ·
    have h : margin profile a4 a3 = 1 := margin_profile_4_3
    simp [h]
  · cases hy rfl

lemma margin_profile_3_le_one (y : A5) (hy : y ≠ a3) (hy0 : y ≠ a0) :
    margin profile a3 y ≤ 1 := by
  fin_cases y
  · cases hy0 rfl
  ·
    have h : margin profile a3 a1 = 1 := margin_profile_3_1
    simp [h]
  ·
    have h : margin profile a3 a2 = 1 := margin_profile_3_2
    simp [h]
  · cases hy rfl
  ·
    have h : margin profile a3 a4 = (-1 : Int) := margin_profile_3_4
    simp [h]

lemma strongestPath_0_1_le_one : strongestPath profile a0 a1 ≤ 1 := by
  classical
  have hne : a0 ≠ a1 := by decide
  have hne_paths :
      (pathsUpTo (A := A5) (Fintype.card A5) a0 a1).Nonempty :=
    pathsUpTo_nonempty_of_ne (A := A5) a0 a1 hne
  rcases exists_max_path_props (P := profile) (a := a0) (b := a1) hne_paths with
    ⟨l, _hl, hhead, _hlast, hnodup, hlen, hstrength⟩
  have hle : pathStrength profile l ≤ 1 := by
    cases l with
    | nil =>
        simp at hlen
    | cons x t =>
        have hx : x = a0 := by
          apply Option.some.inj
          simpa using hhead
        subst hx
        cases t with
        | nil =>
            simp at hlen
        | cons y t' =>
            have hy : y ≠ a0 := by
              have hnot : a0 ∉ (y :: t') := (List.nodup_cons.mp hnodup).1
              intro hyEq
              exact hnot (by simp [hyEq])
            have hmargin : margin profile a0 y ≤ 1 := margin_profile_0_le_one y hy
            have hpath : pathStrength profile (a0 :: y :: t') ≤ margin profile a0 y :=
              pathStrength_le_first_margin profile a0 y t'
            linarith
  simpa [hstrength] using hle

lemma strongestPath_2_1_le_one : strongestPath profile a2 a1 ≤ 1 := by
  classical
  have hne : a2 ≠ a1 := by decide
  have hne_paths :
      (pathsUpTo (A := A5) (Fintype.card A5) a2 a1).Nonempty :=
    pathsUpTo_nonempty_of_ne (A := A5) a2 a1 hne
  rcases exists_max_path_props (P := profile) (a := a2) (b := a1) hne_paths with
    ⟨l, _hl, hhead, _hlast, hnodup, hlen, hstrength⟩
  have hle : pathStrength profile l ≤ 1 := by
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
            have hmargin : margin profile a2 y ≤ 1 := margin_profile_2_le_one y hy
            have hpath : pathStrength profile (a2 :: y :: t') ≤ margin profile a2 y :=
              pathStrength_le_first_margin profile a2 y t'
            linarith
  simpa [hstrength] using hle

lemma strongestPath_4_1_le_one : strongestPath profile a4 a1 ≤ 1 := by
  classical
  have hne : a4 ≠ a1 := by decide
  have hne_paths :
      (pathsUpTo (A := A5) (Fintype.card A5) a4 a1).Nonempty :=
    pathsUpTo_nonempty_of_ne (A := A5) a4 a1 hne
  rcases exists_max_path_props (P := profile) (a := a4) (b := a1) hne_paths with
    ⟨l, _hl, hhead, _hlast, hnodup, hlen, hstrength⟩
  have hle : pathStrength profile l ≤ 1 := by
    cases l with
    | nil =>
        simp at hlen
    | cons x t =>
        have hx : x = a4 := by
          apply Option.some.inj
          simpa using hhead
        subst hx
        cases t with
        | nil =>
            simp at hlen
        | cons y t' =>
            have hy : y ≠ a4 := by
              have hnot : a4 ∉ (y :: t') := (List.nodup_cons.mp hnodup).1
              intro hyEq
              exact hnot (by simp [hyEq])
            have hmargin : margin profile a4 y ≤ 1 := margin_profile_4_le_one y hy
            have hpath : pathStrength profile (a4 :: y :: t') ≤ margin profile a4 y :=
              pathStrength_le_first_margin profile a4 y t'
            linarith
  simpa [hstrength] using hle

lemma strongestPath_3_1_le_one : strongestPath profile a3 a1 ≤ 1 := by
  classical
  have hne : a3 ≠ a1 := by decide
  have hne_paths :
      (pathsUpTo (A := A5) (Fintype.card A5) a3 a1).Nonempty :=
    pathsUpTo_nonempty_of_ne (A := A5) a3 a1 hne
  rcases exists_max_path_props (P := profile) (a := a3) (b := a1) hne_paths with
    ⟨l, _hl, hhead, hlast, hnodup, hlen, hstrength⟩
  have hle : pathStrength profile l ≤ 1 := by
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
            by_cases hy0 : y = a0
            · subst hy0
              cases t' with
              | nil =>
                  -- path is [a3, a0], contradict last = a1
                  have : (a0 : A5) = a1 := by
                    apply Option.some.inj
                    simpa using hlast.symm
                  cases (by decide : (a0 : A5) ≠ a1) this
              | cons z t'' =>
                  have hz : z ≠ a0 := by
                    have htail_nodup : (a0 :: z :: t'').Nodup :=
                      (List.nodup_cons.mp hnodup).2
                    have hnot : a0 ∉ (z :: t'') := (List.nodup_cons.mp htail_nodup).1
                    intro hzEq
                    exact hnot (by simp [hzEq])
                  have hmargin : margin profile a0 z ≤ 1 := margin_profile_0_le_one z hz
                  have htail : pathStrength profile (a0 :: z :: t'') ≤ margin profile a0 z :=
                    pathStrength_le_first_margin profile a0 z t''
                  have htail' : pathStrength profile (a0 :: z :: t'') ≤ 1 := by
                    linarith
                  have hpath :
                      pathStrength profile (a3 :: a0 :: z :: t'') ≤ 1 := by
                    have hstep :
                        pathStrength profile (a3 :: a0 :: z :: t'') =
                          min (margin profile a3 a0) (pathStrength profile (a0 :: z :: t'')) :=
                      pathStrength_cons_cons_cons profile a3 a0 z t''
                    -- margin 3->0 is 3, so min ≤ tail
                    have hmin : min (margin profile a3 a0) (pathStrength profile (a0 :: z :: t'')) ≤
                        pathStrength profile (a0 :: z :: t'') := by
                      exact min_le_right _ _
                    linarith [hstep, htail']
                  simpa using hpath
            ·
              have hmargin : margin profile a3 y ≤ 1 := margin_profile_3_le_one y hy hy0
              have hpath : pathStrength profile (a3 :: y :: t') ≤ margin profile a3 y :=
                pathStrength_le_first_margin profile a3 y t'
              linarith
  simpa [hstrength] using hle

lemma a1_in_schulze_profile : a1 ∈ schulze profile := by
  classical
  simp [schulze]
  intro b
  fin_cases b
  ·
    have hle : strongestPath profile a0 a1 ≤ 1 := strongestPath_0_1_le_one
    have hge : (1 : Int) ≤ strongestPath profile a1 a0 := strongestPath_1_0_ge_one
    intro hdef
    exact (not_lt_of_ge (le_trans hle hge)) hdef
  ·
    intro hdef
    exact (schulzeDefeats_ne (P := profile) hdef) rfl
  ·
    have hle : strongestPath profile a2 a1 ≤ 1 := strongestPath_2_1_le_one
    have hge : (1 : Int) ≤ strongestPath profile a1 a2 := strongestPath_1_2_ge_one
    intro hdef
    exact (not_lt_of_ge (le_trans hle hge)) hdef
  ·
    have hle : strongestPath profile a3 a1 ≤ 1 := strongestPath_3_1_le_one
    have hge : (1 : Int) ≤ strongestPath profile a1 a3 := strongestPath_1_3_ge_one
    intro hdef
    exact (not_lt_of_ge (le_trans hle hge)) hdef
  ·
    have hle : strongestPath profile a4 a1 ≤ 1 := strongestPath_4_1_le_one
    have hge : (1 : Int) ≤ strongestPath profile a1 a4 := strongestPath_1_4_ge_one
    intro hdef
    exact (not_lt_of_ge (le_trans hle hge)) hdef

noncomputable def profile' :
    Profile (Fin (ballotList blocks).length) {x : A5 // x ≠ a0} :=
  restrictProfile profile a0

def cand1 : {x : A5 // x ≠ a0} := ⟨a1, by decide⟩
def cand2 : {x : A5 // x ≠ a0} := ⟨a2, by decide⟩
def cand3 : {x : A5 // x ≠ a0} := ⟨a3, by decide⟩
def cand4 : {x : A5 // x ≠ a0} := ⟨a4, by decide⟩

lemma margin_restrict_eq (x y : {x : A5 // x ≠ a0}) :
    margin profile' x y = margin profile x y := by
  simpa [profile'] using
    (margin_eq_margin_restrictProfile (P := profile) (c := a0) (a := x) (b := y)).symm

lemma margin_profile'_2_1 : margin profile' cand2 cand1 = 1 := by
  calc
    margin profile' cand2 cand1 = margin profile cand2 cand1 := margin_restrict_eq _ _
    _ = 1 := by simpa [cand2, cand1] using margin_profile_2_1

lemma margin_profile'_1_2 : margin profile' cand1 cand2 = (-1 : Int) := by
  calc
    margin profile' cand1 cand2 = margin profile cand1 cand2 := margin_restrict_eq _ _
    _ = (-1 : Int) := by simp [cand1, cand2, margin_profile_1_2]

lemma strongestPath_profile'_2_1_ge_one : (1 : Int) ≤ strongestPath profile' cand2 cand1 := by
  have hne : cand2 ≠ cand1 := by decide
  have h := margin_le_strongestPath_of_ne (P := profile') (a := cand2) (b := cand1) hne
  simpa [margin_profile'_2_1] using h

lemma strongestPath_profile'_1_2_le_neg_one : strongestPath profile' cand1 cand2 ≤ (-1 : Int) := by
  classical
  have hne : cand1 ≠ cand2 := by decide
  have hne_paths :
      (pathsUpTo (A := {x : A5 // x ≠ a0}) (Fintype.card _) cand1 cand2).Nonempty :=
    pathsUpTo_nonempty_of_ne (A := {x : A5 // x ≠ a0}) cand1 cand2 hne
  rcases exists_max_path_props (P := profile') (a := cand1) (b := cand2) hne_paths with
    ⟨l, _hl, hhead, _hlast, hnodup, hlen, hstrength⟩
  have hle : pathStrength profile' l ≤ (-1 : Int) := by
    cases l with
    | nil =>
        simp at hlen
    | cons x t =>
        have hx : x = cand1 := by
          apply Option.some.inj
          simpa using hhead
        subst hx
        cases t with
        | nil =>
            simp at hlen
        | cons y t' =>
            have hy : y ≠ cand1 := by
              have hnot : cand1 ∉ (y :: t') := (List.nodup_cons.mp hnodup).1
              intro hyEq
              exact hnot (by simp [hyEq])
            rcases y with ⟨y, hy0⟩
            fin_cases y
            · cases hy0 rfl
            ·
              -- y = 1 contradicts hy
              cases hy (by rfl)
            ·
              have hmargin : margin profile' cand1 ⟨2, by decide⟩ = (-1 : Int) := by
                simpa [cand2] using margin_profile'_1_2
              have hpath : pathStrength profile' (cand1 :: ⟨2, by decide⟩ :: t') ≤
                  margin profile' cand1 ⟨2, by decide⟩ :=
                pathStrength_le_first_margin profile' cand1 ⟨2, by decide⟩ t'
              simpa [hmargin] using hpath
            ·
              have hmargin : margin profile' cand1 ⟨3, by decide⟩ = (-1 : Int) := by
                calc
                  margin profile' cand1 ⟨3, by decide⟩ = margin profile cand1 ⟨3, by decide⟩ :=
                    margin_restrict_eq _ _
                  _ = (-1 : Int) := by
                    simp [cand1, margin_profile_1_3]
              have hpath : pathStrength profile' (cand1 :: ⟨3, by decide⟩ :: t') ≤
                  margin profile' cand1 ⟨3, by decide⟩ :=
                pathStrength_le_first_margin profile' cand1 ⟨3, by decide⟩ t'
              simpa [hmargin] using hpath
            ·
              have hmargin : margin profile' cand1 ⟨4, by decide⟩ = (-1 : Int) := by
                calc
                  margin profile' cand1 ⟨4, by decide⟩ = margin profile cand1 ⟨4, by decide⟩ :=
                    margin_restrict_eq _ _
                  _ = (-1 : Int) := by
                    simpa [cand1] using margin_profile_1_4
              have hpath : pathStrength profile' (cand1 :: ⟨4, by decide⟩ :: t') ≤
                  margin profile' cand1 ⟨4, by decide⟩ :=
                pathStrength_le_first_margin profile' cand1 ⟨4, by decide⟩ t'
              simpa [hmargin] using hpath
  simpa [hstrength] using hle

lemma cand1_not_in_schulze_profile' : cand1 ∉ schulze profile' := by
  classical
  intro hmem
  have hcond : ∀ y, ¬ schulzeDefeats profile' y cand1 := (Finset.mem_filter.mp hmem).2
  have hge : (1 : Int) ≤ strongestPath profile' cand2 cand1 :=
    strongestPath_profile'_2_1_ge_one
  have hle : strongestPath profile' cand1 cand2 ≤ (-1 : Int) :=
    strongestPath_profile'_1_2_le_neg_one
  have hdef : schulzeDefeats profile' cand2 cand1 := by
    -- 1 > -1
    have hlt : strongestPath profile' cand2 cand1 > strongestPath profile' cand1 cand2 := by
      linarith
    exact hlt
  exact (hcond cand2) hdef

lemma mem_liftWinners_iff {A : Type} [DecidableEq A] {p : A → Prop} [DecidablePred p]
    {s : Finset {a : A // p a}} {a : A} (ha : p a) :
    a ∈ liftWinners s ↔ (⟨a, ha⟩ : {a : A // p a}) ∈ s := by
  classical
  simp [liftWinners, Finset.mem_image, ha]

lemma a1_not_in_lift_schulze_profile' :
    (a1 : A5) ∉ liftWinners (schulze profile') := by
  intro hmem
  have hmem' :
      (⟨a1, by decide⟩ : {x : A5 // x ≠ a0}) ∈ schulze profile' :=
    (mem_liftWinners_iff (A := A5) (p := fun x => x ≠ a0) (s := schulze profile') (a := a1)
      (by decide)).1 hmem
  simpa [cand1] using (cand1_not_in_schulze_profile' hmem')

end SchulzeIndependenceCounterexample

open SchulzeIndependenceCounterexample

theorem schulze_not_independenceOfDominated : ¬ IndependenceOfDominated schulze := by
  intro hind
  have hlen : (ballotList blocks).length = 3 := by
    simp [blocks, ballotList, ballotCopies]
  have hcard : (Fintype.card (Fin (ballotList blocks).length) : Int) = 3 := by
    simp [hlen]
  have hle :
      (Fintype.card (Fin (ballotList blocks).length) : Int) ≤ margin profile a3 a0 := by
    linarith [hcard, margin_profile_3_0]
  have hdomin : ∀ v : Fin (ballotList blocks).length, Prefers profile v a3 a0 :=
    unanimous_of_margin_ge_card (P := profile) (a := a3) (b := a0) hle
  have hnonempty : Nonempty (Fin (ballotList blocks).length) := by
    refine ⟨⟨0, ?_⟩⟩
    simp [hlen]
  let _ := hnonempty
  have hEq := hind (P := profile) (c := a3) (d := a0) hdomin
  have h1_in : a1 ∈ schulze profile := a1_in_schulze_profile
  have h1_left :
      a1 ∈ liftWinners (schulze (restrictCandidates profile (fun x => x ≠ a0))) := by
    simpa [hEq] using h1_in
  have h1_left' : a1 ∈ liftWinners (schulze profile') := by
    simpa [profile', restrictProfile] using h1_left
  exact a1_not_in_lift_schulze_profile' h1_left'

end SocialChoice
