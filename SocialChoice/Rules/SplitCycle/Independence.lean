import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Independence
import SocialChoice.ListBallot
import SocialChoice.Margin
import SocialChoice.Rules.SplitCycle.Defs
import SocialChoice.Rules.SplitCycle.Clones

namespace SocialChoice

open Finset

namespace SplitCycleIndependenceCounterexample

abbrev A4 := Fin 4

abbrev a : A4 := 0
abbrev b : A4 := 1
abbrev c : A4 := 2
abbrev d : A4 := 3

def ballot_cbad : ListBallot 4 := ListBallot.mk' [c, b, a, d]
def ballot_badc : ListBallot 4 := ListBallot.mk' [b, a, d, c]
def ballot_dcba : ListBallot 4 := ListBallot.mk' [d, c, b, a]
def ballot_dbac : ListBallot 4 := ListBallot.mk' [d, b, a, c]
def ballot_bdca : ListBallot 4 := ListBallot.mk' [b, d, c, a]
def ballot_dbca : ListBallot 4 := ListBallot.mk' [d, b, c, a]

def blocks : List (Nat × ListBallot 4) :=
  [(9, ballot_cbad), (6, ballot_badc), (3, ballot_dcba),
   (2, ballot_dbac), (1, ballot_bdca), (1, ballot_dbca)]

noncomputable def profile : Profile (Fin (ballotList blocks).length) A4 :=
  profileOfBlocks blocks

lemma marginBlocks_b_a : marginBlocks blocks b a = 22 := by decide
lemma marginBlocks_a_d : marginBlocks blocks a d = 8 := by decide
lemma marginBlocks_c_a : marginBlocks blocks c a = 6 := by decide
lemma marginBlocks_c_b : marginBlocks blocks c b = 2 := by decide
lemma marginBlocks_b_d : marginBlocks blocks b d = 10 := by decide
lemma marginBlocks_d_c : marginBlocks blocks d c = 4 := by decide

lemma margin_profile_b_a : margin profile b a = 22 := by
  simpa [profile, marginBlocks_b_a] using
    (margin_profileOfBlocks (blocks := blocks) (a := b) (b := a) (hne := by decide))

lemma margin_profile_a_d : margin profile a d = 8 := by
  simpa [profile, marginBlocks_a_d] using
    (margin_profileOfBlocks (blocks := blocks) (a := a) (b := d) (hne := by decide))

lemma margin_profile_c_a : margin profile c a = 6 := by
  simpa [profile, marginBlocks_c_a] using
    (margin_profileOfBlocks (blocks := blocks) (a := c) (b := a) (hne := by decide))

lemma margin_profile_c_b : margin profile c b = 2 := by
  simpa [profile, marginBlocks_c_b] using
    (margin_profileOfBlocks (blocks := blocks) (a := c) (b := b) (hne := by decide))

lemma margin_profile_b_d : margin profile b d = 10 := by
  simpa [profile, marginBlocks_b_d] using
    (margin_profileOfBlocks (blocks := blocks) (a := b) (b := d) (hne := by decide))

lemma margin_profile_d_c : margin profile d c = 4 := by
  simpa [profile, marginBlocks_d_c] using
    (margin_profileOfBlocks (blocks := blocks) (a := d) (b := c) (hne := by decide))

lemma margin_profile_a_c : margin profile a c = (-6 : Int) := by
  have h := margin_antisymmetric (P := profile) a c
  simpa [margin_profile_c_a] using h

lemma margin_profile_b_c : margin profile b c = (-2 : Int) := by
  have h := margin_antisymmetric (P := profile) b c
  simpa [margin_profile_c_b] using h

lemma margin_profile_c_d : margin profile c d = (-4 : Int) := by
  have h := margin_antisymmetric (P := profile) c d
  simpa [margin_profile_d_c] using h

lemma not_margin_pos_a_c : ¬ margin_pos profile a c := by
  simp [margin_pos, margin_profile_a_c]

lemma not_margin_pos_b_c : ¬ margin_pos profile b c := by
  simp [margin_pos, margin_profile_b_c]

lemma not_splitCycleDefeats_of_not_margin_pos {x y : A4}
    (h : ¬ margin_pos profile x y) : ¬ splitCycleDefeats profile x y := by
  intro hdef
  exact h hdef.1

lemma not_splitCycleDefeats_d_c : ¬ splitCycleDefeats profile d c := by
  intro hdef
  rcases hdef with ⟨_hpos, hno⟩
  let R : A4 → A4 → Prop := fun x y => margin profile d c ≤ margin profile x y
  have hchain : List.IsChain R [d, c, a, d] := by
    simp [R, margin_profile_d_c, margin_profile_c_a, margin_profile_a_d, List.isChain_cons]
  have hcycle : cycle R [c, a, d] := by
    refine ⟨by decide, ?_⟩
    simpa [R] using hchain
  have hmemd : d ∈ ([c, a, d] : List A4) := by simp
  have hmemc : c ∈ ([c, a, d] : List A4) := by simp
  exact hno ⟨[c, a, d], hmemd, hmemc, hcycle⟩

lemma c_in_splitCycle_profile : c ∈ splitCycle profile := by
  classical
  simp [splitCycle]
  intro y
  fin_cases y
  · exact not_splitCycleDefeats_of_not_margin_pos not_margin_pos_a_c
  · exact not_splitCycleDefeats_of_not_margin_pos not_margin_pos_b_c
  · intro hdef
    exact (margin_pos_irrefl (P := profile) c) hdef.1
  · exact not_splitCycleDefeats_d_c

noncomputable def profile' :
    Profile (Fin (ballotList blocks).length) {x : A4 // x ≠ a} :=
  restrictProfile profile a

def candB : {x : A4 // x ≠ a} := ⟨b, by decide⟩
def candC : {x : A4 // x ≠ a} := ⟨c, by decide⟩
def candD : {x : A4 // x ≠ a} := ⟨d, by decide⟩

lemma margin_restrict_eq (x y : {x : A4 // x ≠ a}) :
    margin profile' x y = margin profile x y := by
  simpa [profile'] using
    (margin_eq_margin_restrictProfile (P := profile) (c := a) (a := x) (b := y)).symm

lemma margin_profile'_d_c : margin profile' candD candC = 4 := by
  calc
    margin profile' candD candC = margin profile candD candC := margin_restrict_eq _ _
    _ = 4 := by simpa [candD, candC] using margin_profile_d_c

lemma margin_profile'_c_b : margin profile' candC candB = 2 := by
  calc
    margin profile' candC candB = margin profile candC candB := margin_restrict_eq _ _
    _ = 2 := by simpa [candC, candB] using margin_profile_c_b

lemma margin_profile'_c_d : margin profile' candC candD = (-4 : Int) := by
  calc
    margin profile' candC candD = margin profile candC candD := margin_restrict_eq _ _
    _ = (-4 : Int) := by simpa [candC, candD] using margin_profile_c_d

lemma no_rel_from_c (x : {x : A4 // x ≠ a}) :
    ¬ margin profile' candD candC ≤ margin profile' candC x := by
  rcases x with ⟨x, hx⟩
  fin_cases x
  · cases hx rfl
  ·
    have hx' : (⟨1, hx⟩ : {x : A4 // x ≠ a}) = candB := by
      apply Subtype.ext
      rfl
    have hdc : margin profile' candD candC = 4 := margin_profile'_d_c
    have hcb : margin profile' candC candB = 2 := margin_profile'_c_b
    intro hle
    have hle' : margin profile' candD candC ≤ margin profile' candC candB := by
      simpa [hx'] using hle
    linarith [hle', hdc, hcb]
  ·
    have hx' : (⟨2, hx⟩ : {x : A4 // x ≠ a}) = candC := by
      apply Subtype.ext
      rfl
    have hdc : margin profile' candD candC = 4 := margin_profile'_d_c
    have hcc : margin profile' candC candC = 0 := by
      simp [self_margin_zero]
    intro hle
    have hle' : margin profile' candD candC ≤ margin profile' candC candC := by
      simpa [hx'] using hle
    linarith [hle', hdc, hcc]
  ·
    have hx' : (⟨3, hx⟩ : {x : A4 // x ≠ a}) = candD := by
      apply Subtype.ext
      rfl
    have hdc : margin profile' candD candC = 4 := margin_profile'_d_c
    have hcd : margin profile' candC candD = (-4 : Int) := margin_profile'_c_d
    intro hle
    have hle' : margin profile' candD candC ≤ margin profile' candC candD := by
      simpa [hx'] using hle
    linarith [hle', hdc, hcd]

lemma no_path_from_c_to_d :
    ¬ ∃ l : List {x : A4 // x ≠ a}, ∃ h : l ≠ [],
      l.Nodup ∧
        l[0]'(List.length_pos_of_ne_nil h) = candC ∧
          l.getLast h = candD ∧
            List.IsChain (fun x y => margin profile' candD candC ≤ margin profile' x y) l := by
  intro hex
  rcases hex with ⟨l, hne, _hnodup, hfirst, hlast, hchain⟩
  cases l with
  | nil =>
      exact (hne rfl).elim
  | cons x t =>
      have hx : x = candC := by
        simpa using hfirst
      cases t with
      | nil =>
          have hlast' : x = candD := by
            simpa using hlast
          have hEq : candC = candD := by
            simpa [hx] using hlast'
          have hne : (candC : {x : A4 // x ≠ a}) ≠ candD := by decide
          exact (hne hEq).elim
      | cons y t' =>
          have hrel :
              margin profile' candD candC ≤ margin profile' x y := by
            simpa using hchain.rel
          have hrel' : margin profile' candD candC ≤ margin profile' candC y := by
            simpa [hx] using hrel
          exact (no_rel_from_c y) hrel'

lemma splitCycleDefeats_restrict_d_c :
    splitCycleDefeats profile' candD candC := by
  have hpos : margin_pos profile' candD candC := by
    simp [margin_pos, margin_profile'_d_c]
  refine (splitCycleDefeats_iff_path (P := profile') (x := candD) (y := candC)).2 ?_
  exact ⟨hpos, no_path_from_c_to_d⟩

lemma candC_not_in_splitCycle_restrict : candC ∉ splitCycle profile' := by
  classical
  intro hmem
  have hcond : ∀ y, ¬ splitCycleDefeats profile' y candC :=
    (Finset.mem_filter.mp hmem).2
  exact (hcond candD) splitCycleDefeats_restrict_d_c

lemma mem_liftWinners_iff {A : Type} [DecidableEq A] {p : A → Prop} [DecidablePred p]
    {s : Finset {a : A // p a}} {a : A} (ha : p a) :
    a ∈ liftWinners s ↔ (⟨a, ha⟩ : {a : A // p a}) ∈ s := by
  classical
  simp [liftWinners, Finset.mem_image, ha]

lemma c_not_in_lift_splitCycle_restrict :
    (c : A4) ∉ liftWinners (splitCycle profile') := by
  intro hc
  have hc' :
      (⟨c, by decide⟩ : {x : A4 // x ≠ a}) ∈ splitCycle profile' :=
    (mem_liftWinners_iff (A := A4) (p := fun x => x ≠ a) (s := splitCycle profile') (a := c)
      (by decide)).1 hc
  simpa [candC] using (candC_not_in_splitCycle_restrict hc')

end SplitCycleIndependenceCounterexample

open SplitCycleIndependenceCounterexample

theorem splitCycle_not_independenceOfDominated : ¬ IndependenceOfDominated splitCycle := by
  intro hind
  have hlen : (ballotList blocks).length = 22 := by
    simp [blocks, ballotList, ballotCopies]
  have hcard : (Fintype.card (Fin (ballotList blocks).length) : Int) = 22 := by
    simp [hlen]
  have hle :
      (Fintype.card (Fin (ballotList blocks).length) : Int) ≤ margin profile b a := by
    linarith [hcard, margin_profile_b_a]
  have hdomin : ∀ v : Fin (ballotList blocks).length, Prefers profile v b a :=
    unanimous_of_margin_ge_card (P := profile) (a := b) (b := a) hle
  have hnonempty : Nonempty (Fin (ballotList blocks).length) := by
    refine ⟨⟨0, ?_⟩⟩
    simp [hlen]
  let _ := hnonempty
  have hEq := hind (P := profile) (c := b) (d := a) hdomin
  have hc_in : c ∈ splitCycle profile := c_in_splitCycle_profile
  have hc_left :
      c ∈ liftWinners (splitCycle (restrictCandidates profile (fun x => x ≠ a))) := by
    simpa [hEq] using hc_in
  have hc_left' : c ∈ liftWinners (splitCycle profile') := by
    simpa [profile', restrictProfile] using hc_left
  exact c_not_in_lift_splitCycle_restrict hc_left'

end SocialChoice
