import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Monotonicity
import SocialChoice.ListBallot
import SocialChoice.Rules.Nanson.Condorcet
import SocialChoice.Rules.Nanson.Reversal

namespace SocialChoice

open Classical
open Finset
open scoped BigOperators

attribute [instance] Classical.decEq Classical.decPred

/-!
# Nanson fails monotonicity

Counterexample with 4 candidates and 5 voters. Candidate 2 wins under Nanson.
After lifting 2 above 1 in one ballot, candidate 2 loses.
-/

namespace NansonMonotonicityCounterexample

abbrev A4 := Fin 4
abbrev a0 : A4 := 0
abbrev a1 : A4 := 1
abbrev a2 : A4 := 2
abbrev a3 : A4 := 3

def ballot1320 : ListBallot 4 := ListBallot.mk' [1, 3, 2, 0]
def ballot2130 : ListBallot 4 := ListBallot.mk' [2, 1, 3, 0]
def ballot3012 : ListBallot 4 := ListBallot.mk' [3, 0, 1, 2]
def ballot3021 : ListBallot 4 := ListBallot.mk' [3, 0, 2, 1]
def ballot3201 : ListBallot 4 := ListBallot.mk' [3, 2, 0, 1]

def ballots : Fin 5 → ListBallot 4
  | 0 => ballot1320
  | 1 => ballot2130
  | 2 => ballot2130
  | 3 => ballot3012
  | 4 => ballot3201
  | _ => ballot3201

def ballots' : Fin 5 → ListBallot 4
  | 0 => ballot1320
  | 1 => ballot2130
  | 2 => ballot2130
  | 3 => ballot3021
  | 4 => ballot3201
  | _ => ballot3201

noncomputable def profile : Profile (Fin 5) A4 :=
  profileOfListBallots ballots

noncomputable def profile' : Profile (Fin 5) A4 :=
  profileOfListBallots ballots'

-- margins for the original profile
private lemma marginList_profile_0_1 :
    marginList (fun v => (ballots v).ranking) (0 : Fin 4) (1 : Fin 4) = -1 := by
  decide

private lemma marginList_profile_0_2 :
    marginList (fun v => (ballots v).ranking) (0 : Fin 4) (2 : Fin 4) = -3 := by
  decide

private lemma marginList_profile_0_3 :
    marginList (fun v => (ballots v).ranking) (0 : Fin 4) (3 : Fin 4) = -5 := by
  decide

private lemma marginList_profile_1_2 :
    marginList (fun v => (ballots v).ranking) (1 : Fin 4) (2 : Fin 4) = -1 := by
  decide

private lemma marginList_profile_1_3 :
    marginList (fun v => (ballots v).ranking) (1 : Fin 4) (3 : Fin 4) = 1 := by
  decide

private lemma marginList_profile_2_3 :
    marginList (fun v => (ballots v).ranking) (2 : Fin 4) (3 : Fin 4) = -1 := by
  decide

private lemma margin_profile_0_1 : margin profile (0 : Fin 4) (1 : Fin 4) = -1 := by
  have h :=
    margin_eq_marginList (ballots := ballots) (a := (0 : Fin 4)) (b := (1 : Fin 4))
  simpa [profile, marginList_profile_0_1] using h

private lemma margin_profile_0_2 : margin profile (0 : Fin 4) (2 : Fin 4) = -3 := by
  have h :=
    margin_eq_marginList (ballots := ballots) (a := (0 : Fin 4)) (b := (2 : Fin 4))
  simpa [profile, marginList_profile_0_2] using h

private lemma margin_profile_0_3 : margin profile (0 : Fin 4) (3 : Fin 4) = -5 := by
  have h :=
    margin_eq_marginList (ballots := ballots) (a := (0 : Fin 4)) (b := (3 : Fin 4))
  simpa [profile, marginList_profile_0_3] using h

private lemma margin_profile_1_2 : margin profile (1 : Fin 4) (2 : Fin 4) = -1 := by
  have h :=
    margin_eq_marginList (ballots := ballots) (a := (1 : Fin 4)) (b := (2 : Fin 4))
  simpa [profile, marginList_profile_1_2] using h

private lemma margin_profile_1_3 : margin profile (1 : Fin 4) (3 : Fin 4) = 1 := by
  have h :=
    margin_eq_marginList (ballots := ballots) (a := (1 : Fin 4)) (b := (3 : Fin 4))
  simpa [profile, marginList_profile_1_3] using h

private lemma margin_profile_2_3 : margin profile (2 : Fin 4) (3 : Fin 4) = -1 := by
  have h :=
    margin_eq_marginList (ballots := ballots) (a := (2 : Fin 4)) (b := (3 : Fin 4))
  simpa [profile, marginList_profile_2_3] using h

private lemma margin_profile_1_0 : margin profile (1 : Fin 4) (0 : Fin 4) = 1 := by
  have h := margin_antisymmetric (P := profile) (1 : Fin 4) (0 : Fin 4)
  simpa [margin_profile_0_1] using h

private lemma margin_profile_2_0 : margin profile (2 : Fin 4) (0 : Fin 4) = 3 := by
  have h := margin_antisymmetric (P := profile) (2 : Fin 4) (0 : Fin 4)
  simpa [margin_profile_0_2] using h

private lemma margin_profile_3_0 : margin profile (3 : Fin 4) (0 : Fin 4) = 5 := by
  have h := margin_antisymmetric (P := profile) (3 : Fin 4) (0 : Fin 4)
  simpa [margin_profile_0_3] using h

private lemma margin_profile_2_1 : margin profile (2 : Fin 4) (1 : Fin 4) = 1 := by
  have h := margin_antisymmetric (P := profile) (2 : Fin 4) (1 : Fin 4)
  simpa [margin_profile_1_2] using h

private lemma margin_profile_3_1 : margin profile (3 : Fin 4) (1 : Fin 4) = -1 := by
  have h := margin_antisymmetric (P := profile) (3 : Fin 4) (1 : Fin 4)
  simpa [margin_profile_1_3] using h

private lemma margin_profile_3_2 : margin profile (3 : Fin 4) (2 : Fin 4) = 1 := by
  have h := margin_antisymmetric (P := profile) (3 : Fin 4) (2 : Fin 4)
  simpa [margin_profile_2_3] using h

private lemma c2Borda_profile_0 : c2BordaScore profile (0 : Fin 4) = -9 := by
  simp [c2BordaScore, Fin.sum_univ_four, self_margin_zero, margin_profile_0_1,
    margin_profile_0_2, margin_profile_0_3]

private lemma c2Borda_profile_1 : c2BordaScore profile (1 : Fin 4) = 1 := by
  simp [c2BordaScore, Fin.sum_univ_four, self_margin_zero, margin_profile_1_0,
    margin_profile_1_2, margin_profile_1_3]

private lemma c2Borda_profile_2 : c2BordaScore profile (2 : Fin 4) = 3 := by
  simp [c2BordaScore, Fin.sum_univ_four, self_margin_zero, margin_profile_2_0,
    margin_profile_2_1, margin_profile_2_3]

private lemma c2Borda_profile_3 : c2BordaScore profile (3 : Fin 4) = 5 := by
  simp [c2BordaScore, Fin.sum_univ_four, self_margin_zero, margin_profile_3_0,
    margin_profile_3_1, margin_profile_3_2]

abbrev PosCand := {x : A4 // c2BordaScore profile x > 0}

@[reducible] noncomputable def profilePos : Profile (Fin 5) PosCand :=
  restrictCandidates profile (fun x => c2BordaScore profile x > 0)

def cand1 : PosCand := ⟨1, by linarith [c2Borda_profile_1]⟩
def cand2 : PosCand := ⟨2, by linarith [c2Borda_profile_2]⟩
def cand3 : PosCand := ⟨3, by linarith [c2Borda_profile_3]⟩

lemma univ_profilePos_eq : (Finset.univ : Finset PosCand) = {cand1, cand2, cand3} := by
  classical
  ext x
  constructor
  · intro _
    rcases x with ⟨x, hxpos⟩
    fin_cases x
    · have : (0 : Int) < c2BordaScore profile (0 : Fin 4) := hxpos
      linarith [c2Borda_profile_0]
    · simp [cand1, cand2, cand3]
    · simp [cand1, cand2, cand3]
    · simp [cand1, cand2, cand3]
  · intro hx
    simp at hx
    simp

lemma margin_profilePos_cand1_cand2 : margin profilePos cand1 cand2 = -1 := by
  have h :=
    margin_eq_margin_restrictCandidates (P := profile)
      (p := fun x => c2BordaScore profile x > 0) (a := cand1) (b := cand2)
  simpa [profilePos, cand1, cand2, margin_profile_1_2] using h.symm

lemma margin_profilePos_cand1_cand3 : margin profilePos cand1 cand3 = 1 := by
  have h :=
    margin_eq_margin_restrictCandidates (P := profile)
      (p := fun x => c2BordaScore profile x > 0) (a := cand1) (b := cand3)
  simpa [profilePos, cand1, cand3, margin_profile_1_3] using h.symm

lemma margin_profilePos_cand2_cand3 : margin profilePos cand2 cand3 = -1 := by
  have h :=
    margin_eq_margin_restrictCandidates (P := profile)
      (p := fun x => c2BordaScore profile x > 0) (a := cand2) (b := cand3)
  simpa [profilePos, cand2, cand3, margin_profile_2_3] using h.symm

lemma margin_profilePos_cand2_cand1 : margin profilePos cand2 cand1 = 1 := by
  have h := margin_antisymmetric (P := profilePos) cand2 cand1
  simpa [margin_profilePos_cand1_cand2] using h

lemma margin_profilePos_cand3_cand1 : margin profilePos cand3 cand1 = -1 := by
  have h := margin_antisymmetric (P := profilePos) cand3 cand1
  simpa [margin_profilePos_cand1_cand3] using h

lemma margin_profilePos_cand3_cand2 : margin profilePos cand3 cand2 = 1 := by
  have h := margin_antisymmetric (P := profilePos) cand3 cand2
  simpa [margin_profilePos_cand2_cand3] using h

lemma c2Borda_profilePos_cand1 : c2BordaScore profilePos cand1 = 0 := by
  classical
  have hne : cand2 ≠ cand3 := by decide
  have hsum :
      c2BordaScore profilePos cand1 =
        ∑ x ∈ ({cand2, cand3} : Finset PosCand), margin profilePos cand1 x := by
    simp [c2BordaScore, univ_profilePos_eq, self_margin_zero, Finset.sum_insert,
      Finset.sum_singleton, cand1, cand2, cand3]
  calc
    c2BordaScore profilePos cand1 =
        ∑ x ∈ ({cand2, cand3} : Finset PosCand), margin profilePos cand1 x := hsum
    _ = margin profilePos cand1 cand2 + margin profilePos cand1 cand3 := by
        simp [Finset.sum_pair hne]
    _ = 0 := by simp [margin_profilePos_cand1_cand2, margin_profilePos_cand1_cand3]

lemma c2Borda_profilePos_cand2 : c2BordaScore profilePos cand2 = 0 := by
  classical
  have hne : cand1 ≠ cand3 := by decide
  have h12 : cand1 ≠ cand2 := by decide
  have h23 : cand2 ≠ cand3 := by decide
  have hsum :
      c2BordaScore profilePos cand2 =
        ∑ x ∈ ({cand1, cand3} : Finset PosCand), margin profilePos cand2 x := by
    unfold c2BordaScore
    have hunivSum := congrArg
      (fun s : Finset PosCand => Finset.sum s (fun x => margin profilePos cand2 x))
      univ_profilePos_eq
    have hmem : cand2 ∈ ({cand1, cand2, cand3} : Finset PosCand) := by simp
    have herase :
        ({cand1, cand2, cand3} : Finset PosCand).erase cand2 = {cand1, cand3} := by
      native_decide
    calc
      ∑ x : PosCand, margin profilePos cand2 x =
          Finset.sum ({cand1, cand2, cand3} : Finset PosCand)
            (fun x => margin profilePos cand2 x) := hunivSum
      _ = Finset.sum (({cand1, cand2, cand3} : Finset PosCand).erase cand2)
            (fun x => margin profilePos cand2 x) + margin profilePos cand2 cand2 :=
        (Finset.sum_erase_add _ _ hmem).symm
      _ = ∑ x ∈ ({cand1, cand3} : Finset PosCand), margin profilePos cand2 x := by
        rw [herase, self_margin_zero, add_zero]
  calc
    c2BordaScore profilePos cand2 =
        ∑ x ∈ ({cand1, cand3} : Finset PosCand), margin profilePos cand2 x := hsum
    _ = margin profilePos cand2 cand1 + margin profilePos cand2 cand3 := by
        simp [Finset.sum_pair hne]
    _ = 0 := by simp [margin_profilePos_cand2_cand1, margin_profilePos_cand2_cand3]

lemma c2Borda_profilePos_cand3 : c2BordaScore profilePos cand3 = 0 := by
  classical
  have hne : cand1 ≠ cand2 := by decide
  have h13 : cand1 ≠ cand3 := by decide
  have h23 : cand2 ≠ cand3 := by decide
  have hsum :
      c2BordaScore profilePos cand3 =
        ∑ x ∈ ({cand1, cand2} : Finset PosCand), margin profilePos cand3 x := by
    unfold c2BordaScore
    have hunivSum := congrArg
      (fun s : Finset PosCand => Finset.sum s (fun x => margin profilePos cand3 x))
      univ_profilePos_eq
    have hmem : cand3 ∈ ({cand1, cand2, cand3} : Finset PosCand) := by simp
    have herase :
        ({cand1, cand2, cand3} : Finset PosCand).erase cand3 = {cand1, cand2} := by
      native_decide
    calc
      ∑ x : PosCand, margin profilePos cand3 x =
          Finset.sum ({cand1, cand2, cand3} : Finset PosCand)
            (fun x => margin profilePos cand3 x) := hunivSum
      _ = Finset.sum (({cand1, cand2, cand3} : Finset PosCand).erase cand3)
            (fun x => margin profilePos cand3 x) + margin profilePos cand3 cand3 :=
        (Finset.sum_erase_add _ _ hmem).symm
      _ = ∑ x ∈ ({cand1, cand2} : Finset PosCand), margin profilePos cand3 x := by
        rw [herase, self_margin_zero, add_zero]
  calc
    c2BordaScore profilePos cand3 =
        ∑ x ∈ ({cand1, cand2} : Finset PosCand), margin profilePos cand3 x := hsum
    _ = margin profilePos cand3 cand1 + margin profilePos cand3 cand2 := by
        simp [Finset.sum_pair hne]
    _ = 0 := by simp [margin_profilePos_cand3_cand1, margin_profilePos_cand3_cand2]

lemma c2Borda_profilePos_all_zero (x : PosCand) : c2BordaScore profilePos x = 0 := by
  rcases x with ⟨x, hxpos⟩
  fin_cases x
  · have : (0 : Int) < c2BordaScore profile (0 : Fin 4) := hxpos
    linarith [c2Borda_profile_0]
  ·
    have hx' : (⟨1, hxpos⟩ : PosCand) = cand1 := by
      apply Subtype.ext
      rfl
    simpa [hx'] using c2Borda_profilePos_cand1
  ·
    have hx' : (⟨2, hxpos⟩ : PosCand) = cand2 := by
      apply Subtype.ext
      rfl
    simpa [hx'] using c2Borda_profilePos_cand2
  ·
    have hx' : (⟨3, hxpos⟩ : PosCand) = cand3 := by
      apply Subtype.ext
      rfl
    simpa [hx'] using c2Borda_profilePos_cand3

lemma nanson_profile : nanson profile = ({1, 2, 3} : Finset A4) := by
  classical
  have hnotall : ¬ ∀ x, c2BordaScore profile x = 0 := by
    intro hall
    have := hall (3 : Fin 4)
    linarith [c2Borda_profile_3]
  have hsurv :
      (Finset.univ.filter (fun x => c2BordaScore profile x > 0)).Nonempty := by
    refine ⟨(1 : Fin 4), ?_⟩
    simp [c2Borda_profile_1]
  have hallPos : ∀ x : PosCand, c2BordaScore profilePos x = 0 := by
    intro x
    exact c2Borda_profilePos_all_zero x
  have hauxPos : nansonAux 3 PosCand profilePos = (Finset.univ : Finset PosCand) := by
    simp [nansonAux, hallPos]
  have haux : nanson profile = liftWinners (nansonAux 3 PosCand profilePos) := by
    simp [nanson, nansonAux, hnotall, hsurv, profilePos]
  calc
    nanson profile = liftWinners (nansonAux 3 PosCand profilePos) := haux
    _ = liftWinners (Finset.univ : Finset PosCand) := by simp [hauxPos]
    _ = ({1, 2, 3} : Finset A4) := by
      ext x
      fin_cases x <;>
        simp [liftWinners, univ_profilePos_eq, cand1, cand2, cand3]

-- margins for the updated profile
private lemma marginList_profile'_0_1 :
    marginList (fun v => (ballots' v).ranking) (0 : Fin 4) (1 : Fin 4) = -1 := by
  decide

private lemma marginList_profile'_0_2 :
    marginList (fun v => (ballots' v).ranking) (0 : Fin 4) (2 : Fin 4) = -3 := by
  decide

private lemma marginList_profile'_0_3 :
    marginList (fun v => (ballots' v).ranking) (0 : Fin 4) (3 : Fin 4) = -5 := by
  decide

private lemma marginList_profile'_1_2 :
    marginList (fun v => (ballots' v).ranking) (1 : Fin 4) (2 : Fin 4) = -3 := by
  decide

private lemma marginList_profile'_1_3 :
    marginList (fun v => (ballots' v).ranking) (1 : Fin 4) (3 : Fin 4) = 1 := by
  decide

private lemma marginList_profile'_2_3 :
    marginList (fun v => (ballots' v).ranking) (2 : Fin 4) (3 : Fin 4) = -1 := by
  decide

private lemma margin_profile'_0_1 : margin profile' (0 : Fin 4) (1 : Fin 4) = -1 := by
  have h :=
    margin_eq_marginList (ballots := ballots') (a := (0 : Fin 4)) (b := (1 : Fin 4))
  simpa [profile', marginList_profile'_0_1] using h

private lemma margin_profile'_0_2 : margin profile' (0 : Fin 4) (2 : Fin 4) = -3 := by
  have h :=
    margin_eq_marginList (ballots := ballots') (a := (0 : Fin 4)) (b := (2 : Fin 4))
  simpa [profile', marginList_profile'_0_2] using h

private lemma margin_profile'_0_3 : margin profile' (0 : Fin 4) (3 : Fin 4) = -5 := by
  have h :=
    margin_eq_marginList (ballots := ballots') (a := (0 : Fin 4)) (b := (3 : Fin 4))
  simpa [profile', marginList_profile'_0_3] using h

private lemma margin_profile'_1_2 : margin profile' (1 : Fin 4) (2 : Fin 4) = -3 := by
  have h :=
    margin_eq_marginList (ballots := ballots') (a := (1 : Fin 4)) (b := (2 : Fin 4))
  simpa [profile', marginList_profile'_1_2] using h

private lemma margin_profile'_1_3 : margin profile' (1 : Fin 4) (3 : Fin 4) = 1 := by
  have h :=
    margin_eq_marginList (ballots := ballots') (a := (1 : Fin 4)) (b := (3 : Fin 4))
  simpa [profile', marginList_profile'_1_3] using h

private lemma margin_profile'_2_3 : margin profile' (2 : Fin 4) (3 : Fin 4) = -1 := by
  have h :=
    margin_eq_marginList (ballots := ballots') (a := (2 : Fin 4)) (b := (3 : Fin 4))
  simpa [profile', marginList_profile'_2_3] using h

private lemma margin_profile'_1_0 : margin profile' (1 : Fin 4) (0 : Fin 4) = 1 := by
  have h := margin_antisymmetric (P := profile') (1 : Fin 4) (0 : Fin 4)
  simpa [margin_profile'_0_1] using h

private lemma margin_profile'_2_0 : margin profile' (2 : Fin 4) (0 : Fin 4) = 3 := by
  have h := margin_antisymmetric (P := profile') (2 : Fin 4) (0 : Fin 4)
  simpa [margin_profile'_0_2] using h

private lemma margin_profile'_3_0 : margin profile' (3 : Fin 4) (0 : Fin 4) = 5 := by
  have h := margin_antisymmetric (P := profile') (3 : Fin 4) (0 : Fin 4)
  simpa [margin_profile'_0_3] using h

private lemma margin_profile'_2_1 : margin profile' (2 : Fin 4) (1 : Fin 4) = 3 := by
  have h := margin_antisymmetric (P := profile') (2 : Fin 4) (1 : Fin 4)
  simpa [margin_profile'_1_2] using h

private lemma margin_profile'_3_1 : margin profile' (3 : Fin 4) (1 : Fin 4) = -1 := by
  have h := margin_antisymmetric (P := profile') (3 : Fin 4) (1 : Fin 4)
  simpa [margin_profile'_1_3] using h

private lemma margin_profile'_3_2 : margin profile' (3 : Fin 4) (2 : Fin 4) = 1 := by
  have h := margin_antisymmetric (P := profile') (3 : Fin 4) (2 : Fin 4)
  simpa [margin_profile'_2_3] using h

private lemma c2Borda_profile'_0 : c2BordaScore profile' (0 : Fin 4) = -9 := by
  simp [c2BordaScore, Fin.sum_univ_four, self_margin_zero, margin_profile'_0_1,
    margin_profile'_0_2, margin_profile'_0_3]

private lemma c2Borda_profile'_1 : c2BordaScore profile' (1 : Fin 4) = -1 := by
  simp [c2BordaScore, Fin.sum_univ_four, self_margin_zero, margin_profile'_1_0,
    margin_profile'_1_2, margin_profile'_1_3]

private lemma c2Borda_profile'_2 : c2BordaScore profile' (2 : Fin 4) = 5 := by
  simp [c2BordaScore, Fin.sum_univ_four, self_margin_zero, margin_profile'_2_0,
    margin_profile'_2_1, margin_profile'_2_3]

private lemma c2Borda_profile'_3 : c2BordaScore profile' (3 : Fin 4) = 5 := by
  simp [c2BordaScore, Fin.sum_univ_four, self_margin_zero, margin_profile'_3_0,
    margin_profile'_3_1, margin_profile'_3_2]

abbrev PosCand' := {x : A4 // c2BordaScore profile' x > 0}

@[reducible] noncomputable def profilePos' : Profile (Fin 5) PosCand' :=
  restrictCandidates profile' (fun x => c2BordaScore profile' x > 0)

def cand2' : PosCand' := ⟨2, by linarith [c2Borda_profile'_2]⟩
def cand3' : PosCand' := ⟨3, by linarith [c2Borda_profile'_3]⟩

lemma univ_profilePos'_eq : (Finset.univ : Finset PosCand') = {cand2', cand3'} := by
  classical
  ext x
  constructor
  · intro _
    rcases x with ⟨x, hxpos⟩
    fin_cases x
    · have : (0 : Int) < c2BordaScore profile' (0 : Fin 4) := hxpos
      linarith [c2Borda_profile'_0]
    · have : (0 : Int) < c2BordaScore profile' (1 : Fin 4) := hxpos
      linarith [c2Borda_profile'_1]
    · simp [cand2', cand3']
    · simp [cand2', cand3']
  · intro hx
    simp at hx
    simp

lemma margin_profilePos'_cand2_cand3 : margin profilePos' cand2' cand3' = -1 := by
  have h :=
    margin_eq_margin_restrictCandidates (P := profile')
      (p := fun x => c2BordaScore profile' x > 0) (a := cand2') (b := cand3')
  simpa [profilePos', cand2', cand3', margin_profile'_2_3] using h.symm

lemma margin_profilePos'_cand3_cand2 : margin profilePos' cand3' cand2' = 1 := by
  have h := margin_antisymmetric (P := profilePos') cand3' cand2'
  simpa [margin_profilePos'_cand2_cand3] using h

lemma c2Borda_profilePos'_cand2 : c2BordaScore profilePos' cand2' = -1 := by
  classical
  have hsum :
      c2BordaScore profilePos' cand2' =
        ∑ x ∈ ({cand2', cand3'} : Finset PosCand'), margin profilePos' cand2' x := by
    simp [c2BordaScore, univ_profilePos'_eq, self_margin_zero, Finset.sum_insert,
      Finset.sum_singleton, cand2', cand3']
  have hne : cand2' ≠ cand3' := by decide
  calc
    c2BordaScore profilePos' cand2' =
        ∑ x ∈ ({cand2', cand3'} : Finset PosCand'), margin profilePos' cand2' x := hsum
    _ = margin profilePos' cand2' cand2' + margin profilePos' cand2' cand3' := by
        simp [Finset.sum_pair hne]
    _ = -1 := by
        simp [self_margin_zero, margin_profilePos'_cand2_cand3]

lemma c2Borda_profilePos'_cand3 : c2BordaScore profilePos' cand3' = 1 := by
  classical
  have hsum :
      c2BordaScore profilePos' cand3' =
        ∑ x ∈ ({cand2', cand3'} : Finset PosCand'), margin profilePos' cand3' x := by
    simp [c2BordaScore, univ_profilePos'_eq, self_margin_zero, Finset.sum_insert,
      Finset.sum_singleton, cand2', cand3']
  have hne : cand2' ≠ cand3' := by decide
  calc
    c2BordaScore profilePos' cand3' =
        ∑ x ∈ ({cand2', cand3'} : Finset PosCand'), margin profilePos' cand3' x := hsum
    _ = margin profilePos' cand3' cand2' + margin profilePos' cand3' cand3' := by
        simp [Finset.sum_pair hne]
    _ = 1 := by
        simp [self_margin_zero, margin_profilePos'_cand3_cand2]

lemma profilePos'_pos_iff (x : PosCand') :
    0 < c2BordaScore profilePos' x ↔ x = cand3' := by
  rcases x with ⟨x, hxpos⟩
  fin_cases x
  · have : (0 : Int) < c2BordaScore profile' (0 : Fin 4) := hxpos
    linarith [c2Borda_profile'_0]
  · have : (0 : Int) < c2BordaScore profile' (1 : Fin 4) := hxpos
    linarith [c2Borda_profile'_1]
  ·
    have hx' : (⟨2, hxpos⟩ : PosCand') = cand2' := by
      apply Subtype.ext
      rfl
    have hne : cand2' ≠ cand3' := by decide
    simp [hx', c2Borda_profilePos'_cand2, hne]
  ·
    have hx' : (⟨3, hxpos⟩ : PosCand') = cand3' := by
      apply Subtype.ext
      rfl
    simp [hx', c2Borda_profilePos'_cand3]

abbrev PosCand'' := {x : PosCand' // c2BordaScore profilePos' x > 0}

@[reducible] noncomputable def profilePos'' : Profile (Fin 5) PosCand'' :=
  restrictCandidates profilePos' (fun x => c2BordaScore profilePos' x > 0)

def cand3'' : PosCand'' := ⟨cand3', by linarith [c2Borda_profilePos'_cand3]⟩

lemma univ_profilePos''_eq : (Finset.univ : Finset PosCand'') = {cand3''} := by
  classical
  ext x
  constructor
  · intro _
    have hx : x.1 = cand3' := (profilePos'_pos_iff x.1).1 x.property
    apply Finset.mem_singleton.mpr
    apply Subtype.ext
    simp [cand3'', hx]
  · intro hx
    simp at hx
    simp

lemma poscand''_subsingleton : Subsingleton PosCand'' := by
  classical
  refine ⟨?_⟩
  intro x y
  have hx : x.1 = cand3' := (profilePos'_pos_iff x.1).1 x.property
  have hy : y.1 = cand3' := (profilePos'_pos_iff y.1).1 y.property
  apply Subtype.ext
  simp [hx, hy]

lemma c2Borda_profilePos''_all_zero (x : PosCand'') : c2BordaScore profilePos'' x = 0 := by
  classical
  haveI : Subsingleton PosCand'' := poscand''_subsingleton
  exact c2BordaScore_eq_zero_of_subsingleton (P := profilePos'') (a := x)

lemma nansonAux_profilePos' : nansonAux 3 PosCand' profilePos' = ({cand3'} : Finset PosCand') := by
  classical
  have hnotall : ¬ ∀ x : PosCand', c2BordaScore profilePos' x = 0 := by
    intro hall
    have := hall cand3'
    linarith [c2Borda_profilePos'_cand3]
  have hsurv :
      (Finset.univ.filter (fun x => c2BordaScore profilePos' x > 0)).Nonempty := by
    refine ⟨cand3', ?_⟩
    simp [c2Borda_profilePos'_cand3]
  have haux :
      nansonAux 3 PosCand' profilePos' =
        liftWinners (nansonAux 2 PosCand'' profilePos'') := by
    by_cases hall : ∀ x : PosCand', c2BordaScore profilePos' x = 0
    · exact (hnotall hall).elim
    ·
      have hsurv' :
          (Finset.univ.filter (fun x => c2BordaScore profilePos' x > 0)).Nonempty := hsurv
      have haux' :
          nansonAux 3 PosCand' profilePos' =
            liftWinners
              (nansonAux 2 {x : PosCand' // c2BordaScore profilePos' x > 0}
                (restrictCandidates profilePos' (fun x => c2BordaScore profilePos' x > 0))) := by
        have hall' :
            ¬ ∀ (a : A4) (b : 0 < c2BordaScore profile' a),
              c2BordaScore profilePos' ⟨a, b⟩ = 0 := by
          simpa [PosCand'] using hall
        have hsurv'' :
            (Finset.univ.filter (fun x : PosCand' =>
              c2BordaScore profilePos' x > 0)).Nonempty := hsurv'
        simp [nansonAux, hall', hsurv'']
      simpa [PosCand'', profilePos''] using haux'
  have haux' : nansonAux 2 PosCand'' profilePos'' = (Finset.univ : Finset PosCand'') := by
    have hall'' : ∀ x : PosCand'', c2BordaScore profilePos'' x = 0 := by
      intro x
      exact c2Borda_profilePos''_all_zero x
    simp [nansonAux, hall'']
  calc
    nansonAux 3 PosCand' profilePos' =
        liftWinners (nansonAux 2 PosCand'' profilePos'') := haux
    _ = liftWinners (Finset.univ : Finset PosCand'') := by simp [haux']
    _ = ({cand3'} : Finset PosCand') := by
      simp [liftWinners, univ_profilePos''_eq, cand3'']

lemma nanson_profile' : nanson profile' = ({3} : Finset A4) := by
  classical
  have hnotall : ¬ ∀ x, c2BordaScore profile' x = 0 := by
    intro hall
    have := hall (3 : Fin 4)
    linarith [c2Borda_profile'_3]
  have hsurv :
      (Finset.univ.filter (fun x => c2BordaScore profile' x > 0)).Nonempty := by
    refine ⟨(2 : Fin 4), ?_⟩
    simp [c2Borda_profile'_2]
  have haux : nanson profile' = liftWinners (nansonAux 3 PosCand' profilePos') := by
    simp [nanson, nansonAux, hnotall, hsurv, profilePos']
  calc
    nanson profile' = liftWinners (nansonAux 3 PosCand' profilePos') := haux
    _ = liftWinners ({cand3'} : Finset PosCand') := by
      simp [nansonAux_profilePos']
    _ = ({3} : Finset A4) := by
      simp [liftWinners, cand3']

private lemma simpleLift_profile : simpleLift profile' profile (2 : Fin 4) := by
  classical
  constructor
  · intro v a b ha hb
    fin_cases v <;> fin_cases a <;> fin_cases b
    all_goals
      (first
        | cases ha rfl
        | cases hb rfl
        | (simp [profile, profile', ballots, ballots', prefers_iff_prefersInList, prefersInList] <;> decide))
  · intro a v
    constructor
    · fin_cases a <;> fin_cases v <;>
        simp [profile, profile', ballots, ballots', prefers_iff_prefersInList, prefersInList] <;>
        decide
    · fin_cases a <;> fin_cases v <;>
        simp [profile, profile', ballots, ballots', prefers_iff_prefersInList, prefersInList] <;>
        decide

theorem nanson_not_monotonicity : ¬ Monotonicity nanson := by
  intro hmono
  have hx : (2 : Fin 4) ∈ nanson profile := by
    simp [nanson_profile]
  have hlift : simpleLift profile' profile (2 : Fin 4) := simpleLift_profile
  have hx' : (2 : Fin 4) ∈ nanson profile' := hmono profile profile' 2 hx hlift
  have hnot : (2 : Fin 4) ∉ nanson profile' := by
    simp [nanson_profile']
  exact hnot hx'

end NansonMonotonicityCounterexample

end SocialChoice
