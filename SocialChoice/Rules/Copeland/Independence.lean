import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Clones
import SocialChoice.Axioms.Independence
import SocialChoice.ListBallot
import SocialChoice.Rules.Copeland.Defs

namespace SocialChoice

open Finset

/-!
## Copeland fails independence of dominated

Counterexample with 3 candidates (0,1,2) and 2 voters:
v0: 1 > 2 > 0
v1: 2 > 0 > 1
Candidate 2 Pareto-dominates 0.
Copeland selects {2}, but after removing 0, Copeland selects {1,2}.
-/

namespace CopelandIndependenceCounterexample

abbrev A3 := Fin 3
abbrev a : A3 := 0
abbrev b : A3 := 1
abbrev c : A3 := 2

def ballot120 : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballot201 : ListBallot 3 := ListBallot.mk' [2, 0, 1]

def ballots : Fin 2 → ListBallot 3
  | ⟨0, _⟩ => ballot120
  | ⟨1, _⟩ => ballot201

noncomputable def profile : Profile (Fin 2) A3 :=
  profileOfListBallots ballots

lemma prefers_2_0 : ∀ v : Fin 2, Prefers profile v c a := by
  simp only [profile, prefers_iff_prefersInList]; decide

noncomputable def profile' : Profile (Fin 2) {x : A3 // x ≠ a} :=
  restrictProfile profile a

def cand1 : {x : A3 // x ≠ a} := ⟨b, by decide⟩
def cand2 : {x : A3 // x ≠ a} := ⟨c, by decide⟩

lemma margin_profile_b_c : margin profile b c = 0 := by
  rw [profile, margin_profileOfListBallots]; decide

lemma margin_profile_b_a : margin profile b a = 0 := by
  rw [profile, margin_profileOfListBallots]; decide

lemma margin_profile_c_a : margin profile c a = 2 := by
  rw [profile, margin_profileOfListBallots]; decide

lemma margin_profile_c_b : margin profile c b = 0 := by
  rw [profile, margin_profileOfListBallots]; decide

lemma margin_profile_a_b : margin profile a b = 0 := by
  rw [profile, margin_profileOfListBallots]; decide

lemma margin_profile_a_c : margin profile a c = -2 := by
  rw [profile, margin_profileOfListBallots]; decide

lemma copelandScore2_profile_a : copelandScore2 profile a = 2 := by
  simp [copelandScore2, Fin.sum_univ_three, self_margin_zero, margin_profile_a_b,
    margin_profile_a_c, copelandPairScore2]

lemma copelandScore2_profile_b : copelandScore2 profile b = 3 := by
  simp [copelandScore2, Fin.sum_univ_three, self_margin_zero, margin_profile_b_a,
    margin_profile_b_c, copelandPairScore2]

lemma copelandScore2_profile_c : copelandScore2 profile c = 4 := by
  simp [copelandScore2, Fin.sum_univ_three, self_margin_zero, margin_profile_c_a,
    margin_profile_c_b, copelandPairScore2]

lemma copelandMaxScore2_profile : copelandMaxScore2 (P := profile) = 4 := by
  classical
  let scores : Finset Int := Finset.univ.image (fun x => copelandScore2 profile x)
  have hA : (Finset.univ : Finset A3).Nonempty := by simp
  have hScores : scores.Nonempty := hA.image (fun x => copelandScore2 profile x)
  have hmem : (4 : Int) ∈ scores := by
    refine Finset.mem_image.mpr ?_
    exact ⟨c, by simp, copelandScore2_profile_c⟩
  have hle : ∀ b, b ∈ scores → b ≤ (4 : Int) := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨x, _hx, rfl⟩
    fin_cases x <;> simp [copelandScore2_profile_a, copelandScore2_profile_b,
      copelandScore2_profile_c]
  have hmax :
      Finset.max' scores hScores = (4 : Int) :=
    (Finset.max'_eq_iff (s := scores) (H := hScores) (a := 4)).2 ⟨hmem, hle⟩
  simp [copelandMaxScore2, hA, scores, hmax]

lemma copeland_profile : copeland profile = ({c} : Finset A3) := by
  classical
  have hA : Nonempty A3 := ⟨a⟩
  have hmax : copelandMaxScore2 (P := profile) = 4 := copelandMaxScore2_profile
  apply Finset.ext
  intro x
  fin_cases x <;>
    simp [copeland, hA, hmax, copelandScore2_profile_a, copelandScore2_profile_b,
      copelandScore2_profile_c, c]

lemma margin_profile'_cand1_cand2 : margin profile' cand1 cand2 = 0 := by
  rw [profile', ← margin_eq_margin_restrictProfile]
  exact margin_profile_b_c

lemma margin_profile'_cand2_cand1 : margin profile' cand2 cand1 = 0 := by
  have h := margin_antisymmetric (P := profile') cand2 cand1
  simpa [margin_profile'_cand1_cand2] using h

lemma univ_profile'_eq : (Finset.univ : Finset {x : A3 // x ≠ a}) = {cand1, cand2} := by
  classical
  ext x
  constructor
  · intro _
    rcases x with ⟨x, hxne⟩
    fin_cases x
    · cases hxne rfl
    · simp [cand1, cand2]
    · simp [cand1, cand2]
  · intro hx
    simp at hx
    simp

lemma copelandScore2_profile'_cand1 : copelandScore2 profile' cand1 = 2 := by
  classical
  have hne : cand1 ≠ cand2 := by
    intro h
    have : (b : A3) = c := congrArg Subtype.val h
    cases this
  calc
    copelandScore2 profile' cand1 =
        (∑ x ∈ ({cand1, cand2} : Finset {x : A3 // x ≠ a}),
          copelandPairScore2 (margin profile' cand1 x)) := by
          simp [copelandScore2, univ_profile'_eq]
    _ = copelandPairScore2 (margin profile' cand1 cand1) +
          (∑ x ∈ ({cand2} : Finset {x : A3 // x ≠ a}),
            copelandPairScore2 (margin profile' cand1 x)) := by
          simp [Finset.sum_insert, hne]
    _ = copelandPairScore2 (margin profile' cand1 cand1) +
          copelandPairScore2 (margin profile' cand1 cand2) := by
          simp
    _ = 2 := by
          simp [copelandPairScore2, self_margin_zero, margin_profile'_cand1_cand2]

lemma copelandScore2_profile'_cand2 : copelandScore2 profile' cand2 = 2 := by
  classical
  have hne : cand2 ≠ cand1 := by
    intro h
    have : (c : A3) = b := congrArg Subtype.val h
    cases this
  calc
    copelandScore2 profile' cand2 =
        (∑ x ∈ ({cand1, cand2} : Finset {x : A3 // x ≠ a}),
          copelandPairScore2 (margin profile' cand2 x)) := by
          simp [copelandScore2, univ_profile'_eq]
    _ = copelandPairScore2 (margin profile' cand2 cand1) +
          copelandPairScore2 (margin profile' cand2 cand2) := by
          have hne' : cand1 ≠ cand2 := by
            intro h
            have : (b : A3) = c := congrArg Subtype.val h
            cases this
          simp [Finset.sum_insert, hne', Finset.sum_singleton]
    _ = 2 := by
          simp [copelandPairScore2, self_margin_zero, margin_profile'_cand2_cand1]

lemma copelandMaxScore2_profile' : copelandMaxScore2 (P := profile') = 2 := by
  classical
  let scores : Finset Int := Finset.univ.image (fun x => copelandScore2 profile' x)
  have hA : (Finset.univ : Finset {x : A3 // x ≠ a}).Nonempty := by
    refine ⟨cand1, by simp⟩
  have hScores : scores.Nonempty := hA.image (fun x => copelandScore2 profile' x)
  have hmem : (2 : Int) ∈ scores := by
    refine Finset.mem_image.mpr ?_
    exact ⟨cand1, by simp, copelandScore2_profile'_cand1⟩
  have hle : ∀ b, b ∈ scores → b ≤ (2 : Int) := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨x, _hx, rfl⟩
    rcases x with ⟨x, hxne⟩
    fin_cases x
    · cases hxne rfl
    ·
      have hx' : (⟨b, hxne⟩ : {x : A3 // x ≠ a}) = cand1 := by
        apply Subtype.ext
        rfl
      simp [hx', copelandScore2_profile'_cand1]
    ·
      have hx' : (⟨c, hxne⟩ : {x : A3 // x ≠ a}) = cand2 := by
        apply Subtype.ext
        rfl
      simp [hx', copelandScore2_profile'_cand2]
  have hmax :
      Finset.max' scores hScores = (2 : Int) :=
    (Finset.max'_eq_iff (s := scores) (H := hScores) (a := 2)).2 ⟨hmem, hle⟩
  simp [copelandMaxScore2, hA, scores, hmax]

lemma copeland_profile' :
    copeland profile' = (Finset.univ : Finset {x : A3 // x ≠ a}) := by
  classical
  have hA : Nonempty {x : A3 // x ≠ a} := ⟨cand1⟩
  have hmax : copelandMaxScore2 (P := profile') = 2 := copelandMaxScore2_profile'
  apply Finset.ext
  intro x
  rcases x with ⟨x, hxne⟩
  fin_cases x
  · cases hxne rfl
  ·
    have hx' : (⟨b, hxne⟩ : {x : A3 // x ≠ a}) = cand1 := by
      apply Subtype.ext
      rfl
    simp [copeland, hA, hmax, hx', copelandScore2_profile'_cand1]
  ·
    have hx' : (⟨c, hxne⟩ : {x : A3 // x ≠ a}) = cand2 := by
      apply Subtype.ext
      rfl
    simp [copeland, hA, hmax, hx', copelandScore2_profile'_cand2]

lemma copeland_profile'_has_1 : cand1 ∈ copeland profile' := by
  simp [copeland_profile']

lemma copeland_profile_not_1 : (b : A3) ∉ copeland profile := by
  simp [copeland_profile, b, c]

lemma lift_copeland_profile'_has_1 : (b : A3) ∈ liftWinners (copeland profile') := by
  have h : cand1 ∈ copeland profile' := copeland_profile'_has_1
  simpa [liftWinners, cand1] using h

end CopelandIndependenceCounterexample

open CopelandIndependenceCounterexample

theorem copeland_not_independenceOfDominated : ¬ IndependenceOfDominated copeland := by
  intro hind
  have hpref : ∀ v : Fin 2, Prefers profile v c a :=
    prefers_2_0
  have hEq := hind (P := profile) (c := c) (d := a) hpref
  have hmem :
      (b : A3) ∈
        liftWinners (copeland (restrictCandidates profile (fun x => x ≠ a))) := by
    simpa [profile', restrictProfile] using lift_copeland_profile'_has_1
  have hmem' : (b : A3) ∈ copeland profile := by
    simpa [hEq] using hmem
  exact (copeland_profile_not_1 hmem').elim

namespace CopelandClonesCounterexample

abbrev A3 := Fin 3
abbrev a : A3 := 0
abbrev b : A3 := 1
abbrev c : A3 := 2

def ballot021 : ListBallot 3 := ListBallot.mk' [0, 2, 1]
def ballot120 : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballot201 : ListBallot 3 := ListBallot.mk' [2, 0, 1]

def ballots : Fin 4 → ListBallot 3
  | ⟨0, _⟩ => ballot021
  | ⟨1, _⟩ => ballot120
  | ⟨2, _⟩ => ballot120
  | ⟨3, _⟩ => ballot201

noncomputable def profile : Profile (Fin 4) A3 :=
  profileOfListBallots ballots

def cloneSet : Set A3 := {a, c}

lemma cloneSet_profile : CloneSet profile cloneSet := by
  refine ⟨⟨0, by simp [cloneSet]⟩, ?_⟩
  simp only [cloneSet, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
    profile, prefers_iff_prefersInList]
  decide

lemma margin_profile_a_b : margin profile a b = 0 := by
  rw [profile, margin_profileOfListBallots]; decide

lemma margin_profile_b_a : margin profile b a = 0 := by
  rw [profile, margin_profileOfListBallots]; decide

lemma margin_profile_b_c : margin profile b c = 0 := by
  rw [profile, margin_profileOfListBallots]; decide

lemma margin_profile_c_b : margin profile c b = 0 := by
  rw [profile, margin_profileOfListBallots]; decide

lemma margin_profile_c_a : margin profile c a = 2 := by
  rw [profile, margin_profileOfListBallots]; decide

lemma margin_profile_a_c : margin profile a c = -2 := by
  rw [profile, margin_profileOfListBallots]; decide

lemma copelandScore2_profile_a : copelandScore2 profile a = 2 := by
  simp [copelandScore2, Fin.sum_univ_three, self_margin_zero, margin_profile_a_b,
    margin_profile_a_c, copelandPairScore2]

lemma copelandScore2_profile_b : copelandScore2 profile b = 3 := by
  simp [copelandScore2, Fin.sum_univ_three, self_margin_zero, margin_profile_b_a,
    margin_profile_b_c, copelandPairScore2]

lemma copelandScore2_profile_c : copelandScore2 profile c = 4 := by
  simp [copelandScore2, Fin.sum_univ_three, self_margin_zero, margin_profile_c_a,
    margin_profile_c_b, copelandPairScore2]

lemma copelandMaxScore2_profile : copelandMaxScore2 (P := profile) = 4 := by
  classical
  let scores : Finset Int := Finset.univ.image (fun x => copelandScore2 profile x)
  have hA : (Finset.univ : Finset A3).Nonempty := by simp
  have hScores : scores.Nonempty := hA.image (fun x => copelandScore2 profile x)
  have hmem : (4 : Int) ∈ scores := by
    refine Finset.mem_image.mpr ?_
    exact ⟨c, by simp, copelandScore2_profile_c⟩
  have hle : ∀ b, b ∈ scores → b ≤ (4 : Int) := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨x, _hx, rfl⟩
    fin_cases x <;> simp [copelandScore2_profile_a, copelandScore2_profile_b,
      copelandScore2_profile_c]
  have hmax :
      Finset.max' scores hScores = (4 : Int) :=
    (Finset.max'_eq_iff (s := scores) (H := hScores) (a := 4)).2 ⟨hmem, hle⟩
  simp [copelandMaxScore2, hA, scores, hmax]

lemma copeland_profile : copeland profile = ({c} : Finset A3) := by
  classical
  have hA : Nonempty A3 := ⟨a⟩
  have hmax : copelandMaxScore2 (P := profile) = 4 := copelandMaxScore2_profile
  apply Finset.ext
  intro x
  fin_cases x <;>
    simp [copeland, hA, hmax, copelandScore2_profile_a, copelandScore2_profile_b,
      copelandScore2_profile_c, c]

lemma copeland_profile_not_b : (b : A3) ∉ copeland profile := by
  simp [copeland_profile, b, c]

noncomputable def profile' :
    Profile (Fin 4) {x : A3 // clonePred cloneSet c x} :=
  removeClonesExcept profile cloneSet c

def cand1 : {x : A3 // clonePred cloneSet c x} :=
  ⟨b, Or.inl (by simp [cloneSet, a, b, c])⟩

def cand2 : {x : A3 // clonePred cloneSet c x} :=
  ⟨c, Or.inr rfl⟩

lemma margin_profile'_cand1_cand2 : margin profile' cand1 cand2 = 0 := by
  rw [profile', removeClonesExcept, ← margin_eq_margin_restrictCandidates]
  exact margin_profile_b_c

lemma margin_profile'_cand2_cand1 : margin profile' cand2 cand1 = 0 := by
  have h := margin_antisymmetric (P := profile') cand2 cand1
  simpa [margin_profile'_cand1_cand2] using h

lemma univ_profile'_eq :
    (Finset.univ : Finset {x : A3 // clonePred cloneSet c x}) = {cand1, cand2} := by
  classical
  ext x
  constructor
  · intro _
    rcases x with ⟨x, hx⟩
    fin_cases x
    · have hfalse : ¬ clonePred cloneSet c (0 : A3) := by
        simp [clonePred, cloneSet, a, c]
      have : False := (hfalse hx)
      exact this.elim
    · simp [cand1, cand2]
    · simp [cand1, cand2]
  · intro hx
    simp at hx
    simp

lemma copelandScore2_profile'_cand1 : copelandScore2 profile' cand1 = 2 := by
  classical
  have hne : cand1 ≠ cand2 := by
    intro h
    have : (b : A3) = c := congrArg Subtype.val h
    cases this
  calc
    copelandScore2 profile' cand1 =
        (∑ x ∈ ({cand1, cand2} : Finset {x : A3 // clonePred cloneSet c x}),
          copelandPairScore2 (margin profile' cand1 x)) := by
          simp [copelandScore2, univ_profile'_eq]
    _ = copelandPairScore2 (margin profile' cand1 cand1) +
          (∑ x ∈ ({cand2} : Finset {x : A3 // clonePred cloneSet c x}),
            copelandPairScore2 (margin profile' cand1 x)) := by
          simp [Finset.sum_insert, hne]
    _ = copelandPairScore2 (margin profile' cand1 cand1) +
          copelandPairScore2 (margin profile' cand1 cand2) := by
          simp
    _ = 2 := by
          simp [copelandPairScore2, self_margin_zero, margin_profile'_cand1_cand2]

lemma copelandScore2_profile'_cand2 : copelandScore2 profile' cand2 = 2 := by
  classical
  have hne : cand2 ≠ cand1 := by
    intro h
    have : (c : A3) = b := congrArg Subtype.val h
    cases this
  calc
    copelandScore2 profile' cand2 =
        (∑ x ∈ ({cand1, cand2} : Finset {x : A3 // clonePred cloneSet c x}),
          copelandPairScore2 (margin profile' cand2 x)) := by
          simp [copelandScore2, univ_profile'_eq]
    _ = copelandPairScore2 (margin profile' cand2 cand1) +
          copelandPairScore2 (margin profile' cand2 cand2) := by
          have hne' : cand1 ≠ cand2 := by
            intro h
            have : (b : A3) = c := congrArg Subtype.val h
            cases this
          simp [Finset.sum_insert, hne', Finset.sum_singleton]
    _ = 2 := by
          simp [copelandPairScore2, self_margin_zero, margin_profile'_cand2_cand1]

lemma copelandMaxScore2_profile' : copelandMaxScore2 (P := profile') = 2 := by
  classical
  let scores : Finset Int := Finset.univ.image (fun x => copelandScore2 profile' x)
  have hA : (Finset.univ : Finset {x : A3 // clonePred cloneSet c x}).Nonempty := by
    refine ⟨cand1, by simp⟩
  have hScores : scores.Nonempty := hA.image (fun x => copelandScore2 profile' x)
  have hmem : (2 : Int) ∈ scores := by
    refine Finset.mem_image.mpr ?_
    exact ⟨cand1, by simp, copelandScore2_profile'_cand1⟩
  have hle : ∀ b, b ∈ scores → b ≤ (2 : Int) := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨x, _hx, rfl⟩
    rcases x with ⟨x, hx⟩
    fin_cases x
    · have hfalse : ¬ clonePred cloneSet c (0 : A3) := by
        simp [clonePred, cloneSet, a, c]
      have : False := (hfalse hx)
      exact this.elim
    ·
      have hx' : (⟨b, hx⟩ : {x : A3 // clonePred cloneSet c x}) = cand1 := by
        apply Subtype.ext
        rfl
      simp [hx', copelandScore2_profile'_cand1]
    ·
      have hx' : (⟨c, hx⟩ : {x : A3 // clonePred cloneSet c x}) = cand2 := by
        apply Subtype.ext
        rfl
      simp [hx', copelandScore2_profile'_cand2]
  have hmax :
      Finset.max' scores hScores = (2 : Int) :=
    (Finset.max'_eq_iff (s := scores) (H := hScores) (a := 2)).2 ⟨hmem, hle⟩
  simp [copelandMaxScore2, hA, scores, hmax]

lemma copeland_profile' :
    copeland profile' = (Finset.univ : Finset {x : A3 // clonePred cloneSet c x}) := by
  classical
  have hA : Nonempty {x : A3 // clonePred cloneSet c x} := ⟨cand1⟩
  have hmax : copelandMaxScore2 (P := profile') = 2 := copelandMaxScore2_profile'
  apply Finset.ext
  intro x
  rcases x with ⟨x, hx⟩
  fin_cases x
  · have hfalse : ¬ clonePred cloneSet c (0 : A3) := by
      simp [clonePred, cloneSet, a, c]
    have : False := (hfalse hx)
    exact this.elim
  ·
    have hx' : (⟨b, hx⟩ : {x : A3 // clonePred cloneSet c x}) = cand1 := by
      apply Subtype.ext
      rfl
    simp [copeland, hA, hmax, hx', copelandScore2_profile'_cand1]
  ·
    have hx' : (⟨c, hx⟩ : {x : A3 // clonePred cloneSet c x}) = cand2 := by
      apply Subtype.ext
      rfl
    simp [copeland, hA, hmax, hx', copelandScore2_profile'_cand2]

lemma copeland_profile'_has_b : cand1 ∈ copeland profile' := by
  simp [copeland_profile']

end CopelandClonesCounterexample

theorem copeland_not_independenceOfClones : ¬ IndependenceOfClones copeland := by
  intro hind
  have hclone :
      CloneSet CopelandClonesCounterexample.profile
        CopelandClonesCounterexample.cloneSet :=
    CopelandClonesCounterexample.cloneSet_profile
  have hx : (CopelandClonesCounterexample.c : CopelandClonesCounterexample.A3) ∈
      CopelandClonesCounterexample.cloneSet := by
    simp [CopelandClonesCounterexample.cloneSet]
  have h := hind (P := CopelandClonesCounterexample.profile)
    (X := CopelandClonesCounterexample.cloneSet)
    (x := CopelandClonesCounterexample.c) hclone hx
  have hc :
      (CopelandClonesCounterexample.b : CopelandClonesCounterexample.A3) ∉
        CopelandClonesCounterexample.cloneSet := by
    intro hmem
    have hmem' :
        (CopelandClonesCounterexample.b : CopelandClonesCounterexample.A3) =
          CopelandClonesCounterexample.a ∨
        (CopelandClonesCounterexample.b : CopelandClonesCounterexample.A3) =
          CopelandClonesCounterexample.c := by
      simpa [CopelandClonesCounterexample.cloneSet] using hmem
    cases hmem' with
    | inl h => cases h
    | inr h => cases h
  have hnonclone := h.1 (CopelandClonesCounterexample.b) hc
  have hb_left :
      (⟨CopelandClonesCounterexample.b, Or.inl hc⟩ :
        {x : CopelandClonesCounterexample.A3 //
          clonePred CopelandClonesCounterexample.cloneSet
            CopelandClonesCounterexample.c x}) ∈
          copeland (removeClonesExcept CopelandClonesCounterexample.profile
            CopelandClonesCounterexample.cloneSet CopelandClonesCounterexample.c) := by
    simpa [CopelandClonesCounterexample.profile',
      CopelandClonesCounterexample.cand1] using
        CopelandClonesCounterexample.copeland_profile'_has_b
  have hb_right :
      (CopelandClonesCounterexample.b : CopelandClonesCounterexample.A3) ∈
        copeland CopelandClonesCounterexample.profile :=
    (hnonclone).2 hb_left
  exact (CopelandClonesCounterexample.copeland_profile_not_b hb_right).elim

end SocialChoice
