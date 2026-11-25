import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Independence
import SocialChoice.ListBallot
import SocialChoice.Rules.UncoveredSet.Defs

namespace SocialChoice

open Finset

/-!
# Uncovered Set fails independence of dominated alternatives

Counterexample with 4 candidates and 4 voters:

Full profile (4 voters):
2 voters: 2 > 1 > 3 > 0
1 voter : 3 > 0 > 2 > 1
1 voter : 3 > 1 > 0 > 2

Candidate 0 is Pareto-dominated by 3. uncoveredSet selects {1,2,3}.
Removing 0 yields winners {2,3}, so 1 drops out.
-/

namespace UncoveredSetIndependenceCounterexample

abbrev A4 := Fin 4
abbrev a : A4 := 0
abbrev b : A4 := 1
abbrev c : A4 := 2
abbrev d : A4 := 3

def ballot2130 : ListBallot 4 := ListBallot.mk' [2, 1, 3, 0]
def ballot3021 : ListBallot 4 := ListBallot.mk' [3, 0, 2, 1]
def ballot3102 : ListBallot 4 := ListBallot.mk' [3, 1, 0, 2]

def ballots : Fin 4 → ListBallot 4
  | ⟨0, _⟩ => ballot2130
  | ⟨1, _⟩ => ballot2130
  | ⟨2, _⟩ => ballot3021
  | ⟨3, _⟩ => ballot3102

noncomputable def profile : Profile (Fin 4) A4 :=
  profileOfListBallots ballots

noncomputable def profile' : Profile (Fin 4) {x : A4 // x ≠ a} :=
  restrictProfile profile a

abbrev cand1 : {x : A4 // x ≠ a} := ⟨b, by decide⟩
abbrev cand2 : {x : A4 // x ≠ a} := ⟨c, by decide⟩
abbrev cand3 : {x : A4 // x ≠ a} := ⟨d, by decide⟩

lemma prefers_3_0 : ∀ v : Fin 4, Prefers profile v d a := by
  simp only [profile, prefers_iff_prefersInList]
  decide

private lemma margin_pos_profile_1_0 : margin_pos profile (1 : A4) (0 : A4) := by
  rw [margin_pos, profile, margin_profileOfListBallots]; decide

private lemma not_margin_pos_profile_2_0 : ¬ margin_pos profile (2 : A4) (0 : A4) := by
  rw [margin_pos, profile, margin_profileOfListBallots]; decide

private lemma not_margin_pos_profile_0_1 : ¬ margin_pos profile (0 : A4) (1 : A4) := by
  rw [margin_pos, profile, margin_profileOfListBallots]; decide

private lemma not_margin_pos_profile_3_1 : ¬ margin_pos profile (3 : A4) (1 : A4) := by
  rw [margin_pos, profile, margin_profileOfListBallots]; decide

private lemma not_covers_profile_2_1 : ¬ covers profile (2 : A4) (1 : A4) := by
  intro hcov
  have h := hcov.2.1 (0 : A4) margin_pos_profile_1_0
  exact not_margin_pos_profile_2_0 h

private lemma not_covers_profile_3_1 : ¬ covers profile (3 : A4) (1 : A4) := by
  intro hcov
  exact not_margin_pos_profile_3_1 hcov.1

private lemma not_covers_profile_0_1 : ¬ covers profile (0 : A4) (1 : A4) := by
  intro hcov
  exact not_margin_pos_profile_0_1 hcov.1

private lemma uncovered_profile_1 : uncovered profile (1 : A4) := by
  intro y hy
  fin_cases y
  · exact not_covers_profile_0_1
  · cases hy rfl
  · exact not_covers_profile_2_1
  · exact not_covers_profile_3_1

lemma uncoveredSet_profile_has_1 : (1 : A4) ∈ uncoveredSet profile := by
  classical
  refine Finset.mem_filter.mpr ?_
  exact ⟨by simp, uncovered_profile_1⟩

private lemma margin_pos_profile'_2_1 : margin_pos profile' cand2 cand1 := by
  rw [margin_pos, profile', ← margin_eq_margin_restrictProfile, profile,
    margin_profileOfListBallots]
  decide

private lemma not_margin_pos_profile'_1_2 : ¬ margin_pos profile' cand1 cand2 := by
  rw [margin_pos, profile', ← margin_eq_margin_restrictProfile, profile,
    margin_profileOfListBallots]
  decide

private lemma not_margin_pos_profile'_1_3 : ¬ margin_pos profile' cand1 cand3 := by
  rw [margin_pos, profile', ← margin_eq_margin_restrictProfile, profile,
    margin_profileOfListBallots]
  decide

private lemma not_margin_pos_profile'_3_2 : ¬ margin_pos profile' cand3 cand2 := by
  rw [margin_pos, profile', ← margin_eq_margin_restrictProfile, profile,
    margin_profileOfListBallots]
  decide

private lemma covers_profile'_2_1 : covers profile' cand2 cand1 := by
  refine ⟨margin_pos_profile'_2_1, ?_, ?_⟩
  · intro z hz
    cases z with
    | mk z hz0 =>
        fin_cases z
        · cases hz0 rfl
        ·
          have hz' : margin_pos profile' cand1 cand1 := by
            simpa [cand1] using hz
          exact (margin_pos_irrefl (P := profile') (x := cand1) hz').elim
        · exact (not_margin_pos_profile'_1_2 (by simpa [cand1, cand2] using hz)).elim
        · exact (not_margin_pos_profile'_1_3 (by simpa [cand1, cand3] using hz)).elim
  · intro z hz
    cases z with
    | mk z hz0 =>
        fin_cases z
        · cases hz0 rfl
        · exact (not_margin_pos_profile'_1_2 (by simpa [cand1, cand2] using hz)).elim
        ·
          have hz' : margin_pos profile' cand2 cand2 := by
            simpa [cand2] using hz
          exact (margin_pos_irrefl (P := profile') (x := cand2) hz').elim
        · exact (not_margin_pos_profile'_3_2 (by simpa [cand3, cand2] using hz)).elim

private lemma cand1_not_in_uncovered_profile' : cand1 ∉ uncoveredSet profile' := by
  classical
  intro hmem
  have huncov : uncovered profile' cand1 := (Finset.mem_filter.mp hmem).2
  have hcov : covers profile' cand2 cand1 := covers_profile'_2_1
  exact (huncov cand2 (by decide) hcov).elim

lemma mem_liftWinners_iff {A : Type} [DecidableEq A] {p : A → Prop} [DecidablePred p]
    {s : Finset {a : A // p a}} {x : A} (hx : p x) :
    x ∈ liftWinners s ↔ (⟨x, hx⟩ : {a : A // p a}) ∈ s := by
  classical
  simp [liftWinners, Finset.mem_image, hx]

lemma cand1_not_in_liftWinners_profile' : (b : A4) ∉ liftWinners (uncoveredSet profile') := by
  intro hmem
  have hmem' :
      (cand1 : {x : A4 // x ≠ a}) ∈ uncoveredSet profile' :=
    (mem_liftWinners_iff (p := fun x => x ≠ a) (s := uncoveredSet profile') (x := b)
      (by decide)).1 hmem
  exact (cand1_not_in_uncovered_profile' hmem').elim

end UncoveredSetIndependenceCounterexample

open UncoveredSetIndependenceCounterexample

theorem uncoveredSet_not_independenceOfDominated : ¬ IndependenceOfDominated uncoveredSet := by
  intro hind
  have hpref : ∀ v : Fin 4, Prefers profile v d a := prefers_3_0
  have hEq := hind (P := profile) (c := d) (d := a) hpref
  have hmem_full : (b : A4) ∈ uncoveredSet profile := uncoveredSet_profile_has_1
  have hmem_restrict :
      (b : A4) ∈ liftWinners (uncoveredSet (restrictCandidates profile (fun x => x ≠ a))) := by
    simpa [hEq] using hmem_full
  have hmem_restrict' : (b : A4) ∈ liftWinners (uncoveredSet profile') := by
    simpa [profile', restrictProfile] using hmem_restrict
  exact cand1_not_in_liftWinners_profile' hmem_restrict'

end SocialChoice
