import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Independence
import SocialChoice.ListBallot
import SocialChoice.Rules.UncoveredSet.Defs

namespace SocialChoice

open Finset
open Classical
attribute [instance] Classical.decEq

set_option maxHeartbeats 5000000

/-!
# Uncovered Set fails independence of dominated alternatives

Counterexample with 4 candidates and 4 voters:

Full profile (4 voters):
2 voters: 2 > 1 > 3 > 0
1 voter : 3 > 0 > 2 > 1
1 voter : 3 > 1 > 0 > 2

Candidate 0 is Pareto-dominated by 3. UncoveredSet selects {1,2,3}.
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
  intro v
  change Prefers (profileOfListBallots ballots) v d a
  rw [prefers_iff_prefersInList]
  fin_cases v <;> decide

lemma margin_eq_card_diff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x y : A) :
    margin P x y =
      Int.ofNat (votersPreferring P x y).card -
        Int.ofNat (votersPreferring P y x).card := by
  classical
  simp [margin, votersPreferring]

private lemma votersPreferring_profile_eq_filter (x y : A4) :
    votersPreferring profile x y =
      Finset.univ.filter (fun v => prefersInList (ballots v).ranking x y) := by
  simpa [profile] using votersPreferring_eq_filter_prefersInList ballots x y

lemma votersPreferring_profile_1_0 :
    votersPreferring profile (1 : A4) (0 : A4) =
      ({0, 1, 3} : Finset (Fin 4)) := by
  classical
  rw [votersPreferring_profile_eq_filter]
  ext v
  fin_cases v <;> decide

lemma votersPreferring_profile_0_1 :
    votersPreferring profile (0 : A4) (1 : A4) =
      ({2} : Finset (Fin 4)) := by
  classical
  rw [votersPreferring_profile_eq_filter]
  ext v
  fin_cases v <;> decide

lemma votersPreferring_profile_2_0 :
    votersPreferring profile (2 : A4) (0 : A4) =
      ({0, 1} : Finset (Fin 4)) := by
  classical
  rw [votersPreferring_profile_eq_filter]
  ext v
  fin_cases v <;> decide

lemma votersPreferring_profile_0_2 :
    votersPreferring profile (0 : A4) (2 : A4) =
      ({2, 3} : Finset (Fin 4)) := by
  classical
  rw [votersPreferring_profile_eq_filter]
  ext v
  fin_cases v <;> decide

lemma votersPreferring_profile_2_1 :
    votersPreferring profile (2 : A4) (1 : A4) =
      ({0, 1, 2} : Finset (Fin 4)) := by
  classical
  rw [votersPreferring_profile_eq_filter]
  ext v
  fin_cases v <;> decide

lemma votersPreferring_profile_1_2 :
    votersPreferring profile (1 : A4) (2 : A4) =
      ({3} : Finset (Fin 4)) := by
  classical
  rw [votersPreferring_profile_eq_filter]
  ext v
  fin_cases v <;> decide

lemma votersPreferring_profile_3_1 :
    votersPreferring profile (3 : A4) (1 : A4) =
      ({2, 3} : Finset (Fin 4)) := by
  classical
  rw [votersPreferring_profile_eq_filter]
  ext v
  fin_cases v <;> decide

lemma votersPreferring_profile_1_3 :
    votersPreferring profile (1 : A4) (3 : A4) =
      ({0, 1} : Finset (Fin 4)) := by
  classical
  rw [votersPreferring_profile_eq_filter]
  ext v
  fin_cases v <;> decide

lemma votersPreferring_profile_3_2 :
    votersPreferring profile (3 : A4) (2 : A4) =
      ({2, 3} : Finset (Fin 4)) := by
  classical
  rw [votersPreferring_profile_eq_filter]
  ext v
  fin_cases v <;> decide

lemma votersPreferring_profile_2_3 :
    votersPreferring profile (2 : A4) (3 : A4) =
      ({0, 1} : Finset (Fin 4)) := by
  classical
  rw [votersPreferring_profile_eq_filter]
  ext v
  fin_cases v <;> decide

private lemma margin_profile_1_0 : margin profile (1 : A4) (0 : A4) = 2 := by
  classical
  simp [margin_eq_card_diff, votersPreferring_profile_1_0, votersPreferring_profile_0_1]

private lemma margin_profile_2_0 : margin profile (2 : A4) (0 : A4) = 0 := by
  classical
  simp [margin_eq_card_diff, votersPreferring_profile_2_0, votersPreferring_profile_0_2]

private lemma margin_profile_0_1 : margin profile (0 : A4) (1 : A4) = -2 := by
  classical
  simp [margin_eq_card_diff, votersPreferring_profile_0_1, votersPreferring_profile_1_0]

private lemma margin_profile_3_1 : margin profile (3 : A4) (1 : A4) = 0 := by
  classical
  simp [margin_eq_card_diff, votersPreferring_profile_3_1, votersPreferring_profile_1_3]

private lemma margin_profile_2_1 : margin profile (2 : A4) (1 : A4) = 2 := by
  classical
  simp [margin_eq_card_diff, votersPreferring_profile_2_1, votersPreferring_profile_1_2]

private lemma margin_profile_1_2 : margin profile (1 : A4) (2 : A4) = -2 := by
  classical
  simp [margin_eq_card_diff, votersPreferring_profile_1_2, votersPreferring_profile_2_1]

private lemma margin_profile_1_3 : margin profile (1 : A4) (3 : A4) = 0 := by
  classical
  simp [margin_eq_card_diff, votersPreferring_profile_1_3, votersPreferring_profile_3_1]

private lemma margin_profile_3_2 : margin profile (3 : A4) (2 : A4) = 0 := by
  classical
  simp [margin_eq_card_diff, votersPreferring_profile_3_2, votersPreferring_profile_2_3]

private lemma margin_pos_profile_1_0 : margin_pos profile (1 : A4) (0 : A4) := by
  simp [margin_pos, margin_profile_1_0]

private lemma not_margin_pos_profile_2_0 : ¬ margin_pos profile (2 : A4) (0 : A4) := by
  simp [margin_pos, margin_profile_2_0]

private lemma not_margin_pos_profile_0_1 : ¬ margin_pos profile (0 : A4) (1 : A4) := by
  simp [margin_pos, margin_profile_0_1]

private lemma not_margin_pos_profile_3_1 : ¬ margin_pos profile (3 : A4) (1 : A4) := by
  simp [margin_pos, margin_profile_3_1]

private lemma margin_pos_profile_2_1 : margin_pos profile (2 : A4) (1 : A4) := by
  simp [margin_pos, margin_profile_2_1]

private lemma not_margin_pos_profile_1_2 : ¬ margin_pos profile (1 : A4) (2 : A4) := by
  simp [margin_pos, margin_profile_1_2]

private lemma not_margin_pos_profile_1_3 : ¬ margin_pos profile (1 : A4) (3 : A4) := by
  simp [margin_pos, margin_profile_1_3]

private lemma not_margin_pos_profile_3_2 : ¬ margin_pos profile (3 : A4) (2 : A4) := by
  simp [margin_pos, margin_profile_3_2]

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

lemma uncoveredSet_profile_has_1 : (1 : A4) ∈ UncoveredSet profile := by
  classical
  refine Finset.mem_filter.mpr ?_
  exact ⟨by simp, uncovered_profile_1⟩

private lemma margin_pos_profile'_2_1 : margin_pos profile' cand2 cand1 := by
  have hmargin : margin profile cand2 cand1 = 2 := by
    simpa [cand1, cand2] using margin_profile_2_1
  have hEq :
      margin profile cand2 cand1 = margin profile' cand2 cand1 := by
    change margin profile cand2 cand1 = margin (restrictProfile profile a) cand2 cand1
    exact margin_eq_margin_restrictProfile
  have hmargin' : margin profile' cand2 cand1 = 2 := by
    calc
      margin profile' cand2 cand1 = margin profile cand2 cand1 := by
        simp [hEq]
      _ = 2 := hmargin
  simp [margin_pos, hmargin']

private lemma not_margin_pos_profile'_1_2 : ¬ margin_pos profile' cand1 cand2 := by
  have hmargin : margin profile cand1 cand2 = -2 := by
    simpa [cand1, cand2] using margin_profile_1_2
  have hEq :
      margin profile cand1 cand2 = margin profile' cand1 cand2 := by
    change margin profile cand1 cand2 = margin (restrictProfile profile a) cand1 cand2
    exact margin_eq_margin_restrictProfile
  have hmargin' : margin profile' cand1 cand2 = -2 := by
    calc
      margin profile' cand1 cand2 = margin profile cand1 cand2 := by
        simp [hEq]
      _ = -2 := hmargin
  simp [margin_pos, hmargin']

private lemma not_margin_pos_profile'_1_3 : ¬ margin_pos profile' cand1 cand3 := by
  have hmargin : margin profile cand1 cand3 = 0 := by
    simpa [cand1, cand3] using margin_profile_1_3
  have hEq :
      margin profile cand1 cand3 = margin profile' cand1 cand3 := by
    change margin profile cand1 cand3 = margin (restrictProfile profile a) cand1 cand3
    exact margin_eq_margin_restrictProfile
  have hmargin' : margin profile' cand1 cand3 = 0 := by
    calc
      margin profile' cand1 cand3 = margin profile cand1 cand3 := by
        simp [hEq]
      _ = 0 := hmargin
  simp [margin_pos, hmargin']

private lemma not_margin_pos_profile'_3_2 : ¬ margin_pos profile' cand3 cand2 := by
  have hmargin : margin profile cand3 cand2 = 0 := by
    simpa [cand2, cand3] using margin_profile_3_2
  have hEq :
      margin profile cand3 cand2 = margin profile' cand3 cand2 := by
    change margin profile cand3 cand2 = margin (restrictProfile profile a) cand3 cand2
    exact margin_eq_margin_restrictProfile
  have hmargin' : margin profile' cand3 cand2 = 0 := by
    calc
      margin profile' cand3 cand2 = margin profile cand3 cand2 := by
        simp [hEq]
      _ = 0 := hmargin
  simp [margin_pos, hmargin']

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

private lemma cand1_not_in_uncovered_profile' : cand1 ∉ UncoveredSet profile' := by
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

lemma cand1_not_in_liftWinners_profile' : (b : A4) ∉ liftWinners (UncoveredSet profile') := by
  intro hmem
  have hmem' :
      (cand1 : {x : A4 // x ≠ a}) ∈ UncoveredSet profile' :=
    (mem_liftWinners_iff (p := fun x => x ≠ a) (s := UncoveredSet profile') (x := b)
      (by decide)).1 hmem
  exact (cand1_not_in_uncovered_profile' hmem').elim

end UncoveredSetIndependenceCounterexample

open UncoveredSetIndependenceCounterexample

theorem uncoveredSet_not_independenceOfDominated : ¬ IndependenceOfDominated UncoveredSet := by
  intro hind
  have hpref : ∀ v : Fin 4, Prefers profile v d a := prefers_3_0
  have hEq := hind (P := profile) (c := d) (d := a) hpref
  have hmem_full : (b : A4) ∈ UncoveredSet profile := uncoveredSet_profile_has_1
  have hmem_restrict :
      (b : A4) ∈ liftWinners (UncoveredSet (restrictCandidates profile (fun x => x ≠ a))) := by
    simpa [hEq] using hmem_full
  have hmem_restrict' : (b : A4) ∈ liftWinners (UncoveredSet profile') := by
    simpa [profile', restrictProfile] using hmem_restrict
  exact cand1_not_in_liftWinners_profile' hmem_restrict'

end SocialChoice
