import SocialChoice.Axioms.Condorcet
import SocialChoice.Axioms.Participation
import SocialChoice.Examples
import Mathlib.Tactic

/-
This file contains a proof that no voting rule can satisfy
resoluteness, Condorcet consistency, and resolute participation
simultaneously. It works by analyzing several explicit profiles
with m=4 alternatvies and up to n=12 voters.

The proof follows the computer-aided proof of
Brandt et al. (2016), in the improved version presented
in Dominik Peters' 2019 DPhil thesis:
https://dominik-peters.de/publications/thesis.pdf#page=27
-/

namespace SocialChoice

open Finset

namespace CondorcetParticipation

-- Ballots used in the proof
def ballotABCD : ListBallot 4 := ListBallot.mk' [0, 1, 2, 3]
def ballotABDC : ListBallot 4 := ListBallot.mk' [0, 1, 3, 2]
def ballotBDCA : ListBallot 4 := ListBallot.mk' [1, 3, 2, 0]
def ballotCABD : ListBallot 4 := ListBallot.mk' [2, 0, 1, 3]
def ballotDCAB : ListBallot 4 := ListBallot.mk' [3, 2, 0, 1]
def ballotDCBA : ListBallot 4 := ListBallot.mk' [3, 2, 1, 0]

-- The master list of ballots for the maximum profiles (P1) and (P5)
def P1Ballots : Fin 12 → ListBallot 4
  | 0 => ballotABDC
  | 1 => ballotABDC
  | 2 => ballotBDCA
  | 3 => ballotBDCA
  | 4 => ballotBDCA
  | 5 => ballotCABD
  | 6 => ballotCABD
  | 7 => ballotCABD
  | 8 => ballotDCAB
  | 9 => ballotDCAB
  | 10 => ballotABCD
  | 11 => ballotABCD

-- The master list of ballots for the maximum profile (P1)
def P5Ballots : Fin 12 → ListBallot 4
  | 0 => ballotABDC
  | 1 => ballotABDC
  | 2 => ballotBDCA
  | 3 => ballotBDCA
  | 4 => ballotBDCA
  | 5 => ballotCABD
  | 6 => ballotCABD
  | 7 => ballotCABD
  | 8 => ballotDCAB
  | 9 => ballotDCAB
  | 10 => ballotDCBA
  | 11 => ballotDCBA

-- Sets of voters for different profiles
def V0 : Finset (Fin 12) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
def V1 : Finset (Fin 12) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}
def V2 : Finset (Fin 12) := {0, 1, 5, 6, 7, 8, 9, 10, 11}
def V3 : Finset (Fin 12) := {0, 1, 2, 3, 4, 5, 6, 7, 10, 11}
def V4 : Finset (Fin 12) := {0, 1, 2, 3, 4, 10, 11}
def V5 : Finset (Fin 12) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}
def V6 : Finset (Fin 12) := {0, 1, 2, 3, 4, 8, 9, 10, 11}
def V7 : Finset (Fin 12) := {2, 3, 4, 5, 6, 7, 8, 9, 10, 11}
def V8 : Finset (Fin 12) := {5, 6, 7, 8, 9, 10, 11}

-- Generic profile definition on a subset of voters, using P1Ballots
noncomputable def profileOnSubset (S : Finset (Fin 12)) :
    Profile (Electorate (Fin 12) S) (Fin 4) :=
  { pref := fun v => (P1Ballots v.1).toLinearOrder }

-- Generic profile definition on a subset of voters, using P5Ballots
noncomputable def profileOnSubsetP5 (S : Finset (Fin 12)) :
    Profile (Electorate (Fin 12) S) (Fin 4) :=
  { pref := fun v => (P5Ballots v.1).toLinearOrder }

-- Specific profiles
noncomputable def P0ProfileSub : Profile (Electorate (Fin 12) V0) (Fin 4) :=
  profileOnSubset V0

noncomputable def P1ProfileSub : Profile (Electorate (Fin 12) V1) (Fin 4) :=
  profileOnSubset V1

noncomputable def P2ProfileSub : Profile (Electorate (Fin 12) V2) (Fin 4) :=
  profileOnSubset V2

noncomputable def P3ProfileSub : Profile (Electorate (Fin 12) V3) (Fin 4) :=
  profileOnSubset V3

noncomputable def P4ProfileSub : Profile (Electorate (Fin 12) V4) (Fin 4) :=
  profileOnSubset V4

noncomputable def P0ProfileSubP5 : Profile (Electorate (Fin 12) V0) (Fin 4) :=
  profileOnSubsetP5 V0

noncomputable def P5ProfileSub : Profile (Electorate (Fin 12) V5) (Fin 4) :=
  profileOnSubsetP5 V5

noncomputable def P6ProfileSub : Profile (Electorate (Fin 12) V6) (Fin 4) :=
  profileOnSubsetP5 V6

noncomputable def P7ProfileSub : Profile (Electorate (Fin 12) V7) (Fin 4) :=
  profileOnSubsetP5 V7

noncomputable def P8ProfileSub : Profile (Electorate (Fin 12) V8) (Fin 4) :=
  profileOnSubsetP5 V8

-- Lemma for restrictElectorate equality for P5
lemma restrictElectorate_eq_profileOnSubsetP5 {S T : Finset (Fin 12)} (hST : S ⊆ T) :
    restrictElectorate (profileOnSubsetP5 T) S hST = profileOnSubsetP5 S := by
  simp [restrictElectorate, profileOnSubsetP5]

lemma P0_P5_coincide : P0ProfileSub = P0ProfileSubP5 := by
  apply Profile.ext
  rintro ⟨v, hv⟩
  change v ∈ V0 at hv
  fin_cases v <;> simp_all [P0ProfileSub, P0ProfileSubP5, profileOnSubset,
    profileOnSubsetP5, V0, P1Ballots, P5Ballots]
  all_goals
    exfalso
    revert hv
    native_decide

-- Lemma for restrictElectorate equality
lemma restrictElectorate_eq_profileOnSubset {S T : Finset (Fin 12)} (hST : S ⊆ T) :
    restrictElectorate (profileOnSubset T) S hST = profileOnSubset S := by
  simp [restrictElectorate, profileOnSubset]

-- UpperSet properties for the ballots

lemma ballotABCD_UpperSet_ab : UpperSet ballotABCD.toLinearOrder ({0, 1} : Finset (Fin 4)) := by
  intro x y hlt hy
  fin_cases x <;> fin_cases y <;> simp [ballotABCD, ListBallot.lt_iff_idxOf] at hlt <;> try contradiction
  all_goals { simp at *; try contradiction }

lemma ballotBDCA_UpperSet_not_a : UpperSet ballotBDCA.toLinearOrder ({1, 2, 3} : Finset (Fin 4)) := by
  intro x y hlt hy
  fin_cases x <;> fin_cases y <;> simp [ballotBDCA, ListBallot.lt_iff_idxOf] at hlt <;> try contradiction
  all_goals { simp at *; try contradiction }

lemma ballotDCAB_UpperSet_not_b : UpperSet ballotDCAB.toLinearOrder ({0, 2, 3} : Finset (Fin 4)) := by
  intro x y hlt hy
  fin_cases x <;> fin_cases y <;> simp [ballotDCAB, ListBallot.lt_iff_idxOf] at hlt <;> try contradiction
  all_goals { simp at *; try contradiction }

lemma ballotCABD_UpperSet_ca : UpperSet ballotCABD.toLinearOrder ({0, 2} : Finset (Fin 4)) := by
  intro x y hlt hy
  fin_cases x <;> fin_cases y <;> simp [ballotCABD, ListBallot.lt_iff_idxOf] at hlt <;> try contradiction
  all_goals { simp at *; try contradiction }

lemma ballotDCBA_UpperSet_dc : UpperSet ballotDCBA.toLinearOrder ({2, 3} : Finset (Fin 4)) := by
  intro x y hlt hy
  fin_cases x <;> fin_cases y <;> simp [ballotDCBA, ListBallot.lt_iff_idxOf] at hlt <;> try contradiction
  all_goals { simp at *; try contradiction }

lemma ballotCABD_UpperSet_not_d : UpperSet ballotCABD.toLinearOrder ({0, 1, 2} : Finset (Fin 4)) := by
  intro x y hlt hy
  fin_cases x <;> fin_cases y <;> simp [ballotCABD, ListBallot.lt_iff_idxOf] at hlt <;> try contradiction
  all_goals { simp at *; try contradiction }

lemma ballotABDC_UpperSet_not_c : UpperSet ballotABDC.toLinearOrder ({0, 1, 3} : Finset (Fin 4)) := by
  intro x y hlt hy
  fin_cases x <;> fin_cases y <;> simp [ballotABDC, ListBallot.lt_iff_idxOf] at hlt <;> try contradiction
  all_goals { simp at *; try contradiction }

lemma ballotBDCA_UpperSet_bd : UpperSet ballotBDCA.toLinearOrder ({1, 3} : Finset (Fin 4)) := by
  intro x y hlt hy
  fin_cases x <;> fin_cases y <;> simp [ballotBDCA, ListBallot.lt_iff_idxOf] at hlt <;> try contradiction
  all_goals { simp at *; try contradiction }

-- Proof steps using resoluteParticipation_superset

lemma P0_to_P1_preserve_ab {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) {x y : Fin 4}
    (hx : x ∈ ({0, 1} : Finset (Fin 4)))
    (hP0 : f P0ProfileSub = {x}) (hP1 : f P1ProfileSub = {y}) :
    y ∈ ({0, 1} : Finset (Fin 4)) := by
  let S : Finset (Fin 4) := {0, 1}
  have hsubset : f P1ProfileSub ⊆ S := by
    apply resoluteParticipation_superset hf hpart V0 V1 (by simp [V0, V1]) P1ProfileSub S x
    · erw [restrictElectorate_eq_profileOnSubset (hST := by simp [V0, V1])]
      exact hP0
    · exact hx
    · intro w hw
      simp [V0, V1] at hw
      fin_cases w <;> try contradiction
      all_goals {
        simp [P1ProfileSub, profileOnSubset, P1Ballots]
        exact ballotABCD_UpperSet_ab
      }
  have hy_mem : y ∈ f P1ProfileSub := by rw [hP1]; simp
  exact hsubset hy_mem

lemma P1_to_P2_preserve_a {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) {y : Fin 4}
    (hP1 : f P1ProfileSub = {0}) (hP2 : f P2ProfileSub = {y}) :
    y = 0 := by
  let S : Finset (Fin 4) := {1, 2, 3}
  by_contra hy
  have hyS : y ∈ S := by
    fin_cases y <;> simp [S] at *
  have hsubset : f P1ProfileSub ⊆ S := by
    apply resoluteParticipation_superset hf hpart V2 V1 (by simp [V2, V1]; intro x hx; simp_all) P1ProfileSub S y
    · erw [restrictElectorate_eq_profileOnSubset (hST := by simp [V2, V1]; intro x hx; simp_all)]
      exact hP2
    · exact hyS
    · intro w hw
      simp [V2, V1] at hw
      fin_cases w <;> try contradiction
      all_goals {
        simp [P1ProfileSub, profileOnSubset, P1Ballots]
        exact ballotBDCA_UpperSet_not_a
      }
  have h0_mem : (0 : Fin 4) ∈ f P1ProfileSub := by rw [hP1]; simp
  have h0S : (0 : Fin 4) ∈ S := hsubset h0_mem
  simp [S] at h0S

lemma P1_to_P3_preserve_b {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) {y : Fin 4}
    (hP1 : f P1ProfileSub = {1}) (hP3 : f P3ProfileSub = {y}) :
    y = 1 := by
  let S : Finset (Fin 4) := {0, 2, 3}
  by_contra hy
  have hyS : y ∈ S := by
    fin_cases y <;> simp [S] at *
  have hsubset : f P1ProfileSub ⊆ S := by
    apply resoluteParticipation_superset hf hpart V3 V1 (by simp [V3, V1]; intro x hx; simp_all) P1ProfileSub S y
    · erw [restrictElectorate_eq_profileOnSubset (hST := by simp [V3, V1]; intro x hx; simp_all)]
      exact hP3
    · exact hyS
    · intro w hw
      simp [V3, V1] at hw
      fin_cases w <;> try contradiction
      all_goals {
        simp [P1ProfileSub, profileOnSubset, P1Ballots]
        exact ballotDCAB_UpperSet_not_b
      }
  have h1_mem : (1 : Fin 4) ∈ f P1ProfileSub := by rw [hP1]; simp
  have h1S : (1 : Fin 4) ∈ S := hsubset h1_mem
  simp [S] at h1S

lemma P3_to_P4_preserve_bd {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) {y : Fin 4}
    (hP3 : f P3ProfileSub = {1}) (hP4 : f P4ProfileSub = {y}) :
    y ∈ ({1, 3} : Finset (Fin 4)) := by
  let S : Finset (Fin 4) := {0, 2}
  by_contra hy
  have hyS : y ∈ S := by
    by_contra hy_not_S
    simp [S] at hy_not_S
    have hy_in : y ∈ ({1, 3} : Finset (Fin 4)) := by
      fin_cases y <;> simp at *
    contradiction
  have hsubset : f P3ProfileSub ⊆ S := by
    apply resoluteParticipation_superset hf hpart V4 V3 (by simp [V3, V4]; intro x hx; simp_all) P3ProfileSub S y
    · erw [restrictElectorate_eq_profileOnSubset (hST := by simp [V3, V4]; intro x hx; simp_all)]
      exact hP4
    · exact hyS
    · intro w hw
      simp [V3, V4] at hw
      fin_cases w <;> try contradiction
      all_goals {
        simp [P3ProfileSub, profileOnSubset, P1Ballots]
        exact ballotCABD_UpperSet_ca
      }
  have h1_mem : (1 : Fin 4) ∈ f P3ProfileSub := by rw [hP3]; simp
  have h1S : (1 : Fin 4) ∈ S := hsubset h1_mem
  simp [S] at h1S

lemma P0_to_P5_preserve_cd {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) {x y : Fin 4}
    (hx : x ∈ ({2, 3} : Finset (Fin 4)))
    (hP0 : f P0ProfileSubP5 = {x}) (hP5 : f P5ProfileSub = {y}) :
    y ∈ ({2, 3} : Finset (Fin 4)) := by
  let S : Finset (Fin 4) := {2, 3}
  have hVW : V0 ⊆ V5 := by
    intro z hz
    simp [V0, V5] at hz ⊢
    tauto
  have hsubset : f P5ProfileSub ⊆ S := by
    refine resoluteParticipation_superset hf hpart V0 V5 hVW P5ProfileSub S x ?hx ?hxS ?hUpper
    · erw [restrictElectorate_eq_profileOnSubsetP5 (hST := hVW)]
      exact hP0
    · simpa [S] using hx
    · intro w hw
      simp [V0, V5] at hw
      fin_cases w <;> try contradiction
      all_goals {
        simp [P5ProfileSub, profileOnSubsetP5, P5Ballots]
        exact ballotDCBA_UpperSet_dc
      }
  have hy_mem : y ∈ f P5ProfileSub := by rw [hP5]; simp
  exact hsubset hy_mem

lemma P5_to_P6_preserve_d {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) {y : Fin 4}
    (hP5 : f P5ProfileSub = {3}) (hP6 : f P6ProfileSub = {y}) :
    y = 3 := by
  let S : Finset (Fin 4) := {0, 1, 2}
  by_contra hy
  have hyS : y ∈ S := by
    fin_cases y <;> simp [S] at *
  have hsubset : f P5ProfileSub ⊆ S := by
    apply resoluteParticipation_superset hf hpart V6 V5 (by simp [V6, V5]; intro x hx; simp_all) P5ProfileSub S y
    · erw [restrictElectorate_eq_profileOnSubsetP5 (hST := by simp [V6, V5]; intro x hx; simp_all)]
      exact hP6
    · exact hyS
    · intro w hw
      simp [V6, V5] at hw
      fin_cases w <;> try contradiction
      all_goals {
        simp [P5ProfileSub, profileOnSubsetP5, P5Ballots]
        exact ballotCABD_UpperSet_not_d
      }
  have h3_mem : (3 : Fin 4) ∈ f P5ProfileSub := by rw [hP5]; simp
  have h3S : (3 : Fin 4) ∈ S := hsubset h3_mem
  simp [S] at h3S

lemma P5_to_P7_preserve_c {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) {y : Fin 4}
    (hP5 : f P5ProfileSub = {2}) (hP7 : f P7ProfileSub = {y}) :
    y = 2 := by
  let S : Finset (Fin 4) := {0, 1, 3}
  by_contra hy
  have hyS : y ∈ S := by
    fin_cases y <;> simp [S] at *
  have hsubset : f P5ProfileSub ⊆ S := by
    apply resoluteParticipation_superset hf hpart V7 V5 (by simp [V7, V5]; intro x hx; simp_all) P5ProfileSub S y
    · erw [restrictElectorate_eq_profileOnSubsetP5 (hST := by simp [V7, V5]; intro x hx; simp_all)]
      exact hP7
    · exact hyS
    · intro w hw
      simp [V7, V5] at hw
      fin_cases w <;> try contradiction
      all_goals {
        simp [P5ProfileSub, profileOnSubsetP5, P5Ballots]
        exact ballotABDC_UpperSet_not_c
      }
  have h2_mem : (2 : Fin 4) ∈ f P5ProfileSub := by rw [hP5]; simp
  have h2S : (2 : Fin 4) ∈ S := hsubset h2_mem
  simp [S] at h2S

lemma P7_to_P8_preserve_ac {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) {y : Fin 4}
    (hP7 : f P7ProfileSub = {2}) (hP8 : f P8ProfileSub = {y}) :
    y ∈ ({0, 2} : Finset (Fin 4)) := by
  let S : Finset (Fin 4) := {1, 3}
  by_contra hy
  have hyS : y ∈ S := by
    by_contra hy_not_S
    simp [S] at hy_not_S
    have hy_in : y ∈ ({0, 2} : Finset (Fin 4)) := by
      fin_cases y <;> simp at *
    contradiction
  have hsubset : f P7ProfileSub ⊆ S := by
    apply resoluteParticipation_superset hf hpart V8 V7 (by simp [V7, V8]; intro x hx; simp_all) P7ProfileSub S y
    · erw [restrictElectorate_eq_profileOnSubsetP5 (hST := by simp [V7, V8]; intro x hx; simp_all)]
      exact hP8
    · exact hyS
    · intro w hw
      simp [V7, V8] at hw
      fin_cases w <;> try contradiction
      all_goals {
        simp [P7ProfileSub, profileOnSubsetP5, P5Ballots]
        exact ballotBDCA_UpperSet_bd
      }
  have h2_mem : (2 : Fin 4) ∈ f P7ProfileSub := by rw [hP7]; simp
  have h2S : (2 : Fin 4) ∈ S := hsubset h2_mem
  simp [S] at h2S

-- Condorcet winners for the four key profiles.

private lemma votersPreferring_subsetProfile_eq_filter
    (S : Finset (Fin m)) (ballots : Fin m → ListBallot n) (a b : Fin n) :
    votersPreferring
        ({ pref := fun v : Electorate (Fin m) S => (ballots v.1).toLinearOrder } :
          Profile (Electorate (Fin m) S) (Fin n)) a b =
      Finset.univ.filter (fun v => prefersInList (ballots v.1).ranking a b) := by
  ext v
  simp only [votersPreferring, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold Prefers prefersInList
  rw [ListBallot.lt_iff_idxOf]
  simp [decide_eq_true_eq]

@[simp] private lemma P2_strict_majority_0 : StrictMajority (votersPreferring P2ProfileSub 2 0) := by
  unfold StrictMajority
  rw [show votersPreferring P2ProfileSub 2 0 = _ by
    simpa [P2ProfileSub, profileOnSubset] using
      votersPreferring_subsetProfile_eq_filter V2 P1Ballots 2 0]
  simp [V2, P1Ballots, ballotABCD, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
    prefersInList]
  decide +revert

@[simp] private lemma P2_strict_majority_1 : StrictMajority (votersPreferring P2ProfileSub 2 1) := by
  unfold StrictMajority
  rw [show votersPreferring P2ProfileSub 2 1 = _ by
    simpa [P2ProfileSub, profileOnSubset] using
      votersPreferring_subsetProfile_eq_filter V2 P1Ballots 2 1]
  simp [V2, P1Ballots, ballotABCD, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
    prefersInList]
  decide +revert

@[simp] private lemma P2_strict_majority_3 : StrictMajority (votersPreferring P2ProfileSub 2 3) := by
  unfold StrictMajority
  rw [show votersPreferring P2ProfileSub 2 3 = _ by
    simpa [P2ProfileSub, profileOnSubset] using
      votersPreferring_subsetProfile_eq_filter V2 P1Ballots 2 3]
  simp [V2, P1Ballots, ballotABCD, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
    prefersInList]
  decide +revert

@[simp] private lemma P4_strict_majority_1 : StrictMajority (votersPreferring P4ProfileSub 0 1) := by
  unfold StrictMajority
  rw [show votersPreferring P4ProfileSub 0 1 = _ by
    simpa [P4ProfileSub, profileOnSubset] using
      votersPreferring_subsetProfile_eq_filter V4 P1Ballots 0 1]
  simp [V4, P1Ballots, ballotABCD, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
    prefersInList]
  decide +revert

@[simp] private lemma P4_strict_majority_2 : StrictMajority (votersPreferring P4ProfileSub 0 2) := by
  unfold StrictMajority
  rw [show votersPreferring P4ProfileSub 0 2 = _ by
    simpa [P4ProfileSub, profileOnSubset] using
      votersPreferring_subsetProfile_eq_filter V4 P1Ballots 0 2]
  simp [V4, P1Ballots, ballotABCD, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
    prefersInList]
  decide +revert

@[simp] private lemma P4_strict_majority_3 : StrictMajority (votersPreferring P4ProfileSub 0 3) := by
  unfold StrictMajority
  rw [show votersPreferring P4ProfileSub 0 3 = _ by
    simpa [P4ProfileSub, profileOnSubset] using
      votersPreferring_subsetProfile_eq_filter V4 P1Ballots 0 3]
  simp [V4, P1Ballots, ballotABCD, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
    prefersInList]
  decide +revert

@[simp] private lemma P6_strict_majority_0 : StrictMajority (votersPreferring P6ProfileSub 1 0) := by
  unfold StrictMajority
  rw [show votersPreferring P6ProfileSub 1 0 = _ by
    simpa [P6ProfileSub, profileOnSubsetP5] using
      votersPreferring_subsetProfile_eq_filter V6 P5Ballots 1 0]
  simp [V6, P5Ballots, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB, ballotDCBA,
    prefersInList]
  decide +revert

@[simp] private lemma P6_strict_majority_2 : StrictMajority (votersPreferring P6ProfileSub 1 2) := by
  unfold StrictMajority
  rw [show votersPreferring P6ProfileSub 1 2 = _ by
    simpa [P6ProfileSub, profileOnSubsetP5] using
      votersPreferring_subsetProfile_eq_filter V6 P5Ballots 1 2]
  simp [V6, P5Ballots, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB, ballotDCBA,
    prefersInList]
  decide +revert

@[simp] private lemma P6_strict_majority_3 : StrictMajority (votersPreferring P6ProfileSub 1 3) := by
  unfold StrictMajority
  rw [show votersPreferring P6ProfileSub 1 3 = _ by
    simpa [P6ProfileSub, profileOnSubsetP5] using
      votersPreferring_subsetProfile_eq_filter V6 P5Ballots 1 3]
  simp [V6, P5Ballots, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB, ballotDCBA,
    prefersInList]
  decide +revert

@[simp] private lemma P8_strict_majority_0 : StrictMajority (votersPreferring P8ProfileSub 3 0) := by
  unfold StrictMajority
  rw [show votersPreferring P8ProfileSub 3 0 = _ by
    simpa [P8ProfileSub, profileOnSubsetP5] using
      votersPreferring_subsetProfile_eq_filter V8 P5Ballots 3 0]
  simp [V8, P5Ballots, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB, ballotDCBA,
    prefersInList]
  decide +revert

@[simp] private lemma P8_strict_majority_1 : StrictMajority (votersPreferring P8ProfileSub 3 1) := by
  unfold StrictMajority
  rw [show votersPreferring P8ProfileSub 3 1 = _ by
    simpa [P8ProfileSub, profileOnSubsetP5] using
      votersPreferring_subsetProfile_eq_filter V8 P5Ballots 3 1]
  simp [V8, P5Ballots, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB, ballotDCBA,
    prefersInList]
  decide +revert

@[simp] private lemma P8_strict_majority_2 : StrictMajority (votersPreferring P8ProfileSub 3 2) := by
  unfold StrictMajority
  rw [show votersPreferring P8ProfileSub 3 2 = _ by
    simpa [P8ProfileSub, profileOnSubsetP5] using
      votersPreferring_subsetProfile_eq_filter V8 P5Ballots 3 2]
  simp [V8, P5Ballots, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB, ballotDCBA,
    prefersInList]
  decide +revert

lemma P2_CondorcetWinner_c : CondorcetWinner P2ProfileSub 2 := by
  intro y hy
  fin_cases y <;> first | cases hy rfl | simp

lemma P4_CondorcetWinner_a : CondorcetWinner P4ProfileSub 0 := by
  intro y hy
  fin_cases y <;> first | cases hy rfl | simp

lemma P6_CondorcetWinner_b : CondorcetWinner P6ProfileSub 1 := by
  intro y hy
  fin_cases y <;> first | cases hy rfl | simp

lemma P8_CondorcetWinner_d : CondorcetWinner P8ProfileSub 3 := by
  intro y hy
  fin_cases y <;> first | cases hy rfl | simp

/-! ### Main theorem -/

end CondorcetParticipation

open CondorcetParticipation

theorem no_resolute_condorcet_participation_m4_n12 :
    ¬ ∃ (f : VotingRule) (hf : Resolute f), CondorcetConsistency f ∧ ResoluteParticipation f hf := by
  rintro ⟨f, hf, hcond, hpart⟩
  -- P0 must have result {0} or {1} (a or b) w.l.o.g.
  have h_P0_res : (f P0ProfileSub).card = 1 := hf P0ProfileSub
  rcases Finset.card_eq_one.mp h_P0_res with ⟨x, hx⟩

  by_cases h_ab : x ∈ ({0, 1} : Finset (Fin 4))
  · -- Case x \in {a,b}
    have h_P1_res : (f P1ProfileSub).card = 1 := hf P1ProfileSub
    rcases Finset.card_eq_one.mp h_P1_res with ⟨y, hy⟩
    have hy_ab : y ∈ ({0, 1} : Finset (Fin 4)) :=
      P0_to_P1_preserve_ab hf hpart h_ab hx hy

    -- Split y = 0 or y = 1
    rw [Finset.mem_insert, Finset.mem_singleton] at hy_ab
    rcases hy_ab with (rfl | rfl)
    · -- y = 0 (a)
      -- Path to P2
      have h_P2_res : (f P2ProfileSub).card = 1 := hf P2ProfileSub
      rcases Finset.card_eq_one.mp h_P2_res with ⟨z, hz⟩
      have hz_eq : z = 0 := P1_to_P2_preserve_a hf hpart hy hz
      rw [hz_eq] at hz
      -- P2 has CW c (2). f(P2) = {a} (0).
      have h_cw : f P2ProfileSub = {2} := hcond P2ProfileSub 2 P2_CondorcetWinner_c
      rw [hz] at h_cw
      have : (0 : Fin 4) = 2 := by
        have : 0 ∈ ({2} : Finset (Fin 4)) := by rw [← h_cw]; simp
        simpa
      contradiction
    · -- y = 1 (b)
      -- Path to P3, then P4
      have h_P3_res : (f P3ProfileSub).card = 1 := hf P3ProfileSub
      rcases Finset.card_eq_one.mp h_P3_res with ⟨z, hz⟩
      have hz_eq : z = 1 := P1_to_P3_preserve_b hf hpart hy hz
      rw [hz_eq] at hz
      -- Path to P4
      have h_P4_res : (f P4ProfileSub).card = 1 := hf P4ProfileSub
      rcases Finset.card_eq_one.mp h_P4_res with ⟨w, hw⟩
      have hw_bd : w ∈ ({1, 3} : Finset (Fin 4)) :=
        P3_to_P4_preserve_bd hf hpart hz hw
      -- P4 has CW a (0). f(P4) = {w}. w \in {b, d}.
      have h_cw : f P4ProfileSub = {0} := hcond P4ProfileSub 0 P4_CondorcetWinner_a
      rw [hw] at h_cw
      have : w = 0 := by
         have : w ∈ ({0} : Finset (Fin 4)) := by rw [← h_cw]; simp
         simpa
      rw [this] at hw_bd
      simp at hw_bd -- 0 \in {1, 3} is False
  · -- Case x \in {c,d}
    -- Switch to P5 world
    have h_P0_res_P5 : (f P0ProfileSubP5).card = 1 := by rw [← P0_P5_coincide]; exact h_P0_res
    -- Since P0ProfileSub = P0ProfileSubP5, f(P0) is same.
    rw [P0_P5_coincide] at hx

    have hx_cd : x ∈ ({2, 3} : Finset (Fin 4)) := by
      simp at h_ab
      fin_cases x <;> simp at *

    have h_P5_res : (f P5ProfileSub).card = 1 := hf P5ProfileSub
    rcases Finset.card_eq_one.mp h_P5_res with ⟨y, hy⟩
    have hy_cd : y ∈ ({2, 3} : Finset (Fin 4)) :=
      P0_to_P5_preserve_cd hf hpart hx_cd hx hy

    rw [Finset.mem_insert, Finset.mem_singleton] at hy_cd
    rcases hy_cd with (rfl | rfl)
    · -- y = 2 (c)
      -- Path to P7, then P8
      have h_P7_res : (f P7ProfileSub).card = 1 := hf P7ProfileSub
      rcases Finset.card_eq_one.mp h_P7_res with ⟨z, hz⟩
      have hz_eq : z = 2 := P5_to_P7_preserve_c hf hpart hy hz
      rw [hz_eq] at hz
      -- Path to P8
      have h_P8_res : (f P8ProfileSub).card = 1 := hf P8ProfileSub
      rcases Finset.card_eq_one.mp h_P8_res with ⟨w, hw⟩
      have hw_ac : w ∈ ({0, 2} : Finset (Fin 4)) :=
        P7_to_P8_preserve_ac hf hpart hz hw
      -- P8 has CW d (3). f(P8) = {w}. w \in {a, c}.
      have h_cw : f P8ProfileSub = {3} := hcond P8ProfileSub 3 P8_CondorcetWinner_d
      rw [hw] at h_cw
      have : w = 3 := by
         have : w ∈ ({3} : Finset (Fin 4)) := by rw [← h_cw]; simp
         simpa
      rw [this] at hw_ac
      simp at hw_ac -- 3 \in {0, 2} is False
    · -- y = 3 (d)
      -- Path to P6
      have h_P6_res : (f P6ProfileSub).card = 1 := hf P6ProfileSub
      rcases Finset.card_eq_one.mp h_P6_res with ⟨z, hz⟩
      have hz_eq : z = 3 := P5_to_P6_preserve_d hf hpart hy hz
      rw [hz_eq] at hz
      -- P6 has CW b (1). f(P6) = {d} (3).
      have h_cw : f P6ProfileSub = {1} := hcond P6ProfileSub 1 P6_CondorcetWinner_b
      rw [hz] at h_cw
      have : (3 : Fin 4) = 1 := by
         have : 3 ∈ ({1} : Finset (Fin 4)) := by rw [← h_cw]; simp
         simpa
      contradiction

theorem no_condorcet_strongFishburn_participation_m4_n12 :
    ¬ ∃ (f : VotingRule) (_hf : IsVotingRule f),
      CondorcetConsistency f ∧ StrongFishburnParticipation f := by
  rintro ⟨f, hf, hcond, hpart⟩
  have hcond' : CondorcetConsistency (tieBrokenVotingRule f hf) := by
    intro V A _ _ P c hcw
    classical
    have hA : Nonempty A := ⟨c⟩
    letI : Nonempty A := hA
    have hc : f P = {c} := hcond P c hcw
    simp [tieBrokenVotingRule, hA, tieBrokenRule, hc]
  have hpart' :
      ResoluteParticipation (tieBrokenVotingRule f hf)
        (tieBrokenVotingRule_resolute f hf) :=
    tieBrokenVotingRule_resoluteParticipation f hf hpart
  exact no_resolute_condorcet_participation_m4_n12
    ⟨tieBrokenVotingRule f hf, tieBrokenVotingRule_resolute f hf, hcond', hpart'⟩

/-! ### Optimist participation impossibility (m=4, n=17) -/

namespace CondorcetOptimistParticipation

open Finset

-- Additional ballots needed for the optimist proof.
def ballotACBD : ListBallot 4 := ListBallot.mk' [0, 2, 1, 3]
def ballotBACD : ListBallot 4 := ListBallot.mk' [1, 0, 2, 3]
def ballotDBCA : ListBallot 4 := ListBallot.mk' [3, 1, 2, 0]
def ballotCDBA : ListBallot 4 := ListBallot.mk' [2, 3, 1, 0]

-- Voter sets.
def V0 : Finset (Fin 17) := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
def V10 : Finset (Fin 17) := insert 10 V0
def V11 : Finset (Fin 17) := insert 11 V10
def V12 : Finset (Fin 17) := insert 12 V11
def V13 : Finset (Fin 17) := insert 13 V12
def V14 : Finset (Fin 17) := insert 14 V13
def V15 : Finset (Fin 17) := insert 15 V14
def V16 : Finset (Fin 17) := insert 16 V15

set_option maxHeartbeats 500000 in
lemma V14_eq :
    V14 =
      {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14} := by
  ext v
  fin_cases v <;> simp [V14, V13, V12, V11, V10, V0]

set_option maxHeartbeats 500000 in
lemma V16_eq :
    V16 =
      {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16} := by
  ext v
  fin_cases v <;> simp [V16, V15, V14, V13, V12, V11, V10, V0]

-- Ballot lists for the two branches (a/b and c/d).
def ballotsAlpha3 : Fin 17 → ListBallot 4
  | 0 => ballotABDC
  | 1 => ballotABDC
  | 2 => ballotBDCA
  | 3 => ballotBDCA
  | 4 => ballotBDCA
  | 5 => ballotCABD
  | 6 => ballotCABD
  | 7 => ballotCABD
  | 8 => ballotDCAB
  | 9 => ballotDCAB
  | 10 => ballotABCD
  | 11 => ballotABCD
  | 12 => ballotACBD
  | 13 => ballotACBD
  | 14 => ballotACBD
  | 15 => ballotACBD
  | 16 => ballotACBD
  | _ => ballotACBD

def ballotsAlpha5 : Fin 17 → ListBallot 4
  | 0 => ballotABDC
  | 1 => ballotABDC
  | 2 => ballotBDCA
  | 3 => ballotBDCA
  | 4 => ballotBDCA
  | 5 => ballotCABD
  | 6 => ballotCABD
  | 7 => ballotCABD
  | 8 => ballotDCAB
  | 9 => ballotDCAB
  | 10 => ballotABCD
  | 11 => ballotABCD
  | 12 => ballotBACD
  | 13 => ballotBACD
  | 14 => ballotBACD
  | 15 => ballotBACD
  | 16 => ballotBACD
  | _ => ballotBACD

def ballotsBeta3 : Fin 17 → ListBallot 4
  | 0 => ballotABDC
  | 1 => ballotABDC
  | 2 => ballotBDCA
  | 3 => ballotBDCA
  | 4 => ballotBDCA
  | 5 => ballotCABD
  | 6 => ballotCABD
  | 7 => ballotCABD
  | 8 => ballotDCAB
  | 9 => ballotDCAB
  | 10 => ballotDCBA
  | 11 => ballotDCBA
  | 12 => ballotDBCA
  | 13 => ballotDBCA
  | 14 => ballotDBCA
  | 15 => ballotDBCA
  | 16 => ballotDBCA
  | _ => ballotDBCA

def ballotsBeta5 : Fin 17 → ListBallot 4
  | 0 => ballotABDC
  | 1 => ballotABDC
  | 2 => ballotBDCA
  | 3 => ballotBDCA
  | 4 => ballotBDCA
  | 5 => ballotCABD
  | 6 => ballotCABD
  | 7 => ballotCABD
  | 8 => ballotDCAB
  | 9 => ballotDCAB
  | 10 => ballotDCBA
  | 11 => ballotDCBA
  | 12 => ballotCDBA
  | 13 => ballotCDBA
  | 14 => ballotCDBA
  | 15 => ballotCDBA
  | 16 => ballotCDBA
  | _ => ballotCDBA

noncomputable def profileOnSubsetAlpha3 (S : Finset (Fin 17)) :
    Profile (Electorate (Fin 17) S) (Fin 4) :=
  { pref := fun v => (ballotsAlpha3 v.1).toLinearOrder }

noncomputable def profileOnSubsetAlpha5 (S : Finset (Fin 17)) :
    Profile (Electorate (Fin 17) S) (Fin 4) :=
  { pref := fun v => (ballotsAlpha5 v.1).toLinearOrder }

noncomputable def profileOnSubsetBeta3 (S : Finset (Fin 17)) :
    Profile (Electorate (Fin 17) S) (Fin 4) :=
  { pref := fun v => (ballotsBeta3 v.1).toLinearOrder }

noncomputable def profileOnSubsetBeta5 (S : Finset (Fin 17)) :
    Profile (Electorate (Fin 17) S) (Fin 4) :=
  { pref := fun v => (ballotsBeta5 v.1).toLinearOrder }

-- Named profiles.
noncomputable def RProfile : Profile (Electorate (Fin 17) V0) (Fin 4) :=
  profileOnSubsetAlpha3 V0

noncomputable def RalphaProfile : Profile (Electorate (Fin 17) V11) (Fin 4) :=
  profileOnSubsetAlpha3 V11

noncomputable def Ralpha3Profile : Profile (Electorate (Fin 17) V14) (Fin 4) :=
  profileOnSubsetAlpha3 V14

noncomputable def Ralpha5Profile : Profile (Electorate (Fin 17) V16) (Fin 4) :=
  profileOnSubsetAlpha5 V16

noncomputable def RbetaProfile : Profile (Electorate (Fin 17) V11) (Fin 4) :=
  profileOnSubsetBeta3 V11

noncomputable def Rbeta3Profile : Profile (Electorate (Fin 17) V14) (Fin 4) :=
  profileOnSubsetBeta3 V14

noncomputable def Rbeta5Profile : Profile (Electorate (Fin 17) V16) (Fin 4) :=
  profileOnSubsetBeta5 V16

-- Agreement lemmas between the shared subprofiles.
lemma alpha3_alpha5_coincide_V11 :
    profileOnSubsetAlpha3 V11 = profileOnSubsetAlpha5 V11 := by
  apply Profile.ext
  rintro ⟨v, hv⟩
  change v ∈ V11 at hv
  fin_cases v <;> simp_all [profileOnSubsetAlpha3, profileOnSubsetAlpha5,
    V11, V10, V0, ballotsAlpha3, ballotsAlpha5]
  all_goals
    exfalso
    revert hv
    native_decide

lemma alpha3_beta3_coincide_V0 :
    profileOnSubsetAlpha3 V0 = profileOnSubsetBeta3 V0 := by
  apply Profile.ext
  rintro ⟨v, hv⟩
  change v ∈ V0 at hv
  fin_cases v <;> simp_all [profileOnSubsetAlpha3, profileOnSubsetBeta3,
    V0, ballotsAlpha3, ballotsBeta3]
  all_goals
    exfalso
    revert hv
    native_decide

lemma beta3_beta5_coincide_V11 :
    profileOnSubsetBeta3 V11 = profileOnSubsetBeta5 V11 := by
  apply Profile.ext
  rintro ⟨v, hv⟩
  change v ∈ V11 at hv
  fin_cases v <;> simp_all [profileOnSubsetBeta3, profileOnSubsetBeta5,
    V11, V10, V0, ballotsBeta3, ballotsBeta5]
  all_goals
    exfalso
    revert hv
    native_decide

-- Basic TopInSet helpers.
lemma topInSet_of_ballotTop {A : Type} [DecidableEq A]
    {r : LinearOrder A} {s : Finset A} {c : A} (hc : c ∈ s) (htop : BallotTop r c) :
    TopInSet r s c := by
  refine ⟨hc, ?_⟩
  intro b _ hb
  exact htop b hb

lemma topInSet_unique {A : Type} [DecidableEq A] {r : LinearOrder A} {s : Finset A} {a b : A}
    (ha : TopInSet r s a) (hb : TopInSet r s b) : a = b := by
  by_contra hne
  have hlt1 : r.lt a b := ha.2 b hb.1 (by simpa [eq_comm] using hne)
  have hlt2 : r.lt b a := hb.2 a ha.1 hne
  exact (lt_asymm hlt1 hlt2)

lemma ballot_le_iff_idxOf {n : ℕ} (b : ListBallot n) (a c : Fin n) :
    b.toLinearOrder.le a c ↔ b.ranking.idxOf a ≤ b.ranking.idxOf c := by
  rfl

lemma not_lt_of_ge_r {A : Type} (r : LinearOrder A) {a b : A} (hle : r.le a b) :
    ¬ r.lt b a := by
  letI : PartialOrder A := r.toPartialOrder
  have hle' : a ≤ b := by simpa using hle
  have hnot : ¬ b < a := not_lt_of_ge hle'
  simpa using hnot

-- BallotTop lemmas for the relevant ballots.
lemma ballotABCD_top_a : BallotTop ballotABCD.toLinearOrder 0 := by
  intro x hx
  fin_cases x <;> simp [ballotABCD, ListBallot.lt_iff_idxOf, ListBallot.mk'] at hx ⊢

lemma ballotACBD_top_a : BallotTop ballotACBD.toLinearOrder 0 := by
  intro x hx
  fin_cases x <;> simp [ballotACBD, ListBallot.lt_iff_idxOf, ListBallot.mk'] at hx ⊢

lemma ballotBACD_top_b : BallotTop ballotBACD.toLinearOrder 1 := by
  intro x hx
  fin_cases x <;> simp [ballotBACD, ListBallot.lt_iff_idxOf, ListBallot.mk'] at hx ⊢

lemma ballotDCBA_top_d : BallotTop ballotDCBA.toLinearOrder 3 := by
  intro x hx
  fin_cases x <;> simp [ballotDCBA, ListBallot.lt_iff_idxOf, ListBallot.mk'] at hx ⊢

lemma ballotDBCA_top_d : BallotTop ballotDBCA.toLinearOrder 3 := by
  intro x hx
  fin_cases x <;> simp [ballotDBCA, ListBallot.lt_iff_idxOf, ListBallot.mk'] at hx ⊢

lemma ballotCDBA_top_c : BallotTop ballotCDBA.toLinearOrder 2 := by
  intro x hx
  fin_cases x <;> simp [ballotCDBA, ListBallot.lt_iff_idxOf, ListBallot.mk'] at hx ⊢

-- Top-two reasoning for the abcd ballot.
lemma topInSet_abcd_of_mem_b_of_not_mem_a {s : Finset (Fin 4)}
    (hb : (1 : Fin 4) ∈ s) (ha : (0 : Fin 4) ∉ s) :
    TopInSet ballotABCD.toLinearOrder s 1 := by
  refine ⟨hb, ?_⟩
  intro x hx hne
  fin_cases x
  · exact (ha hx).elim
  · exact (hne rfl).elim
  · simp [ballotABCD, ListBallot.lt_iff_idxOf, ListBallot.mk']
  · simp [ballotABCD, ListBallot.lt_iff_idxOf, ListBallot.mk']

lemma abcd_le_one {x : Fin 4} :
    (ballotABCD.toLinearOrder).le x 1 → x = 0 ∨ x = 1 := by
  fin_cases x <;> intro hle
  · exact Or.inl rfl
  · exact Or.inr rfl
  ·
    have hnot : ¬ (ballotABCD.toLinearOrder).le 2 1 := by
      simp [ballot_le_iff_idxOf, ballotABCD, ListBallot.mk']
    exact (hnot hle).elim
  ·
    have hnot : ¬ (ballotABCD.toLinearOrder).le 3 1 := by
      simp [ballot_le_iff_idxOf, ballotABCD, ListBallot.mk']
    exact (hnot hle).elim

-- Top-two reasoning for the dcba ballot.
lemma topInSet_dcba_of_mem_c_of_not_mem_d {s : Finset (Fin 4)}
    (hc : (2 : Fin 4) ∈ s) (hd : (3 : Fin 4) ∉ s) :
    TopInSet ballotDCBA.toLinearOrder s 2 := by
  refine ⟨hc, ?_⟩
  intro x hx hne
  fin_cases x
  · simp [ballotDCBA, ListBallot.lt_iff_idxOf, ListBallot.mk']
  · simp [ballotDCBA, ListBallot.lt_iff_idxOf, ListBallot.mk']
  · exact (hne rfl).elim
  · exact (hd hx).elim

lemma dcba_le_two {x : Fin 4} :
    (ballotDCBA.toLinearOrder).le x 2 → x = 3 ∨ x = 2 := by
  fin_cases x <;> intro hle
  ·
    have hnot : ¬ (ballotDCBA.toLinearOrder).le 0 2 := by
      simp [ballot_le_iff_idxOf, ballotDCBA, ListBallot.mk']
    exact (hnot hle).elim
  ·
    have hnot : ¬ (ballotDCBA.toLinearOrder).le 1 2 := by
      simp [ballot_le_iff_idxOf, ballotDCBA, ListBallot.mk']
    exact (hnot hle).elim
  · exact Or.inr rfl
  · exact Or.inl rfl

-- Optimist participation preserves a top winner for a single new voter.
lemma optimist_preserve_top {f : VotingRule} (hopt : OptimistParticipation f) :
    ∀ (V : Finset (Fin 17)) (u : Fin 17) (hu : u ∉ V)
      (P : Profile (Electorate (Fin 17) V) (Fin 4))
      (Q : Profile (Electorate (Fin 17) (insert u V)) (Fin 4)) (c : Fin 4),
      (∀ v : Electorate (Fin 17) V, Q.pref (liftVoter (u := u) v) = P.pref v) →
      BallotTop (Q.pref (newVoter (u := u) (V := V) hu)) c →
      c ∈ f P →
      c ∈ f Q := by
  intro V u hu P Q c hagree htop hc
  let r := Q.pref (newVoter (u := u) (V := V) hu)
  have hweak :
      @OptimistWeak (Fin 4) (fun a b => LinearOrder.toDecidableEq a b) r (f Q) (f P) := by
    simpa [OptimistParticipation, StrongParticipation, OptimistExtension, r] using
      (hopt (V := V) (u := u) hu P Q hagree)
  rcases hweak with ⟨x, y, hxTop, hyTop, hle⟩
  have hTopC : TopInSet r (f P) c :=
    topInSet_of_ballotTop (r := r) (s := f P) hc htop
  have hyc' : c = y := by
    apply topInSet_unique (r := r) (s := f P) (a := c) (b := y)
    · exact hTopC
    · exact hyTop
  have hyc : y = c := by simpa using hyc'.symm
  have hx : x = y := by
    by_contra hne
    have hle' : r.le x y := by simpa using hle
    have hne' : x ≠ c := by
      intro hxc
      apply hne
      simpa [hyc] using hxc
    have hlt : r.lt y x := by
      have hlt' : r.lt c x := htop x hne'
      simpa [hyc] using hlt'
    exact (not_lt_of_ge_r r hle' hlt)
  simpa [hx, hyc] using hxTop.1

-- Optimist participation preserves membership in {a,b} for abcd voters.
lemma optimist_preserve_abcd {f : VotingRule} (hopt : OptimistParticipation f)
    (V : Finset (Fin 17)) (u : Fin 17) (hu : u ∉ V)
    (P : Profile (Electorate (Fin 17) V) (Fin 4))
    (Q : Profile (Electorate (Fin 17) (insert u V)) (Fin 4)) :
    (∀ v : Electorate (Fin 17) V, Q.pref (liftVoter (u := u) v) = P.pref v) →
    Q.pref (newVoter (u := u) (V := V) hu) = ballotABCD.toLinearOrder →
    ((0 : Fin 4) ∈ f P ∨ (1 : Fin 4) ∈ f P) →
    ((0 : Fin 4) ∈ f Q ∨ (1 : Fin 4) ∈ f Q) := by
  intro hagree hnew hmem
  have hweak :
      @OptimistWeak (Fin 4)
        (fun a b => (Q.pref (newVoter (u := u) (V := V) hu)).toDecidableEq a b)
        (Q.pref (newVoter (u := u) (V := V) hu)) (f Q) (f P) := by
    simpa [OptimistParticipation, StrongParticipation, OptimistExtension] using
      (hopt (V := V) (u := u) hu P Q hagree)
  have hweak' :
      @OptimistWeak (Fin 4)
        (fun a b => (Q.pref (newVoter (u := u) (V := V) hu)).toDecidableEq a b)
        ballotABCD.toLinearOrder (f Q) (f P) := by
    simpa [hnew] using hweak
  let r := ballotABCD.toLinearOrder
  rcases hweak' with ⟨x, y, hxTop, hyTop, hle⟩
  by_cases h0 : (0 : Fin 4) ∈ f P
  · have hTop0 : TopInSet ballotABCD.toLinearOrder (f P) 0 :=
      topInSet_of_ballotTop (r := ballotABCD.toLinearOrder) (s := f P) h0 ballotABCD_top_a
    have hy0' : 0 = y := by
      apply topInSet_unique (r := ballotABCD.toLinearOrder) (s := f P) (a := 0) (b := y)
      · exact hTop0
      · exact hyTop
    have hy0 : y = 0 := by simpa using hy0'.symm
    subst hy0
    have hx0 : x = 0 := by
      by_contra hne
      have hle' : r.le x 0 := by simpa using hle
      have hlt : r.lt 0 x := by simpa using (ballotABCD_top_a x hne)
      exact (not_lt_of_ge_r r hle' hlt)
    subst hx0
    exact Or.inl hxTop.1
  · have h1 : (1 : Fin 4) ∈ f P := by
      cases hmem with
      | inl h0' => exact (h0 h0').elim
      | inr h1 => exact h1
    have hTop1 : TopInSet ballotABCD.toLinearOrder (f P) 1 :=
      topInSet_abcd_of_mem_b_of_not_mem_a h1 h0
    have hy1' : 1 = y := by
      apply topInSet_unique (r := ballotABCD.toLinearOrder) (s := f P) (a := 1) (b := y)
      · exact hTop1
      · exact hyTop
    have hy1 : y = 1 := by simpa using hy1'.symm
    subst hy1
    have hx01 : x = 0 ∨ x = 1 := abcd_le_one (by simpa using hle)
    cases hx01 with
    | inl hx0 =>
        subst hx0
        exact Or.inl hxTop.1
    | inr hx1 =>
        subst hx1
        exact Or.inr hxTop.1

-- Optimist participation preserves membership in {c,d} for dcba voters.
lemma optimist_preserve_dcba {f : VotingRule} (hopt : OptimistParticipation f)
    (V : Finset (Fin 17)) (u : Fin 17) (hu : u ∉ V)
    (P : Profile (Electorate (Fin 17) V) (Fin 4))
    (Q : Profile (Electorate (Fin 17) (insert u V)) (Fin 4)) :
    (∀ v : Electorate (Fin 17) V, Q.pref (liftVoter (u := u) v) = P.pref v) →
    Q.pref (newVoter (u := u) (V := V) hu) = ballotDCBA.toLinearOrder →
    ((2 : Fin 4) ∈ f P ∨ (3 : Fin 4) ∈ f P) →
    ((2 : Fin 4) ∈ f Q ∨ (3 : Fin 4) ∈ f Q) := by
  intro hagree hnew hmem
  have hweak :
      @OptimistWeak (Fin 4)
        (fun a b => (Q.pref (newVoter (u := u) (V := V) hu)).toDecidableEq a b)
        (Q.pref (newVoter (u := u) (V := V) hu)) (f Q) (f P) := by
    simpa [OptimistParticipation, StrongParticipation, OptimistExtension] using
      (hopt (V := V) (u := u) hu P Q hagree)
  have hweak' :
      @OptimistWeak (Fin 4)
        (fun a b => (Q.pref (newVoter (u := u) (V := V) hu)).toDecidableEq a b)
        ballotDCBA.toLinearOrder (f Q) (f P) := by
    simpa [hnew] using hweak
  let r := ballotDCBA.toLinearOrder
  rcases hweak' with ⟨x, y, hxTop, hyTop, hle⟩
  by_cases h3 : (3 : Fin 4) ∈ f P
  · have hTop3 : TopInSet ballotDCBA.toLinearOrder (f P) 3 :=
      topInSet_of_ballotTop (r := ballotDCBA.toLinearOrder) (s := f P) h3 ballotDCBA_top_d
    have hy3' : 3 = y := by
      apply topInSet_unique (r := ballotDCBA.toLinearOrder) (s := f P) (a := 3) (b := y)
      · exact hTop3
      · exact hyTop
    have hy3 : y = 3 := by simpa using hy3'.symm
    subst hy3
    have hx3 : x = 3 := by
      by_contra hne
      have hle' : r.le x 3 := by simpa using hle
      have hlt : r.lt 3 x := by simpa using (ballotDCBA_top_d x hne)
      exact (not_lt_of_ge_r r hle' hlt)
    subst hx3
    exact Or.inr hxTop.1
  · have h2 : (2 : Fin 4) ∈ f P := by
      cases hmem with
      | inl h2 => exact h2
      | inr h3' => exact (h3 h3').elim
    have hTop2 : TopInSet ballotDCBA.toLinearOrder (f P) 2 :=
      topInSet_dcba_of_mem_c_of_not_mem_d h2 h3
    have hy2' : 2 = y := by
      apply topInSet_unique (r := ballotDCBA.toLinearOrder) (s := f P) (a := 2) (b := y)
      · exact hTop2
      · exact hyTop
    have hy2 : y = 2 := by simpa using hy2'.symm
    subst hy2
    have hx23 : x = 3 ∨ x = 2 := dcba_le_two (by simpa using hle)
    cases hx23 with
    | inl hx3 =>
        subst hx3
        exact Or.inr hxTop.1
    | inr hx2 =>
        subst hx2
        exact Or.inl hxTop.1

-- Condorcet winners for the constructed profiles.

@[simp] private lemma Ralpha3_strict_majority_0 :
    StrictMajority (votersPreferring Ralpha3Profile 2 0) := by
  unfold StrictMajority
  rw [show votersPreferring Ralpha3Profile 2 0 = _ by
    simpa [Ralpha3Profile, profileOnSubsetAlpha3] using
      votersPreferring_subsetProfile_eq_filter V14 ballotsAlpha3 2 0]
  simp [V14_eq, ballotsAlpha3, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
    ballotABCD, ballotACBD, prefersInList]
  decide +revert

@[simp] private lemma Ralpha3_strict_majority_1 :
    StrictMajority (votersPreferring Ralpha3Profile 2 1) := by
  unfold StrictMajority
  rw [show votersPreferring Ralpha3Profile 2 1 = _ by
    simpa [Ralpha3Profile, profileOnSubsetAlpha3] using
      votersPreferring_subsetProfile_eq_filter V14 ballotsAlpha3 2 1]
  simp [V14_eq, ballotsAlpha3, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
    ballotABCD, ballotACBD, prefersInList]
  decide +revert

@[simp] private lemma Ralpha3_strict_majority_3 :
    StrictMajority (votersPreferring Ralpha3Profile 2 3) := by
  unfold StrictMajority
  rw [show votersPreferring Ralpha3Profile 2 3 = _ by
    simpa [Ralpha3Profile, profileOnSubsetAlpha3] using
      votersPreferring_subsetProfile_eq_filter V14 ballotsAlpha3 2 3]
  simp [V14_eq, ballotsAlpha3, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
    ballotABCD, ballotACBD, prefersInList]
  decide +revert

@[simp] private lemma Ralpha5_strict_majority_1 :
    StrictMajority (votersPreferring Ralpha5Profile 0 1) := by
  unfold StrictMajority
  rw [show votersPreferring Ralpha5Profile 0 1 = _ by
    simpa [Ralpha5Profile, profileOnSubsetAlpha5] using
      votersPreferring_subsetProfile_eq_filter V16 ballotsAlpha5 0 1]
  simp [V16_eq, ballotsAlpha5, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
    ballotABCD, ballotBACD, prefersInList]
  decide +revert

@[simp] private lemma Ralpha5_strict_majority_2 :
    StrictMajority (votersPreferring Ralpha5Profile 0 2) := by
  unfold StrictMajority
  rw [show votersPreferring Ralpha5Profile 0 2 = _ by
    simpa [Ralpha5Profile, profileOnSubsetAlpha5] using
      votersPreferring_subsetProfile_eq_filter V16 ballotsAlpha5 0 2]
  simp [V16_eq, ballotsAlpha5, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
    ballotABCD, ballotBACD, prefersInList]
  decide +revert

@[simp] private lemma Ralpha5_strict_majority_3 :
    StrictMajority (votersPreferring Ralpha5Profile 0 3) := by
  unfold StrictMajority
  rw [show votersPreferring Ralpha5Profile 0 3 = _ by
    simpa [Ralpha5Profile, profileOnSubsetAlpha5] using
      votersPreferring_subsetProfile_eq_filter V16 ballotsAlpha5 0 3]
  simp [V16_eq, ballotsAlpha5, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
    ballotABCD, ballotBACD, prefersInList]
  decide +revert

@[simp] private lemma Rbeta3_strict_majority_0 :
    StrictMajority (votersPreferring Rbeta3Profile 1 0) := by
  unfold StrictMajority
  rw [show votersPreferring Rbeta3Profile 1 0 = _ by
    simpa [Rbeta3Profile, profileOnSubsetBeta3] using
      votersPreferring_subsetProfile_eq_filter V14 ballotsBeta3 1 0]
  simp [V14_eq, ballotsBeta3, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
    ballotDCBA, ballotDBCA, prefersInList]
  decide +revert

@[simp] private lemma Rbeta3_strict_majority_2 :
    StrictMajority (votersPreferring Rbeta3Profile 1 2) := by
  unfold StrictMajority
  rw [show votersPreferring Rbeta3Profile 1 2 = _ by
    simpa [Rbeta3Profile, profileOnSubsetBeta3] using
      votersPreferring_subsetProfile_eq_filter V14 ballotsBeta3 1 2]
  simp [V14_eq, ballotsBeta3, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
    ballotDCBA, ballotDBCA, prefersInList]
  decide +revert

@[simp] private lemma Rbeta3_strict_majority_3 :
    StrictMajority (votersPreferring Rbeta3Profile 1 3) := by
  unfold StrictMajority
  rw [show votersPreferring Rbeta3Profile 1 3 = _ by
    simpa [Rbeta3Profile, profileOnSubsetBeta3] using
      votersPreferring_subsetProfile_eq_filter V14 ballotsBeta3 1 3]
  simp [V14_eq, ballotsBeta3, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
    ballotDCBA, ballotDBCA, prefersInList]
  decide +revert

@[simp] private lemma Rbeta5_strict_majority_0 :
    StrictMajority (votersPreferring Rbeta5Profile 3 0) := by
  unfold StrictMajority
  rw [show votersPreferring Rbeta5Profile 3 0 = _ by
    simpa [Rbeta5Profile, profileOnSubsetBeta5] using
      votersPreferring_subsetProfile_eq_filter V16 ballotsBeta5 3 0]
  simp [V16_eq, ballotsBeta5, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
    ballotDCBA, ballotCDBA, prefersInList]
  decide +revert

@[simp] private lemma Rbeta5_strict_majority_1 :
    StrictMajority (votersPreferring Rbeta5Profile 3 1) := by
  unfold StrictMajority
  rw [show votersPreferring Rbeta5Profile 3 1 = _ by
    simpa [Rbeta5Profile, profileOnSubsetBeta5] using
      votersPreferring_subsetProfile_eq_filter V16 ballotsBeta5 3 1]
  simp [V16_eq, ballotsBeta5, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
    ballotDCBA, ballotCDBA, prefersInList]
  decide +revert

@[simp] private lemma Rbeta5_strict_majority_2 :
    StrictMajority (votersPreferring Rbeta5Profile 3 2) := by
  unfold StrictMajority
  rw [show votersPreferring Rbeta5Profile 3 2 = _ by
    simpa [Rbeta5Profile, profileOnSubsetBeta5] using
      votersPreferring_subsetProfile_eq_filter V16 ballotsBeta5 3 2]
  simp [V16_eq, ballotsBeta5, ballotABDC, ballotBDCA, ballotCABD, ballotDCAB,
    ballotDCBA, ballotCDBA, prefersInList]
  decide +revert

lemma Ralpha3_CondorcetWinner_c : CondorcetWinner Ralpha3Profile 2 := by
  intro y hy
  fin_cases y <;> first | cases hy rfl | simp

lemma Ralpha5_CondorcetWinner_a : CondorcetWinner Ralpha5Profile 0 := by
  intro y hy
  fin_cases y <;> first | cases hy rfl | simp

lemma Rbeta3_CondorcetWinner_b : CondorcetWinner Rbeta3Profile 1 := by
  intro y hy
  fin_cases y <;> first | cases hy rfl | simp

lemma Rbeta5_CondorcetWinner_d : CondorcetWinner Rbeta5Profile 3 := by
  intro y hy
  fin_cases y <;> first | cases hy rfl | simp

theorem no_condorcet_optimist_participation_m4_n17 :
    ¬ ∃ (f : VotingRule), CondorcetConsistency f ∧ OptimistParticipation f := by
  rintro ⟨f, hcond, hopt⟩
  classical

  -- Derive that f RProfile is nonempty from optimistic participation.
  let R10 : Profile (Electorate (Fin 17) V10) (Fin 4) := profileOnSubsetAlpha3 V10
  have h10 : (10 : Fin 17) ∉ V0 := by simp [V0]
  have hagree10 : ∀ v : Electorate (Fin 17) V0,
      R10.pref (liftVoter (u := 10) v) = RProfile.pref v := by
    intro v; rfl
  have hweak := hopt (V := V0) (u := 10) h10 RProfile R10 hagree10
  rcases hweak with ⟨_, y0, _, hy0, _⟩
  have hnonempty : (f RProfile).Nonempty := ⟨y0, hy0.1⟩
  rcases hnonempty with ⟨x, hx⟩

  -- Case split on a/b vs c/d.
  have hcontra_ab :
      ((0 : Fin 4) ∈ f RProfile ∨ (1 : Fin 4) ∈ f RProfile) → False := by
    intro h_ab
    -- Add two abcd voters.
    let R10 : Profile (Electorate (Fin 17) V10) (Fin 4) := profileOnSubsetAlpha3 V10
    let R11 : Profile (Electorate (Fin 17) V11) (Fin 4) := RalphaProfile
    have h10 : (10 : Fin 17) ∉ V0 := by simp [V0]
    have h11 : (11 : Fin 17) ∉ V10 := by simp [V10, V0]
    have h_ab_R10 : (0 : Fin 4) ∈ f R10 ∨ (1 : Fin 4) ∈ f R10 := by
      apply optimist_preserve_abcd hopt V0 10 h10 RProfile R10
      · intro v; rfl
      ·
        change (ballotsAlpha3 10).toLinearOrder = ballotABCD.toLinearOrder
        simp [ballotsAlpha3]
      · exact h_ab
    have h_ab_R11 : (0 : Fin 4) ∈ f R11 ∨ (1 : Fin 4) ∈ f R11 := by
      apply optimist_preserve_abcd hopt V10 11 h11 R10 R11
      · intro v; rfl
      ·
        change (ballotsAlpha3 11).toLinearOrder = ballotABCD.toLinearOrder
        simp [ballotsAlpha3]
      · exact h_ab_R10
    rcases h_ab_R11 with h0 | h1
    · -- If a is a winner, add three acbd voters and reach CW c.
      let R12 : Profile (Electorate (Fin 17) V12) (Fin 4) := profileOnSubsetAlpha3 V12
      let R13 : Profile (Electorate (Fin 17) V13) (Fin 4) := profileOnSubsetAlpha3 V13
      let R14 : Profile (Electorate (Fin 17) V14) (Fin 4) := Ralpha3Profile
      have h12 : (12 : Fin 17) ∉ V11 := by simp [V11, V10, V0]
      have h13 : (13 : Fin 17) ∉ V12 := by simp [V12, V11, V10, V0]
      have h14 : (14 : Fin 17) ∉ V13 := by simp [V13, V12, V11, V10, V0]
      have h0_R12 : (0 : Fin 4) ∈ f R12 := by
        apply optimist_preserve_top hopt V11 12 h12 R11 R12 0
        · intro v; rfl
        ·
          change BallotTop ballotACBD.toLinearOrder (0 : Fin 4)
          exact ballotACBD_top_a
        · exact h0
      have h0_R13 : (0 : Fin 4) ∈ f R13 := by
        apply optimist_preserve_top hopt V12 13 h13 R12 R13 0
        · intro v; rfl
        ·
          change BallotTop ballotACBD.toLinearOrder (0 : Fin 4)
          exact ballotACBD_top_a
        · exact h0_R12
      have h0_R14 : (0 : Fin 4) ∈ f R14 := by
        apply optimist_preserve_top hopt V13 14 h14 R13 R14 0
        · intro v; rfl
        ·
          change BallotTop ballotACBD.toLinearOrder (0 : Fin 4)
          exact ballotACBD_top_a
        · exact h0_R13
      have hcw : f Ralpha3Profile = {2} :=
        hcond Ralpha3Profile 2 Ralpha3_CondorcetWinner_c
      simp [R14, hcw] at h0_R14
    · -- If b is a winner, switch to the alpha5 profile and add five bacd voters.
      let R11A5 : Profile (Electorate (Fin 17) V11) (Fin 4) := profileOnSubsetAlpha5 V11
      let R12A5 : Profile (Electorate (Fin 17) V12) (Fin 4) := profileOnSubsetAlpha5 V12
      let R13A5 : Profile (Electorate (Fin 17) V13) (Fin 4) := profileOnSubsetAlpha5 V13
      let R14A5 : Profile (Electorate (Fin 17) V14) (Fin 4) := profileOnSubsetAlpha5 V14
      let R15A5 : Profile (Electorate (Fin 17) V15) (Fin 4) := profileOnSubsetAlpha5 V15
      let R16A5 : Profile (Electorate (Fin 17) V16) (Fin 4) := Ralpha5Profile
      have hEq11 : R11A5 = R11 := by
        simpa [R11A5, R11, RalphaProfile] using (alpha3_alpha5_coincide_V11).symm
      have h1A5 : (1 : Fin 4) ∈ f R11A5 := by
        simpa [hEq11] using h1
      have h12 : (12 : Fin 17) ∉ V11 := by simp [V11, V10, V0]
      have h13 : (13 : Fin 17) ∉ V12 := by simp [V12, V11, V10, V0]
      have h14 : (14 : Fin 17) ∉ V13 := by simp [V13, V12, V11, V10, V0]
      have h15 : (15 : Fin 17) ∉ V14 := by simp [V14, V13, V12, V11, V10, V0]
      have h16 : (16 : Fin 17) ∉ V15 := by simp [V15, V14, V13, V12, V11, V10, V0]
      have h1_R12 : (1 : Fin 4) ∈ f R12A5 := by
        apply optimist_preserve_top hopt V11 12 h12 R11A5 R12A5 1
        · intro v; rfl
        ·
          change BallotTop ballotBACD.toLinearOrder (1 : Fin 4)
          exact ballotBACD_top_b
        · exact h1A5
      have h1_R13 : (1 : Fin 4) ∈ f R13A5 := by
        apply optimist_preserve_top hopt V12 13 h13 R12A5 R13A5 1
        · intro v; rfl
        ·
          change BallotTop ballotBACD.toLinearOrder (1 : Fin 4)
          exact ballotBACD_top_b
        · exact h1_R12
      have h1_R14 : (1 : Fin 4) ∈ f R14A5 := by
        apply optimist_preserve_top hopt V13 14 h14 R13A5 R14A5 1
        · intro v; rfl
        ·
          change BallotTop ballotBACD.toLinearOrder (1 : Fin 4)
          exact ballotBACD_top_b
        · exact h1_R13
      have h1_R15 : (1 : Fin 4) ∈ f R15A5 := by
        apply optimist_preserve_top hopt V14 15 h15 R14A5 R15A5 1
        · intro v; rfl
        ·
          change BallotTop ballotBACD.toLinearOrder (1 : Fin 4)
          exact ballotBACD_top_b
        · exact h1_R14
      have h1_R16 : (1 : Fin 4) ∈ f R16A5 := by
        apply optimist_preserve_top hopt V15 16 h16 R15A5 R16A5 1
        · intro v; rfl
        ·
          change BallotTop ballotBACD.toLinearOrder (1 : Fin 4)
          exact ballotBACD_top_b
        · exact h1_R15
      have hcw : f Ralpha5Profile = {0} :=
        hcond Ralpha5Profile 0 Ralpha5_CondorcetWinner_a
      simp [R16A5, hcw] at h1_R16

  have hcontra_cd :
      ((2 : Fin 4) ∈ f RProfile ∨ (3 : Fin 4) ∈ f RProfile) → False := by
    intro h_cd
    -- Switch to the beta3 profile (R + 2·dcba).
    let R0B : Profile (Electorate (Fin 17) V0) (Fin 4) := profileOnSubsetBeta3 V0
    let R10B : Profile (Electorate (Fin 17) V10) (Fin 4) := profileOnSubsetBeta3 V10
    let R11B : Profile (Electorate (Fin 17) V11) (Fin 4) := RbetaProfile
    have hEq0 : R0B = RProfile := by
      simpa [R0B, RProfile] using (alpha3_beta3_coincide_V0).symm
    have h_cd_B : (2 : Fin 4) ∈ f R0B ∨ (3 : Fin 4) ∈ f R0B := by
      simpa [hEq0] using h_cd
    have h10 : (10 : Fin 17) ∉ V0 := by simp [V0]
    have h11 : (11 : Fin 17) ∉ V10 := by simp [V10, V0]
    have h_cd_R10 : (2 : Fin 4) ∈ f R10B ∨ (3 : Fin 4) ∈ f R10B := by
      apply optimist_preserve_dcba hopt V0 10 h10 R0B R10B
      · intro v; rfl
      ·
        change (ballotsBeta3 10).toLinearOrder = ballotDCBA.toLinearOrder
        simp [ballotsBeta3]
      · exact h_cd_B
    have h_cd_R11 : (2 : Fin 4) ∈ f R11B ∨ (3 : Fin 4) ∈ f R11B := by
      apply optimist_preserve_dcba hopt V10 11 h11 R10B R11B
      · intro v; rfl
      ·
        change (ballotsBeta3 11).toLinearOrder = ballotDCBA.toLinearOrder
        simp [ballotsBeta3]
      · exact h_cd_R10
    rcases h_cd_R11 with h2 | h3
    · -- If c is a winner, switch to beta5 and add five cdba voters (CW d).
      let R11B5 : Profile (Electorate (Fin 17) V11) (Fin 4) := profileOnSubsetBeta5 V11
      let R12B5 : Profile (Electorate (Fin 17) V12) (Fin 4) := profileOnSubsetBeta5 V12
      let R13B5 : Profile (Electorate (Fin 17) V13) (Fin 4) := profileOnSubsetBeta5 V13
      let R14B5 : Profile (Electorate (Fin 17) V14) (Fin 4) := profileOnSubsetBeta5 V14
      let R15B5 : Profile (Electorate (Fin 17) V15) (Fin 4) := profileOnSubsetBeta5 V15
      let R16B5 : Profile (Electorate (Fin 17) V16) (Fin 4) := Rbeta5Profile
      have hEq11 : R11B5 = R11B := by
        simpa [R11B5, R11B, RbetaProfile] using (beta3_beta5_coincide_V11).symm
      have h2B5 : (2 : Fin 4) ∈ f R11B5 := by
        simpa [hEq11] using h2
      have h12 : (12 : Fin 17) ∉ V11 := by simp [V11, V10, V0]
      have h13 : (13 : Fin 17) ∉ V12 := by simp [V12, V11, V10, V0]
      have h14 : (14 : Fin 17) ∉ V13 := by simp [V13, V12, V11, V10, V0]
      have h15 : (15 : Fin 17) ∉ V14 := by simp [V14, V13, V12, V11, V10, V0]
      have h16 : (16 : Fin 17) ∉ V15 := by simp [V15, V14, V13, V12, V11, V10, V0]
      have h2_R12 : (2 : Fin 4) ∈ f R12B5 := by
        apply optimist_preserve_top hopt V11 12 h12 R11B5 R12B5 2
        · intro v; rfl
        ·
          change BallotTop ballotCDBA.toLinearOrder (2 : Fin 4)
          exact ballotCDBA_top_c
        · exact h2B5
      have h2_R13 : (2 : Fin 4) ∈ f R13B5 := by
        apply optimist_preserve_top hopt V12 13 h13 R12B5 R13B5 2
        · intro v; rfl
        ·
          change BallotTop ballotCDBA.toLinearOrder (2 : Fin 4)
          exact ballotCDBA_top_c
        · exact h2_R12
      have h2_R14 : (2 : Fin 4) ∈ f R14B5 := by
        apply optimist_preserve_top hopt V13 14 h14 R13B5 R14B5 2
        · intro v; rfl
        ·
          change BallotTop ballotCDBA.toLinearOrder (2 : Fin 4)
          exact ballotCDBA_top_c
        · exact h2_R13
      have h2_R15 : (2 : Fin 4) ∈ f R15B5 := by
        apply optimist_preserve_top hopt V14 15 h15 R14B5 R15B5 2
        · intro v; rfl
        ·
          change BallotTop ballotCDBA.toLinearOrder (2 : Fin 4)
          exact ballotCDBA_top_c
        · exact h2_R14
      have h2_R16 : (2 : Fin 4) ∈ f R16B5 := by
        apply optimist_preserve_top hopt V15 16 h16 R15B5 R16B5 2
        · intro v; rfl
        ·
          change BallotTop ballotCDBA.toLinearOrder (2 : Fin 4)
          exact ballotCDBA_top_c
        · exact h2_R15
      have hcw : f Rbeta5Profile = {3} :=
        hcond Rbeta5Profile 3 Rbeta5_CondorcetWinner_d
      simp [R16B5, hcw] at h2_R16
    · -- If d is a winner, add three dbca voters (CW b).
      let R12B : Profile (Electorate (Fin 17) V12) (Fin 4) := profileOnSubsetBeta3 V12
      let R13B : Profile (Electorate (Fin 17) V13) (Fin 4) := profileOnSubsetBeta3 V13
      let R14B : Profile (Electorate (Fin 17) V14) (Fin 4) := Rbeta3Profile
      have h12 : (12 : Fin 17) ∉ V11 := by simp [V11, V10, V0]
      have h13 : (13 : Fin 17) ∉ V12 := by simp [V12, V11, V10, V0]
      have h14 : (14 : Fin 17) ∉ V13 := by simp [V13, V12, V11, V10, V0]
      have h3_R12 : (3 : Fin 4) ∈ f R12B := by
        apply optimist_preserve_top hopt V11 12 h12 R11B R12B 3
        · intro v; rfl
        ·
          change BallotTop ballotDBCA.toLinearOrder (3 : Fin 4)
          exact ballotDBCA_top_d
        · exact h3
      have h3_R13 : (3 : Fin 4) ∈ f R13B := by
        apply optimist_preserve_top hopt V12 13 h13 R12B R13B 3
        · intro v; rfl
        ·
          change BallotTop ballotDBCA.toLinearOrder (3 : Fin 4)
          exact ballotDBCA_top_d
        · exact h3_R12
      have h3_R14 : (3 : Fin 4) ∈ f R14B := by
        apply optimist_preserve_top hopt V13 14 h14 R13B R14B 3
        · intro v; rfl
        ·
          change BallotTop ballotDBCA.toLinearOrder (3 : Fin 4)
          exact ballotDBCA_top_d
        · exact h3_R13
      have hcw : f Rbeta3Profile = {1} :=
        hcond Rbeta3Profile 1 Rbeta3_CondorcetWinner_b
      simp [R14B, hcw] at h3_R14

  fin_cases x
  · exact hcontra_ab (Or.inl hx)
  · exact hcontra_ab (Or.inr hx)
  · exact hcontra_cd (Or.inl hx)
  · exact hcontra_cd (Or.inr hx)

end CondorcetOptimistParticipation

end SocialChoice
