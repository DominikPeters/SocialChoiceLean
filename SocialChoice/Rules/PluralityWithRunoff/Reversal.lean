import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Reversal
import SocialChoice.ListBallot
import SocialChoice.Rules.PluralityWithRunoff.Defs

namespace SocialChoice

open Finset

namespace PluralityWithRunoffReversalCounterexample

def ballotBCA : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballotCAB : ListBallot 3 := ListBallot.mk' [2, 0, 1]
def ballotABC : ListBallot 3 := ListBallot.mk' [0, 1, 2]

def ballots : Fin 5 → ListBallot 3
  | ⟨0, _⟩ => ballotBCA
  | ⟨1, _⟩ => ballotBCA
  | ⟨2, _⟩ => ballotCAB
  | ⟨3, _⟩ => ballotABC
  | ⟨4, _⟩ => ballotABC

noncomputable def profile : Profile (Fin 5) (Fin 3) :=
  profileOfListBallots ballots

private lemma bottomRank_iff_prefersInList {m n : ℕ} (ballots : Fin m → ListBallot n)
    (v : Fin m) (c : Fin n) :
    BottomRank (profileOfListBallots ballots) v c ↔
      ∀ d : Fin n, d ≠ c → prefersInList (ballots v).ranking d c = true := by
  constructor
  · intro h d hd
    exact (prefers_iff_prefersInList ballots v d c).1 (h d hd)
  · intro h d hd
    exact (prefers_iff_prefersInList ballots v d c).2 (h d hd)

private lemma topRank_reverse_profile_iff_bottomRank {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (c : A) :
    TopRank (reverse_profile P) v c ↔ BottomRank P v c := by
  constructor
  · intro h d hd
    simpa using (h d hd)
  · intro h d hd
    simpa using (h d hd)

private lemma votersBottom_profile_0 :
    votersBottom profile (0 : Fin 3) = ({0, 1} : Finset (Fin 5)) := by
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersBottom, bottomRank_iff_prefersInList, prefersInList] <;>
    decide

private lemma votersBottom_profile_1 :
    votersBottom profile (1 : Fin 3) = ({2} : Finset (Fin 5)) := by
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersBottom, bottomRank_iff_prefersInList, prefersInList] <;>
    decide

private lemma votersBottom_profile_2 :
    votersBottom profile (2 : Fin 3) = ({3, 4} : Finset (Fin 5)) := by
  ext v
  fin_cases v <;>
    simp [profile, ballots, votersBottom, bottomRank_iff_prefersInList, prefersInList] <;>
    decide

private lemma plurality_profile_eq : plurality profile = ({0, 1} : Finset (Fin 3)) := by
  rw [profile]
  simp only [plurality, topCount, votersTop_eq_filter_isTopOfList]
  decide

private lemma margin_profile_0_1 : margin profile (0 : Fin 3) (1 : Fin 3) = 1 := by
  rw [profile, margin_profileOfListBallots]
  decide

private lemma margin_profile_1_0 : margin profile (1 : Fin 3) (0 : Fin 3) = -1 := by
  rw [profile, margin_profileOfListBallots]
  decide

private lemma margin_profile_2_0 : margin profile (2 : Fin 3) (0 : Fin 3) = 1 := by
  rw [profile, margin_profileOfListBallots]
  decide

private lemma pair_01_mem_pairs :
    ({0, 1} : Finset (Fin 3)) ∈ pluralityWithRunoffPairs profile := by
  have hS : (plurality profile).card ≥ 2 := by
    simp [plurality_profile_eq]
  have hsubset : ({0, 1} : Finset (Fin 3)) ⊆ plurality profile := by
    intro x hx
    simpa [plurality_profile_eq] using hx
  have hcardpair : ({0, 1} : Finset (Fin 3)).card = 2 := by
    simp
  have hmem :
      ({0, 1} : Finset (Fin 3)) ∈ (plurality profile).powersetCard 2 := by
    exact Finset.mem_powersetCard.mpr ⟨hsubset, hcardpair⟩
  simpa [pluralityWithRunoffPairs, hS] using hmem

private lemma pluralityWithRunoff_profile_has_0 :
    (0 : Fin 3) ∈ pluralityWithRunoff profile :=
  (mem_pluralityWithRunoff_iff profile 0 (by decide)).2
    ⟨1, pair_01_mem_pairs, by simp [margin_profile_0_1]⟩

private lemma pluralityWithRunoffPairs_profile :
    pluralityWithRunoffPairs profile =
      ({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
  ext s
  constructor
  · intro hs
    have hs' : s ∈ (plurality profile).powersetCard 2 := by
      have hS : (plurality profile).card ≥ 2 := by
        simp [plurality_profile_eq]
      simpa [pluralityWithRunoffPairs, hS] using hs
    rcases Finset.mem_powersetCard.mp hs' with ⟨hsS, hcard⟩
    have hsS' : s ⊆ ({0, 1} : Finset (Fin 3)) := by
      simpa [plurality_profile_eq] using hsS
    have hcardpair : ({0, 1} : Finset (Fin 3)).card = 2 := by
      simp
    have hcard_le : ({0, 1} : Finset (Fin 3)).card ≤ s.card := by
      simp [hcardpair, hcard]
    have hEq : s = ({0, 1} : Finset (Fin 3)) :=
      Finset.eq_of_subset_of_card_le hsS' hcard_le
    simp [hEq]
  · intro hs
    have hs' : s = ({0, 1} : Finset (Fin 3)) := by
      simpa [Finset.mem_singleton] using hs
    subst hs'
    simpa using pair_01_mem_pairs

private lemma pluralityWithRunoff_profile_not_1 :
    (1 : Fin 3) ∉ pluralityWithRunoff profile := by
  intro h
  obtain ⟨y, hyPair, hyMargin⟩ := (mem_pluralityWithRunoff_iff profile 1 (by decide)).1 h
  rw [pluralityWithRunoffPairs_profile] at hyPair
  fin_cases y
  · simp [margin_profile_1_0] at hyMargin
  · exact absurd hyPair (by decide)
  · exact absurd hyPair (by decide)

private lemma pluralityWithRunoff_profile_not_2 :
    (2 : Fin 3) ∉ pluralityWithRunoff profile := by
  intro h
  obtain ⟨y, hyPair, -⟩ := (mem_pluralityWithRunoff_iff profile 2 (by decide)).1 h
  rw [pluralityWithRunoffPairs_profile] at hyPair
  have hnot : ∀ y : Fin 3,
      ({2, y} : Finset (Fin 3)) ∉ ({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
    decide
  exact hnot y hyPair

lemma pluralityWithRunoff_profile_eq_singleton : pluralityWithRunoff profile = {0} := by
  refine (Finset.eq_singleton_iff_unique_mem).2 ?_
  refine ⟨pluralityWithRunoff_profile_has_0, ?_⟩
  intro x hx
  fin_cases x
  · rfl
  · exfalso
    exact pluralityWithRunoff_profile_not_1 hx
  · exfalso
    exact pluralityWithRunoff_profile_not_2 hx

private lemma votersTop_reverse_profile_eq_votersBottom {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) :
    votersTop (reverse_profile P) c = votersBottom P c := by
  ext v
  simp [votersTop, votersBottom, topRank_reverse_profile_iff_bottomRank]

private lemma topCount_reverse_profile_0 :
    topCount (reverse_profile profile) (0 : Fin 3) = 2 := by
  simp [topCount, votersTop_reverse_profile_eq_votersBottom, votersBottom_profile_0]

private lemma topCount_reverse_profile_1 :
    topCount (reverse_profile profile) (1 : Fin 3) = 1 := by
  simp [topCount, votersTop_reverse_profile_eq_votersBottom, votersBottom_profile_1]

private lemma topCount_reverse_profile_2 :
    topCount (reverse_profile profile) (2 : Fin 3) = 2 := by
  simp [topCount, votersTop_reverse_profile_eq_votersBottom, votersBottom_profile_2]

private lemma plurality_reverse_profile_has_0 :
    (0 : Fin 3) ∈ plurality (reverse_profile profile) := by
  have hmax :
      ∀ d : Fin 3,
        topCount (reverse_profile profile) d ≤ topCount (reverse_profile profile) 0 := by
    intro d
    fin_cases d <;>
      simp [topCount_reverse_profile_0, topCount_reverse_profile_1, topCount_reverse_profile_2]
  have hmem :
      (0 : Fin 3) ∈
        (Finset.univ.filter (fun c : Fin 3 =>
          ∀ d : Fin 3,
            topCount (reverse_profile profile) d ≤ topCount (reverse_profile profile) c)) := by
    exact Finset.mem_filter.mpr ⟨by simp, hmax⟩
  simpa [plurality] using hmem

private lemma plurality_reverse_profile_has_2 :
    (2 : Fin 3) ∈ plurality (reverse_profile profile) := by
  have hmax :
      ∀ d : Fin 3,
        topCount (reverse_profile profile) d ≤ topCount (reverse_profile profile) 2 := by
    intro d
    fin_cases d <;>
      simp [topCount_reverse_profile_0, topCount_reverse_profile_1, topCount_reverse_profile_2]
  have hmem :
      (2 : Fin 3) ∈
        (Finset.univ.filter (fun c : Fin 3 =>
          ∀ d : Fin 3,
            topCount (reverse_profile profile) d ≤ topCount (reverse_profile profile) c)) := by
    exact Finset.mem_filter.mpr ⟨by simp, hmax⟩
  simpa [plurality] using hmem

private lemma pair_02_mem_pairs_reverse :
    ({0, 2} : Finset (Fin 3)) ∈ pluralityWithRunoffPairs (reverse_profile profile) := by
  have hmem0 : (0 : Fin 3) ∈ plurality (reverse_profile profile) :=
    plurality_reverse_profile_has_0
  have hmem2 : (2 : Fin 3) ∈ plurality (reverse_profile profile) :=
    plurality_reverse_profile_has_2
  have hS : (plurality (reverse_profile profile)).card ≥ 2 := by
    have hlt :
        1 < (plurality (reverse_profile profile)).card := by
      exact Finset.one_lt_card.mpr ⟨0, hmem0, 2, hmem2, by decide⟩
    exact (Nat.succ_le_iff.mp hlt)
  have hsubset : ({0, 2} : Finset (Fin 3)) ⊆ plurality (reverse_profile profile) := by
    intro x hx
    simp [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcardpair : ({0, 2} : Finset (Fin 3)).card = 2 := by
    simp
  have hmem :
      ({0, 2} : Finset (Fin 3)) ∈ (plurality (reverse_profile profile)).powersetCard 2 := by
    exact Finset.mem_powersetCard.mpr ⟨hsubset, hcardpair⟩
  simpa [pluralityWithRunoffPairs, hS] using hmem

lemma reverse_profile_has_0 :
    (0 : Fin 3) ∈ pluralityWithRunoff (reverse_profile profile) := by
  have hmargin :
      0 ≤ margin (reverse_profile profile) (0 : Fin 3) (2 : Fin 3) := by
    have h :=
      margin_reverse_eq (P := profile) (a := (2 : Fin 3)) (b := (0 : Fin 3))
    have h' : margin (reverse_profile profile) (0 : Fin 3) (2 : Fin 3) = 1 := by
      simpa [margin_profile_2_0] using h
    simp [h']
  exact (mem_pluralityWithRunoff_iff (reverse_profile profile) 0 (by decide)).2
    ⟨2, pair_02_mem_pairs_reverse, hmargin⟩

end PluralityWithRunoffReversalCounterexample

theorem pluralityWithRunoff_not_singletonReversalSymmetry :
    ¬ SingletonReversalSymmetry pluralityWithRunoff := by
  intro h
  have hsingle :
      pluralityWithRunoff PluralityWithRunoffReversalCounterexample.profile = {0} :=
    PluralityWithRunoffReversalCounterexample.pluralityWithRunoff_profile_eq_singleton
  have hne : ∃ y : Fin 3, (0 : Fin 3) ≠ y := by
    exact ⟨1, by decide⟩
  have hnot :=
    h (P := PluralityWithRunoffReversalCounterexample.profile) (x := (0 : Fin 3)) hne hsingle
  have hw :
      (0 : Fin 3) ∈
        pluralityWithRunoff (reverse_profile PluralityWithRunoffReversalCounterexample.profile) :=
    PluralityWithRunoffReversalCounterexample.reverse_profile_has_0
  exact hnot hw

end SocialChoice
