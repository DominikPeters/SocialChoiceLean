import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Reinforcement
import SocialChoice.Axioms.Participation
import SocialChoice.ListBallot
import SocialChoice.Rules.PluralityWithRunoff.CondorcetLoser

namespace SocialChoice

open Finset

/-!
# Plurality with Runoff fails subset reinforcement

We use a 3-candidate counterexample with two disjoint electorates:

- First electorate (8 voters):
  3 voters: a > c > b
  3 voters: c > b > a
  2 voters: b > a > c

- Second electorate (5 voters):
  3 voters: a > c > b
  2 voters: b > a > c

The combined profile (13 voters) yields b as the PWR (and IRV) winner,
while each subprofile yields a. Hence subset reinforcement fails.
-/

private abbrev A3 := Fin 3
private abbrev a : A3 := 0
private abbrev b : A3 := 1
private abbrev c : A3 := 2

def ballot_acb : ListBallot 3 := ListBallot.mk' [0, 2, 1]
def ballot_cba : ListBallot 3 := ListBallot.mk' [2, 1, 0]
def ballot_bac : ListBallot 3 := ListBallot.mk' [1, 0, 2]

def ballots13 : Fin 13 → ListBallot 3
  | 0 => ballot_acb
  | 1 => ballot_acb
  | 2 => ballot_acb
  | 3 => ballot_cba
  | 4 => ballot_cba
  | 5 => ballot_cba
  | 6 => ballot_bac
  | 7 => ballot_bac
  | 8 => ballot_acb
  | 9 => ballot_acb
  | 10 => ballot_acb
  | 11 => ballot_bac
  | 12 => ballot_bac
  | _ => ballot_bac

noncomputable def fullProfile : Profile (Electorate (Fin 13) (Finset.univ)) (Fin 3) :=
  profileOfListBallots (fun v => ballots13 v.1)

def voters8 : Finset (Fin 13) :=
  (Finset.univ.filter fun v : Fin 13 => v.val < 8)

def voters5 : Finset (Fin 13) :=
  (Finset.univ.filter fun v : Fin 13 => 8 ≤ v.val)

noncomputable def profile8 : Profile (Electorate (Fin 13) voters8) (Fin 3) :=
  restrictElectorate fullProfile voters8 (by
    intro x hx
    exact Finset.mem_univ x)

noncomputable def profile5 : Profile (Electorate (Fin 13) voters5) (Fin 3) :=
  restrictElectorate fullProfile voters5 (by
    intro x hx
    exact Finset.mem_univ x)

noncomputable def profileAll : Profile (Electorate (Fin 13) (voters8 ∪ voters5)) (Fin 3) :=
  restrictElectorate fullProfile (voters8 ∪ voters5) (by
    intro x hx
    exact Finset.mem_univ x)

private lemma powersetCard_eq_singleton_of_card_two {A : Type} [DecidableEq A]
    {S : Finset A} (hcard : S.card = 2) :
    S.powersetCard 2 = ({S} : Finset (Finset A)) := by
  apply Finset.ext
  intro T
  constructor
  · intro hT
    have hsubset : T ⊆ S := (Finset.mem_powersetCard.mp hT).1
    have hcardT : T.card = 2 := (Finset.mem_powersetCard.mp hT).2
    have hEq : T = S := by
      apply Finset.eq_of_subset_of_card_le hsubset
      simp [hcard, hcardT]
    simp [hEq]
  · intro hT
    have hEq : T = S := by simpa using hT
    subst hEq
    exact Finset.mem_powersetCard.mpr ⟨by intro x hx; exact hx, hcard⟩

def ballots8 (v : Electorate (Fin 13) voters8) : ListBallot 3 := ballots13 v.1
def ballots5 (v : Electorate (Fin 13) voters5) : ListBallot 3 := ballots13 v.1
def ballotsAll (v : Electorate (Fin 13) (voters8 ∪ voters5)) : ListBallot 3 := ballots13 v.1

private lemma profile8_eq : profile8 = profileOfListBallots ballots8 := by
  rfl

private lemma profile5_eq : profile5 = profileOfListBallots ballots5 := by
  rfl

private lemma profileAll_eq : profileAll = profileOfListBallots ballotsAll := by
  rfl

lemma voters8_disjoint_voters5 : Disjoint voters8 voters5 := by
  refine Finset.disjoint_left.2 ?_
  intro x hx8 hx5
  have hx8' : x.val < 8 := by
    simpa [voters8] using (Finset.mem_filter.mp hx8).2
  have hx5' : 8 ≤ x.val := by
    simpa [voters5] using (Finset.mem_filter.mp hx5).2
  exact (not_lt_of_ge hx5' hx8').elim

private lemma restrictElectorate_nested {U A : Type} [DecidableEq U] [Fintype A]
    {S T W : Finset U} (hST : S ⊆ T) (hTW : T ⊆ W)
    (Q : Profile (Electorate U W) A) :
    restrictElectorate (restrictElectorate Q T hTW) S hST =
      restrictElectorate Q S (by intro x hx; exact hTW (hST hx)) := by
  cases Q
  rfl

lemma restrict_profileAll_voters8 :
    restrictElectorate profileAll voters8
        (by intro x hx; exact Finset.mem_union.mpr (Or.inl hx)) =
      profile8 := by
  unfold profileAll profile8
  have hST : voters8 ⊆ voters8 ∪ voters5 := by
    intro x hx
    exact Finset.mem_union.mpr (Or.inl hx)
  have hTW : voters8 ∪ voters5 ⊆ (Finset.univ : Finset (Fin 13)) := by
    intro x hx
    exact Finset.mem_univ x
  simpa [hST, hTW] using
    (restrictElectorate_nested (U := Fin 13) (A := Fin 3)
      (S := voters8) (T := voters8 ∪ voters5) (W := Finset.univ) hST hTW fullProfile)

lemma restrict_profileAll_voters5 :
    restrictElectorate profileAll voters5
        (by intro x hx; exact Finset.mem_union.mpr (Or.inr hx)) =
      profile5 := by
  unfold profileAll profile5
  have hST : voters5 ⊆ voters8 ∪ voters5 := by
    intro x hx
    exact Finset.mem_union.mpr (Or.inr hx)
  have hTW : voters8 ∪ voters5 ⊆ (Finset.univ : Finset (Fin 13)) := by
    intro x hx
    exact Finset.mem_univ x
  simpa [hST, hTW] using
    (restrictElectorate_nested (U := Fin 13) (A := Fin 3)
      (S := voters5) (T := voters8 ∪ voters5) (W := Finset.univ) hST hTW fullProfile)

private lemma plurality_profile8_eq : plurality profile8 = ({a, c} : Finset (Fin 3)) := by
  rw [profile8_eq]
  simp only [plurality, topCount, votersTop_eq_filter_isTopOfList]
  decide

private lemma plurality_profile5_eq : plurality profile5 = ({a} : Finset (Fin 3)) := by
  rw [profile5_eq]
  simp only [plurality, topCount, votersTop_eq_filter_isTopOfList]
  decide

private lemma plurality_profileAll_eq : plurality profileAll = ({a} : Finset (Fin 3)) := by
  rw [profileAll_eq]
  simp only [plurality, topCount, votersTop_eq_filter_isTopOfList]
  decide

private lemma secondPlurality_profile5 :
    secondPluralitySet profile5 ({a} : Finset (Fin 3)) = ({b} : Finset (Fin 3)) := by
  rw [profile5_eq]
  simp [secondPluralitySet, topCount, votersTop_eq_filter_isTopOfList]
  decide

private lemma secondPlurality_profileAll :
    secondPluralitySet profileAll ({a} : Finset (Fin 3)) = ({b} : Finset (Fin 3)) := by
  rw [profileAll_eq]
  simp [secondPluralitySet, topCount, votersTop_eq_filter_isTopOfList]
  decide

private lemma pluralityWithRunoffPairs_profile8 :
    pluralityWithRunoffPairs profile8 =
      ({({a, c} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
  have hcardS : (plurality profile8).card = 2 := by
    simpa [plurality_profile8_eq] using
      (by decide : ({a, c} : Finset (Fin 3)).card = 2)
  have hS : (plurality profile8).card ≥ 2 := by
    simp [hcardS]
  have hpow :
      (plurality profile8).powersetCard 2 =
        ({plurality profile8} : Finset (Finset (Fin 3))) :=
    powersetCard_eq_singleton_of_card_two (S := plurality profile8) hcardS
  calc
    pluralityWithRunoffPairs profile8
        = (plurality profile8).powersetCard 2 := by
            simp [pluralityWithRunoffPairs, hS]
    _ = ({plurality profile8} : Finset (Finset (Fin 3))) := hpow
    _ = ({({a, c} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
          simp [plurality_profile8_eq]

private lemma pluralityWithRunoffPairs_profile5 :
    pluralityWithRunoffPairs profile5 =
      ({({a, b} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
  have hS : ¬ (plurality profile5).card ≥ 2 := by
    simp [plurality_profile5_eq]
  have hT :
      secondPluralitySet profile5 ({a} : Finset (Fin 3)) = ({b} : Finset (Fin 3)) := by
    simpa using secondPlurality_profile5
  calc
    pluralityWithRunoffPairs profile5
        = (Finset.image (fun p => ({p.1, p.2} : Finset (Fin 3)))
            (({a} : Finset (Fin 3)) ×ˢ secondPluralitySet profile5 {a})) := by
              simp [pluralityWithRunoffPairs, plurality_profile5_eq, -Finset.singleton_product]
    _ = (Finset.image (fun p => ({p.1, p.2} : Finset (Fin 3)))
            (({a} : Finset (Fin 3)) ×ˢ ({b} : Finset (Fin 3)))) := by
          simp [hT]
    _ = ({({a, b} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
          simp

private lemma pluralityWithRunoffPairs_profileAll :
    pluralityWithRunoffPairs profileAll =
      ({({a, b} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
  have hS : ¬ (plurality profileAll).card ≥ 2 := by
    simp [plurality_profileAll_eq]
  have hT :
      secondPluralitySet profileAll ({a} : Finset (Fin 3)) = ({b} : Finset (Fin 3)) := by
    simpa using secondPlurality_profileAll
  calc
    pluralityWithRunoffPairs profileAll
        = (Finset.image (fun p => ({p.1, p.2} : Finset (Fin 3)))
            (({a} : Finset (Fin 3)) ×ˢ secondPluralitySet profileAll {a})) := by
              simp [pluralityWithRunoffPairs, plurality_profileAll_eq, -Finset.singleton_product]
    _ = (Finset.image (fun p => ({p.1, p.2} : Finset (Fin 3)))
            (({a} : Finset (Fin 3)) ×ˢ ({b} : Finset (Fin 3)))) := by
          simp [hT]
    _ = ({({a, b} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
          simp

private lemma margin_profile8_a_c : margin profile8 a c = 2 := by
  rw [profile8_eq, margin_profileOfListBallots]
  decide

private lemma margin_profile8_c_a : margin profile8 c a = -2 := by
  have h := margin_antisymmetric (P := profile8) c a
  simpa [skew_symmetric, margin_profile8_a_c] using h

private lemma margin_profile5_a_b : margin profile5 a b = 1 := by
  rw [profile5_eq, margin_profileOfListBallots]
  decide

private lemma margin_profile5_b_a : margin profile5 b a = -1 := by
  have h := margin_antisymmetric (P := profile5) b a
  simpa [skew_symmetric, margin_profile5_a_b] using h

private lemma margin_profileAll_a_b : margin profileAll a b = -1 := by
  rw [profileAll_eq, margin_profileOfListBallots]
  decide

private lemma margin_profileAll_b_a : margin profileAll b a = 1 := by
  have h := margin_antisymmetric (P := profileAll) b a
  simpa [skew_symmetric, margin_profileAll_a_b] using h

lemma pluralityWithRunoff_profile8 :
    pluralityWithRunoff profile8 = ({a} : Finset (Fin 3)) := by
  have hcard : ¬ Fintype.card (Fin 3) <= 1 := by decide
  apply Finset.ext
  intro x
  fin_cases x
  · constructor
    · intro _; simp
    · intro _
      exact (mem_pluralityWithRunoff_iff (P := profile8) (x := a) (hcard := hcard)).2
        ⟨c, by simp [pluralityWithRunoffPairs_profile8], by simp [margin_profile8_a_c]⟩
  · constructor
    · intro hx
      have hfalse : False := by
        rcases (mem_pluralityWithRunoff_iff (P := profile8) (x := b) (hcard := hcard)).1 hx with
          ⟨y, hy, _⟩
        fin_cases y
        ·
          have hy' :
              ({b, (0 : Fin 3)} : Finset (Fin 3)) = ({a, c} : Finset (Fin 3)) := by
            simpa [pluralityWithRunoffPairs_profile8] using hy
          have hne :
              ({b, (0 : Fin 3)} : Finset (Fin 3)) ≠ ({a, c} : Finset (Fin 3)) := by
            decide
          exact (hne hy').elim
        ·
          have hy' :
              ({b, (1 : Fin 3)} : Finset (Fin 3)) = ({a, c} : Finset (Fin 3)) := by
            simpa [pluralityWithRunoffPairs_profile8] using hy
          have hne :
              ({b, (1 : Fin 3)} : Finset (Fin 3)) ≠ ({a, c} : Finset (Fin 3)) := by
            decide
          exact (hne hy').elim
        ·
          have hy' :
              ({b, (2 : Fin 3)} : Finset (Fin 3)) = ({a, c} : Finset (Fin 3)) := by
            simpa [pluralityWithRunoffPairs_profile8] using hy
          have hne :
              ({b, (2 : Fin 3)} : Finset (Fin 3)) ≠ ({a, c} : Finset (Fin 3)) := by
            decide
          exact (hne hy').elim
      exact hfalse.elim
    · intro hx
      exfalso
      have hne : (b : Fin 3) ≠ a := by decide
      have hx' : (b : Fin 3) = a := by
        simp at hx
      exact hne hx'
  · constructor
    · intro hx
      have hfalse : False := by
        rcases (mem_pluralityWithRunoff_iff (P := profile8) (x := c) (hcard := hcard)).1 hx with
          ⟨y, hy, hmargin⟩
        fin_cases y
        · simp [margin_profile8_c_a] at hmargin
        ·
          have hy' :
              ({c, (1 : Fin 3)} : Finset (Fin 3)) = ({a, c} : Finset (Fin 3)) := by
            simpa [pluralityWithRunoffPairs_profile8] using hy
          have hne :
              ({c, (1 : Fin 3)} : Finset (Fin 3)) ≠ ({a, c} : Finset (Fin 3)) := by
            decide
          exact (hne hy').elim
        ·
          have hy' :
              ({c, (2 : Fin 3)} : Finset (Fin 3)) = ({a, c} : Finset (Fin 3)) := by
            simpa [pluralityWithRunoffPairs_profile8] using hy
          have hne :
              ({c, (2 : Fin 3)} : Finset (Fin 3)) ≠ ({a, c} : Finset (Fin 3)) := by
            decide
          exact (hne hy').elim
      exact hfalse.elim
    · intro hx
      exfalso
      have hne : (c : Fin 3) ≠ a := by decide
      have hx' : (c : Fin 3) = a := by simpa using hx
      exact hne hx'

lemma pluralityWithRunoff_profile5 :
    pluralityWithRunoff profile5 = ({a} : Finset (Fin 3)) := by
  have hcard : ¬ Fintype.card (Fin 3) <= 1 := by decide
  apply Finset.ext
  intro x
  fin_cases x
  · constructor
    · intro _; simp
    · intro _
      exact (mem_pluralityWithRunoff_iff (P := profile5) (x := a) (hcard := hcard)).2
        ⟨b, by simp [pluralityWithRunoffPairs_profile5], by simp [margin_profile5_a_b]⟩
  · constructor
    · intro hx
      have hfalse : False := by
        rcases (mem_pluralityWithRunoff_iff (P := profile5) (x := b) (hcard := hcard)).1 hx with
          ⟨y, hy, hmargin⟩
        fin_cases y
        · simp [margin_profile5_b_a] at hmargin
        ·
          have hy' :
              ({b, (1 : Fin 3)} : Finset (Fin 3)) = ({a, b} : Finset (Fin 3)) := by
            simpa [pluralityWithRunoffPairs_profile5] using hy
          have hne :
              ({b, (1 : Fin 3)} : Finset (Fin 3)) ≠ ({a, b} : Finset (Fin 3)) := by
            decide
          exact (hne hy').elim
        ·
          have hy' :
              ({b, (2 : Fin 3)} : Finset (Fin 3)) = ({a, b} : Finset (Fin 3)) := by
            simpa [pluralityWithRunoffPairs_profile5] using hy
          have hne :
              ({b, (2 : Fin 3)} : Finset (Fin 3)) ≠ ({a, b} : Finset (Fin 3)) := by
            decide
          exact (hne hy').elim
      exact hfalse.elim
    · intro hx
      exfalso
      have hne : (b : Fin 3) ≠ a := by decide
      have hx' : (b : Fin 3) = a := by
        simp at hx
      exact hne hx'
  · constructor
    · intro hx
      have hfalse : False := by
        rcases (mem_pluralityWithRunoff_iff (P := profile5) (x := c) (hcard := hcard)).1 hx with
          ⟨y, hy, _⟩
        fin_cases y
        ·
          have hy' :
              ({c, (0 : Fin 3)} : Finset (Fin 3)) = ({a, b} : Finset (Fin 3)) := by
            simpa [pluralityWithRunoffPairs_profile5] using hy
          have hne :
              ({c, (0 : Fin 3)} : Finset (Fin 3)) ≠ ({a, b} : Finset (Fin 3)) := by
            decide
          exact (hne hy').elim
        ·
          have hy' :
              ({c, (1 : Fin 3)} : Finset (Fin 3)) = ({a, b} : Finset (Fin 3)) := by
            simpa [pluralityWithRunoffPairs_profile5] using hy
          have hne :
              ({c, (1 : Fin 3)} : Finset (Fin 3)) ≠ ({a, b} : Finset (Fin 3)) := by
            decide
          exact (hne hy').elim
        ·
          have hy' :
              ({c, (2 : Fin 3)} : Finset (Fin 3)) = ({a, b} : Finset (Fin 3)) := by
            simpa [pluralityWithRunoffPairs_profile5] using hy
          have hne :
              ({c, (2 : Fin 3)} : Finset (Fin 3)) ≠ ({a, b} : Finset (Fin 3)) := by
            decide
          exact (hne hy').elim
      exact hfalse.elim
    · intro hx
      exfalso
      have hne : (c : Fin 3) ≠ a := by decide
      have hx' : (c : Fin 3) = a := by simpa using hx
      exact hne hx'

lemma pluralityWithRunoff_profileAll :
    pluralityWithRunoff profileAll = ({b} : Finset (Fin 3)) := by
  have hcard : ¬ Fintype.card (Fin 3) <= 1 := by decide
  apply Finset.ext
  intro x
  fin_cases x
  · constructor
    · intro hx
      have hfalse : False := by
        rcases (mem_pluralityWithRunoff_iff (P := profileAll) (x := a) (hcard := hcard)).1 hx with
          ⟨y, hy, hmargin⟩
        fin_cases y
        ·
          have hy' :
              ({a, (0 : Fin 3)} : Finset (Fin 3)) = ({a, b} : Finset (Fin 3)) := by
            simpa [pluralityWithRunoffPairs_profileAll] using hy
          have hne :
              ({a, (0 : Fin 3)} : Finset (Fin 3)) ≠ ({a, b} : Finset (Fin 3)) := by
            decide
          exact (hne hy').elim
        · simp [margin_profileAll_a_b] at hmargin
        ·
          have hy' :
              ({a, (2 : Fin 3)} : Finset (Fin 3)) = ({a, b} : Finset (Fin 3)) := by
            simpa [pluralityWithRunoffPairs_profileAll] using hy
          have hne :
              ({a, (2 : Fin 3)} : Finset (Fin 3)) ≠ ({a, b} : Finset (Fin 3)) := by
            decide
          exact (hne hy').elim
      exact hfalse.elim
    · intro hx
      exfalso
      have hne : (a : Fin 3) ≠ b := by decide
      have hx' : (a : Fin 3) = b := by
        simp at hx
      exact hne hx'
  · constructor
    · intro _; simp
    · intro _
      exact (mem_pluralityWithRunoff_iff (P := profileAll) (x := b) (hcard := hcard)).2
        ⟨a, by simp [pluralityWithRunoffPairs_profileAll, Finset.pair_comm],
          by simp [margin_profileAll_b_a]⟩
  · constructor
    · intro hx
      have hfalse : False := by
        rcases (mem_pluralityWithRunoff_iff (P := profileAll) (x := c) (hcard := hcard)).1 hx with
          ⟨y, hy, _⟩
        fin_cases y
        ·
          have hy' :
              ({c, (0 : Fin 3)} : Finset (Fin 3)) = ({a, b} : Finset (Fin 3)) := by
            simpa [pluralityWithRunoffPairs_profileAll] using hy
          have hne :
              ({c, (0 : Fin 3)} : Finset (Fin 3)) ≠ ({a, b} : Finset (Fin 3)) := by
            decide
          exact (hne hy').elim
        ·
          have hy' :
              ({c, (1 : Fin 3)} : Finset (Fin 3)) = ({a, b} : Finset (Fin 3)) := by
            simpa [pluralityWithRunoffPairs_profileAll] using hy
          have hne :
              ({c, (1 : Fin 3)} : Finset (Fin 3)) ≠ ({a, b} : Finset (Fin 3)) := by
            decide
          exact (hne hy').elim
        ·
          have hy' :
              ({c, (2 : Fin 3)} : Finset (Fin 3)) = ({a, b} : Finset (Fin 3)) := by
            simpa [pluralityWithRunoffPairs_profileAll] using hy
          have hne :
              ({c, (2 : Fin 3)} : Finset (Fin 3)) ≠ ({a, b} : Finset (Fin 3)) := by
            decide
          exact (hne hy').elim
      exact hfalse.elim
    · intro hx
      exfalso
      have hne : (c : Fin 3) ≠ b := by decide
      have hx' := hx
      simp at hx'
      exact hne hx'

theorem pluralityWithRunoff_subsetReinforcement_counterexample_sets :
    ¬ (pluralityWithRunoff profile8 ∩ pluralityWithRunoff profile5 ⊆
        pluralityWithRunoff profileAll) := by
  intro hsubset
  have ha : (a : Fin 3) ∈ pluralityWithRunoff profile8 ∩ pluralityWithRunoff profile5 := by
    simp [pluralityWithRunoff_profile8, pluralityWithRunoff_profile5]
  have ha' : (a : Fin 3) = b := by
    simpa [pluralityWithRunoff_profileAll] using hsubset ha
  exact (by decide : (a : Fin 3) ≠ b) ha'

theorem pluralityWithRunoff_not_subsetReinforcement : ¬ SubsetReinforcement pluralityWithRunoff := by
  intro hsub
  have hsubset := hsub (U := Fin 13) (A := Fin 3)
    (V := voters8) (W := voters5) (hdisj := voters8_disjoint_voters5)
    (P := profile8) (Q := profile5) (R := profileAll)
    restrict_profileAll_voters8 restrict_profileAll_voters5
  exact pluralityWithRunoff_subsetReinforcement_counterexample_sets hsubset

end SocialChoice
