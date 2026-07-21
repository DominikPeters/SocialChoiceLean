import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Participation
import SocialChoice.ListBallot
import SocialChoice.Rules.Black.Condorcet
import SocialChoice.Rules.Black.Defs

namespace SocialChoice

open Finset

open Classical
attribute [instance] Classical.decEq

set_option maxHeartbeats 5000000

/-!
# Black fails singleton positive involvement

Counterexample with 3 candidates (0=a, 1=b, 2=c) and 8+1 voters:

Initial profile (8 voters):
4 voters: a > b > c
3 voters: b > c > a
1 voter : c > a > b
Black selects {b}.

Add one voter with ballot b > a > c.
Black selects {a}.
-/

namespace BlackSingletonPositiveInvolvementCounterexample

def ballotABC : ListBallot 3 := ListBallot.mk' [0, 1, 2]
def ballotBCA : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballotCAB : ListBallot 3 := ListBallot.mk' [2, 0, 1]
def ballotBAC : ListBallot 3 := ListBallot.mk' [1, 0, 2]

def ballots9 : Fin 9 → ListBallot 3
  | ⟨0, _⟩ => ballotABC
  | ⟨1, _⟩ => ballotABC
  | ⟨2, _⟩ => ballotABC
  | ⟨3, _⟩ => ballotABC
  | ⟨4, _⟩ => ballotBCA
  | ⟨5, _⟩ => ballotBCA
  | ⟨6, _⟩ => ballotBCA
  | ⟨7, _⟩ => ballotCAB
  | ⟨8, _⟩ => ballotBAC

def voters8 : Finset (Fin 9) :=
  {0, 1, 2, 3, 4, 5, 6, 7}

noncomputable def fullProfile : Profile (Electorate (Fin 9) (Finset.univ)) (Fin 3) :=
  { pref := fun v => (ballots9 v.1).toLinearOrder }

noncomputable def profile8 : Profile (Electorate (Fin 9) voters8) (Fin 3) :=
  restrictElectorate fullProfile voters8 (by
    intro x hx; exact (Finset.mem_univ x))

noncomputable def profile9 :
    Profile (Electorate (Fin 9) (insert (8 : Fin 9) voters8)) (Fin 3) :=
  restrictElectorate fullProfile (insert (8 : Fin 9) voters8) (by
    intro x hx; exact (Finset.mem_univ x))

lemma voters8_not_mem : (8 : Fin 9) ∉ voters8 := by
  simp [voters8]

lemma profiles_agree :
    ∀ v : Electorate (Fin 9) voters8,
      profile9.pref (liftVoter (u := (8 : Fin 9)) v) = profile8.pref v := by
  intro v
  simpa [profile8, profile9] using
    (restrictElectorate_agrees (Q := fullProfile) (S := voters8)
      (hS := by intro x hx; exact (Finset.mem_univ x))
      (u := (8 : Fin 9))
      (hSu := by intro x hx; exact (Finset.mem_univ x)) v)

lemma ballotBAC_top_b : BallotTop ballotBAC.toLinearOrder (1 : Fin 3) := by
  intro x hx
  fin_cases x <;> simp [ballotBAC, ListBallot.lt_iff_idxOf, ListBallot.mk'] at hx ⊢

lemma newVoter_top_b :
    BallotTop
      (profile9.pref (newVoter (u := (8 : Fin 9)) (V := voters8) voters8_not_mem))
      (1 : Fin 3) := by
  have hpref :
      profile9.pref (newVoter (u := (8 : Fin 9)) (V := voters8) voters8_not_mem) =
        ballotBAC.toLinearOrder := by
    simp [profile9, fullProfile, restrictElectorate, ballots9, newVoter]
  simpa [hpref] using ballotBAC_top_b

lemma voters8_card : (#voters8 : Nat) = 8 := by
  simp [voters8]

lemma voters9_card : (#(insert (8 : Fin 9) voters8) : Nat) = 9 := by
  simp [voters8]

private lemma votersPreferring_profile8_eq_filter (x y : Fin 3) :
    votersPreferring profile8 x y =
      Finset.univ.filter (fun v => prefersInList (ballots9 v.1).ranking x y) := by
  ext v
  simp only [votersPreferring, Finset.mem_filter, Finset.mem_univ, true_and]
  change Prefers (profileOfListBallots ballots9) v.1 x y ↔ _
  exact prefers_iff_prefersInList ballots9 v.1 x y

private lemma votersPreferring_profile9_eq_filter (x y : Fin 3) :
    votersPreferring profile9 x y =
      Finset.univ.filter (fun v => prefersInList (ballots9 v.1).ranking x y) := by
  ext v
  simp only [votersPreferring, Finset.mem_filter, Finset.mem_univ, true_and]
  change Prefers (profileOfListBallots ballots9) v.1 x y ↔ _
  exact prefers_iff_prefersInList ballots9 v.1 x y

lemma votersPreferring_profile8_0_2 :
    votersPreferring profile8 (0 : Fin 3) (2 : Fin 3) =
      ({⟨0, by simp [voters8]⟩,
        ⟨1, by simp [voters8]⟩,
        ⟨2, by simp [voters8]⟩,
        ⟨3, by simp [voters8]⟩} :
        Finset (Electorate (Fin 9) voters8)) := by
  classical
  rw [votersPreferring_profile8_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [ballots9, ballotABC, ballotBCA, ballotCAB, ballotBAC, voters8,
          prefersInList] at hmem ⊢ <;> decide +revert)

lemma votersPreferring_profile8_1_0 :
    votersPreferring profile8 (1 : Fin 3) (0 : Fin 3) =
      ({⟨4, by simp [voters8]⟩,
        ⟨5, by simp [voters8]⟩,
        ⟨6, by simp [voters8]⟩} :
        Finset (Electorate (Fin 9) voters8)) := by
  classical
  rw [votersPreferring_profile8_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [ballots9, ballotABC, ballotBCA, ballotCAB, ballotBAC, voters8,
          prefersInList] at hmem ⊢ <;> decide +revert)

lemma votersPreferring_profile8_2_1 :
    votersPreferring profile8 (2 : Fin 3) (1 : Fin 3) =
      ({⟨7, by simp [voters8]⟩} :
        Finset (Electorate (Fin 9) voters8)) := by
  classical
  rw [votersPreferring_profile8_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [ballots9, ballotABC, ballotBCA, ballotCAB, ballotBAC, voters8,
          prefersInList] at hmem ⊢ <;> decide +revert)

lemma votersPreferring_profile9_0_1 :
    votersPreferring profile9 (0 : Fin 3) (1 : Fin 3) =
      ({⟨0, by simp [voters8]⟩,
        ⟨1, by simp [voters8]⟩,
        ⟨2, by simp [voters8]⟩,
        ⟨3, by simp [voters8]⟩,
        ⟨7, by simp [voters8]⟩} :
        Finset (Electorate (Fin 9) (insert (8 : Fin 9) voters8))) := by
  classical
  rw [votersPreferring_profile9_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [ballots9, ballotABC, ballotBCA, ballotCAB, ballotBAC, voters8,
          prefersInList] at hmem ⊢; decide +revert)

lemma votersPreferring_profile9_0_2 :
    votersPreferring profile9 (0 : Fin 3) (2 : Fin 3) =
      ({⟨0, by simp [voters8]⟩,
        ⟨1, by simp [voters8]⟩,
        ⟨2, by simp [voters8]⟩,
        ⟨3, by simp [voters8]⟩,
        ⟨8, by simp [voters8]⟩} :
        Finset (Electorate (Fin 9) (insert (8 : Fin 9) voters8))) := by
  classical
  rw [votersPreferring_profile9_eq_filter]
  ext v
  cases v with
  | mk val hmem =>
      fin_cases val <;>
        (simp [ballots9, ballotABC, ballotBCA, ballotCAB, ballotBAC, voters8,
          prefersInList] at hmem ⊢; decide +revert)

lemma not_strictMajority_profile8_0_2 :
    ¬ StrictMajority (votersPreferring profile8 (0 : Fin 3) (2 : Fin 3)) := by
  classical
  have hcard : (votersPreferring profile8 (0 : Fin 3) (2 : Fin 3)).card = 4 := by
    simp [votersPreferring_profile8_0_2]
  simp [StrictMajority, hcard, voters8_card]

lemma not_strictMajority_profile8_1_0 :
    ¬ StrictMajority (votersPreferring profile8 (1 : Fin 3) (0 : Fin 3)) := by
  classical
  have hcard : (votersPreferring profile8 (1 : Fin 3) (0 : Fin 3)).card = 3 := by
    simp [votersPreferring_profile8_1_0]
  simp [StrictMajority, hcard, voters8_card]

lemma not_strictMajority_profile8_2_1 :
    ¬ StrictMajority (votersPreferring profile8 (2 : Fin 3) (1 : Fin 3)) := by
  classical
  have hcard : (votersPreferring profile8 (2 : Fin 3) (1 : Fin 3)).card = 1 := by
    simp [votersPreferring_profile8_2_1]
  simp [StrictMajority, hcard, voters8_card]

lemma no_condorcet_profile8 : ¬ ∃ x, CondorcetWinner profile8 x := by
  intro h
  rcases h with ⟨x, hx⟩
  fin_cases x
  · have hmaj := hx (2 : Fin 3) (by decide +revert)
    exact (not_strictMajority_profile8_0_2 hmaj).elim
  · have hmaj := hx (0 : Fin 3) (by decide +revert)
    exact (not_strictMajority_profile8_1_0 hmaj).elim
  · have hmaj := hx (1 : Fin 3) (by decide +revert)
    exact (not_strictMajority_profile8_2_1 hmaj).elim

lemma strictMajority_profile9_0_1 :
    StrictMajority (votersPreferring profile9 (0 : Fin 3) (1 : Fin 3)) := by
  classical
  have hcard :
      (votersPreferring profile9 (0 : Fin 3) (1 : Fin 3)).card = 5 := by
    simp [votersPreferring_profile9_0_1]
  simp [StrictMajority, hcard, voters9_card]

lemma strictMajority_profile9_0_2 :
    StrictMajority (votersPreferring profile9 (0 : Fin 3) (2 : Fin 3)) := by
  classical
  have hcard :
      (votersPreferring profile9 (0 : Fin 3) (2 : Fin 3)).card = 5 := by
    simp [votersPreferring_profile9_0_2]
  simp [StrictMajority, hcard, voters9_card]

lemma condorcet_profile9 : CondorcetWinner profile9 (0 : Fin 3) := by
  intro d hne
  fin_cases d
  · cases hne rfl
  · simpa using strictMajority_profile9_0_1
  · simpa using strictMajority_profile9_0_2

lemma black_profile8 : black profile8 = ({1} : Finset (Fin 3)) := by
  have h : ¬ ∃ x, CondorcetWinner profile8 x := no_condorcet_profile8
  have hborda : borda profile8 = ({1} : Finset (Fin 3)) := by
    decide
  simp [black, h, hborda]

lemma black_profile9 : black profile9 = ({0} : Finset (Fin 3)) := by
  have h : ∃ x, CondorcetWinner profile9 x := ⟨0, condorcet_profile9⟩
  have hchoose : Classical.choose h = (0 : Fin 3) := by
    exact CondorcetWinner_unique (P := profile9)
      (hx := Classical.choose_spec h) (hy := condorcet_profile9)
  simp [black, h, hchoose]

end BlackSingletonPositiveInvolvementCounterexample

open BlackSingletonPositiveInvolvementCounterexample

theorem black_not_singletonPositiveInvolvement : ¬ SingletonPositiveInvolvement black := by
  intro hpos
  classical
  have hmem :
      (1 : Fin 3) ∈ black profile9 := by
    exact hpos (V := voters8) (u := (8 : Fin 9)) (hu := voters8_not_mem)
      (P := profile8) (Q := profile9) (c := (1 : Fin 3))
      profiles_agree black_profile8 newVoter_top_b
  have hfalse : False := by
    simp [black_profile9] at hmem
  exact hfalse

end SocialChoice
