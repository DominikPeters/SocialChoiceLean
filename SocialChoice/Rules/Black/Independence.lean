import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Independence
import SocialChoice.Axioms.Clones
import SocialChoice.ListBallot
import SocialChoice.Rules.Black.Defs

namespace SocialChoice

open Finset

/-!
## Black fails independence of dominated

Counterexample with 3 candidates (0,1,2) and 2 voters:
v0: 1 > 2 > 0
v1: 2 > 0 > 1
Candidate 2 Pareto-dominates 0.
Black selects {2}, but after removing 0, Black selects {1,2}.
-/

namespace BlackIndependenceCounterexample

def ballot120 : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballot201 : ListBallot 3 := ListBallot.mk' [2, 0, 1]

def ballots : Fin 2 → ListBallot 3
  | ⟨0, _⟩ => ballot120
  | ⟨1, _⟩ => ballot201

noncomputable def profile : Profile (Fin 2) (Fin 3) :=
  profileOfListBallots ballots

lemma prefers_2_0 : ∀ v : Fin 2, Prefers profile v (2 : Fin 3) (0 : Fin 3) := by
  simp only [profile, prefers_iff_prefersInList]
  decide

noncomputable def profile' : Profile (Fin 2) {x : Fin 3 // x ≠ (0 : Fin 3)} :=
  restrictProfile profile (0 : Fin 3)

def cand1 : {x : Fin 3 // x ≠ (0 : Fin 3)} := ⟨1, by decide⟩
def cand2 : {x : Fin 3 // x ≠ (0 : Fin 3)} := ⟨2, by decide⟩

lemma votersPreferring_profile_1_2 :
    votersPreferring profile (1 : Fin 3) (2 : Fin 3) = ({0} : Finset (Fin 2)) := by
  rw [profile, votersPreferring_eq_filter_prefersInList]
  decide

lemma votersPreferring_profile_2_1 :
    votersPreferring profile (2 : Fin 3) (1 : Fin 3) = ({1} : Finset (Fin 2)) := by
  rw [profile, votersPreferring_eq_filter_prefersInList]
  decide

lemma votersPreferring_profile_0_2 :
    votersPreferring profile (0 : Fin 3) (2 : Fin 3) = (∅ : Finset (Fin 2)) := by
  rw [profile, votersPreferring_eq_filter_prefersInList]
  decide

lemma not_strictMajority_profile_1_2 :
    ¬ StrictMajority (votersPreferring profile (1 : Fin 3) (2 : Fin 3)) := by
  simp [StrictMajority, votersPreferring_profile_1_2]

lemma not_strictMajority_profile_2_1 :
    ¬ StrictMajority (votersPreferring profile (2 : Fin 3) (1 : Fin 3)) := by
  simp [StrictMajority, votersPreferring_profile_2_1]

lemma not_strictMajority_profile_0_2 :
    ¬ StrictMajority (votersPreferring profile (0 : Fin 3) (2 : Fin 3)) := by
  simp [StrictMajority, votersPreferring_profile_0_2]

lemma votersPreferring_restrict_cand1 :
    votersPreferring profile' cand1 cand2 = votersPreferring profile (1 : Fin 3) (2 : Fin 3) := by
  ext v
  simp [profile', cand1, cand2]

lemma votersPreferring_restrict_cand2 :
    votersPreferring profile' cand2 cand1 = votersPreferring profile (2 : Fin 3) (1 : Fin 3) := by
  ext v
  simp [profile', cand1, cand2]

lemma not_strictMajority_profile'_1_2 :
    ¬ StrictMajority (votersPreferring profile' cand1 cand2) := by
  simpa [votersPreferring_restrict_cand1] using not_strictMajority_profile_1_2

lemma not_strictMajority_profile'_2_1 :
    ¬ StrictMajority (votersPreferring profile' cand2 cand1) := by
  simpa [votersPreferring_restrict_cand2] using not_strictMajority_profile_2_1

lemma no_condorcet_profile : ¬ ∃ x, CondorcetWinner profile x := by
  intro h
  rcases h with ⟨x, hx⟩
  fin_cases x
  · have hmaj := hx (2 : Fin 3) (by decide)
    exact (not_strictMajority_profile_0_2 hmaj).elim
  · have hmaj := hx (2 : Fin 3) (by decide)
    exact (not_strictMajority_profile_1_2 hmaj).elim
  · have hmaj := hx (1 : Fin 3) (by decide)
    exact (not_strictMajority_profile_2_1 hmaj).elim

lemma no_condorcet_profile' : ¬ ∃ x, CondorcetWinner profile' x := by
  intro h
  rcases h with ⟨x, hx⟩
  rcases x with ⟨x, hxne⟩
  fin_cases x
  · cases hxne rfl
  · have hne : cand2 ≠ (⟨1, hxne⟩ : {x : Fin 3 // x ≠ (0 : Fin 3)}) := by
      intro hEq
      have hval : (2 : Fin 3) = 1 := by
        exact congrArg Subtype.val hEq
      cases hval
    have hmaj := hx cand2 hne
    have hx' : (⟨1, hxne⟩ : {x : Fin 3 // x ≠ (0 : Fin 3)}) = cand1 := by
      apply Subtype.ext
      rfl
    have hmaj' : StrictMajority (votersPreferring profile' cand1 cand2) := by
      simpa [hx'] using hmaj
    exact (not_strictMajority_profile'_1_2 hmaj').elim
  · have hne : cand1 ≠ (⟨2, hxne⟩ : {x : Fin 3 // x ≠ (0 : Fin 3)}) := by
      intro hEq
      have hval : (1 : Fin 3) = 2 := by
        exact congrArg Subtype.val hEq
      cases hval
    have hmaj := hx cand1 hne
    have hx' : (⟨2, hxne⟩ : {x : Fin 3 // x ≠ (0 : Fin 3)}) = cand2 := by
      apply Subtype.ext
      rfl
    have hmaj' : StrictMajority (votersPreferring profile' cand2 cand1) := by
      simpa [hx'] using hmaj
    exact (not_strictMajority_profile'_2_1 hmaj').elim

lemma borda_profile_not_1 : (1 : Fin 3) ∉ borda profile := by
  decide

lemma borda_profile'_has_1 : cand1 ∈ borda profile' := by
  decide

lemma black_profile_not_1 : (1 : Fin 3) ∉ black profile := by
  have h : ¬ ∃ x, CondorcetWinner profile x := no_condorcet_profile
  simpa [black, h] using borda_profile_not_1

lemma black_profile'_has_1 : cand1 ∈ black profile' := by
  have h : ¬ ∃ x, CondorcetWinner profile' x := no_condorcet_profile'
  simpa [black, h] using borda_profile'_has_1

lemma lift_black_profile'_has_1 : (1 : Fin 3) ∈ liftWinners (black profile') := by
  have h : cand1 ∈ black profile' := black_profile'_has_1
  simpa [liftWinners, cand1] using h

end BlackIndependenceCounterexample

open BlackIndependenceCounterexample

theorem black_not_independenceOfDominated : ¬ IndependenceOfDominated black := by
  intro hind
  have hpref : ∀ v : Fin 2, Prefers profile v (2 : Fin 3) (0 : Fin 3) :=
    prefers_2_0
  have hEq := hind (P := profile) (c := (2 : Fin 3)) (d := (0 : Fin 3)) hpref
  have hmem :
      (1 : Fin 3) ∈
        liftWinners (black (restrictCandidates profile (fun a => a ≠ (0 : Fin 3)))) := by
    simpa [profile', restrictProfile] using lift_black_profile'_has_1
  have hmem' : (1 : Fin 3) ∈ black profile := by
    simpa [hEq] using hmem
  exact (black_profile_not_1 hmem').elim

/-!
## Black fails independence of clones

Counterexample with 3 candidates (0,1,2) and 4 voters:
v0: 0 > 2 > 1
v1: 1 > 2 > 0
v2: 1 > 2 > 0
v3: 2 > 0 > 1
Clone set {0,2}. Black selects {2}, but after removing clone 0,
Black selects {1,2}.
-/

namespace BlackClonesCounterexample

def ballot021 : ListBallot 3 := ListBallot.mk' [0, 2, 1]
def ballot120 : ListBallot 3 := ListBallot.mk' [1, 2, 0]
def ballot201 : ListBallot 3 := ListBallot.mk' [2, 0, 1]

def ballots : Fin 4 → ListBallot 3
  | ⟨0, _⟩ => ballot021
  | ⟨1, _⟩ => ballot120
  | ⟨2, _⟩ => ballot120
  | ⟨3, _⟩ => ballot201

noncomputable def profile : Profile (Fin 4) (Fin 3) :=
  profileOfListBallots ballots

noncomputable def profile' : Profile (Fin 4) {x : Fin 3 // x ≠ (0 : Fin 3)} :=
  restrictProfile profile (0 : Fin 3)

def cand1 : {x : Fin 3 // x ≠ (0 : Fin 3)} := ⟨1, by decide⟩
def cand2 : {x : Fin 3 // x ≠ (0 : Fin 3)} := ⟨2, by decide⟩

lemma votersPreferring_profile_0_2 :
    votersPreferring profile (0 : Fin 3) (2 : Fin 3) = ({0} : Finset (Fin 4)) := by
  rw [profile, votersPreferring_eq_filter_prefersInList]
  decide

lemma votersPreferring_profile_1_2 :
    votersPreferring profile (1 : Fin 3) (2 : Fin 3) = ({1, 2} : Finset (Fin 4)) := by
  rw [profile, votersPreferring_eq_filter_prefersInList]
  decide

lemma votersPreferring_profile_2_1 :
    votersPreferring profile (2 : Fin 3) (1 : Fin 3) = ({0, 3} : Finset (Fin 4)) := by
  rw [profile, votersPreferring_eq_filter_prefersInList]
  decide

lemma not_strictMajority_profile_0_2 :
    ¬ StrictMajority (votersPreferring profile (0 : Fin 3) (2 : Fin 3)) := by
  simp [StrictMajority, votersPreferring_profile_0_2]

lemma not_strictMajority_profile_1_2 :
    ¬ StrictMajority (votersPreferring profile (1 : Fin 3) (2 : Fin 3)) := by
  simp [StrictMajority, votersPreferring_profile_1_2]

lemma not_strictMajority_profile_2_1 :
    ¬ StrictMajority (votersPreferring profile (2 : Fin 3) (1 : Fin 3)) := by
  simp [StrictMajority, votersPreferring_profile_2_1]

lemma votersPreferring_profile'_1_2 :
    votersPreferring profile' cand1 cand2 = votersPreferring profile (1 : Fin 3) (2 : Fin 3) := by
  ext v
  simp [profile', cand1, cand2]

lemma votersPreferring_profile'_2_1 :
    votersPreferring profile' cand2 cand1 = votersPreferring profile (2 : Fin 3) (1 : Fin 3) := by
  ext v
  simp [profile', cand1, cand2]

lemma not_strictMajority_profile'_1_2 :
    ¬ StrictMajority (votersPreferring profile' cand1 cand2) := by
  simpa [votersPreferring_profile'_1_2] using not_strictMajority_profile_1_2

lemma not_strictMajority_profile'_2_1 :
    ¬ StrictMajority (votersPreferring profile' cand2 cand1) := by
  simpa [votersPreferring_profile'_2_1] using not_strictMajority_profile_2_1

lemma no_condorcet_profile : ¬ ∃ x, CondorcetWinner profile x := by
  intro h
  rcases h with ⟨x, hx⟩
  fin_cases x
  · have hmaj := hx (2 : Fin 3) (by decide)
    exact (not_strictMajority_profile_0_2 hmaj).elim
  · have hmaj := hx (2 : Fin 3) (by decide)
    exact (not_strictMajority_profile_1_2 hmaj).elim
  · have hmaj := hx (1 : Fin 3) (by decide)
    exact (not_strictMajority_profile_2_1 hmaj).elim

lemma no_condorcet_profile' : ¬ ∃ x, CondorcetWinner profile' x := by
  intro h
  rcases h with ⟨x, hx⟩
  rcases x with ⟨x, hxne⟩
  fin_cases x
  · cases hxne rfl
  · have hne : cand2 ≠ (⟨1, hxne⟩ : {x : Fin 3 // x ≠ (0 : Fin 3)}) := by
      intro hEq
      have hval : (2 : Fin 3) = 1 := by
        exact congrArg Subtype.val hEq
      cases hval
    have hmaj := hx cand2 hne
    have hx' : (⟨1, hxne⟩ : {x : Fin 3 // x ≠ (0 : Fin 3)}) = cand1 := by
      apply Subtype.ext
      rfl
    have hmaj' : StrictMajority (votersPreferring profile' cand1 cand2) := by
      simpa [hx'] using hmaj
    exact (not_strictMajority_profile'_1_2 hmaj').elim
  · have hne : cand1 ≠ (⟨2, hxne⟩ : {x : Fin 3 // x ≠ (0 : Fin 3)}) := by
      intro hEq
      have hval : (1 : Fin 3) = 2 := by
        exact congrArg Subtype.val hEq
      cases hval
    have hmaj := hx cand1 hne
    have hx' : (⟨2, hxne⟩ : {x : Fin 3 // x ≠ (0 : Fin 3)}) = cand2 := by
      apply Subtype.ext
      rfl
    have hmaj' : StrictMajority (votersPreferring profile' cand2 cand1) := by
      simpa [hx'] using hmaj
    exact (not_strictMajority_profile'_2_1 hmaj').elim

lemma borda_profile_not_1 : (1 : Fin 3) ∉ borda profile := by
  decide

lemma borda_profile'_has_1 : cand1 ∈ borda profile' := by
  decide

lemma black_profile_not_1 : (1 : Fin 3) ∉ black profile := by
  have h : ¬ ∃ x, CondorcetWinner profile x := no_condorcet_profile
  simpa [black, h] using borda_profile_not_1

lemma black_profile'_has_1 : cand1 ∈ black profile' := by
  have h : ¬ ∃ x, CondorcetWinner profile' x := no_condorcet_profile'
  simpa [black, h] using borda_profile'_has_1

def cloneSet : Set (Fin 3) := {0, 2}

lemma cloneSet_profile : CloneSet profile cloneSet := by
  refine ⟨⟨0, by simp [cloneSet]⟩, ?_⟩
  simp only [cloneSet, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq,
    profile, prefers_iff_prefersInList]
  decide

lemma clonePred_eq_ne :
    clonePred cloneSet (2 : Fin 3) = (fun a : Fin 3 => a ≠ (0 : Fin 3)) := by
  funext a
  apply propext
  fin_cases a <;> simp [cloneSet, clonePred]

def cand1clone : {a : Fin 3 // clonePred cloneSet (2 : Fin 3) a} :=
  ⟨1, by simp [cloneSet, clonePred]⟩

lemma cast_subtype_val {A : Type} {p q : A → Prop}
    (h : p = q) (x : {a : A // p a}) :
    (cast (congrArg (fun r => {a : A // r a}) h) x : {a : A // q a}).1 = x.1 := by
  cases x
  cases h
  rfl

lemma mem_castCandidates_iff {V A : Type} [Fintype V] [Fintype A]
    (f : VotingRule) {p q : A → Prop}
    (dp : DecidablePred p) (dq : DecidablePred q)
    (h : p = q) (x : {a : A // p a}) (P : Profile V {a : A // p a}) :
    x ∈ f P ↔
      ((cast (congrArg (fun r => {a : A // r a}) h) x : {a : A // q a}) ∈
        f (castCandidates (p := p) (q := q) h P)) := by
  classical
  let : DecidablePred p := dp
  let : DecidablePred q := dq
  cases h
  cases (Subsingleton.elim dq dp)
  rfl

lemma black_cloneProfile_has_1_raw :
    cand1clone ∈ black (removeClonesExcept profile cloneSet (2 : Fin 3)) := by
  classical
  let q : Fin 3 → Prop := fun a => a ≠ (0 : Fin 3)
  have hb : cand1 ∈ black (restrictCandidates profile q) := by
    simpa [profile', restrictProfile, q] using black_profile'_has_1
  have hpred : q = clonePred cloneSet (2 : Fin 3) := by
    simpa [q] using clonePred_eq_ne.symm
  have hb_cast :
      (cast (congrArg (fun r => {a : Fin 3 // r a}) hpred) cand1 :
        {a : Fin 3 // clonePred cloneSet (2 : Fin 3) a}) ∈
        black (castCandidates (p := q) (q := clonePred cloneSet (2 : Fin 3)) hpred
          (restrictCandidates profile q)) := by
    exact (mem_castCandidates_iff (f := black)
      (dp := inferInstance) (dq := inferInstance) (h := hpred)
      (x := cand1) (P := restrictCandidates profile q)).1 hb
  have hb_cast' :
      (cast (congrArg (fun r => {a : Fin 3 // r a}) hpred) cand1 :
        {a : Fin 3 // clonePred cloneSet (2 : Fin 3) a}) ∈
        black (restrictCandidates profile (clonePred cloneSet (2 : Fin 3))) := by
    simpa [castCandidates_restrictCandidates] using hb_cast
  have hcast_cand1 :
      (cast (congrArg (fun r => {a : Fin 3 // r a}) hpred) cand1 :
        {a : Fin 3 // clonePred cloneSet (2 : Fin 3) a}) = cand1clone := by
    apply Subtype.ext
    simpa [cand1clone, cand1] using (cast_subtype_val (h := hpred) (x := cand1))
  have hb_final :
      cand1clone ∈ black (restrictCandidates profile (clonePred cloneSet (2 : Fin 3))) := by
    simpa [hcast_cand1] using hb_cast'
  simpa [removeClonesExcept] using hb_final

lemma black_cloneProfile_has_1 :
    (⟨1, Or.inl (by simp [cloneSet])⟩ :
        {a : Fin 3 // clonePred cloneSet (2 : Fin 3) a}) ∈
      black (removeClonesExcept profile cloneSet (2 : Fin 3)) := by
  simpa [cand1clone] using black_cloneProfile_has_1_raw

end BlackClonesCounterexample

theorem black_not_independenceOfClones : ¬ IndependenceOfClones black := by
  intro hind
  have hclone :
      CloneSet BlackClonesCounterexample.profile BlackClonesCounterexample.cloneSet :=
    BlackClonesCounterexample.cloneSet_profile
  have hx : (2 : Fin 3) ∈ BlackClonesCounterexample.cloneSet := by
    simp [BlackClonesCounterexample.cloneSet]
  have h :=
    hind (P := BlackClonesCounterexample.profile)
      (X := BlackClonesCounterexample.cloneSet) (x := (2 : Fin 3)) hclone hx
  have hc : (1 : Fin 3) ∉ BlackClonesCounterexample.cloneSet := by
    simp [BlackClonesCounterexample.cloneSet]
  have hnonclone := h.1 (1 : Fin 3) hc
  have hb_left :
      (⟨1, Or.inl hc⟩ :
        {a : Fin 3 // clonePred BlackClonesCounterexample.cloneSet (2 : Fin 3) a}) ∈
        black
          (removeClonesExcept BlackClonesCounterexample.profile
            BlackClonesCounterexample.cloneSet (2 : Fin 3)) := by
    have hsub : (⟨1, Or.inl hc⟩ :
        {a : Fin 3 // clonePred BlackClonesCounterexample.cloneSet (2 : Fin 3) a}) =
        (⟨1, Or.inl (by simp [BlackClonesCounterexample.cloneSet])⟩ :
          {a : Fin 3 // clonePred BlackClonesCounterexample.cloneSet (2 : Fin 3) a}) := by
      apply Subtype.ext
      rfl
    simpa [hsub] using BlackClonesCounterexample.black_cloneProfile_has_1
  have hb_right : (1 : Fin 3) ∈ black BlackClonesCounterexample.profile :=
    (hnonclone).2 hb_left
  exact (BlackClonesCounterexample.black_profile_not_1 hb_right).elim

end SocialChoice
