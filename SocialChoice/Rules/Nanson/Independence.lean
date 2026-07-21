import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Independence
import SocialChoice.Axioms.Clones
import SocialChoice.ListBallot
import SocialChoice.Rules.Nanson.Reversal

namespace SocialChoice

open Classical
open Finset

attribute [instance] Classical.decEq Classical.decPred

/-!
## Nanson fails independence of dominated

Counterexample with 3 candidates (0,1,2) and 2 voters:
v0: 1 > 2 > 0
v1: 2 > 0 > 1
Candidate 2 Pareto-dominates 0.
Nanson selects {2}, but after removing 0, Nanson selects {1,2}.
-/

namespace NansonIndependenceCounterexample

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
  intro v
  fin_cases v <;>
    simp [profile, ballots, prefers_iff_prefersInList, prefersInList] <;> decide

noncomputable def profile' : Profile (Fin 2) {x : A3 // x ≠ a} :=
  restrictProfile profile a

def cand1 : {x : A3 // x ≠ a} := ⟨b, by decide⟩
def cand2 : {x : A3 // x ≠ a} := ⟨c, by decide⟩

lemma votersPreferring_profile_b_c :
    votersPreferring profile b c = ({0} : Finset (Fin 2)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_c_b :
    votersPreferring profile c b = ({1} : Finset (Fin 2)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_b_a :
    votersPreferring profile b a = ({0} : Finset (Fin 2)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_a_b :
    votersPreferring profile a b = ({1} : Finset (Fin 2)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_c_a :
    votersPreferring profile c a = ({0, 1} : Finset (Fin 2)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma votersPreferring_profile_a_c :
    votersPreferring profile a c = (∅ : Finset (Fin 2)) := by
  classical
  ext v
  fin_cases v <;>
    simp [votersPreferring, profile, ballots, prefers_iff_prefersInList, prefersInList] <;>
    decide

lemma margin_profile_b_c : margin profile b c = 0 := by
  have h1 :
      (Finset.univ.filter (fun v => Prefers profile v b c)) = ({0} : Finset (Fin 2)) := by
    simpa [votersPreferring] using votersPreferring_profile_b_c
  have h2 :
      (Finset.univ.filter (fun v => Prefers profile v c b)) = ({1} : Finset (Fin 2)) := by
    simpa [votersPreferring] using votersPreferring_profile_c_b
  simp [margin, h1, h2]

lemma margin_profile_b_a : margin profile b a = 0 := by
  have h1 :
      (Finset.univ.filter (fun v => Prefers profile v b a)) = ({0} : Finset (Fin 2)) := by
    simpa [votersPreferring] using votersPreferring_profile_b_a
  have h2 :
      (Finset.univ.filter (fun v => Prefers profile v a b)) = ({1} : Finset (Fin 2)) := by
    simpa [votersPreferring] using votersPreferring_profile_a_b
  simp [margin, h1, h2]

lemma margin_profile_c_a : margin profile c a = 2 := by
  have h1 :
      (Finset.univ.filter (fun v => Prefers profile v c a)) = ({0, 1} : Finset (Fin 2)) := by
    simpa [votersPreferring] using votersPreferring_profile_c_a
  have h2 :
      (Finset.univ.filter (fun v => Prefers profile v a c)) = (∅ : Finset (Fin 2)) := by
    simpa [votersPreferring] using votersPreferring_profile_a_c
  simp [margin, h1, h2]

lemma margin_profile_c_b : margin profile c b = 0 := by
  have h1 :
      (Finset.univ.filter (fun v => Prefers profile v c b)) = ({1} : Finset (Fin 2)) := by
    simpa [votersPreferring] using votersPreferring_profile_c_b
  have h2 :
      (Finset.univ.filter (fun v => Prefers profile v b c)) = ({0} : Finset (Fin 2)) := by
    simpa [votersPreferring] using votersPreferring_profile_b_c
  simp [margin, h1, h2]

lemma margin_profile_a_b : margin profile a b = 0 := by
  have h := margin_antisymmetric (P := profile) a b
  simpa [margin_profile_b_a] using h

lemma margin_profile_a_c : margin profile a c = -2 := by
  have h := margin_antisymmetric (P := profile) a c
  simpa [margin_profile_c_a] using h

lemma c2Borda_profile_a : c2BordaScore profile a = -2 := by
  simp [c2BordaScore, Fin.sum_univ_three, self_margin_zero, margin_profile_a_b,
    margin_profile_a_c]

lemma c2Borda_profile_b : c2BordaScore profile b = 0 := by
  simp [c2BordaScore, Fin.sum_univ_three, self_margin_zero, margin_profile_b_a,
    margin_profile_b_c]

lemma c2Borda_profile_c : c2BordaScore profile c = 2 := by
  simp [c2BordaScore, Fin.sum_univ_three, self_margin_zero, margin_profile_c_a,
    margin_profile_c_b]

lemma profile_pos_iff (x : A3) : 0 < c2BordaScore profile x ↔ x = c := by
  fin_cases x <;> simp [c2Borda_profile_a, c2Borda_profile_b, c2Borda_profile_c, c]

lemma nanson_profile : nanson profile = ({c} : Finset A3) := by
  classical
  have hnotall : ¬ ∀ x, c2BordaScore profile x = 0 := by
    intro hall
    have := hall c
    linarith [c2Borda_profile_c]
  have hsurv : (Finset.univ.filter (fun x => c2BordaScore profile x > 0)).Nonempty := by
    refine ⟨c, ?_⟩
    simp [c2Borda_profile_c]
  have hsubset : nanson profile ⊆ {c} := by
    intro x hx
    have hxpos : 0 < c2BordaScore profile x :=
      nanson_score_pos_of_mem (P := profile) hnotall hsurv hx
    have hx' : x = c := (profile_pos_iff x).1 hxpos
    simp [hx']
  have hnonempty : (nanson profile).Nonempty := by
    simpa using (nanson_isVotingRule (P := profile))
  rcases hnonempty with ⟨x, hx⟩
  have hx' : x = c := by
    have : x ∈ ({c} : Finset A3) := hsubset hx
    simpa using this
  have hc : c ∈ nanson profile := by
    simp [hx'] at hx
    exact hx
  apply (Finset.eq_singleton_iff_unique_mem).2
  refine ⟨hc, ?_⟩
  intro y hy
  have : y ∈ ({c} : Finset A3) := hsubset hy
  simpa using this

lemma votersPreferring_restrict_cand1 :
    votersPreferring profile' cand1 cand2 = votersPreferring profile b c := by
  classical
  ext v
  simp [profile', votersPreferring, prefers_restrictProfile_iff, cand1, cand2]

lemma votersPreferring_restrict_cand2 :
    votersPreferring profile' cand2 cand1 = votersPreferring profile c b := by
  classical
  ext v
  simp [profile', votersPreferring, prefers_restrictProfile_iff, cand1, cand2]

lemma margin_profile'_cand1_cand2 : margin profile' cand1 cand2 = 0 := by
  have h1 :
      (Finset.univ.filter (fun v => Prefers profile' v cand1 cand2)) =
        ({0} : Finset (Fin 2)) := by
    simpa [votersPreferring] using votersPreferring_restrict_cand1.trans votersPreferring_profile_b_c
  have h2 :
      (Finset.univ.filter (fun v => Prefers profile' v cand2 cand1)) =
        ({1} : Finset (Fin 2)) := by
    simpa [votersPreferring] using votersPreferring_restrict_cand2.trans votersPreferring_profile_c_b
  simp [margin, h1, h2]

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

lemma c2Borda_profile'_cand1 : c2BordaScore profile' cand1 = 0 := by
  classical
  simp [c2BordaScore, univ_profile'_eq, self_margin_zero, margin_profile'_cand1_cand2]

lemma c2Borda_profile'_cand2 : c2BordaScore profile' cand2 = 0 := by
  classical
  simp [c2BordaScore, univ_profile'_eq, self_margin_zero, margin_profile'_cand2_cand1]

lemma nanson_profile' : nanson profile' = (Finset.univ : Finset {x : A3 // x ≠ a}) := by
  classical
  have hall : ∀ x, c2BordaScore profile' x = 0 := by
    intro x
    rcases x with ⟨x, hxne⟩
    fin_cases x
    · cases hxne rfl
    ·
      have hx' : (⟨b, hxne⟩ : {x : A3 // x ≠ a}) = cand1 := by
        apply Subtype.ext
        rfl
      simpa [hx'] using c2Borda_profile'_cand1
    ·
      have hx' : (⟨c, hxne⟩ : {x : A3 // x ≠ a}) = cand2 := by
        apply Subtype.ext
        rfl
      simpa [hx'] using c2Borda_profile'_cand2
  have haux : nansonAux (Fintype.card {x : A3 // x ≠ a}) {x : A3 // x ≠ a} profile' =
      (Finset.univ : Finset {x : A3 // x ≠ a}) := by
    cases hcard : Fintype.card {x : A3 // x ≠ a} with
    | zero =>
        simp [nansonAux]
    | succ n =>
        simp [nansonAux, hall]
  change nansonAux (Fintype.card {x : A3 // x ≠ a}) {x : A3 // x ≠ a} profile' =
    (Finset.univ : Finset {x : A3 // x ≠ a})
  exact haux

lemma nanson_profile'_has_1 : cand1 ∈ nanson profile' := by
  simp [nanson_profile']

lemma nanson_profile_not_1 : (b : A3) ∉ nanson profile := by
  simp [nanson_profile, b, c]

lemma lift_nanson_profile'_has_1 : (b : A3) ∈ liftWinners (nanson profile') := by
  have h : cand1 ∈ nanson profile' := nanson_profile'_has_1
  simpa [liftWinners, cand1] using h

/-!
## The same profile violates independence of clones

Clone set {0,2}. Removing clone 0 changes whether candidate 1 is a winner.
-/

def cloneSet : Set A3 := {a, c}

lemma a_ne_c : (a : A3) ≠ c := by
  decide

lemma b_ne_a : (b : A3) ≠ a := by
  decide

lemma b_ne_c : (b : A3) ≠ c := by
  decide

lemma b_not_mem_cloneSet : (b : A3) ∉ cloneSet := by
  intro hb
  have hb' : b = a ∨ b = c := by
    simpa [cloneSet] using hb
  cases hb' with
  | inl h => exact (b_ne_a h).elim
  | inr h => exact (b_ne_c h).elim

lemma c_mem_cloneSet : (c : A3) ∈ cloneSet := by
  simp [cloneSet]

lemma cloneSet_profile : CloneSet profile cloneSet := by
  refine ⟨?_, ?_⟩
  · exact ⟨a, by simp [cloneSet]⟩
  · intro v d hd
    fin_cases d
    · exact (hd (by simp [cloneSet])).elim
    · -- d = b
      fin_cases v
      ·
        refine Or.inr ?_
        intro x hx
        have hx' : x = a ∨ x = c := by
          simpa [cloneSet] using hx
        cases hx' with
        | inl hx0 =>
            subst hx0
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
        | inr hx2 =>
            subst hx2
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
      ·
        refine Or.inl ?_
        intro x hx
        have hx' : x = a ∨ x = c := by
          simpa [cloneSet] using hx
        cases hx' with
        | inl hx0 =>
            subst hx0
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
        | inr hx2 =>
            subst hx2
            simp [profile, ballots, prefers_iff_prefersInList, prefersInList]; decide
    · exact (hd (by simp [cloneSet])).elim

lemma clonePred_eq_ne :
    clonePred cloneSet c = (fun x : A3 => x ≠ a) := by
  funext x
  apply propext
  fin_cases x
  · -- x = a
    constructor
    · intro hx
      cases hx with
      | inl hx' => exact (hx' (by simp [cloneSet])).elim
      | inr hx' => exact (a_ne_c hx').elim
    · intro hx
      cases hx rfl
  · -- x = b
    constructor
    · intro _hx
      exact b_ne_a
    · intro _hx
      exact Or.inl b_not_mem_cloneSet
  · -- x = c
    constructor
    · intro _hx
      exact a_ne_c.symm
    · intro _hx
      exact Or.inr rfl

def cand1clone : {a : A3 // clonePred cloneSet c a} :=
  ⟨b, Or.inl b_not_mem_cloneSet⟩

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
  letI : DecidablePred p := dp
  letI : DecidablePred q := dq
  cases h
  cases (Subsingleton.elim dq dp)
  rfl

lemma nanson_cloneProfile_has_1_raw :
    cand1clone ∈ nanson (removeClonesExcept profile cloneSet c) := by
  classical
  let q : A3 → Prop := fun x => x ≠ a
  have hb : cand1 ∈ nanson (restrictCandidates profile q) := by
    simpa [profile', restrictProfile, q] using nanson_profile'_has_1
  have hpred : q = clonePred cloneSet c := by
    simpa [q] using clonePred_eq_ne.symm
  have hb_cast :
      (cast (congrArg (fun r => {a : A3 // r a}) hpred) cand1 :
        {a : A3 // clonePred cloneSet c a}) ∈
        nanson (castCandidates (p := q) (q := clonePred cloneSet c) hpred
          (restrictCandidates profile q)) := by
    exact (mem_castCandidates_iff (f := nanson)
      (dp := inferInstance) (dq := inferInstance) (h := hpred)
      (x := cand1) (P := restrictCandidates profile q)).1 hb
  have hb_cast' :
      (cast (congrArg (fun r => {a : A3 // r a}) hpred) cand1 :
        {a : A3 // clonePred cloneSet c a}) ∈
        nanson (restrictCandidates profile (clonePred cloneSet c)) := by
    simpa [castCandidates_restrictCandidates] using hb_cast
  have hcast_cand1 :
      (cast (congrArg (fun r => {a : A3 // r a}) hpred) cand1 :
        {a : A3 // clonePred cloneSet c a}) = cand1clone := by
    apply Subtype.ext
    simpa [cand1clone, cand1] using (cast_subtype_val (h := hpred) (x := cand1))
  have hb_final :
      cand1clone ∈ nanson (restrictCandidates profile (clonePred cloneSet c)) := by
    simpa [hcast_cand1] using hb_cast'
  simpa [removeClonesExcept] using hb_final

lemma nanson_cloneProfile_has_1 :
    (⟨b, Or.inl b_not_mem_cloneSet⟩ :
        {a : A3 // clonePred cloneSet c a}) ∈
      nanson (removeClonesExcept profile cloneSet c) := by
  simpa [cand1clone] using nanson_cloneProfile_has_1_raw

end NansonIndependenceCounterexample

open NansonIndependenceCounterexample

theorem nanson_not_independenceOfDominated : ¬ IndependenceOfDominated nanson := by
  intro hind
  have hpref : ∀ v : Fin 2, Prefers profile v c a :=
    prefers_2_0
  have hEq := hind (P := profile) (c := c) (d := a) hpref
  have hmem :
      (b : A3) ∈
        liftWinners (nanson (restrictCandidates profile (fun x => x ≠ a))) := by
    simpa [profile', restrictProfile] using lift_nanson_profile'_has_1
  have hmem' : (b : A3) ∈ nanson profile := by
    simpa [hEq] using hmem
  exact (nanson_profile_not_1 hmem').elim

theorem nanson_not_independenceOfClones : ¬ IndependenceOfClones nanson := by
  intro hind
  have hclone : CloneSet profile cloneSet := cloneSet_profile
  have hx : (c : A3) ∈ cloneSet := c_mem_cloneSet
  have h :=
    hind (P := profile) (X := cloneSet) (x := c) hclone hx
  have hc : (b : A3) ∉ cloneSet := b_not_mem_cloneSet
  have hnonclone := h.1 b hc
  have hb_left :
      (⟨b, Or.inl hc⟩ : {a : A3 // clonePred cloneSet c a}) ∈
        nanson (removeClonesExcept profile cloneSet c) := by
    have hsub : (⟨b, Or.inl hc⟩ : {a : A3 // clonePred cloneSet c a}) =
        (⟨b, Or.inl b_not_mem_cloneSet⟩ :
          {a : A3 // clonePred cloneSet c a}) := by
      apply Subtype.ext
      rfl
    simpa [hsub] using nanson_cloneProfile_has_1
  have hb_right : (b : A3) ∈ nanson profile :=
    (hnonclone).2 hb_left
  exact (nanson_profile_not_1 hb_right).elim

end SocialChoice
