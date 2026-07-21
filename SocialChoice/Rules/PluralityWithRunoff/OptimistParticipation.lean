import SocialChoice.Rules.PluralityWithRunoff.Involvement

namespace SocialChoice

/-!
# Plurality with Runoff fails optimist participation

We use a 5-voter, 3-candidate profile where adding a voter with ballot
1 > 0 > 2 changes the winner set from {0, 2} to {2}. Under the optimist
set extension, that voter strictly prefers abstaining.
-/

namespace PluralityWithRunoffOptimistParticipationCounterexample

open Finset
open Classical
open PluralityWithRunoffNegativeInvolvementCounterexample

def ballot021OP : ListBallot 3 := ListBallot.mk' [0, 2, 1]
def ballot102OP : ListBallot 3 := ListBallot.mk' [1, 0, 2]
def ballot210OP : ListBallot 3 := ListBallot.mk' [2, 1, 0]

def ballots5OP : Fin 5 → ListBallot 3
  | 0 => ballot102OP
  | 1 => ballot021OP
  | 2 => ballot102OP
  | 3 => ballot210OP
  | 4 => ballot210OP
  | _ => ballot210OP

noncomputable def fullProfileOP : Profile (Electorate (Fin 5) (Finset.univ)) (Fin 3) :=
  { pref := fun v => (ballots5OP v.1).toLinearOrder }

def voters4OP : Finset (Fin 5) := Finset.univ.erase 0

noncomputable def profile4OP : Profile (Electorate (Fin 5) voters4OP) (Fin 3) :=
  restrictElectorate fullProfileOP voters4OP (by
    intro x hx
    exact Finset.mem_univ x)

noncomputable def profile5OP :
    Profile (Electorate (Fin 5) (insert (0 : Fin 5) voters4OP)) (Fin 3) :=
  restrictElectorate fullProfileOP (insert (0 : Fin 5) voters4OP) (by
    intro x hx
    exact Finset.mem_univ x)

def ballots4OP (v : Electorate (Fin 5) voters4OP) : ListBallot 3 := ballots5OP v.1

def ballots5OP' (v : Electorate (Fin 5) (insert (0 : Fin 5) voters4OP)) : ListBallot 3 :=
  ballots5OP v.1

private lemma profile4OP_eq : profile4OP = profileOfBallotsNI ballots4OP := by
  rfl

private lemma profile5OP_eq : profile5OP = profileOfBallotsNI ballots5OP' := by
  rfl

lemma voters4OP_not_mem : (0 : Fin 5) ∉ voters4OP := by
  simp [voters4OP]

lemma profiles_agreeOP :
    ∀ v : Electorate (Fin 5) voters4OP,
      profile5OP.pref (liftVoter (u := (0 : Fin 5)) v) = profile4OP.pref v := by
  intro v
  rfl

private lemma plurality_profile5OP_eq : plurality profile5OP = ({1, 2} : Finset (Fin 3)) := by
  classical
  change plurality (profileOfBallotsNI ballots5OP') = ({1, 2} : Finset (Fin 3))
  simp [plurality, topCount_eq_countTopNI, countTopNI]
  decide

private lemma plurality_profile4OP_eq : plurality profile4OP = ({2} : Finset (Fin 3)) := by
  classical
  change plurality (profileOfBallotsNI ballots4OP) = ({2} : Finset (Fin 3))
  simp [plurality, topCount_eq_countTopNI, countTopNI]
  decide

private lemma secondPluralitySet_profile4OP :
    secondPluralitySet profile4OP ({2} : Finset (Fin 3)) = ({0, 1} : Finset (Fin 3)) := by
  classical
  change secondPluralitySet (profileOfBallotsNI ballots4OP) ({2} : Finset (Fin 3)) =
    ({0, 1} : Finset (Fin 3))
  simp [secondPluralitySet, topCount_eq_countTopNI, countTopNI]
  decide

private lemma powersetCard_eq_singleton_of_card_two {A : Type} [DecidableEq A]
    {S : Finset A} (hcard : S.card = 2) :
    S.powersetCard 2 = ({S} : Finset (Finset A)) := by
  classical
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

private lemma pluralityWithRunoffPairs_profile5OP :
    pluralityWithRunoffPairs profile5OP =
      ({({1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
  classical
  have hS : (plurality profile5OP).card ≥ 2 := by
    simp [plurality_profile5OP_eq]
  have hcard : (plurality profile5OP).card = 2 := by
    simp [plurality_profile5OP_eq]
  have hpow :
      (plurality profile5OP).powersetCard 2 =
        ({plurality profile5OP} : Finset (Finset (Fin 3))) :=
    powersetCard_eq_singleton_of_card_two (S := plurality profile5OP) hcard
  simpa [pluralityWithRunoffPairs, plurality_profile5OP_eq, hS] using hpow

private lemma pluralityWithRunoffPairs_profile4OP :
    pluralityWithRunoffPairs profile4OP =
      ({({2, 0} : Finset (Fin 3)), ({2, 1} : Finset (Fin 3))} :
        Finset (Finset (Fin 3))) := by
  classical
  change pluralityWithRunoffPairs (profileOfBallotsNI ballots4OP) =
    ({({2, 0} : Finset (Fin 3)), ({2, 1} : Finset (Fin 3))} :
      Finset (Finset (Fin 3)))
  simp [pluralityWithRunoffPairs, secondPluralitySet, plurality, topCount_eq_countTopNI, countTopNI]
  decide

private lemma margin_profile5OP_2_1 : margin profile5OP (2 : Fin 3) (1 : Fin 3) = 1 := by
  classical
  simp [profile5OP_eq, margin_eq_marginListNI]
  decide

private lemma margin_profile5OP_1_2 : margin profile5OP (1 : Fin 3) (2 : Fin 3) = -1 := by
  classical
  simp [profile5OP_eq, margin_eq_marginListNI]
  decide

private lemma margin_profile4OP_0_2 : margin profile4OP (0 : Fin 3) (2 : Fin 3) = 0 := by
  classical
  simp [profile4OP_eq, margin_eq_marginListNI]
  decide

private lemma margin_profile4OP_2_0 : margin profile4OP (2 : Fin 3) (0 : Fin 3) = 0 := by
  classical
  simp [profile4OP_eq, margin_eq_marginListNI]
  decide

private lemma margin_profile4OP_1_2 : margin profile4OP (1 : Fin 3) (2 : Fin 3) = -2 := by
  classical
  simp [profile4OP_eq, margin_eq_marginListNI]
  decide

private noncomputable def pairC {A : Type} (x y : A) : Finset A := by
  classical
  exact {x, y}

@[simp] private lemma pairC_eq_pair (x y : Fin 3) :
    pairC x y = ({x, y} : Finset (Fin 3)) := by
  classical
  ext z
  simp [pairC]

private lemma mem_pluralityWithRunoff_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x : A) (hcard : ¬ Fintype.card A ≤ 1) :
    x ∈ pluralityWithRunoff P ↔
      ∃ y : A,
        pairC x y ∈
          @pluralityWithRunoffPairs V A _ _ (Classical.decEq A) P ∧
          0 ≤ margin P x y := by
  classical
  by_cases hcard' : Fintype.card A ≤ 1
  · exact (hcard hcard').elim
  · constructor
    · intro hx
      simpa [pluralityWithRunoff, hcard', pairC] using hx
    · intro hx
      have hx' :
          x ∈ (Finset.univ : Finset A) ∧
            ∃ y : A,
              pairC x y ∈
                @pluralityWithRunoffPairs V A _ _ (Classical.decEq A) P ∧
                0 ≤ margin P x y := by
        exact ⟨by simp, hx⟩
      simpa [pluralityWithRunoff, hcard', pairC] using hx'

lemma pluralityWithRunoff_profile5OP_has_2 : (2 : Fin 3) ∈ pluralityWithRunoff profile5OP := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) <= 1 := by decide
  have hpair : ({2, 1} : Finset (Fin 3)) ∈ pluralityWithRunoffPairs profile5OP := by
    have hpair' : ({1, 2} : Finset (Fin 3)) ∈ pluralityWithRunoffPairs profile5OP := by
      simp [pluralityWithRunoffPairs_profile5OP]
    simpa [Finset.pair_comm] using hpair'
  have hmargin : 0 <= margin profile5OP (2 : Fin 3) (1 : Fin 3) := by
    simp [margin_profile5OP_2_1]
  have hpair_default : pairC 2 1 ∈ pluralityWithRunoffPairs profile5OP := by
    simpa [pairC_eq_pair] using hpair
  have hpair_classical :
      pairC 2 1 ∈
        @pluralityWithRunoffPairs (Electorate (Fin 5) (insert 0 voters4OP)) (Fin 3) _ _
          (Classical.decEq (Fin 3)) profile5OP := by
    exact
      (mem_pluralityWithRunoffPairs_decEq_congr (P := profile5OP)
          (inst1 := (inferInstance : DecidableEq (Fin 3)))
          (inst2 := Classical.decEq (Fin 3))
          (s := pairC 2 1)).1 hpair_default
  exact (mem_pluralityWithRunoff_iff (P := profile5OP) (x := (2 : Fin 3)) (hcard := hcard)).2
    ⟨(1 : Fin 3), hpair_classical, hmargin⟩

lemma pluralityWithRunoff_profile5OP_not_0 : (0 : Fin 3) ∉ pluralityWithRunoff profile5OP := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) <= 1 := by decide
  intro hmem
  rcases (mem_pluralityWithRunoff_iff (P := profile5OP) (x := (0 : Fin 3)) (hcard := hcard)).1 hmem with
    ⟨y, hyPair_classical, _hmargin⟩
  have hyPair_default : pairC 0 y ∈ pluralityWithRunoffPairs profile5OP := by
    exact
      (mem_pluralityWithRunoffPairs_decEq_congr (P := profile5OP)
          (inst1 := Classical.decEq (Fin 3))
          (inst2 := (inferInstance : DecidableEq (Fin 3)))
          (s := pairC 0 y)).1 hyPair_classical
  have hyPair : ({0, y} : Finset (Fin 3)) ∈ pluralityWithRunoffPairs profile5OP := by
    simpa [pairC_eq_pair] using hyPair_default
  fin_cases y
  ·
    have hEq : ({0} : Finset (Fin 3)) = ({1, 2} : Finset (Fin 3)) := by
      simpa [pluralityWithRunoffPairs_profile5OP] using hyPair
    have hmem1 : (1 : Fin 3) ∈ ({1, 2} : Finset (Fin 3)) := by simp
    have hmem1' : (1 : Fin 3) ∈ ({0} : Finset (Fin 3)) := by
      rw [hEq]
      exact hmem1
    simp at hmem1'
  ·
    have hEq : ({0, 1} : Finset (Fin 3)) = ({1, 2} : Finset (Fin 3)) := by
      simpa [pluralityWithRunoffPairs_profile5OP] using hyPair
    have hmem2 : (2 : Fin 3) ∈ ({1, 2} : Finset (Fin 3)) := by simp
    have hmem2' : (2 : Fin 3) ∈ ({0, 1} : Finset (Fin 3)) := by
      rw [hEq]
      exact hmem2
    simp at hmem2'
  ·
    have hEq : ({0, 2} : Finset (Fin 3)) = ({1, 2} : Finset (Fin 3)) := by
      simpa [pluralityWithRunoffPairs_profile5OP] using hyPair
    have hmem1 : (1 : Fin 3) ∈ ({1, 2} : Finset (Fin 3)) := by simp
    have hmem1' : (1 : Fin 3) ∈ ({0, 2} : Finset (Fin 3)) := by
      rw [hEq]
      exact hmem1
    simp at hmem1'

lemma pluralityWithRunoff_profile5OP_not_1 : (1 : Fin 3) ∉ pluralityWithRunoff profile5OP := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) <= 1 := by decide
  intro hmem
  rcases (mem_pluralityWithRunoff_iff (P := profile5OP) (x := (1 : Fin 3)) (hcard := hcard)).1 hmem with
    ⟨y, hyPair_classical, hmargin⟩
  have hyPair_default : pairC 1 y ∈ pluralityWithRunoffPairs profile5OP := by
    exact
      (mem_pluralityWithRunoffPairs_decEq_congr (P := profile5OP)
          (inst1 := Classical.decEq (Fin 3))
          (inst2 := (inferInstance : DecidableEq (Fin 3)))
          (s := pairC 1 y)).1 hyPair_classical
  have hyPair : ({1, y} : Finset (Fin 3)) ∈ pluralityWithRunoffPairs profile5OP := by
    simpa [pairC_eq_pair] using hyPair_default
  fin_cases y
  ·
    have hEq : ({1, 0} : Finset (Fin 3)) = ({1, 2} : Finset (Fin 3)) := by
      simpa [pluralityWithRunoffPairs_profile5OP] using hyPair
    have hmem2 : (2 : Fin 3) ∈ ({1, 2} : Finset (Fin 3)) := by simp
    have hmem2' : (2 : Fin 3) ∈ ({1, 0} : Finset (Fin 3)) := by
      rw [hEq]
      exact hmem2
    simp at hmem2'
  ·
    have hEq : ({1} : Finset (Fin 3)) = ({1, 2} : Finset (Fin 3)) := by
      simpa [pluralityWithRunoffPairs_profile5OP] using hyPair
    have hmem2 : (2 : Fin 3) ∈ ({1, 2} : Finset (Fin 3)) := by simp
    have hmem2' : (2 : Fin 3) ∈ ({1} : Finset (Fin 3)) := by
      rw [hEq]
      exact hmem2
    simp at hmem2'
  ·
    have hmargin' : 0 <= margin profile5OP (1 : Fin 3) (2 : Fin 3) := by
      exact hmargin
    have hmargin'' := hmargin'
    simp [margin_profile5OP_1_2] at hmargin''

lemma pluralityWithRunoff_profile4OP_has_0 : (0 : Fin 3) ∈ pluralityWithRunoff profile4OP := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) <= 1 := by decide
  have hpair : ({2, 0} : Finset (Fin 3)) ∈ pluralityWithRunoffPairs profile4OP := by
    simp [pluralityWithRunoffPairs_profile4OP]
  have hmargin : 0 <= margin profile4OP (0 : Fin 3) (2 : Fin 3) := by
    simp [margin_profile4OP_0_2]
  have hpair_default : pairC 0 2 ∈ pluralityWithRunoffPairs profile4OP := by
    simpa [pairC_eq_pair, Finset.pair_comm] using hpair
  have hpair_classical :
      pairC 0 2 ∈
        @pluralityWithRunoffPairs (Electorate (Fin 5) voters4OP) (Fin 3) _ _
          (Classical.decEq (Fin 3)) profile4OP := by
    exact
      (mem_pluralityWithRunoffPairs_decEq_congr (P := profile4OP)
          (inst1 := (inferInstance : DecidableEq (Fin 3)))
          (inst2 := Classical.decEq (Fin 3))
          (s := pairC 0 2)).1 hpair_default
  exact (mem_pluralityWithRunoff_iff (P := profile4OP) (x := (0 : Fin 3)) (hcard := hcard)).2
    ⟨(2 : Fin 3), hpair_classical, hmargin⟩

lemma pluralityWithRunoff_profile4OP_has_2 : (2 : Fin 3) ∈ pluralityWithRunoff profile4OP := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) <= 1 := by decide
  have hpair : ({2, 0} : Finset (Fin 3)) ∈ pluralityWithRunoffPairs profile4OP := by
    simp [pluralityWithRunoffPairs_profile4OP]
  have hmargin : 0 <= margin profile4OP (2 : Fin 3) (0 : Fin 3) := by
    simp [margin_profile4OP_2_0]
  have hpair_default : pairC 2 0 ∈ pluralityWithRunoffPairs profile4OP := by
    simpa [pairC_eq_pair] using hpair
  have hpair_classical :
      pairC 2 0 ∈
        @pluralityWithRunoffPairs (Electorate (Fin 5) voters4OP) (Fin 3) _ _
          (Classical.decEq (Fin 3)) profile4OP := by
    exact
      (mem_pluralityWithRunoffPairs_decEq_congr (P := profile4OP)
          (inst1 := (inferInstance : DecidableEq (Fin 3)))
          (inst2 := Classical.decEq (Fin 3))
          (s := pairC 2 0)).1 hpair_default
  exact (mem_pluralityWithRunoff_iff (P := profile4OP) (x := (2 : Fin 3)) (hcard := hcard)).2
    ⟨(0 : Fin 3), hpair_classical, hmargin⟩

lemma pluralityWithRunoff_profile4OP_not_1 : (1 : Fin 3) ∉ pluralityWithRunoff profile4OP := by
  classical
  have hcard : ¬ Fintype.card (Fin 3) <= 1 := by decide
  intro hmem
  rcases (mem_pluralityWithRunoff_iff (P := profile4OP) (x := (1 : Fin 3)) (hcard := hcard)).1 hmem with
    ⟨y, hyPair_classical, hmargin⟩
  have hyPair_default : pairC 1 y ∈ pluralityWithRunoffPairs profile4OP := by
    exact
      (mem_pluralityWithRunoffPairs_decEq_congr (P := profile4OP)
          (inst1 := Classical.decEq (Fin 3))
          (inst2 := (inferInstance : DecidableEq (Fin 3)))
          (s := pairC 1 y)).1 hyPair_classical
  have hyPair : ({1, y} : Finset (Fin 3)) ∈ pluralityWithRunoffPairs profile4OP := by
    simpa [pairC_eq_pair] using hyPair_default
  fin_cases y
  ·
    have hEq : ({1, 0} : Finset (Fin 3)) = ({2, 0} : Finset (Fin 3)) ∨
        ({1, 0} : Finset (Fin 3)) = ({2, 1} : Finset (Fin 3)) := by
      simpa [pluralityWithRunoffPairs_profile4OP] using hyPair
    cases hEq with
    | inl h =>
        have hmem2 : (2 : Fin 3) ∈ ({2, 0} : Finset (Fin 3)) := by simp
        have hmem2' : (2 : Fin 3) ∈ ({1, 0} : Finset (Fin 3)) := by
          rw [h]
          exact hmem2
        simp at hmem2'
    | inr h =>
        have hmem2 : (2 : Fin 3) ∈ ({2, 1} : Finset (Fin 3)) := by simp
        have hmem2' : (2 : Fin 3) ∈ ({1, 0} : Finset (Fin 3)) := by
          rw [h]
          exact hmem2
        simp at hmem2'
  ·
    have hEq : ({1} : Finset (Fin 3)) = ({2, 0} : Finset (Fin 3)) ∨
        ({1} : Finset (Fin 3)) = ({2, 1} : Finset (Fin 3)) := by
      simpa [pluralityWithRunoffPairs_profile4OP] using hyPair
    cases hEq with
    | inl h =>
        have hmem2 : (2 : Fin 3) ∈ ({2, 0} : Finset (Fin 3)) := by simp
        have hmem2' : (2 : Fin 3) ∈ ({1} : Finset (Fin 3)) := by
          rw [h]
          exact hmem2
        simp at hmem2'
    | inr h =>
        have hmem2 : (2 : Fin 3) ∈ ({2, 1} : Finset (Fin 3)) := by simp
        have hmem2' : (2 : Fin 3) ∈ ({1} : Finset (Fin 3)) := by
          rw [h]
          exact hmem2
        simp at hmem2'
  ·
    have hmargin' : 0 <= margin profile4OP (1 : Fin 3) (2 : Fin 3) := by
      exact hmargin
    have hmargin'' := hmargin'
    simp [margin_profile4OP_1_2] at hmargin''

private lemma newVoter_prefers_0_2_OP :
    (profile5OP.pref (newVoter (u := (0 : Fin 5)) (V := voters4OP) voters4OP_not_mem)).lt
      (0 : Fin 3) (2 : Fin 3) := by
  change ballot102OP.toLinearOrder.lt (0 : Fin 3) (2 : Fin 3)
  have hlt :
      ballot102OP.ranking.idxOf (0 : Fin 3) < ballot102OP.ranking.idxOf (2 : Fin 3) := by
    decide
  simpa [ballot102OP, ListBallot.lt_iff_idxOf] using hlt

end PluralityWithRunoffOptimistParticipationCounterexample

open PluralityWithRunoffOptimistParticipationCounterexample

theorem pluralityWithRunoff_not_optimistParticipation :
    ¬ OptimistParticipation pluralityWithRunoff := by
  intro hopt
  let r := profile5OP.pref (newVoter (u := (0 : Fin 5)) (V := voters4OP) voters4OP_not_mem)
  letI : LinearOrder (Fin 3) := r
  have hweak :
      @OptimistWeak (Fin 3) (fun a b => LinearOrder.toDecidableEq a b) r
        (pluralityWithRunoff profile5OP) (pluralityWithRunoff profile4OP) := by
    simpa [OptimistParticipation, StrongParticipation, OptimistExtension, r] using
      hopt (V := voters4OP) (u := (0 : Fin 5)) (hu := voters4OP_not_mem)
        (P := profile4OP) (Q := profile5OP) profiles_agreeOP
  rcases hweak with ⟨a, b, haTop, hbTop, hle⟩
  have ha2 : a = (2 : Fin 3) := by
    have haMem : a ∈ pluralityWithRunoff profile5OP := haTop.1
    fin_cases a
    · exact (pluralityWithRunoff_profile5OP_not_0 haMem).elim
    · exact (pluralityWithRunoff_profile5OP_not_1 haMem).elim
    · rfl
  have hb0 : b = (0 : Fin 3) := by
    have hbMem : b ∈ pluralityWithRunoff profile4OP := hbTop.1
    fin_cases b
    · rfl
    · exact (pluralityWithRunoff_profile4OP_not_1 hbMem).elim
    · have h0mem : (0 : Fin 3) ∈ pluralityWithRunoff profile4OP :=
          pluralityWithRunoff_profile4OP_has_0
      have h0ne : (0 : Fin 3) ≠ (2 : Fin 3) := by decide
      have h20raw := hbTop.2 (0 : Fin 3) h0mem h0ne
      have h20 := h20raw
      simp at h20
  have hle' := hle
  simp [ha2, hb0, r] at hle'

end SocialChoice
