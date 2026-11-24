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
  profileOfListBallots (fun v => ballots5OP v.1)

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

private lemma profile4OP_eq : profile4OP = profileOfListBallots ballots4OP := by
  rfl

private lemma profile5OP_eq : profile5OP = profileOfListBallots ballots5OP' := by
  rfl

lemma voters4OP_not_mem : (0 : Fin 5) ∉ voters4OP := by
  simp [voters4OP]

lemma profiles_agreeOP :
    ∀ v : Electorate (Fin 5) voters4OP,
      profile5OP.pref (liftVoter (u := (0 : Fin 5)) v) = profile4OP.pref v := by
  intro v
  rfl

private lemma plurality_profile5OP_eq : plurality profile5OP = ({1, 2} : Finset (Fin 3)) := by
  rw [profile5OP_eq]
  simp only [plurality, topCount, votersTop_eq_filter_isTopOfList]
  decide

private lemma plurality_profile4OP_eq : plurality profile4OP = ({2} : Finset (Fin 3)) := by
  rw [profile4OP_eq]
  simp only [plurality, topCount, votersTop_eq_filter_isTopOfList]
  decide

private lemma secondPluralitySet_profile4OP :
    secondPluralitySet profile4OP ({2} : Finset (Fin 3)) = ({0, 1} : Finset (Fin 3)) := by
  rw [profile4OP_eq]
  simp [secondPluralitySet, topCount, votersTop_eq_filter_isTopOfList]
  decide

private lemma pluralityWithRunoffPairs_profile5OP :
    pluralityWithRunoffPairs profile5OP =
      ({({1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
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
  simp [pluralityWithRunoffPairs, plurality_profile4OP_eq, secondPluralitySet_profile4OP]

private lemma margin_profile5OP_2_1 : margin profile5OP (2 : Fin 3) (1 : Fin 3) = 1 := by
  rw [profile5OP_eq, margin_profileOfListBallots]
  decide

private lemma margin_profile5OP_1_2 : margin profile5OP (1 : Fin 3) (2 : Fin 3) = -1 := by
  rw [profile5OP_eq, margin_profileOfListBallots]
  decide

private lemma margin_profile4OP_0_2 : margin profile4OP (0 : Fin 3) (2 : Fin 3) = 0 := by
  rw [profile4OP_eq, margin_profileOfListBallots]
  decide

private lemma margin_profile4OP_2_0 : margin profile4OP (2 : Fin 3) (0 : Fin 3) = 0 := by
  rw [profile4OP_eq, margin_profileOfListBallots]
  decide

private lemma margin_profile4OP_1_2 : margin profile4OP (1 : Fin 3) (2 : Fin 3) = -2 := by
  rw [profile4OP_eq, margin_profileOfListBallots]
  decide

lemma pluralityWithRunoff_profile5OP_has_2 : (2 : Fin 3) ∈ pluralityWithRunoff profile5OP :=
  (mem_pluralityWithRunoff_iff profile5OP 2 (by decide)).2
    ⟨1, by simp [pluralityWithRunoffPairs_profile5OP, Finset.pair_comm],
      by simp [margin_profile5OP_2_1]⟩

lemma pluralityWithRunoff_profile5OP_not_0 : (0 : Fin 3) ∉ pluralityWithRunoff profile5OP := by
  intro hmem
  obtain ⟨y, hyPair, -⟩ := (mem_pluralityWithRunoff_iff profile5OP 0 (by decide)).1 hmem
  rw [pluralityWithRunoffPairs_profile5OP] at hyPair
  have hnot : ∀ y : Fin 3,
      ({0, y} : Finset (Fin 3)) ∉ ({({1, 2} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
    decide
  exact hnot y hyPair

lemma pluralityWithRunoff_profile5OP_not_1 : (1 : Fin 3) ∉ pluralityWithRunoff profile5OP := by
  intro hmem
  obtain ⟨y, hyPair, hmargin⟩ := (mem_pluralityWithRunoff_iff profile5OP 1 (by decide)).1 hmem
  rw [pluralityWithRunoffPairs_profile5OP] at hyPair
  fin_cases y
  · exact absurd hyPair (by decide)
  · exact absurd hyPair (by decide)
  · simp [margin_profile5OP_1_2] at hmargin

lemma pluralityWithRunoff_profile4OP_has_0 : (0 : Fin 3) ∈ pluralityWithRunoff profile4OP :=
  (mem_pluralityWithRunoff_iff profile4OP 0 (by decide)).2
    ⟨2, by simp [pluralityWithRunoffPairs_profile4OP, Finset.pair_comm],
      by simp [margin_profile4OP_0_2]⟩

lemma pluralityWithRunoff_profile4OP_has_2 : (2 : Fin 3) ∈ pluralityWithRunoff profile4OP :=
  (mem_pluralityWithRunoff_iff profile4OP 2 (by decide)).2
    ⟨0, by simp [pluralityWithRunoffPairs_profile4OP], by simp [margin_profile4OP_2_0]⟩

lemma pluralityWithRunoff_profile4OP_not_1 : (1 : Fin 3) ∉ pluralityWithRunoff profile4OP := by
  intro hmem
  obtain ⟨y, hyPair, hmargin⟩ := (mem_pluralityWithRunoff_iff profile4OP 1 (by decide)).1 hmem
  rw [pluralityWithRunoffPairs_profile4OP] at hyPair
  fin_cases y
  · exact absurd hyPair (by decide)
  · exact absurd hyPair (by decide)
  · simp [margin_profile4OP_1_2] at hmargin

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
  let : LinearOrder (Fin 3) := r
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
