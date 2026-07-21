import SocialChoice.Axioms.Smith
import SocialChoice.Margin
import SocialChoice.Rules.TopCycle.Defs
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Baldwin.Defs
import SocialChoice.Rules.ScoringElimination.Baldwin.Condorcet

namespace SocialChoice

open Finset

lemma dominatesSet_singleton_condorcetWinner {V A : Type} [Fintype V] [Fintype A]
    {P : Profile V A} {S : Finset A} (hS : dominatesSet P S) (hcard : S.card = 1) :
    ∃ c, S = {c} ∧ CondorcetWinner P c := by
  classical
  rcases Finset.card_eq_one.mp hcard with ⟨c, hc⟩
  refine ⟨c, hc, ?_⟩
  apply (CondorcetWinner_iff_margin_pos P c).2
  intro d hd
  have hcS : c ∈ S := by simp [hc]
  have hd' : d ≠ c := by
    simpa [eq_comm] using hd
  have hdS : d ∉ S := by
    simp [hc, hd']
  exact hS.2 c hcS d hdS

lemma baldwin_subset_of_dominatesSet
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) {S : Finset A} (hS : dominatesSet P S) :
    scoringEliminationAux bordaScore A P ⊆ S := by
  classical
  set n := Fintype.card A with hn
  let Motive : Nat → Prop := fun k =>
    ∀ {A : Type} [Fintype A] [DecidableEq A]
      {V : Type} [Fintype V]
      (P : Profile V A) (S : Finset A),
      dominatesSet P S → Fintype.card A = k →
        scoringEliminationAux bordaScore A P ⊆ S
  have hStrong : Motive n := by
    refine Nat.strongRecOn (motive := Motive) n ?_
    intro k ih A _ _ V _ P S hS hcard
    by_cases hle : Fintype.card A ≤ 1
    · have hdef : scoringEliminationAux bordaScore A P = (Finset.univ : Finset A) := by
        simp [scoringEliminationAux, hle]
      have hsub : (Finset.univ : Finset A) ⊆ S := by
        intro x hx
        have hsubsingle : Subsingleton A :=
          (Fintype.card_le_one_iff_subsingleton).1 hle
        rcases hS.1 with ⟨s, hs⟩
        have hx' : x = s := Subsingleton.elim _ _
        simpa [hx'] using hs
      simpa [hdef] using hsub
    · have haux :=
        scoringEliminationAux_eq_biUnion_of_not_card_le_one
          (score := bordaScore) (P := P) (hcard := hle)
      let m := Fintype.card A
      let scoreVec : Nat → Int := fun r => bordaScore m r
      let L : Finset A := lowestScoring P scoreVec
      have haux' :
          scoringEliminationAux bordaScore A P =
            L.biUnion (fun c => liftFinset
              (scoringEliminationAux bordaScore _ (restrictProfile P c))) := by
        simpa [m, scoreVec, L] using haux
      intro x hx
      have hx' : x ∈
          L.biUnion (fun c => liftFinset
            (scoringEliminationAux bordaScore _ (restrictProfile P c))) := by
        simpa [haux'] using hx
      rcases Finset.mem_biUnion.mp hx' with ⟨c, hcL, hxbranch⟩
      rcases (mem_liftFinset_iff_subtype
        (s := scoringEliminationAux bordaScore {x : A // x ≠ c} (restrictProfile P c))
        (x := x)).1 hxbranch with ⟨hxc, hxsub⟩
      let S' : Finset {x : A // x ≠ c} := Finset.subtype (fun x => x ≠ c) S
      by_cases hcS : c ∈ S
      · by_cases hcardS : S.card = 1
        · rcases dominatesSet_singleton_condorcetWinner (P := P) (S := S) hS hcardS
            with ⟨c', hS_eq, hwin⟩
          have hcc' : c = c' := by
            have : c ∈ ({c'} : Finset A) := by simpa [hS_eq] using hcS
            simpa using this
          have hcardA : 1 < Fintype.card A := Nat.lt_of_not_ge hle
          have hnot_lowest : c ∉ L := by
            have hnot :=
              CondorcetWinner_not_lowest_borda (P := P) (c := c) (hwin := by simpa [hcc'] using hwin)
                (hcard := hcardA)
            simpa [L, scoreVec, m] using hnot
          exact (False.elim (hnot_lowest hcL))
        · have hpos : 0 < S.card := Finset.card_pos.mpr hS.1
          have hge : 1 ≤ S.card := Nat.succ_le_iff.mp hpos
          have hlt : 1 < S.card := lt_of_le_of_ne hge (Ne.symm hcardS)
          rcases Finset.exists_mem_ne hlt c with ⟨t, htS, htne⟩
          have hS'ne : S'.Nonempty := by
            refine ⟨⟨t, htne⟩, ?_⟩
            exact Finset.mem_subtype.mpr htS
          have hdom' : dominatesSet (restrictProfile P c) S' := by
            refine ⟨hS'ne, ?_⟩
            intro a ha b hb
            have haS : (a : A) ∈ S := (Finset.mem_subtype.mp ha)
            have hbS : (b : A) ∉ S := by
              intro hbS
              exact hb (Finset.mem_subtype.mpr hbS)
            have hpos : margin_pos P (a : A) (b : A) := hS.2 a haS b hbS
            dsimp [margin_pos] at hpos ⊢
            have heq := margin_eq_margin_restrictProfile (P := P) (c := c) (a := a) (b := b)
            simpa [heq] using hpos
          have hltcard : Fintype.card {x : A // x ≠ c} < k := by
            have hltcard' := card_restrict_lt (A := A) c
            simpa [hcard] using hltcard'
          have hrec :
              scoringEliminationAux bordaScore {x : A // x ≠ c} (restrictProfile P c) ⊆ S' :=
            (ih (Fintype.card {x : A // x ≠ c}) hltcard)
              (P := restrictProfile P c) (S := S') hdom' rfl
          have hxS' : (⟨x, hxc⟩ : {x : A // x ≠ c}) ∈ S' := hrec hxsub
          exact (Finset.mem_subtype.mp hxS')
      · rcases hS.1 with ⟨t, htS⟩
        have htne : t ≠ c := by
          intro hEq
          subst hEq
          exact hcS htS
        have hS'ne : S'.Nonempty := by
          refine ⟨⟨t, htne⟩, ?_⟩
          exact Finset.mem_subtype.mpr htS
        have hdom' : dominatesSet (restrictProfile P c) S' := by
          refine ⟨hS'ne, ?_⟩
          intro a ha b hb
          have haS : (a : A) ∈ S := (Finset.mem_subtype.mp ha)
          have hbS : (b : A) ∉ S := by
            intro hbS
            exact hb (Finset.mem_subtype.mpr hbS)
          have hpos : margin_pos P (a : A) (b : A) := hS.2 a haS b hbS
          dsimp [margin_pos] at hpos ⊢
          have heq := margin_eq_margin_restrictProfile (P := P) (c := c) (a := a) (b := b)
          simpa [heq] using hpos
        have hltcard : Fintype.card {x : A // x ≠ c} < k := by
          have hltcard' := card_restrict_lt (A := A) c
          simpa [hcard] using hltcard'
        have hrec :
            scoringEliminationAux bordaScore {x : A // x ≠ c} (restrictProfile P c) ⊆ S' :=
          (ih (Fintype.card {x : A // x ≠ c}) hltcard)
            (P := restrictProfile P c) (S := S') hdom' rfl
        have hxS' : (⟨x, hxc⟩ : {x : A // x ≠ c}) ∈ S' := hrec hxsub
        exact (Finset.mem_subtype.mp hxS')
  simpa [hn] using (hStrong (P := P) (S := S) hS rfl)

/-- Baldwin satisfies the Smith criterion. -/
theorem baldwin_smithCriterion : SmithCriterion baldwin := by
  intro V A _ _ P
  classical
  by_cases hA : Nonempty A
  · let _ : Nonempty A := hA
    have hsubset : baldwin P ⊆ topCycleSet (P := P) := by
      have hsubset' :
          scoringEliminationAux bordaScore A P ⊆ topCycleSet (P := P) :=
        baldwin_subset_of_dominatesSet (P := P)
          (S := topCycleSet (P := P)) (topCycleSet_dominates (P := P))
      change scoringEliminationAux bordaScore A P ⊆ topCycleSet (P := P)
      exact hsubset'
    simpa [topCycle, hA] using hsubset
  · have hA' : IsEmpty A := (not_nonempty_iff.mp hA)
    have hcard : Fintype.card A ≤ 1 := by
      have hcard0 : Fintype.card A = 0 := Fintype.card_eq_zero_iff.mpr hA'
      omega
    have hbaldwin : baldwin P = (∅ : Finset A) := by
      -- Unfold and select the base case (empty candidate set).
      simp [baldwin, scoringEliminationRule, scoringEliminationAux]
    simp [topCycle, hA, hbaldwin]

end SocialChoice
