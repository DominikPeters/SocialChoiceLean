import SocialChoice.Axioms.Anonymity
import SocialChoice.Rules.ScoringElimination.Basic

namespace SocialChoice

open Finset
open scoped BigOperators

lemma scoreCandidate_permuteVoters {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm V) (score : Nat → Int) (c : A) :
    scoreCandidate (permuteVoters P σ) score c = scoreCandidate P score c := by
  classical
  unfold scoreCandidate
  refine Finset.sum_equiv (s := (Finset.univ : Finset V))
    (t := (Finset.univ : Finset V)) (e := σ) ?_ ?_
  · intro v
    simp
  · intro v hv
    simp [rank]
    rfl

lemma lowestScoring_permuteVoters {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (σ : Equiv.Perm V) (score : Nat → Int) :
    lowestScoring (permuteVoters P σ) score = lowestScoring P score := by
  classical
  have score_perm :
      ∀ c : A, scoreCandidate (permuteVoters P σ) score c = scoreCandidate P score c := by
    intro c
    exact scoreCandidate_permuteVoters (P := P) (σ := σ) (score := score) (c := c)
  by_cases h : (Finset.univ : Finset A).Nonempty
  · simp [lowestScoring, h, score_perm]
  · simp [lowestScoring, h]

lemma restrictProfile_permuteVoters {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (σ : Equiv.Perm V) (c : A) :
    restrictProfile (permuteVoters P σ) c = permuteVoters (restrictProfile P c) σ := by
  rfl

theorem scoringEliminationAux_anonymous
    (score : Nat → Nat → Int)
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (σ : Equiv.Perm V) :
    scoringEliminationAux score A (permuteVoters P σ) =
      scoringEliminationAux score A P := by
  classical
  set n := Fintype.card A with hn
  let Motive : Nat → Prop := fun k =>
    ∀ {A' : Type} [Fintype A'] [DecidableEq A'] {V' : Type} [Fintype V']
      (P' : Profile V' A') (σ' : Equiv.Perm V'),
        Fintype.card A' = k →
        scoringEliminationAux score A' (permuteVoters P' σ') =
          scoringEliminationAux score A' P'
  have hStrong : Motive n := by
    classical
    refine Nat.strongRecOn (motive := Motive) n ?_
    intro k ih A' _ _ V' _ P' σ' hk
    by_cases hle : Fintype.card A' ≤ 1
    · simp [scoringEliminationAux, hle]
    ·
      let m := Fintype.card A'
      let scoreVec : Nat → Int := fun r => score m r
      have hlowest :
          lowestScoring (permuteVoters P' σ') scoreVec =
            lowestScoring P' scoreVec := by
        simpa [m, scoreVec] using
          (lowestScoring_permuteVoters (P := P') (σ := σ') (score := scoreVec))
      have haux1 :=
        scoringEliminationAux_eq_biUnion_of_not_card_le_one
          (score := score) (P := permuteVoters P' σ') (A := A') (hcard := hle)
      have haux2 :=
        scoringEliminationAux_eq_biUnion_of_not_card_le_one
          (score := score) (P := P') (A := A') (hcard := hle)
      have hbranch :
          ∀ c : A',
            liftFinset (scoringEliminationAux score _ (restrictProfile (permuteVoters P' σ') c)) =
              liftFinset (scoringEliminationAux score _ (restrictProfile P' c)) := by
        intro c
        have hcard_sub_lt : Fintype.card {x : A' // x ≠ c} < Fintype.card A' :=
          card_restrict_lt c
        have hklt : Fintype.card {x : A' // x ≠ c} < k := by
          simpa [hk] using hcard_sub_lt
        have hrec :=
          (ih (Fintype.card {x : A' // x ≠ c}) hklt
            (A' := {x : A' // x ≠ c})
            (V' := V')
            (P' := restrictProfile P' c)
            (σ' := σ')
            (by rfl))
        have hrec' :
            scoringEliminationAux score {x : A' // x ≠ c}
              (restrictProfile (permuteVoters P' σ') c) =
              scoringEliminationAux score {x : A' // x ≠ c} (restrictProfile P' c) := by
          simpa [restrictProfile_permuteVoters] using hrec
        simp [hrec']
      apply Finset.ext
      intro x
      constructor
      · intro hx
        have hx' :
            x ∈ (lowestScoring (permuteVoters P' σ') scoreVec).biUnion
              (fun c => liftFinset
                (scoringEliminationAux score _ (restrictProfile (permuteVoters P' σ') c))) := by
          simpa [haux1, m, scoreVec] using hx
        rcases Finset.mem_biUnion.mp hx' with ⟨c, hc, hxmem⟩
        have hc' : c ∈ lowestScoring P' scoreVec := by
          simpa [hlowest] using hc
        have hxmem' :
            x ∈ liftFinset (scoringEliminationAux score _ (restrictProfile P' c)) := by
          simpa [hbranch c] using hxmem
        have : x ∈ (lowestScoring P' scoreVec).biUnion
            (fun c => liftFinset (scoringEliminationAux score _ (restrictProfile P' c))) := by
          exact Finset.mem_biUnion.mpr ⟨c, hc', hxmem'⟩
        simpa [haux2, m, scoreVec] using this
      · intro hx
        have hx' :
            x ∈ (lowestScoring P' scoreVec).biUnion
              (fun c => liftFinset (scoringEliminationAux score _ (restrictProfile P' c))) := by
          simpa [haux2, m, scoreVec] using hx
        rcases Finset.mem_biUnion.mp hx' with ⟨c, hc, hxmem⟩
        have hc' : c ∈ lowestScoring (permuteVoters P' σ') scoreVec := by
          simpa [hlowest] using hc
        have hxmem' :
            x ∈ liftFinset
              (scoringEliminationAux score _ (restrictProfile (permuteVoters P' σ') c)) := by
          simpa [hbranch c] using hxmem
        have : x ∈ (lowestScoring (permuteVoters P' σ') scoreVec).biUnion
            (fun c => liftFinset
              (scoringEliminationAux score _ (restrictProfile (permuteVoters P' σ') c))) := by
          exact Finset.mem_biUnion.mpr ⟨c, hc', hxmem'⟩
        simpa [haux1, m, scoreVec] using this
  simpa [hn] using (hStrong (P' := P) (σ' := σ) rfl)

theorem scoringEliminationRule_anonymous (score : Nat → Nat → Int) :
    Anonymity (scoringEliminationRule score) := by
  intro V A _ _ P σ
  classical
  simpa [scoringEliminationRule] using
    (scoringEliminationAux_anonymous (score := score) (P := P) (σ := σ))

end SocialChoice
