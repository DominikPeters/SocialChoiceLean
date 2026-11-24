import SocialChoice.Margin
import SocialChoice.Rules.ScoringElimination.Defs

namespace SocialChoice

open Finset

/-!
# Basic lemmas for scoring elimination rules

This file collects general-purpose lemmas about scoring elimination rules and
profile restriction, so they can be reused across proofs.
-/

/-!
### A light recursion equation for scoring elimination

We avoid `simp [scoringEliminationAux, ...]` in large proofs because it tends to
unfold recursive calls and can hit heartbeat limits. The lemma below unfolds only
the *head* occurrence using `unfold1` and then selects the recursive branch.
-/

lemma scoringEliminationAux_eq_biUnion_of_not_card_le_one
    {V : Type} [Fintype V]
    (score : Nat → Nat → Int)
    {A : Type} [Fintype A] [DecidableEq A]
    (P : Profile V A) (hcard : ¬ Fintype.card A ≤ 1) :
    scoringEliminationAux score A P =
      let m := Fintype.card A
      let scoreVec : Nat → Int := fun r => score m r
      let L : Finset A := lowestScoring P scoreVec
      L.biUnion (fun c => liftFinset (scoringEliminationAux score _ (restrictProfile P c))) := by
  classical
  -- Avoid unfolding recursive calls: keep the RHS as a local definition.
  let rhs : Finset A :=
    let m := Fintype.card A
    let scoreVec : Nat → Int := fun r => score m r
    let L : Finset A := lowestScoring P scoreVec
    L.biUnion (fun c => liftFinset (scoringEliminationAux score _ (restrictProfile P c)))
  -- Unfold only the head `scoringEliminationAux` (not the recursive calls inside `rhs`).
  change scoringEliminationAux score A P = rhs
  conv_lhs =>
    unfold SocialChoice.scoringEliminationAux
  -- Now we just select the recursive branch of the `by_cases`.
  simp [hcard, rhs]

/-! ## Basic nonemptiness of winners -/

lemma scoringEliminationAux_nonempty
    (score : Nat → Nat → Int)
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : Profile V A) :
    (scoringEliminationAux score A P).Nonempty := by
  classical
  -- Strong induction on the number of candidates.
  set n := Fintype.card A with hn
  -- Motive generalized over candidate types of a given cardinality.
  let Motive : Nat → Prop := fun k =>
    ∀ {A' : Type} [Fintype A'] [DecidableEq A'] [Nonempty A']
      {V' : Type} [Fintype V']
      (P' : Profile V' A'),
        Fintype.card A' = k → (scoringEliminationAux score A' P').Nonempty
  have hStrong : Motive n := by
    classical
    refine Nat.strongRecOn (motive := Motive) n ?_
    intro k ih A' _ _ _ V' _ P' hk
    by_cases hle : Fintype.card A' ≤ 1
    · -- Base case: definition returns `univ`.
      have hdef : scoringEliminationAux score A' P' = (Finset.univ : Finset A') := by
        simp [scoringEliminationAux, hle]
      rw [hdef]
      exact (Finset.univ_nonempty : (Finset.univ : Finset A').Nonempty)
    · -- Recursive case: pick a lowest-scoring candidate and recurse.
      have haux :=
        scoringEliminationAux_eq_biUnion_of_not_card_le_one
          (score := score) (P := P') (hcard := hle)
      -- Unpack the RHS.
      classical
      let m := Fintype.card A'
      let scoreVec : Nat → Int := fun r => score m r
      let L : Finset A' := lowestScoring P' scoreVec
      have hLne : L.Nonempty := by
        apply lowestScoring_nonempty
        exact (Finset.univ_nonempty : (Finset.univ : Finset A').Nonempty)
      rcases hLne with ⟨ℓ, hℓL⟩
      -- Apply IH on the restricted candidate type.
      have hcard_sub_lt : Fintype.card {x : A' // x ≠ ℓ} < Fintype.card A' :=
        card_restrict_lt ℓ
      have hrec : (scoringEliminationAux score {x : A' // x ≠ ℓ} (restrictProfile P' ℓ)).Nonempty := by
        -- IH expects a strict smaller cardinality.
        have hklt : Fintype.card {x : A' // x ≠ ℓ} < k := by
          -- `card {x // x ≠ ℓ} < card A' = k`.
          simpa [hk] using hcard_sub_lt
        have : Nonempty {x : A' // x ≠ ℓ} := by
          -- Since `card A' > 1` in this branch, removing one element leaves something.
          have : 0 < Fintype.card {x : A' // x ≠ ℓ} := by
            have hposA : 1 < Fintype.card A' := by omega
            have hsub := card_subtype_ne_eq ℓ
            -- card subtype = card A' - 1
            have : Fintype.card {x : A' // x ≠ ℓ} = Fintype.card A' - 1 := hsub
            -- hence positive
            omega
          exact Fintype.card_pos_iff.mp this
        exact ih (Fintype.card {x : A' // x ≠ ℓ}) hklt (P' := restrictProfile P' ℓ) rfl
      rcases hrec with ⟨w, hw⟩
      -- Build an element in the biUnion.
      refine ⟨(w : A'), ?_⟩
      -- Rewrite using `haux` and show membership in the RHS.
      -- (We avoid `simp` over the `let`s by unfolding them locally.)
      have hw_lift : (w : A') ∈ liftFinset (scoringEliminationAux score _ (restrictProfile P' ℓ)) := by
        -- `liftFinset` is `image Subtype.val`.
        refine Finset.mem_image.mpr ?_
        exact ⟨w, hw, rfl⟩
      -- Now place it into the biUnion.
      have : (w : A') ∈
          (lowestScoring P' scoreVec).biUnion
            (fun c => liftFinset (scoringEliminationAux score _ (restrictProfile P' c))) := by
        refine Finset.mem_biUnion.mpr ?_
        refine ⟨ℓ, ?_, ?_⟩
        · simpa [L, scoreVec, m] using hℓL
        · simpa [scoreVec, m] using hw_lift
      -- Convert back to the LHS using `haux`.
      simpa [haux, m, scoreVec, L] using this
  -- Specialize the strong induction result.
  simpa [hn] using (hStrong (P' := P) rfl)

theorem scoringEliminationRule_isVotingRule
    (score : Nat → Nat → Int) : IsVotingRule (scoringEliminationRule score) := by
  intro V A _ _ _ P
  classical
  simpa [scoringEliminationRule] using (scoringEliminationAux_nonempty (score := score) (P := P))

end SocialChoice
