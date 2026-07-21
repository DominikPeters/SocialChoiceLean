import SocialChoice.Axioms.Anonymity
import SocialChoice.Rules.ScoringRules.Defs

namespace SocialChoice

-- Any scoring rule is anonymous.
theorem scoringRule_anonymous (score : Nat → Nat → Int) : Anonymity (scoringRule score) := by
  intro V A _ _ P σ
  classical
  have score_perm :
      ∀ (score : Nat → Int) (c : A),
        scoreCandidate (permuteVoters P σ) score c = scoreCandidate P score c := by
    intro score c
    unfold scoreCandidate
    refine Finset.sum_equiv (s := (Finset.univ : Finset V))
      (t := (Finset.univ : Finset V)) (e := σ) ?_ ?_
    · intro v
      simp
    · intro v hv
      exact rfl
  unfold scoringRule
  by_cases h : (Finset.univ : Finset A).Nonempty
  · simp [scoringWinners, h, score_perm]
  · simp [scoringWinners, h]

end SocialChoice
