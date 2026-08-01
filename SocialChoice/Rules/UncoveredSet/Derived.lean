import SocialChoice.Axioms.Implications
import SocialChoice.Impossibilities.CondorcetReinforcement
import SocialChoice.Impossibilities.CondorcetParticipation
import SocialChoice.Rules.UncoveredSet.Smith
import SocialChoice.Rules.UncoveredSet.InformationalBasis
import SocialChoice.Rules.UncoveredSet.Involvement
import SocialChoice.Rules.UncoveredSet.Independence
import SocialChoice.Rules.UncoveredSet.Monotonicity

namespace SocialChoice

theorem uncoveredSet_mutualMajorityCriterion : MutualMajorityCriterion uncoveredSet := by
  apply Implies.apply smithCriterion_implies_mutualMajorityCriterion_Imp (f := uncoveredSet)
  · exact uncoveredSet_isVotingRule
  · exact uncoveredSet_smithCriterion

theorem uncoveredSet_condorcetConsistency : CondorcetConsistency uncoveredSet := by
  apply Implies.apply smithCriterion_implies_condorcetConsistency_Imp (f := uncoveredSet)
  · exact uncoveredSet_isVotingRule
  · exact uncoveredSet_smithCriterion

theorem uncoveredSet_condorcetLoserCriterion : CondorcetLoserCriterion uncoveredSet := by
  apply Implies.apply smithCriterion_implies_condorcetLoserCriterion_Imp (f := uncoveredSet)
  · exact uncoveredSet_isVotingRule
  · exact uncoveredSet_smithCriterion

theorem uncoveredSet_majorityCriterion : MajorityCriterion uncoveredSet := by
  apply Implies.apply condorcetConsistency_implies_majorityCriterion (f := uncoveredSet)
  · exact uncoveredSet_isVotingRule
  · exact uncoveredSet_condorcetConsistency

theorem uncoveredSet_unanimity : Unanimity uncoveredSet := by
  apply Implies.apply majorityCriterion_implies_unanimity (f := uncoveredSet)
  · exact uncoveredSet_isVotingRule
  · exact uncoveredSet_majorityCriterion

theorem uncoveredSet_majorityLoserCriterion : MajorityLoserCriterion uncoveredSet := by
  apply Implies.apply condorcetLoserCriterion_implies_majorityLoserCriterion (f := uncoveredSet)
  · exact uncoveredSet_isVotingRule
  · exact uncoveredSet_condorcetLoserCriterion

theorem uncoveredSet_anonymous : Anonymity uncoveredSet := by
  apply Implies.apply marginBased_implies_anonymity (f := uncoveredSet)
  · exact uncoveredSet_isVotingRule
  · exact uncoveredSet_marginBased

theorem uncoveredSet_not_subsetReinforcement : ¬ SubsetReinforcement uncoveredSet := by
  intro hsub
  exact no_condorcet_subset_reinforcement uncoveredSet
    uncoveredSet_isVotingRule uncoveredSet_condorcetConsistency hsub

theorem uncoveredSet_not_reinforcement : ¬ Reinforcement uncoveredSet := by
  intro hrein
  exact no_condorcet_reinforcement uncoveredSet
    uncoveredSet_isVotingRule uncoveredSet_condorcetConsistency hrein

theorem uncoveredSet_not_strongFishburnParticipation :
    ¬ StrongFishburnParticipation uncoveredSet := by
  intro hpart
  exact no_condorcet_strongFishburn_participation_m4_n12
    ⟨uncoveredSet, uncoveredSet_isVotingRule, uncoveredSet_condorcetConsistency, hpart⟩

theorem uncoveredSet_not_optimistParticipation : ¬ OptimistParticipation uncoveredSet := by
  intro hpart
  exact CondorcetOptimistParticipation.no_condorcet_optimist_participation_m4_n17
    ⟨uncoveredSet, uncoveredSet_condorcetConsistency, hpart⟩

theorem uncoveredSet_not_positiveInvolvement : ¬ PositiveInvolvement uncoveredSet := by
  intro hpos
  have hiff : PositiveInvolvement uncoveredSet ↔ NegativeInvolvement uncoveredSet :=
    Implies.apply marginBased_positiveInvolvement_iff_negativeInvolvement
      (f := uncoveredSet) uncoveredSet_isVotingRule uncoveredSet_marginBased
  exact uncoveredSet_not_negativeInvolvement (hiff.mp hpos)

end SocialChoice
