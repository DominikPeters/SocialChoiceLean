import SocialChoice.Axioms.Pareto
import SocialChoice.Rules.ScoringRules.Borda.Defs
import SocialChoice.Rules.ScoringRules.Borda.C2Borda
import SocialChoice.Rules.ScoringRules.Pareto

namespace SocialChoice

open Finset

theorem borda_pareto_efficiency : ParetoEfficiency borda := by
  intro V A _ _ _ P c d hpref hd
  classical
  have hstrict : strictlyDecreasingScore bordaScore := bordaScore_strictlyDecreasing
  have hpareto : ParetoEfficiency (scoringRule bordaScore) :=
    scoringRule_pareto_nonempty (score := bordaScore) hstrict
  simpa [borda] using (hpareto (P := P) (c := c) (d := d) hpref hd)

end SocialChoice
