import SocialChoice.Rules.ScoringElimination.Defs
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringRules.Veto.Defs
import SocialChoice.Meta

namespace SocialChoice

/-!
# Coombs' Method

Coombs' method is a scoring elimination rule based on anti-plurality (veto) scoring.

In each round, candidates are scored by the number of voters who do NOT rank them last.
Equivalently, each candidate receives 1 point from each voter except those who rank
them in the last position. The candidate(s) with the lowest score (i.e., the most
last-place rankings) are eliminated, and the process repeats until one candidate remains.

When there are ties for elimination, we use parallel-universe tie-breaking.

**Definitional variant.** This formalization eliminates until a single
candidate remains, with *no majority-stopping condition*. Coombs' original
rule stops as soon as some candidate has a strict majority of first places,
and — unlike for instant-runoff voting, where the two conventions coincide —
this genuinely matters: a strict-majority-top candidate can simultaneously be
(tied for) most-last-placed and get eliminated. Consequently the rule
formalized here does **not** satisfy `MajorityCriterion` (only
`MajorityLoserCriterion`, see `Coombs/Majority.lean`), whereas
majority-stopping Coombs trivially satisfies it. Example (n = 100 over
{a,b,c}): 49 × a≻b≻c, 2 × a≻c≻b, 47 × b≻c≻a, 2 × c≻b≻a — candidate `a` has 51
first places but ties with `c` for most last places, and this rule returns
{a, b}.
-/

/-- Coombs' method (veto/anti-plurality elimination). -/
@[scRule]
noncomputable def coombs : VotingRule :=
  scoringEliminationRule vetoScore

/-- Alias for Coombs' method. -/
noncomputable abbrev vetoElimination : VotingRule := coombs

theorem coombs_isVotingRule : IsVotingRule coombs := by
  intro V A _ _ _ P
  classical
  simpa [coombs] using
    (scoringEliminationRule_isVotingRule (score := vetoScore) (V := V) (A := A) (P := P))

theorem vetoElimination_isVotingRule : IsVotingRule vetoElimination := by
  intro V A _ _ _ P
  simpa [vetoElimination] using (coombs_isVotingRule (V := V) (A := A) (P := P))

end SocialChoice
