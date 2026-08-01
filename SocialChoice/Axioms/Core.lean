import SocialChoice.Profile
import SocialChoice.Axioms.Resolute
import SocialChoice.Meta

namespace SocialChoice

/-!
# Core Voting Rule Properties

This file collects basic properties of voting rules.
The `Resolute` definition is in `Axioms/Resolute.lean`.
-/

/-- A voting rule is non-trivial if some candidate can lose. -/
@[scAxiom]
def NonTrivial (f : VotingRule) : Prop :=
  ∃ (V A : Type) (instV : Fintype V) (instA : Fintype A),
    let _ := instV
    let _ := instA
    ∃ (P : Profile V A) (c : A), c ∉ f P

/-- A voting rule is onto if every candidate can be the unique winner at some profile.

The `[Nonempty V]` guard is essential: without it the axiom is unsatisfiable,
since over the empty electorate there is exactly one profile, whose winner set
cannot equal `{c}` for two distinct candidates `c`. -/
@[scAxiom]
def Onto (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [Nonempty V] (c : A), ∃ P : Profile V A, f P = {c}

end SocialChoice
