import SocialChoice.Profile
import SocialChoice.Meta

namespace SocialChoice

@[implicit_reducible] def reverse_ballot {A : Type} (r : LinearOrder A) : LinearOrder A :=
  LinearOrder.swap A r

def reverse_profile {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) : Profile V A :=
  { pref := fun v => reverse_ballot (P.pref v) }

@[simp] lemma prefers_reverse_profile {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (a b : A) :
    Prefers (reverse_profile P) v a b ↔ Prefers P v b a := by
  rfl

@[scAxiom]
def SingletonReversalSymmetry (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) (x : A),
    (∃ y, x ≠ y) → f P = {x} → x ∉ f (reverse_profile P)

@[scAxiom]
def ReversalSymmetry (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [DecidableEq A] (P : Profile V A),
    f P ≠ Finset.univ → f P ∩ f (reverse_profile P) = ∅

-- Neutral Reversal (Donald G. Saari, Capturing the "will of the people", 2003).
@[scAxiom]
def NeutralReversal (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) (r : LinearOrder A),
    f P = f (addVoter (addVoter P r) (reverse_ballot r))

end SocialChoice
