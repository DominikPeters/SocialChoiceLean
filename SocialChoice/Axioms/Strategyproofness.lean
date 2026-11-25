import SocialChoice.Profile
import SocialChoice.Axioms.Core
import SocialChoice.Meta

namespace SocialChoice

/-- Replace one voter's ballot with a new linear order. -/
noncomputable def updateProfile {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (ballot : LinearOrder A) : Profile V A := by
  classical
  exact { pref := fun w => if w = v then ballot else P.pref w }

lemma updateProfile_pref_self {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (ballot : LinearOrder A) :
    (updateProfile P v ballot).pref v = ballot :=
  ite_eq_left rfl

lemma updateProfile_pref_of_ne {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {v w : V} (ballot : LinearOrder A) (h : w ≠ v) :
    (updateProfile P v ballot).pref w = P.pref w :=
  ite_eq_right h

/-- Strategyproofness for resolute rules: no voter can gain by misreporting. -/
@[scAxiom]
def ResoluteStrategyproofness (f : VotingRule) (_hf : Resolute f) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A]
      (P : Profile V A) (v : V) (ballot : LinearOrder A) (x y : A),
    f P = {x} →
    f (updateProfile P v ballot) = {y} →
    ¬ Prefers P v y x

/-!
# Strategyproofness for Multi-Valued Voting Rules (Duggan-Schwartz)

The Duggan-Schwartz theorem uses different notions of strategyproofness
for voting rules that may return multiple winners. An **optimist** wants
to improve the best outcome, while a **pessimist** wants to improve the
worst outcome in the winner set.
-/

/-- A voting system can be manipulated by an **optimist** if some voter can
    file a disingenuous ballot such that at least one new winner is preferred
    (according to their true preferences) to ALL old winners.

    Equivalently: the max of the new winner set (under true preferences)
    is better than the max of the old winner set.

    We say a system is **optimist strategyproof** if no such manipulation exists. -/
@[scAxiom]
def OptimistStrategyproof (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A]
      (P : Profile V A) (v : V) (ballot : LinearOrder A),
    ¬∃ y ∈ f (updateProfile P v ballot),
        ∀ x ∈ f P, Prefers P v y x

/-- A voting system can be manipulated by a **pessimist** if some voter can
    file a disingenuous ballot such that ALL new winners are preferred
    (according to their true preferences) to at least one old winner.

    Equivalently: the min of the new winner set (under true preferences)
    is better than the min of the old winner set.

    We say a system is **pessimist strategyproof** if no such manipulation exists. -/
@[scAxiom]
def PessimistStrategyproof (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A]
      (P : Profile V A) (v : V) (ballot : LinearOrder A),
    ¬∃ x ∈ f P,
        ∀ y ∈ f (updateProfile P v ballot), Prefers P v y x

end SocialChoice
