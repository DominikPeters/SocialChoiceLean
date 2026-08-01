import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max
import SocialChoice.ArgExtrema
import SocialChoice.Rank

namespace SocialChoice

open Finset
open scoped BigOperators

-- Total score for a candidate under a scoring vector.
def scoreCandidate {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (score : Nat → Int) (c : A) : Int :=
  ((Finset.univ : Finset V).sum fun v => score (rank (P.pref v) c))

-- Winners for a given scoring vector.
noncomputable def scoringWinners {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (score : Nat → Int) : Finset A := by
  classical
  by_cases h : (Finset.univ : Finset A).Nonempty
  · let maxScore : Int :=
      (Finset.univ.image (fun c => scoreCandidate P score c)).max' (h.image _)
    exact
      (Finset.univ.filter (fun c => scoreCandidate P score c = maxScore))
  · exact ∅

/-- `scoringWinners` is an instance of the generic `argmaxSet`. -/
lemma scoringWinners_eq_argmaxSet {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (score : Nat → Int) :
    scoringWinners P score = argmaxSet Finset.univ (scoreCandidate P score) := by
  classical
  unfold scoringWinners argmaxSet
  by_cases hA : (Finset.univ : Finset A).Nonempty <;> simp [hA]

lemma scoringWinners_iff_forall_le {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (score : Nat → Int) (_hA : (Finset.univ : Finset A).Nonempty) (c : A) :
    c ∈ scoringWinners P score ↔
      ∀ d : A, scoreCandidate P score d ≤ scoreCandidate P score c := by
  rw [scoringWinners_eq_argmaxSet, mem_argmaxSet_iff]
  simp

-- Generic positional scoring rule.
noncomputable def scoringRule (score : Nat → Nat → Int) : VotingRule :=
  fun {V A} _ _ (P : Profile V A) =>
    scoringWinners P (fun r => score (Fintype.card A) r)

lemma mem_scoringRule_castCandidates_iff {V A : Type} [Fintype V] [Fintype A]
    (score : Nat → Nat → Int) {p q : A → Prop}
    (dp : DecidablePred p) (dq : DecidablePred q)
    (h : p = q) (x : {a : A // p a}) (P : Profile V {a : A // p a}) :
    x ∈ scoringRule score P ↔
      ((cast (congrArg (fun r => {a : A // r a}) h) x : {a : A // q a}) ∈
        scoringRule score (castCandidates (p := p) (q := q) h P)) := by
  classical
  letI : DecidablePred p := dp
  letI : DecidablePred q := dq
  cases h
  cases (Subsingleton.elim dq dp)
  rfl

lemma scoringWinners_nonempty {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (P : Profile V A) (score : Nat → Int) : (scoringWinners P score).Nonempty := by
  rw [scoringWinners_eq_argmaxSet]
  exact argmaxSet_nonempty Finset.univ_nonempty _

theorem scoringRule_isVotingRule (score : Nat → Nat → Int) : IsVotingRule (scoringRule score) := by
  intro V A _ _ _ P
  classical
  simpa [scoringRule] using
    (scoringWinners_nonempty (P := P) (score := fun r => score (Fintype.card A) r))

def weaklyDecreasingScore (score : Nat → Nat → Int) : Prop :=
  ∀ m r s, r ≤ s → r < m → s < m → score m s ≤ score m r

def strictlyDecreasingScore (score : Nat → Nat → Int) : Prop :=
  ∀ m r s, r < s → r < m → s < m → score m s < score m r

lemma strictlyDecreasingScore.to_weakly {score : Nat → Nat → Int}
    (hstrict : strictlyDecreasingScore score) : weaklyDecreasingScore score := by
  intro m r s hrs hrm hsm
  rcases lt_or_eq_of_le hrs with hlt | hEq
  · exact (hstrict m r s hlt hrm hsm).le
  · simp [hEq]

end SocialChoice
