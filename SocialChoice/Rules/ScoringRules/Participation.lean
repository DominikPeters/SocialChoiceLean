import Mathlib.Tactic
import SocialChoice.Axioms.Participation
import SocialChoice.Rules.ScoringRules.Defs

namespace SocialChoice

open Finset

noncomputable def oldVoterEquiv {U : Type} [DecidableEq U] {V : Finset U} {u : U} (hu : u ∉ V) :
    Electorate U V ≃
      {v : Electorate U (insert u V) // v ≠ newVoter (u := u) (V := V) hu} := by
  classical
  refine
    { toFun := fun v =>
        ⟨liftVoter (u := u) v, ?_⟩
      invFun := fun v =>
        ⟨v.1.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro h
    have hval : v.1 = u := congrArg Subtype.val h
    exact hu (by simpa [hval] using v.2)
  · have hmem : v.1.1 ∈ V := by
      have hmem' : v.1.1 = u ∨ v.1.1 ∈ V := by
        simpa using (Finset.mem_insert.mp v.1.2)
      cases hmem' with
      | inl h =>
          have : v.1 = newVoter (u := u) (V := V) hu := by
            apply Subtype.ext
            exact h
          exact (v.2 this).elim
      | inr h => exact h
    exact hmem
  · intro v
    rfl
  · intro v
    apply Subtype.ext
    rfl

lemma scoreCandidate_add_newVoter {U A : Type} [DecidableEq U] [Fintype A] [DecidableEq A]
    {V : Finset U} {u : U} (hu : u ∉ V)
    (P : Profile (Electorate U V) A)
    (Q : Profile (Electorate U (insert u V)) A)
    (hagree : ∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v)
    (scoreFun : Nat → Int) (c : A) :
    scoreCandidate Q scoreFun c =
      scoreCandidate P scoreFun c +
        scoreFun (rank (Q.pref (newVoter (u := u) (V := V) hu)) c) := by
  classical
  have hsumQ :
      (∑ v : Electorate U (insert u V), scoreFun (rank (Q.pref v) c)) =
        scoreFun (rank (Q.pref (newVoter (u := u) (V := V) hu)) c) +
          ∑ v : {v : Electorate U (insert u V) // v ≠ newVoter (u := u) (V := V) hu},
            scoreFun (rank (Q.pref v.1) c) := by
    simpa using
      (Fintype.sum_eq_add_sum_subtype_ne
        (f := fun v : Electorate U (insert u V) => scoreFun (rank (Q.pref v) c))
        (a := newVoter (u := u) (V := V) hu))
  have hsumOld :
      (∑ v : Electorate U V, scoreFun (rank (P.pref v) c)) =
        ∑ v :
            {v : Electorate U (insert u V) // v ≠ newVoter (u := u) (V := V) hu},
          scoreFun (rank (Q.pref v.1) c) := by
    refine Fintype.sum_equiv (oldVoterEquiv (u := u) (V := V) hu)
      (f := fun v : Electorate U V => (scoreFun (rank (P.pref v) c) : Int))
      (g := fun v :
        {v : Electorate U (insert u V) // v ≠ newVoter (u := u) (V := V) hu} =>
          (scoreFun (rank (Q.pref v.1) c) : Int)) ?_
    intro v
    have hEq : ((oldVoterEquiv (u := u) (V := V) hu) v : Electorate U (insert u V)) =
        liftVoter (u := u) v := rfl
    rw [hEq, hagree v]
  have hsumQ' :
      (∑ v : Electorate U (insert u V), scoreFun (rank (Q.pref v) c)) =
        scoreFun (rank (Q.pref (newVoter (u := u) (V := V) hu)) c) +
          ∑ v : Electorate U V, scoreFun (rank (P.pref v) c) := by
    calc
      (∑ v : Electorate U (insert u V), scoreFun (rank (Q.pref v) c)) =
          scoreFun (rank (Q.pref (newVoter (u := u) (V := V) hu)) c) +
            ∑ v :
              {v : Electorate U (insert u V) // v ≠ newVoter (u := u) (V := V) hu},
              scoreFun (rank (Q.pref v.1) c) := hsumQ
      _ = scoreFun (rank (Q.pref (newVoter (u := u) (V := V) hu)) c) +
            ∑ v : Electorate U V, scoreFun (rank (P.pref v) c) := by
          rw [← hsumOld]
  simpa [scoreCandidate, add_comm, add_left_comm, add_assoc] using hsumQ'

lemma rank_lt_of_score_gt {A : Type} [Fintype A] (r : LinearOrder A)
    (score : Nat → Nat → Int) (hmono : weaklyDecreasingScore score) {x y : A}
    (h : score (Fintype.card A) (rank r x) > score (Fintype.card A) (rank r y)) :
    rank r x < rank r y := by
  by_contra hnot
  have hle : rank r y ≤ rank r x := le_of_not_gt hnot
  have hle' : score (Fintype.card A) (rank r x) ≤ score (Fintype.card A) (rank r y) :=
    hmono (Fintype.card A) _ _ hle (rank_lt_card r y) (rank_lt_card r x)
  exact (not_le_of_gt h) hle'

lemma lt_of_rank_lt {A : Type} [Fintype A] (r : LinearOrder A) {x y : A}
    (h : rank r x < rank r y) : r.lt x y := by
  classical
  by_contra hnot
  by_cases hxy : x = y
  · subst hxy
    exact (lt_irrefl _ h)
  · have hlt : r.lt y x := by
      have hlt_or_gt : r.lt x y ∨ r.lt y x := lt_or_gt_of_ne hxy
      cases hlt_or_gt with
      | inl hlt => exact (hnot hlt).elim
      | inr hlt => exact hlt
    have h' : rank r y < rank r x := rank_lt_of_lt r hlt
    exact (lt_asymm h h')

lemma lt_of_score_gt {A : Type} [Fintype A] (r : LinearOrder A)
    (score : Nat → Nat → Int) (hmono : weaklyDecreasingScore score) {x y : A}
    (h : score (Fintype.card A) (rank r x) > score (Fintype.card A) (rank r y)) :
    r.lt x y :=
  lt_of_rank_lt r (rank_lt_of_score_gt r score hmono h)

theorem scoringRule_strongFishburnParticipation (score : Nat → Nat → Int)
    (hmono : weaklyDecreasingScore score) :
    StrongFishburnParticipation (scoringRule score) := by
  intro U A _ _ _ _ V u hu P Q hagree
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · let scoreFun : Nat → Int := fun r => score (Fintype.card A) r
    let r := Q.pref (newVoter (u := u) (V := V) hu)
    let _ : DecidableEq A := r.toDecidableEq
    have hscore :
        ∀ c : A,
          scoreCandidate Q scoreFun c =
            scoreCandidate P scoreFun c + scoreFun (rank r c) := by
      intro c
      simpa [r] using
        (scoreCandidate_add_newVoter (u := u) (V := V) hu P Q hagree scoreFun c)
    refine ?_
    constructor
    · intro x hx y hy
      have hxQ : x ∈ scoringRule score Q := (Finset.mem_sdiff.mp hx).1
      have hyQ : y ∈ scoringRule score Q := (Finset.mem_inter.mp hy).1
      have hyP : y ∈ scoringRule score P := (Finset.mem_inter.mp hy).2
      have hxP : x ∉ scoringRule score P := (Finset.mem_sdiff.mp hx).2
      have hQle : scoreCandidate Q scoreFun y ≤ scoreCandidate Q scoreFun x := by
        have hxQ' : x ∈ scoringWinners Q scoreFun := by
          simpa [scoringRule, scoreFun] using hxQ
        have := (scoringWinners_iff_forall_le Q scoreFun hA x).1 hxQ'
        exact this y
      have hPgt : scoreCandidate P scoreFun x < scoreCandidate P scoreFun y := by
        have hyP' : y ∈ scoringWinners P scoreFun := by
          simpa [scoringRule, scoreFun] using hyP
        have hPmax : ∀ d, scoreCandidate P scoreFun d ≤ scoreCandidate P scoreFun y :=
          (scoringWinners_iff_forall_le P scoreFun hA y).1 hyP'
        have hxP' : ¬ ∀ d, scoreCandidate P scoreFun d ≤ scoreCandidate P scoreFun x := by
          intro h
          exact hxP ((scoringWinners_iff_forall_le P scoreFun hA x).2 h)
        have hxPexists : ∃ d, scoreCandidate P scoreFun x < scoreCandidate P scoreFun d := by
          simpa [not_forall, not_le] using hxP'
        rcases hxPexists with ⟨d, hxd⟩
        exact lt_of_lt_of_le hxd (hPmax d)
      have hdelta : scoreFun (rank r x) > scoreFun (rank r y) := by
        have hQle' :
            scoreCandidate P scoreFun y + scoreFun (rank r y) ≤
              scoreCandidate P scoreFun x + scoreFun (rank r x) := by
          simpa [hscore, add_comm, add_left_comm, add_assoc] using hQle
        linarith
      exact le_of_lt (lt_of_score_gt r score hmono hdelta)
    · constructor
      · intro y hy z hz
        have hyQ : y ∈ scoringRule score Q := (Finset.mem_inter.mp hy).1
        have hyP : y ∈ scoringRule score P := (Finset.mem_inter.mp hy).2
        have hzP : z ∈ scoringRule score P := (Finset.mem_sdiff.mp hz).1
        have hzQ : z ∉ scoringRule score Q := (Finset.mem_sdiff.mp hz).2
        have hQgt : scoreCandidate Q scoreFun z < scoreCandidate Q scoreFun y := by
          have hyQ' : y ∈ scoringWinners Q scoreFun := by
            simpa [scoringRule, scoreFun] using hyQ
          have hQmax : ∀ d, scoreCandidate Q scoreFun d ≤ scoreCandidate Q scoreFun y :=
            (scoringWinners_iff_forall_le Q scoreFun hA y).1 hyQ'
          have hzQ' : ¬ ∀ d, scoreCandidate Q scoreFun d ≤ scoreCandidate Q scoreFun z := by
            intro h
            exact hzQ ((scoringWinners_iff_forall_le Q scoreFun hA z).2 h)
          have hzQexists : ∃ d, scoreCandidate Q scoreFun z < scoreCandidate Q scoreFun d := by
            simpa [not_forall, not_le] using hzQ'
          rcases hzQexists with ⟨d, hzd⟩
          exact lt_of_lt_of_le hzd (hQmax d)
        have hP_eq : scoreCandidate P scoreFun y = scoreCandidate P scoreFun z := by
          have hyP' : y ∈ scoringWinners P scoreFun := by
            simpa [scoringRule, scoreFun] using hyP
          have hzP' : z ∈ scoringWinners P scoreFun := by
            simpa [scoringRule, scoreFun] using hzP
          have hPmax_y : ∀ d, scoreCandidate P scoreFun d ≤ scoreCandidate P scoreFun y :=
            (scoringWinners_iff_forall_le P scoreFun hA y).1 hyP'
          have hPmax_z : ∀ d, scoreCandidate P scoreFun d ≤ scoreCandidate P scoreFun z :=
            (scoringWinners_iff_forall_le P scoreFun hA z).1 hzP'
          exact le_antisymm (hPmax_z y) (hPmax_y z)
        have hQgt' :
            scoreCandidate P scoreFun z + scoreFun (rank r z) <
              scoreCandidate P scoreFun y + scoreFun (rank r y) := by
          simpa [hscore, add_comm, add_left_comm, add_assoc] using hQgt
        have hdelta : scoreFun (rank r y) > scoreFun (rank r z) := by
          linarith [hQgt', hP_eq]
        exact le_of_lt (lt_of_score_gt r score hmono hdelta)
      · intro x hx z hz
        have hxQ : x ∈ scoringRule score Q := (Finset.mem_sdiff.mp hx).1
        have hxP : x ∉ scoringRule score P := (Finset.mem_sdiff.mp hx).2
        have hzP : z ∈ scoringRule score P := (Finset.mem_sdiff.mp hz).1
        have hzQ : z ∉ scoringRule score Q := (Finset.mem_sdiff.mp hz).2
        have hQgt : scoreCandidate Q scoreFun z < scoreCandidate Q scoreFun x := by
          have hxQ' : x ∈ scoringWinners Q scoreFun := by
            simpa [scoringRule, scoreFun] using hxQ
          have hQmax : ∀ d, scoreCandidate Q scoreFun d ≤ scoreCandidate Q scoreFun x :=
            (scoringWinners_iff_forall_le Q scoreFun hA x).1 hxQ'
          have hzQ' : ¬ ∀ d, scoreCandidate Q scoreFun d ≤ scoreCandidate Q scoreFun z := by
            intro h
            exact hzQ ((scoringWinners_iff_forall_le Q scoreFun hA z).2 h)
          have hzQexists : ∃ d, scoreCandidate Q scoreFun z < scoreCandidate Q scoreFun d := by
            simpa [not_forall, not_le] using hzQ'
          rcases hzQexists with ⟨d, hzd⟩
          exact lt_of_lt_of_le hzd (hQmax d)
        have hPgt : scoreCandidate P scoreFun x < scoreCandidate P scoreFun z := by
          have hzP' : z ∈ scoringWinners P scoreFun := by
            simpa [scoringRule, scoreFun] using hzP
          have hPmax : ∀ d, scoreCandidate P scoreFun d ≤ scoreCandidate P scoreFun z :=
            (scoringWinners_iff_forall_le P scoreFun hA z).1 hzP'
          have hxP' : ¬ ∀ d, scoreCandidate P scoreFun d ≤ scoreCandidate P scoreFun x := by
            intro h
            exact hxP ((scoringWinners_iff_forall_le P scoreFun hA x).2 h)
          have hxPexists : ∃ d, scoreCandidate P scoreFun x < scoreCandidate P scoreFun d := by
            simpa [not_forall, not_le] using hxP'
          rcases hxPexists with ⟨d, hxd⟩
          exact lt_of_lt_of_le hxd (hPmax d)
        have hQgt' :
            scoreCandidate P scoreFun z + scoreFun (rank r z) <
              scoreCandidate P scoreFun x + scoreFun (rank r x) := by
          simpa [hscore, add_comm, add_left_comm, add_assoc] using hQgt
        have hdelta : scoreFun (rank r x) > scoreFun (rank r z) := by
          linarith [hQgt', hPgt]
        exact le_of_lt (lt_of_score_gt r score hmono hdelta)
  · simp [FishburnExtension, FishburnWeak, scoringRule, scoringWinners, hA]

end SocialChoice
