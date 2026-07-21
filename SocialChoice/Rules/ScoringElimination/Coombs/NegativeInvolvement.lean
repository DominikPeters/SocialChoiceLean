import Mathlib.Tactic
import SocialChoice.Axioms.Participation
import SocialChoice.Rank
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Coombs.Defs
import SocialChoice.Rules.ScoringRules.Participation
import SocialChoice.Rules.ScoringRules.Veto.Common

namespace SocialChoice

open Finset

/-!
# Coombs satisfies negative involvement
-/

theorem coombs_negative_involvement : NegativeInvolvement coombs := by
  intro U A _ _ V u hu P Q x hagree hxnot hbottom
  classical
  have hxnot' : x ∉ scoringEliminationAux vetoScore A P := by
    simpa [coombs, scoringEliminationRule] using hxnot
  have hxnotQ : x ∉ scoringEliminationAux vetoScore A Q := by
    intro hxQ
    -- Strong induction on the number of candidates.
    let Motive : Nat → Prop := fun k =>
      ∀ {A : Type} [Fintype A] [DecidableEq A]
          (P : Profile (Electorate U V) A)
          (Q : Profile (Electorate U (insert u V)) A) (x : A),
        (∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v) →
        BallotBottom (Q.pref (newVoter (u := u) (V := V) hu)) x →
        Fintype.card A = k →
        x ∈ scoringEliminationAux vetoScore A Q →
        x ∈ scoringEliminationAux vetoScore A P
    have hStrong : Motive (Fintype.card A) := by
      classical
      refine Nat.strongRecOn (motive := Motive) (Fintype.card A) ?_
      intro k ih A _ _ P Q x hagree hbottom hk hxQ
      by_cases hle : Fintype.card A ≤ 1
      · -- Base case: elimination returns all candidates.
        simp [scoringEliminationAux, hle]
      · -- Recursive case: follow the same elimination choice.
        let m := Fintype.card A
        let scoreVec : Nat → Int := fun r => vetoScore m r
        let LQ : Finset A := lowestScoring Q scoreVec
        have hauxQ :=
          scoringEliminationAux_eq_biUnion_of_not_card_le_one
            (score := vetoScore) (P := Q) (hcard := hle)
        have hxQ' :
            x ∈ LQ.biUnion
              (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile Q c))) := by
          simpa [hauxQ, m, scoreVec, LQ] using hxQ
        rcases Finset.mem_biUnion.mp hxQ' with ⟨c, hcLQ, hxrec⟩
        obtain ⟨hxne, hxrec'⟩ :=
          (mem_liftFinset_iff_subtype
              (s := scoringEliminationAux vetoScore _ (restrictProfile Q c)) (x := x)).1
            hxrec
        let x' : {x : A // x ≠ c} := ⟨x, hxne⟩
        let P' := restrictProfile P c
        let Q' := restrictProfile Q c
        have hagree' :
            ∀ v : Electorate U V,
              Q'.pref (liftVoter (u := u) v) = P'.pref v := by
          intro v
          have h :=
            congrArg (fun r => restrictBallot r (fun x => x ≠ c)) (hagree v)
          simpa [P', Q', restrictProfile, restrictCandidates] using h
        have hbottom' :
            BallotBottom (Q'.pref (newVoter (u := u) (V := V) hu)) x' := by
          intro d hd
          have hd' : (d : A) ≠ x := by
            intro hdx
            apply hd
            ext
            exact hdx
          have hlt : (Q.pref (newVoter (u := u) (V := V) hu)).lt d x := hbottom d hd'
          have hpref : Prefers Q (newVoter (u := u) (V := V) hu) d x' := by
            exact hlt
          have hpref' :
              Prefers (restrictProfile Q c) (newVoter (u := u) (V := V) hu) d x' := by
            exact (prefers_restrictProfile_iff (P := Q) (c := c)
              (v := newVoter (u := u) (V := V) hu) (a := d) (b := x')).2 hpref
          simpa [Prefers] using hpref'
        have hklt : Fintype.card {x : A // x ≠ c} < k := by
          have hlt : Fintype.card {x : A // x ≠ c} < Fintype.card A :=
            card_restrict_lt c
          simpa [hk] using hlt
        have hrec :
            x' ∈ scoringEliminationAux vetoScore {x : A // x ≠ c} P' := by
          exact ih (Fintype.card {x : A // x ≠ c}) hklt
            (P := P') (Q := Q') (x := x') hagree' hbottom' rfl hxrec'
        -- Show the eliminated candidate is still lowest-scoring in P.
        let ballot := Q.pref (newVoter (u := u) (V := V) hu)
        have hbottomRank : BottomRank Q (newVoter (u := u) (V := V) hu) x := by
          intro d hd
          have hlt : ballot.lt d x := hbottom d hd
          simpa [Prefers, ballot] using hlt
        have hscore_add :
            ∀ d : A,
              scoreCandidate Q scoreVec d =
                scoreCandidate P scoreVec d + (if d = x then 0 else 1) := by
          intro d
          have hscore :=
            scoreCandidate_add_newVoter (u := u) (V := V) hu P Q hagree scoreVec d
          have hdelta : scoreVec (rank ballot d) = (if d = x then 0 else 1) := by
            by_cases hdx : d = x
            · cases hdx
              have hrank' : rank ballot x = Fintype.card A - 1 := by
                exact (rank_eq_card_sub_one_iff_bottomRank (P := Q)
                  (v := newVoter (u := u) (V := V) hu) (c := x)).2 hbottomRank
              have hrank : rank ballot x = m - 1 := by
                simpa [m] using hrank'
              simp [scoreVec, vetoScore, hrank]
            · have hnotbottom :
                ¬ BottomRank Q (newVoter (u := u) (V := V) hu) d := by
                have hdx' : x ≠ d := by
                  simpa [eq_comm] using hdx
                exact
                  bottomRank_imp_not_bottomRank (P := Q) (c := x) (d := d) hdx'
                    (newVoter (u := u) (V := V) hu) hbottomRank
              have hne : rank ballot d ≠ m - 1 := by
                intro hEq
                apply hnotbottom
                have hEq' : rank ballot d = Fintype.card A - 1 := by
                  simpa [m] using hEq
                exact (rank_eq_card_sub_one_iff_bottomRank (P := Q)
                  (v := newVoter (u := u) (V := V) hu) (c := d)).1 hEq'
              simp [scoreVec, vetoScore, hne, hdx]
          simpa [ballot, hdelta] using hscore
        have hA : (Finset.univ : Finset A).Nonempty := by
          have hcard' : 1 < Fintype.card A := Nat.lt_of_not_ge hle
          have hpos : 0 < Fintype.card A := Nat.lt_trans Nat.zero_lt_one hcard'
          haveI : Nonempty A := Fintype.card_pos_iff.mp hpos
          exact Finset.univ_nonempty
        have hc_le_Q :
            ∀ d : A, scoreCandidate Q scoreVec c ≤ scoreCandidate Q scoreVec d :=
          (lowestScoring_iff_forall_le (P := Q) (score := scoreVec) hA c).1 hcLQ
        have hcx : c ≠ x := by
          simpa [eq_comm] using hxne
        have hc_le_P :
            ∀ d : A, scoreCandidate P scoreVec c ≤ scoreCandidate P scoreVec d := by
          intro d
          have hleQ : scoreCandidate Q scoreVec c ≤ scoreCandidate Q scoreVec d := hc_le_Q d
          by_cases hdx : d = x
          · cases hdx
            have hleQ' :
                scoreCandidate P scoreVec c + 1 ≤ scoreCandidate P scoreVec x + 0 := by
              simpa [hscore_add, hcx] using hleQ
            linarith
          · have hleQ' :
                scoreCandidate P scoreVec c + 1 ≤ scoreCandidate P scoreVec d + 1 := by
              simpa [hscore_add, hcx, hdx] using hleQ
            exact (add_le_add_iff_right 1).1 hleQ'
        let L : Finset A := lowestScoring P scoreVec
        have hcL : c ∈ L :=
          (lowestScoring_iff_forall_le (P := P) (score := scoreVec) hA c).2 hc_le_P
        -- Lift the recursive membership back to A.
        have hxrecP :
            x ∈ liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P c)) := by
          exact
            (mem_liftFinset_iff_subtype
                (s := scoringEliminationAux vetoScore _ (restrictProfile P c)) (x := x)).2
              ⟨hxne, hrec⟩
        -- Conclude membership in the full elimination on P.
        have hauxP :=
          scoringEliminationAux_eq_biUnion_of_not_card_le_one
            (score := vetoScore) (P := P) (hcard := hle)
        have hxP' :
            x ∈ L.biUnion
              (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P c))) := by
          refine Finset.mem_biUnion.mpr ?_
          exact ⟨c, by simpa [L] using hcL, by simpa using hxrecP⟩
        simpa [hauxP, m, scoreVec, L] using hxP'
    have hxP : x ∈ scoringEliminationAux vetoScore A P :=
      hStrong (P := P) (Q := Q) (x := x) hagree hbottom rfl hxQ
    exact hxnot' hxP
  simpa [coombs, scoringEliminationRule] using hxnotQ

end SocialChoice
