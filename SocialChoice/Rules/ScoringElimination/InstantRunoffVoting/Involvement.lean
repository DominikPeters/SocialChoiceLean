import Mathlib.Tactic
import SocialChoice.Axioms.Participation
import SocialChoice.Rank
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.Defs
import SocialChoice.Rules.ScoringRules.Participation
import SocialChoice.Rules.ScoringRules.Plurality.Defs

namespace SocialChoice

open Finset

theorem instantRunoffVoting_positive_involvement : PositiveInvolvement instantRunoffVoting := by
  intro U A _ _ V u hu P Q x hagree hx htop
  classical
  have hx' : x ∈ scoringEliminationAux pluralityScore A P := by
    simpa [instantRunoffVoting, scoringEliminationRule] using hx
  -- Strong induction on the number of candidates.
  let Motive : Nat → Prop := fun k =>
    ∀ {A : Type} [Fintype A] [DecidableEq A]
        (P : Profile (Electorate U V) A)
        (Q : Profile (Electorate U (insert u V)) A) (x : A),
      (∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v) →
      BallotTop (Q.pref (newVoter (u := u) (V := V) hu)) x →
      Fintype.card A = k →
      x ∈ scoringEliminationAux pluralityScore A P →
      x ∈ scoringEliminationAux pluralityScore A Q
  have hStrong : Motive (Fintype.card A) := by
    classical
    refine Nat.strongRecOn (motive := Motive) (Fintype.card A) ?_
    intro k ih A _ _ P Q x hagree htop hk hxP
    by_cases hle : Fintype.card A ≤ 1
    · -- Base case: IRV returns all candidates.
      simp [scoringEliminationAux, hle]
    · -- Recursive case: follow the same elimination choice.
      let m := Fintype.card A
      let scoreVec : Nat → Int := fun r => pluralityScore m r
      let L : Finset A := lowestScoring P scoreVec
      have hauxP :=
        scoringEliminationAux_eq_biUnion_of_not_card_le_one
          (score := pluralityScore) (P := P) (hcard := hle)
      have hxP' :
          x ∈ L.biUnion
            (fun c => liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P c))) := by
        simpa [hauxP, m, scoreVec, L] using hxP
      rcases Finset.mem_biUnion.mp hxP' with ⟨c, hcL, hxrec⟩
      obtain ⟨hxne, hxrec'⟩ :=
        (mem_liftFinset_iff_subtype
            (s := scoringEliminationAux pluralityScore _ (restrictProfile P c)) (x := x)).1
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
      have htop' :
          BallotTop (Q'.pref (newVoter (u := u) (V := V) hu)) x' := by
        intro d hd
        have hd' : (d : A) ≠ x := by
          intro hdx
          apply hd
          ext
          exact hdx
        have hlt : (Q.pref (newVoter (u := u) (V := V) hu)).lt x d := htop d hd'
        have hpref : Prefers Q (newVoter (u := u) (V := V) hu) x' d := by
          exact hlt
        have hpref' :
            Prefers (restrictProfile Q c) (newVoter (u := u) (V := V) hu) x' d := by
          exact (prefers_restrictProfile_iff (P := Q) (c := c)
            (v := newVoter (u := u) (V := V) hu) (a := x') (b := d)).2 hpref
        simpa [Prefers] using hpref'
      have hklt : Fintype.card {x : A // x ≠ c} < k := by
        have hlt : Fintype.card {x : A // x ≠ c} < Fintype.card A :=
          card_restrict_lt c
        simpa [hk] using hlt
      have hrec :
          x' ∈ scoringEliminationAux pluralityScore {x : A // x ≠ c} Q' := by
        exact ih (Fintype.card {x : A // x ≠ c}) hklt
          (P := P') (Q := Q') (x := x') hagree' htop' rfl hxrec'
      -- Show the eliminated candidate remains lowest-scoring after adding the top-x voter.
      let ballot := Q.pref (newVoter (u := u) (V := V) hu)
      have hrank_x : rank ballot x = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro d hd
        have hdx : ballot.lt d x := (Finset.mem_filter.mp hd).2
        let _ := ballot
        have hdx_ne : d ≠ x := ne_of_lt hdx
        have hxd : ballot.lt x d := htop d hdx_ne
        let _ : Preorder A := ballot.toPreorder
        exact (lt_asymm (a := x) (b := d) hxd) hdx
      have hscore_add :
          ∀ d : A,
            scoreCandidate Q scoreVec d =
              scoreCandidate P scoreVec d + (if d = x then 1 else 0) := by
        intro d
        have hscore :=
          scoreCandidate_add_newVoter (u := u) (V := V) hu P Q hagree scoreVec d
        have hdelta : scoreVec (rank ballot d) = (if d = x then 1 else 0) := by
          by_cases hdx : d = x
          · subst hdx
            simp [scoreVec, pluralityScore, hrank_x]
          · have hlt :
                rank ballot x < rank ballot d :=
              rank_lt_of_lt (r := ballot) (c := x) (d := d) (htop d hdx)
            have hpos : 0 < rank ballot d := by
              simpa [hrank_x] using hlt
            have hne0 : rank ballot d ≠ 0 := ne_of_gt hpos
            simp [scoreVec, pluralityScore, hne0, hdx]
        simpa [ballot, hdelta] using hscore
      have hA : (Finset.univ : Finset A).Nonempty := by
        have hcard' : 1 < Fintype.card A := Nat.lt_of_not_ge hle
        have hpos : 0 < Fintype.card A := Nat.lt_trans Nat.zero_lt_one hcard'
        haveI : Nonempty A := Fintype.card_pos_iff.mp hpos
        exact Finset.univ_nonempty
      have hcL' : c ∈ lowestScoring P scoreVec := by
        simpa [L] using hcL
      have hc_le :
          ∀ d : A, scoreCandidate P scoreVec c ≤ scoreCandidate P scoreVec d :=
        (lowestScoring_iff_forall_le (P := P) (score := scoreVec) hA c).1 hcL'
      have hcx : c ≠ x := by
        simpa [eq_comm] using hxne
      have hleQ :
          ∀ d : A, scoreCandidate Q scoreVec c ≤ scoreCandidate Q scoreVec d := by
        intro d
        by_cases hdx : d = x
        · have hscore_c := hscore_add c
          have hscore_d := hscore_add d
          have hc0 : (if c = x then (1 : Int) else 0) = 0 := by simp [hcx]
          have hd1 : (if d = x then (1 : Int) else 0) = 1 := by simp [hdx]
          have h01 : (0 : Int) ≤ 1 := by decide
          have hle' :
              scoreCandidate P scoreVec c + 0 ≤ scoreCandidate P scoreVec d + 1 :=
            add_le_add (hc_le d) h01
          simpa [hscore_c, hscore_d, hc0, hd1] using hle'
        · have hscore_c := hscore_add c
          have hscore_d := hscore_add d
          have hc0 : (if c = x then (1 : Int) else 0) = 0 := by simp [hcx]
          have hd0 : (if d = x then (1 : Int) else 0) = 0 := by simp [hdx]
          have h00 : (0 : Int) ≤ 0 := by decide
          have hle' :
              scoreCandidate P scoreVec c + 0 ≤ scoreCandidate P scoreVec d + 0 :=
            add_le_add (hc_le d) h00
          simpa [hscore_c, hscore_d, hc0, hd0] using hle'
      have hlowest :
          c ∈ lowestScoring Q scoreVec :=
        (lowestScoring_iff_forall_le (P := Q) (score := scoreVec) hA c).2 hleQ
      let LQ : Finset A := lowestScoring Q scoreVec
      have hauxQ :=
        scoringEliminationAux_eq_biUnion_of_not_card_le_one
          (score := pluralityScore) (P := Q) (hcard := hle)
      have hxrecQ :
          x ∈ liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile Q c)) := by
        exact
          (mem_liftFinset_iff_subtype
              (s := scoringEliminationAux pluralityScore _ (restrictProfile Q c)) (x := x)).2
            ⟨hxne, hrec⟩
      have hxQ' :
          x ∈ LQ.biUnion
            (fun c => liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile Q c))) := by
        refine Finset.mem_biUnion.mpr ?_
        exact ⟨c, by simpa [LQ] using hlowest, by simpa using hxrecQ⟩
      simpa [hauxQ, m, scoreVec, LQ] using hxQ'
  have hxQ :
      x ∈ scoringEliminationAux pluralityScore A Q :=
    hStrong (P := P) (Q := Q) (x := x) hagree htop rfl hx'
  simpa [instantRunoffVoting, scoringEliminationRule] using hxQ

end SocialChoice
