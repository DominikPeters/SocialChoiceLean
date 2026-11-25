import Mathlib.Data.Finset.Card
import SocialChoice.Axioms.Pareto
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Coombs.Defs
import SocialChoice.Rules.ScoringRules.Veto.Common

namespace SocialChoice

open Finset

theorem coombs_paretoEfficiency : ParetoEfficiency coombs := by
  intro V A _ _ _ P c d hpref
  classical
  set n := Fintype.card A with hn
  let Motive : Nat → Prop := fun k =>
    ∀ {A' : Type} [Fintype A'] [DecidableEq A']
      {V' : Type} [Fintype V'] [Nonempty V']
      (P' : Profile V' A') (c d : A'),
        Fintype.card A' = k →
        (∀ v : V', Prefers P' v c d) →
          d ∉ scoringEliminationAux vetoScore A' P'
  have hStrong : Motive n := by
    classical
    refine Nat.strongRecOn (motive := Motive) n ?_
    intro k ih A' _ _ V' _ _ P' c d hk hpref
    by_cases hle : Fintype.card A' ≤ 1
    · have hsub : Subsingleton A' :=
        (Fintype.card_le_one_iff_subsingleton).1 hle
      have hcd : c = d := Subsingleton.elim _ _
      rcases Classical.choice (inferInstance : Nonempty V') with v0
      have hpref0 : Prefers P' v0 c d := hpref v0
      subst hcd
      have hfalse : False := by
        let _ := P'.pref v0
        exact (lt_irrefl _ hpref0)
      exact hfalse.elim
    · let m := Fintype.card A'
      let scoreVec : Nat → Int := fun r => vetoScore m r
      have hnot_bottom_c : ∀ v : V', ¬ BottomRank P' v c := by
        intro v hbottom
        have hprefv : Prefers P' v c d := hpref v
        have hcd : c ≠ d := by
          let _ := P'.pref v
          exact ne_of_lt hprefv
        have hdc : Prefers P' v d c := hbottom d hcd.symm
        let _ := P'.pref v
        exact lt_asymm hprefv hdc
      have hscore_c :
          scoreCandidate P' scoreVec c = (Fintype.card V' : Int) := by
        have hscore_c' :
            scoreCandidate P' scoreVec c =
              ((Finset.univ.filter (fun v => ¬ BottomRank P' v c)).card : Int) := by
          simpa [scoreVec, vetoScore] using
            (vetoScore_scoreCandidate_eq_notBottom_card (P := P') (c := c))
        have hfilter :
            (Finset.univ.filter (fun v => ¬ BottomRank P' v c)) =
              (Finset.univ : Finset V') := by
          apply Finset.ext
          intro v
          simp [hnot_bottom_c v]
        simp [hscore_c', hfilter]
      rcases Classical.choice (inferInstance : Nonempty V') with v0
      let _ := P'.pref v0
      have hA' : (Finset.univ : Finset A').Nonempty := by
        have hpos : 0 < Fintype.card A' := by
          have hpos' : 1 < Fintype.card A' := Nat.lt_of_not_ge hle
          exact lt_trans Nat.zero_lt_one hpos'
        have : Nonempty A' := Fintype.card_pos_iff.mp hpos
        exact Finset.univ_nonempty
      let b : A' := (Finset.univ : Finset A').max' hA'
      have hb_bottom : BottomRank P' v0 b := by
        intro a hab
        have hle' : a ≤ b := by
          exact Finset.le_max' (s := (Finset.univ : Finset A')) a (by simp)
        have hlt' : a < b := lt_of_le_of_ne hle' hab
        simpa [Prefers] using hlt'
      have hscore_b_lt :
          scoreCandidate P' scoreVec b < scoreCandidate P' scoreVec c := by
        have hscore_b :
            scoreCandidate P' scoreVec b =
              ((Finset.univ.filter (fun v => ¬ BottomRank P' v b)).card : Int) := by
          simpa [scoreVec, vetoScore] using
            (vetoScore_scoreCandidate_eq_notBottom_card (P := P') (c := b))
        have hnotmem :
            v0 ∉ (Finset.univ.filter (fun v => ¬ BottomRank P' v b)) := by
          simp [hb_bottom]
        have hssub :
            (Finset.univ.filter (fun v => ¬ BottomRank P' v b)) ⊂
              (Finset.univ : Finset V') := by
          refine (Finset.ssubset_iff_of_subset
            (Finset.filter_subset (s := (Finset.univ : Finset V'))
              (p := fun v => ¬ BottomRank P' v b))).2 ?_
          refine ⟨v0, by simp, hnotmem⟩
        have hcard_lt :
            (Finset.univ.filter (fun v => ¬ BottomRank P' v b)).card <
              (Finset.univ : Finset V').card := by
          exact Finset.card_lt_card hssub
        have hcard_lt' :
            (Finset.univ.filter (fun v => ¬ BottomRank P' v b)).card <
              Fintype.card V' := by
          simpa using hcard_lt
        have hcard_lt_int :
            ((Finset.univ.filter (fun v => ¬ BottomRank P' v b)).card : Int) <
              (Fintype.card V' : Int) := by
          exact_mod_cast hcard_lt'
        simpa [hscore_b, hscore_c] using hcard_lt_int
      have hnotc : c ∉ lowestScoring P' scoreVec := by
        intro hc
        have hle :=
          scoreCandidate_le_of_mem_lowestScoring
            (P := P') (score := scoreVec) (c := c) (e := b) hc
        exact (not_lt_of_ge hle) hscore_b_lt
      have haux :=
        scoringEliminationAux_eq_biUnion_of_not_card_le_one
          (score := vetoScore) (P := P') (A := A') (hcard := hle)
      intro hd
      have hd' :
          d ∈ (lowestScoring P' scoreVec).biUnion
            (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P' c))) := by
        simpa [haux, m, scoreVec] using hd
      rcases Finset.mem_biUnion.mp hd' with ⟨ℓ, hℓL, hdmem⟩
      have hne_c : c ≠ ℓ := by
        intro hEq
        subst hEq
        exact hnotc hℓL
      rcases (mem_liftFinset_iff_subtype
        (s := scoringEliminationAux vetoScore _ (restrictProfile P' ℓ)) (x := d)).1 hdmem
        with ⟨hdne, hdsub⟩
      have hpref' :
          ∀ v : V', Prefers (restrictProfile P' ℓ) v ⟨c, hne_c⟩ ⟨d, hdne⟩ := by
        intro v
        simpa using (hpref v)
      have hklt : Fintype.card {x : A' // x ≠ ℓ} < k := by
        have hcard_sub_lt : Fintype.card {x : A' // x ≠ ℓ} < Fintype.card A' :=
          card_restrict_lt ℓ
        simpa [hk] using hcard_sub_lt
      have hrec :=
        ih (Fintype.card {x : A' // x ≠ ℓ}) hklt
          (A' := {x : A' // x ≠ ℓ}) (V' := V')
          (P' := restrictProfile P' ℓ)
          (c := ⟨c, hne_c⟩) (d := ⟨d, hdne⟩) (by rfl) hpref'
      exact hrec hdsub
  simpa [coombs, scoringEliminationRule, hn] using
    (hStrong (A' := A) (V' := V) (P' := P) (c := c) (d := d) (by rfl) hpref)

end SocialChoice
