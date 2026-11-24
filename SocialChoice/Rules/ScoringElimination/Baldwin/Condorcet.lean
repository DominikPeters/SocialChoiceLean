import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import SocialChoice.Axioms.Condorcet
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Baldwin.Defs
import SocialChoice.Rules.ScoringRules.Borda.C2Borda

namespace SocialChoice

open Finset
open scoped BigOperators

lemma c2BordaScore_lt_iff_bordaScore_lt {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x y : A) :
    c2BordaScore P x < c2BordaScore P y ↔
      scoreCandidate P (fun r => bordaScore (Fintype.card A) r) x <
        scoreCandidate P (fun r => bordaScore (Fintype.card A) r) y := by
  classical
  set k : Int := (Fintype.card V : Int) * ((Fintype.card A : Int) - 1)
  have hx :
      c2BordaScore P x =
        2 * scoreCandidate P (fun r => bordaScore (Fintype.card A) r) x - k := by
    simp [k]
    exact c2BordaScore_eq_affine (P := P) (x := x)
  have hy :
      c2BordaScore P y =
        2 * scoreCandidate P (fun r => bordaScore (Fintype.card A) r) y - k := by
    simp [k]
    exact c2BordaScore_eq_affine (P := P) (x := y)
  constructor
  · intro hlt
    linarith [hx, hy]
  · intro hlt
    linarith [hx, hy]

lemma CondorcetWinner_not_lowest_borda
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (c : A) (hwin : CondorcetWinner P c)
    (hcard : 1 < Fintype.card A) :
    c ∉ lowestScoring P (fun r => bordaScore (Fintype.card A) r) := by
  classical
  rcases Fintype.exists_ne_of_one_lt_card hcard c with ⟨y, hy⟩
  have hpos : 0 < c2BordaScore P c :=
    c2BordaScore_pos_of_CondorcetWinner (P := P) (x := c) hwin ⟨y, hy⟩
  have hneg : ∃ d, c2BordaScore P d < 0 :=
    exists_neg_c2BordaScore_of_pos (P := P) (c := c) hpos
  rcases hneg with ⟨d, hdneg⟩
  have hlt_c2 : c2BordaScore P d < c2BordaScore P c := lt_trans hdneg hpos
  have hlt_borda :
      scoreCandidate P (fun r => bordaScore (Fintype.card A) r) d <
        scoreCandidate P (fun r => bordaScore (Fintype.card A) r) c :=
    (c2BordaScore_lt_iff_bordaScore_lt (P := P) (x := d) (y := c)).1 hlt_c2
  intro hc
  have hle :
      scoreCandidate P (fun r => bordaScore (Fintype.card A) r) c ≤
        scoreCandidate P (fun r => bordaScore (Fintype.card A) r) d :=
    scoreCandidate_le_of_mem_lowestScoring (P := P)
      (score := fun r => bordaScore (Fintype.card A) r) (c := c) (e := d) hc
  exact (not_lt_of_ge hle) hlt_borda

lemma CondorcetWinner_restrictProfile {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) {c d : A} (hcd : c ≠ d)
    (hwin : CondorcetWinner P c) :
    CondorcetWinner (restrictProfile P d) (⟨c, hcd⟩ : {x : A // x ≠ d}) := by
  intro y hy
  have hne : c ≠ (y : A) := by
    intro hEq
    apply hy
    apply Subtype.ext
    exact hEq.symm
  have hpos : margin_pos P c (y : A) :=
    (CondorcetWinner_iff_margin_pos P c).mp hwin (y : A) hne
  have hpos' : margin_pos (restrictProfile P d) (⟨c, hcd⟩ : {x : A // x ≠ d}) y := by
    dsimp [margin_pos] at hpos ⊢
    have heq := margin_eq_margin_restrictProfile (P := P) (c := d)
      (a := (⟨c, hcd⟩ : {x : A // x ≠ d})) (b := y)
    simpa [heq] using hpos
  exact (strictMajority_votersPreferring_iff_margin_pos
    (P := restrictProfile P d) (c := (⟨c, hcd⟩ : {x : A // x ≠ d})) (d := y)
      (hcd := Ne.symm hy)).2
    hpos'

theorem baldwin_condorcet_consistency : CondorcetConsistency baldwin := by
  intro V A _ _ P c hwin
  classical
  let : DecidableEq A := Classical.decEq A
  simp [baldwin, scoringEliminationRule]
  set n : Nat := Fintype.card A
  let Motive : Nat → Prop := fun k =>
    ∀ {A : Type} [Fintype A] [DecidableEq A],
      Fintype.card A = k →
        ∀ {V : Type} [Fintype V] (P : Profile V A) (c : A),
          CondorcetWinner P c → scoringEliminationAux bordaScore A P = {c}
  have hStrong : Motive n := by
    classical
    refine Nat.strongRecOn (motive := Motive) n (fun k ih => ?_)
    intro A _ _ hcard V _ P c hwin
    classical
    by_cases hle : Fintype.card A ≤ 1
    · have hsub : Subsingleton A := (Fintype.card_le_one_iff_subsingleton).1 hle
      have haux : scoringEliminationAux bordaScore A P = (Finset.univ : Finset A) := by
        simp [scoringEliminationAux, hle]
      apply Finset.ext
      intro x
      constructor
      · intro hx
        have hx' : x = c := Subsingleton.elim _ _
        simp [hx']
      · intro hx
        simp [haux]
    · have haux :=
        scoringEliminationAux_eq_biUnion_of_not_card_le_one
          (score := bordaScore) (P := P) (hcard := hle)
      let scoreVec : Nat → Int := fun r => bordaScore (Fintype.card A) r
      let L : Finset A := lowestScoring P scoreVec
      have haux' :
          scoringEliminationAux bordaScore A P =
            L.biUnion (fun d => liftFinset
              (scoringEliminationAux bordaScore _ (restrictProfile P d))) := by
        exact haux
      have hcard_gt1 : 1 < Fintype.card A := Nat.lt_of_not_ge hle
      have hnot_lowest : c ∉ L := by
        have hnot_lowest' :=
          CondorcetWinner_not_lowest_borda (P := P) (c := c) hwin hcard_gt1
        exact hnot_lowest'
      apply Finset.ext
      intro x
      constructor
      · intro hx
        have hx' := hx
        rw [haux'] at hx'
        rcases Finset.mem_biUnion.mp hx' with ⟨d, hdL, hxbranch⟩
        have hcd : c ≠ d := by
          intro hEq
          subst hEq
          exact hnot_lowest hdL
        rcases (mem_liftFinset_iff_subtype
          (s := scoringEliminationAux bordaScore {x : A // x ≠ d} (restrictProfile P d))
          (x := x)).1 hxbranch with ⟨hxd, hxsub⟩
        have hltcard : Fintype.card {x : A // x ≠ d} < k := by
          have hltcard' := card_restrict_lt (A := A) d
          rw [hcard] at hltcard'
          exact hltcard'
        have hwin' :
            CondorcetWinner (restrictProfile P d) (⟨c, hcd⟩ : {x : A // x ≠ d}) :=
          CondorcetWinner_restrictProfile (P := P) (c := c) (d := d) hcd hwin
        have hrec :
            scoringEliminationAux bordaScore {x : A // x ≠ d} (restrictProfile P d) =
              {⟨c, hcd⟩} := by
          have := ih (m := Fintype.card {x : A // x ≠ d}) hltcard
            (A := {x : A // x ≠ d}) (by rfl) (V := V) (P := restrictProfile P d)
            (c := (⟨c, hcd⟩ : {x : A // x ≠ d})) hwin'
          exact this
        have hxeq :
            (⟨x, hxd⟩ : {x : A // x ≠ d}) = ⟨c, hcd⟩ := by
          have hxmem := hxsub
          rw [hrec] at hxmem
          exact Finset.mem_singleton.mp hxmem
        have hxval : x = c := congrArg Subtype.val hxeq
        simp [hxval]
      · intro hx
        have hx' : x = c := by
          exact Finset.mem_singleton.mp hx
        subst x
        rw [haux']
        have hpos : 0 < Fintype.card A :=
          lt_trans (Nat.succ_pos 0) hcard_gt1
        have hA : (Finset.univ : Finset A).Nonempty := by
          classical
          let : Nonempty A := Fintype.card_pos_iff.mp hpos
          exact (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty)
        have hL : L.Nonempty := lowestScoring_nonempty (P := P) (score := scoreVec) hA
        rcases hL with ⟨d, hdL⟩
        refine Finset.mem_biUnion.mpr ?_
        have hcd : c ≠ d := by
          intro hEq
          subst hEq
          exact hnot_lowest hdL
        have hwin' :
            CondorcetWinner (restrictProfile P d) (⟨c, hcd⟩ : {x : A // x ≠ d}) :=
          CondorcetWinner_restrictProfile (P := P) (c := c) (d := d) hcd hwin
        have hltcard : Fintype.card {x : A // x ≠ d} < k := by
          have hltcard' := card_restrict_lt (A := A) d
          rw [hcard] at hltcard'
          exact hltcard'
        have hrec :
            scoringEliminationAux bordaScore {x : A // x ≠ d} (restrictProfile P d) =
              {⟨c, hcd⟩} := by
          have := ih (m := Fintype.card {x : A // x ≠ d}) hltcard
            (A := {x : A // x ≠ d}) (by rfl) (V := V) (P := restrictProfile P d)
            (c := (⟨c, hcd⟩ : {x : A // x ≠ d})) hwin'
          exact this
        refine ⟨d, hdL, ?_⟩
        have hc_sub : (⟨c, hcd⟩ : {x : A // x ≠ d}) ∈
            scoringEliminationAux bordaScore {x : A // x ≠ d} (restrictProfile P d) := by
          simp [hrec]
        exact (mem_liftFinset_iff_subtype
          (s := scoringEliminationAux bordaScore {x : A // x ≠ d} (restrictProfile P d))
          (x := c)).2 ⟨hcd, hc_sub⟩
  exact hStrong (A := A) (by rfl) (V := V) (P := P) (c := c) hwin

end SocialChoice
