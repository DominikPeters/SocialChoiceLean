import Mathlib.Tactic
import SocialChoice.Axioms.Pareto
import SocialChoice.Rank
import SocialChoice.Rules.Nanson.Defs
import SocialChoice.Rules.ScoringRules.Borda.Defs

namespace SocialChoice

open Finset

private lemma bordaScoreCandidate_lt_of_pareto {V A : Type} [Fintype V] [Fintype A]
    [Nonempty V] (P : Profile V A) (c d : A)
    (hpref : ∀ v : V, Prefers P v c d) :
    scoreCandidate P (fun r => bordaScore (Fintype.card A) r) d <
      scoreCandidate P (fun r => bordaScore (Fintype.card A) r) c := by
  classical
  let scoreFun : Nat → Int := fun r => bordaScore (Fintype.card A) r
  have hlt_rank : ∀ v, rank (P.pref v) c < rank (P.pref v) d := by
    intro v
    exact rank_lt_of_lt (r := P.pref v) (c := c) (d := d) (hpref v)
  have hlt_score : ∀ v, scoreFun (rank (P.pref v) d) < scoreFun (rank (P.pref v) c) := by
    intro v
    have h := bordaScore_strictlyDecreasing (Fintype.card A)
      (rank (P.pref v) c) (rank (P.pref v) d) (hlt_rank v)
      (rank_lt_card (P.pref v) c) (rank_lt_card (P.pref v) d)
    simpa [scoreFun] using h
  rcases Classical.choice (inferInstance : Nonempty V) with v0
  let diff : V → Int :=
    fun v => scoreFun (rank (P.pref v) c) - scoreFun (rank (P.pref v) d)
  have hdiff_pos : ∀ v, 0 < diff v := by
    intro v
    exact sub_pos.mpr (hlt_score v)
  have hsum_rest_nonneg :
      0 ≤ (Finset.univ.erase v0 : Finset V).sum fun v : V => diff v := by
    have hnonneg :
        ∀ v ∈ (Finset.univ.erase v0 : Finset V), 0 ≤ diff v := by
      intro v hv
      exact (hdiff_pos v).le
    exact Finset.sum_nonneg hnonneg
  have hsum_pos :
      0 < diff v0 + (Finset.univ.erase v0 : Finset V).sum fun v : V => diff v :=
    add_pos_of_pos_of_nonneg (hdiff_pos v0) hsum_rest_nonneg
  have hsum_eq :
      (Finset.univ.sum fun v : V => diff v) =
        diff v0 + (Finset.univ.erase v0 : Finset V).sum fun v : V => diff v := by
    have hv0_mem : v0 ∈ (Finset.univ : Finset V) := by simp
    have h :=
      Finset.sum_erase_add (s := (Finset.univ : Finset V))
        (a := v0) (f := fun v => diff v) hv0_mem
    -- sum_erase_add gives the same identity with terms swapped
    simpa [diff, hv0_mem, add_comm, add_left_comm, add_assoc] using h.symm
  have hsum_pos' : 0 < (Finset.univ.sum fun v : V => diff v) := by
    calc
      0 < diff v0 + (Finset.univ.erase v0 : Finset V).sum (fun v : V => diff v) :=
        hsum_pos
      _ = (Finset.univ.sum fun v : V => diff v) := by
        symm
        exact hsum_eq
  have hsum_pos'' :
      0 <
        (Finset.univ.sum fun v : V => scoreFun (rank (P.pref v) c)) -
          (Finset.univ.sum fun v : V => scoreFun (rank (P.pref v) d)) := by
    simpa [diff, Finset.sum_sub_distrib] using hsum_pos'
  have hsum_lt :
      (Finset.univ.sum fun v : V => scoreFun (rank (P.pref v) d)) <
        (Finset.univ.sum fun v : V => scoreFun (rank (P.pref v) c)) :=
    sub_pos.mp hsum_pos''
  simpa [scoreCandidate, scoreFun] using hsum_lt

private lemma c2BordaScore_lt_of_pareto {V A : Type} [Fintype V] [Fintype A]
    [Nonempty V] (P : Profile V A) (c d : A)
    (hpref : ∀ v : V, Prefers P v c d) :
    c2BordaScore P d < c2BordaScore P c := by
  classical
  let scoreFun : Nat → Int := fun r => bordaScore (Fintype.card A) r
  have hlt_borda :
      scoreCandidate P scoreFun d < scoreCandidate P scoreFun c :=
    bordaScoreCandidate_lt_of_pareto (P := P) (c := c) (d := d) hpref
  set k : Int := (Fintype.card V : Int) * ((Fintype.card A : Int) - 1)
  have hd : c2BordaScore P d = 2 * scoreCandidate P scoreFun d - k := by
    simpa [scoreFun, k] using (c2BordaScore_eq_affine (P := P) (x := d))
  have hc : c2BordaScore P c = 2 * scoreCandidate P scoreFun c - k := by
    simpa [scoreFun, k] using (c2BordaScore_eq_affine (P := P) (x := c))
  linarith [hd, hc, hlt_borda]

/-- Nanson satisfies Pareto efficiency. -/
theorem nanson_pareto_efficiency : ParetoEfficiency nanson := by
  intro V A _ _ _ P c d hpref
  classical
  let : DecidableEq A := Classical.decEq A
  set k : Nat := Fintype.card A
  let Motive : Nat → Prop := fun n =>
    ∀ {A : Type} [Fintype A] [DecidableEq A],
      Fintype.card A ≤ n →
        ∀ {V : Type} [Fintype V] [Nonempty V] (P : Profile V A) (c d : A),
          (∀ v : V, Prefers P v c d) → d ∉ nansonAux n A P
  have hStrong : Motive k := by
    classical
    refine Nat.strongRecOn (motive := Motive) k ?_
    intro n ih A _ _ hcard_le V _ _ P c d hpref
    classical
    cases n with
    | zero =>
        have hcard_eq : Fintype.card A = 0 :=
          Nat.le_antisymm hcard_le (Nat.zero_le _)
        have hEmpty : IsEmpty A := (Fintype.card_eq_zero_iff.mp hcard_eq)
        exact (hEmpty.false c).elim
    | succ n =>
        by_cases hle : Fintype.card A ≤ 1
        ·
          have hsub : Subsingleton A := (Fintype.card_le_one_iff_subsingleton).1 hle
          have hcd : c = d := Subsingleton.elim _ _
          rcases Classical.choice (inferInstance : Nonempty V) with v0
          have hcc : (P.pref v0).lt c c := by
            simpa [Prefers, hcd] using hpref v0
          have hfalse : False := by
            let _ := P.pref v0
            exact (lt_irrefl _ hcc)
          exact (False.elim hfalse)
        ·
          have hlt_c2 : c2BordaScore P d < c2BordaScore P c :=
            c2BordaScore_lt_of_pareto (P := P) (c := c) (d := d) hpref
          have hall : ¬ ∀ a : A, c2BordaScore P a = 0 := by
            intro hall
            have hd0 : c2BordaScore P d = 0 := hall d
            have hc0 : c2BordaScore P c = 0 := hall c
            exact (ne_of_lt hlt_c2) (by simp [hd0, hc0])
          have hneg_ex : ∃ x, c2BordaScore P x < 0 := by
            by_cases hpos : 0 < c2BordaScore P c
            · exact exists_neg_c2BordaScore_of_pos (P := P) (c := c) hpos
            ·
              have hle : c2BordaScore P c ≤ 0 := not_lt.mp hpos
              have hdneg : c2BordaScore P d < 0 := lt_of_lt_of_le hlt_c2 hle
              exact ⟨d, hdneg⟩
          rcases hneg_ex with ⟨e, he_neg⟩
          have hpos_ex : ∃ x, 0 < c2BordaScore P x :=
            exists_pos_c2BordaScore_of_neg (P := P) (c := e) he_neg
          rcases hpos_ex with ⟨a, ha_pos⟩
          let p : A → Prop := fun a => c2BordaScore P a > 0
          have hsurv : (Finset.univ.filter (fun a => p a)).Nonempty := by
            refine ⟨a, ?_⟩
            simp [p, ha_pos]
          let P' : Profile V {a : A // p a} := restrictCandidates P p
          have hnotp : ¬ p e := by
            dsimp [p]
            exact not_lt_of_ge (le_of_lt he_neg)
          have hcard_lt : Fintype.card {a : A // p a} < Fintype.card A :=
            Fintype.card_subtype_lt (p := p) (x := e) hnotp
          have hcard_le' : Fintype.card {a : A // p a} ≤ n := by
            have hlt : Fintype.card {a : A // p a} < Nat.succ n :=
              lt_of_lt_of_le hcard_lt hcard_le
            exact Nat.lt_succ_iff.mp hlt
          intro hd
          have hd' :
              d ∈ liftWinners (nansonAux n {a : A // p a} P') := by
            simpa [nansonAux, hall, hsurv, p, P'] using hd
          have hd'' :
              ∃ d' ∈ nansonAux n {a : A // p a} P', (d' : A) = d := by
            classical
            simpa [liftWinners] using hd'
          rcases hd'' with ⟨d', hd_mem, rfl⟩
          have hdpos : p (d' : A) := d'.property
          have hcpos : p c := by
            dsimp [p] at hdpos ⊢
            exact lt_trans hdpos hlt_c2
          let c' : {a : A // p a} := ⟨c, hcpos⟩
          have hpref' : ∀ v : V, Prefers P' v c' d' := by
            intro v
            have := hpref v
            simpa [P', prefers_restrictCandidates_iff] using this
          have hrec : d' ∉ nansonAux n {a : A // p a} P' := by
            exact ih (m := n) (Nat.lt_succ_self n)
              (A := {a : A // p a}) hcard_le' (V := V) (P := P') (c := c') (d := d') hpref'
          exact (hrec hd_mem)
  exact hStrong (A := A) (by simp [k]) (V := V) (P := P) (c := c) (d := d) hpref

end SocialChoice
