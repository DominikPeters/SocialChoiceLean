import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import SocialChoice.Axioms.Smith
import SocialChoice.Margin
import SocialChoice.Rules.TopCycle.Defs
import SocialChoice.Rules.Nanson.Defs
import SocialChoice.Rules.ScoringRules.Borda.C2Borda

namespace SocialChoice

open Finset
open scoped BigOperators

lemma sum_margin_self_eq_zero {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (S : Finset A) :
    Finset.sum S (fun s => Finset.sum S (fun y => margin P s y)) = 0 := by
  classical
  have hskew : ∀ x y, margin P y x = - margin P x y := by
    intro x y
    simpa [skew_symmetric] using (margin_antisymmetric (P := P) y x)
  have hneg :
      Finset.sum S (fun s => Finset.sum S (fun y => margin P s y)) =
        - Finset.sum S (fun s => Finset.sum S (fun y => margin P s y)) := by
    calc
      Finset.sum S (fun s => Finset.sum S (fun y => margin P s y)) =
          Finset.sum S (fun s => Finset.sum S (fun y => margin P y s)) := by
              simpa using
                (Finset.sum_comm (s := S) (t := S) (f := fun s y => margin P s y))
      _ = Finset.sum S (fun s => Finset.sum S (fun y => - margin P s y)) := by
              refine Finset.sum_congr rfl ?_
              intro s hs
              refine Finset.sum_congr rfl ?_
              intro y hy
              simp [hskew s y]
      _ = - Finset.sum S (fun s => Finset.sum S (fun y => margin P s y)) := by
              simp [Finset.sum_neg_distrib]
  linarith

lemma exists_pos_c2BordaScore_of_dominatesSet {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) {S : Finset A} (hS : dominatesSet P S)
    (hproper : S ≠ (Finset.univ : Finset A)) :
    ∃ s ∈ S, 0 < c2BordaScore P s := by
  classical
  let T : Finset A := (Finset.univ.filter (fun a => a ∉ S))
  have hTne : T.Nonempty := by
    by_contra hT
    have hT' : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    have hSuniv : S = (Finset.univ : Finset A) := by
      ext x
      constructor
      · intro hx
        exact mem_univ x
      · intro _hx
        by_contra hxS
        have hxT : x ∈ T := by
          simp [T, hxS]
        simp [hT'] at hxT
    exact hproper hSuniv
  have hdisj : Disjoint S T := by
    refine Finset.disjoint_left.2 ?_
    intro x hxS hxT
    exact (Finset.mem_filter.mp hxT).2 hxS
  have hunion : S ∪ T = (Finset.univ : Finset A) := by
    ext x
    by_cases hxS : x ∈ S <;> simp [T, hxS]
  have hsplit : ∀ s : A,
      Finset.sum (Finset.univ : Finset A) (fun y => margin P s y) =
        Finset.sum S (fun y => margin P s y) + Finset.sum T (fun y => margin P s y) := by
    intro s
    simpa [hunion] using (Finset.sum_union hdisj (f := fun y => margin P s y))
  have hsum_eq :
      Finset.sum S (fun s => c2BordaScore P s) =
        Finset.sum S (fun s => Finset.sum S (fun y => margin P s y)) +
          Finset.sum S (fun s => Finset.sum T (fun y => margin P s y)) := by
    calc
      Finset.sum S (fun s => c2BordaScore P s) =
          Finset.sum S (fun s =>
            Finset.sum (Finset.univ : Finset A) (fun y => margin P s y)) := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            simp [c2BordaScore]
      _ = Finset.sum S (fun s =>
            Finset.sum S (fun y => margin P s y) +
              Finset.sum T (fun y => margin P s y)) := by
            refine Finset.sum_congr rfl ?_
            intro s hs
            simp [hsplit s]
      _ = Finset.sum S (fun s => Finset.sum S (fun y => margin P s y)) +
            Finset.sum S (fun s => Finset.sum T (fun y => margin P s y)) := by
            simp [Finset.sum_add_distrib]
  have hsum_eq' :
      Finset.sum S (fun s => c2BordaScore P s) =
        Finset.sum S (fun s => Finset.sum T (fun y => margin P s y)) := by
    calc
      Finset.sum S (fun s => c2BordaScore P s) =
          Finset.sum S (fun s => Finset.sum S (fun y => margin P s y)) +
            Finset.sum S (fun s => Finset.sum T (fun y => margin P s y)) := hsum_eq
      _ = 0 + Finset.sum S (fun s => Finset.sum T (fun y => margin P s y)) := by
            simp [sum_margin_self_eq_zero (P := P) (S := S)]
      _ = Finset.sum S (fun s => Finset.sum T (fun y => margin P s y)) := by simp
  have hsum_pos : 0 < Finset.sum S (fun s => c2BordaScore P s) := by
    have hpos_cross :
        0 < Finset.sum S (fun s => Finset.sum T (fun y => margin P s y)) := by
      refine Finset.sum_pos ?_ hS.1
      intro s hs
      refine Finset.sum_pos ?_ hTne
      intro y hy
      have hyS : y ∉ S := (Finset.mem_filter.mp hy).2
      have hpos : margin_pos P s y := hS.2 s hs y hyS
      simpa [margin_pos] using hpos
    simpa [hsum_eq'] using hpos_cross
  by_contra hnone
  have hnonpos : ∀ s ∈ S, c2BordaScore P s ≤ 0 := by
    intro s hs
    have hnotpos : ¬ 0 < c2BordaScore P s := by
      intro hspos
      exact hnone ⟨s, hs, hspos⟩
    exact le_of_not_gt hnotpos
  have hsum_nonpos : Finset.sum S (fun s => c2BordaScore P s) ≤ 0 :=
    Finset.sum_nonpos hnonpos
  exact (not_le_of_gt hsum_pos) hsum_nonpos

lemma dominatesSet_restrictCandidates_of_subset {V A : Type} [Fintype V] [Fintype A]
    [DecidableEq A] (P : Profile V A) {p : A → Prop} [DecidablePred p]
    {S : Finset A} (hS : dominatesSet P S) (hpos : ∃ s ∈ S, p s) :
    dominatesSet (restrictCandidates P p) (Finset.subtype (fun a => p a) S) := by
  classical
  set S' : Finset {a : A // p a} := Finset.subtype (fun a => p a) S
  rcases hpos with ⟨s, hsS, hspos⟩
  have hS'ne : S'.Nonempty := by
    refine ⟨⟨s, hspos⟩, ?_⟩
    exact Finset.mem_subtype.mpr hsS
  refine ⟨hS'ne, ?_⟩
  intro a ha b hb
  have haS : (a : A) ∈ S := (Finset.mem_subtype.mp ha)
  have hbS : (b : A) ∉ S := by
    intro hbS
    exact hb (Finset.mem_subtype.mpr hbS)
  have hpos' : margin_pos P (a : A) (b : A) := hS.2 a haS b hbS
  dsimp [margin_pos] at hpos' ⊢
  have heq := margin_eq_margin_restrictCandidates (P := P) (p := p) (a := a) (b := b)
  simpa [heq] using hpos'

lemma nansonAux_subset_of_dominatesSet :
    ∀ n : Nat, ∀ {A : Type} [Fintype A] [DecidableEq A],
      Fintype.card A ≤ n →
        ∀ {V : Type} [Fintype V] (P : Profile V A) (S : Finset A),
          dominatesSet P S → nansonAux n A P ⊆ S := by
  classical
  intro n
  refine Nat.strongRecOn (motive := fun n =>
    ∀ {A : Type} [Fintype A] [DecidableEq A],
      Fintype.card A ≤ n →
        ∀ {V : Type} [Fintype V] (P : Profile V A) (S : Finset A),
          dominatesSet P S → nansonAux n A P ⊆ S) n ?_
  intro n ih A _ _ hcard_le V _ P S hS
  cases n with
  | zero =>
      have hA' : IsEmpty A := by
        have hcard0 : Fintype.card A = 0 :=
          Nat.le_antisymm hcard_le (Nat.zero_le _)
        exact Fintype.card_eq_zero_iff.mp hcard0
      intro x hx
      exact (IsEmpty.elim hA' x)
  | succ n =>
      classical
      by_cases hSuniv : S = (Finset.univ : Finset A)
      · subst hSuniv
        intro x hx
        exact mem_univ x
      · have hpos_ex : ∃ s ∈ S, 0 < c2BordaScore P s :=
          exists_pos_c2BordaScore_of_dominatesSet (P := P) (S := S) hS hSuniv
        have hall : ¬ ∀ a : A, c2BordaScore P a = 0 := by
          intro hall
          rcases hpos_ex with ⟨s, hsS, hspos⟩
          have h0 := hall s
          linarith
        let p : A → Prop := fun a => c2BordaScore P a > 0
        have hsurv : (Finset.univ.filter (fun a => p a)).Nonempty := by
          rcases hpos_ex with ⟨s, hsS, hspos⟩
          refine ⟨s, ?_⟩
          simp [p, hspos]
        let P' : Profile V {a : A // p a} := restrictCandidates P p
        let S' : Finset {a : A // p a} := Finset.subtype (fun a => p a) S
        have hdom' : dominatesSet P' S' :=
          dominatesSet_restrictCandidates_of_subset (P := P) (p := p) hS hpos_ex
        rcases hpos_ex with ⟨s, hsS, hspos⟩
        have hneg_ex : ∃ d, c2BordaScore P d < 0 :=
          exists_neg_c2BordaScore_of_pos (P := P) (c := s) hspos
        rcases hneg_ex with ⟨d, hdneg⟩
        have hnotp : ¬ p d := by
          dsimp [p]
          exact not_lt_of_ge (le_of_lt hdneg)
        have hcard_lt : Fintype.card {a : A // p a} < Fintype.card A :=
          Fintype.card_subtype_lt (p := p) (x := d) hnotp
        have hcard_le' : Fintype.card {a : A // p a} ≤ n := by
          have hlt : Fintype.card {a : A // p a} < Nat.succ n :=
            lt_of_lt_of_le hcard_lt hcard_le
          exact Nat.lt_succ_iff.mp hlt
        have hrec :
            nansonAux n {a : A // p a} P' ⊆ S' := by
          have := ih (m := n) (Nat.lt_succ_self n)
            (A := {a : A // p a}) hcard_le' (V := V) (P := P') (S := S') hdom'
          exact this
        intro x hx
        have hx' : x ∈ liftWinners (nansonAux n {a : A // p a} P') := by
          simpa [nansonAux, hall, hsurv, p, P'] using hx
        have hx'' :
            ∃ a, a ∈ nansonAux n {a : A // p a} P' ∧ (a : A) = x := by
          classical
          simpa [liftWinners] using hx'
        rcases hx'' with ⟨a, ha, rfl⟩
        have haS' : a ∈ S' := hrec ha
        exact (Finset.mem_subtype.mp haS')

/-- Nanson satisfies the Smith criterion. -/
theorem nanson_smithCriterion : SmithCriterion nanson := by
  intro V A _ _ P
  classical
  by_cases hA : Nonempty A
  · let _ : Nonempty A := hA
    have hsubset :
        nansonAux (Fintype.card A) A P ⊆ topCycleSet (P := P) := by
      have hdom : dominatesSet P (topCycleSet (P := P)) := topCycleSet_dominates (P := P)
      exact nansonAux_subset_of_dominatesSet (n := Fintype.card A)
        (A := A) (P := P) (S := topCycleSet (P := P)) (by rfl) hdom
    simpa [nanson, topCycle, hA] using hsubset
  ·
    have hA' : IsEmpty A := (not_nonempty_iff.mp hA)
    have : IsEmpty A := hA'
    have hnanson : nanson P = (∅ : Finset A) := by
      simp [nanson, nansonAux]
    have htop : topCycle P = (∅ : Finset A) := by
      simp [topCycle, hA]
    simp [hnanson, htop]

end SocialChoice
