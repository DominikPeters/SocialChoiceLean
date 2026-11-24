import Mathlib.Tactic
import SocialChoice.Axioms.Independence
import SocialChoice.Margin
import SocialChoice.Rules.Minimax.Defs
import SocialChoice.Rules.Minimax.Pareto

namespace SocialChoice

open Finset

private lemma mem_minimax_iff {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (P : Profile V A) (a : A) :
    a ∈ minimax P ↔ maxLoss P a = minimaxScore P := by
  classical
  simp [minimax, Finset.mem_filter, (inferInstance : Nonempty A)]

private lemma mem_liftWinners_iff {A : Type} [DecidableEq A]
    {p : A → Prop} [DecidablePred p]
    (s : Finset {x : A // p x}) (a : A) (ha : p a) :
    a ∈ liftWinners s ↔ (⟨a, ha⟩ : {x : A // p x}) ∈ s := by
  classical
  simp [liftWinners, Finset.mem_image, ha]

private lemma margin_dominated_le {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c d a : A) (hpref : ∀ v : V, Prefers P v c d) :
    margin P d a ≤ margin P c a := by
  classical
  let Sda : Finset V := Finset.univ.filter (fun v => Prefers P v d a)
  let Sca : Finset V := Finset.univ.filter (fun v => Prefers P v c a)
  let Sad : Finset V := Finset.univ.filter (fun v => Prefers P v a d)
  let Sac : Finset V := Finset.univ.filter (fun v => Prefers P v a c)
  have hda_le : Sda.card ≤ Sca.card := by
    refine cardinality_lemma
      (p := fun v => Prefers P v d a)
      (q := fun v => Prefers P v c a) ?_
    intro v hv
    let _ := P.pref v
    exact lt_trans (hpref v) hv
  have hac_le : Sac.card ≤ Sad.card := by
    refine cardinality_lemma
      (p := fun v => Prefers P v a c)
      (q := fun v => Prefers P v a d) ?_
    intro v hv
    let _ := P.pref v
    exact lt_trans hv (hpref v)
  have hda_le' : (Int.ofNat Sda.card) ≤ Int.ofNat Sca.card :=
    Int.ofNat_le_ofNat_of_le hda_le
  have hac_le' : (Int.ofNat Sac.card) ≤ Int.ofNat Sad.card :=
    Int.ofNat_le_ofNat_of_le hac_le
  have hneg : -Int.ofNat Sad.card ≤ -Int.ofNat Sac.card :=
    neg_le_neg hac_le'
  have hadd :
      Int.ofNat Sda.card + (-Int.ofNat Sad.card) ≤
        Int.ofNat Sca.card + (-Int.ofNat Sac.card) :=
    add_le_add hda_le' hneg
  simpa [margin, Sda, Sca, Sad, Sac, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd

private lemma maxLoss_restrict_eq_of_dominated {V A : Type}
    [Fintype V] [Fintype A] [DecidableEq A] [Nonempty V]
    (P : Profile V A) (c d a : A) (ha : a ≠ d)
    (hpref : ∀ v : V, Prefers P v c d) :
    maxLoss P a = maxLoss (restrictCandidates P (fun x => x ≠ d)) ⟨a, ha⟩ := by
  classical
  let P' : Profile V {x : A // x ≠ d} := restrictCandidates P (fun x => x ≠ d)
  have hcd : c ≠ d := by
    rcases Classical.choice (inferInstance : Nonempty V) with v0
    let _ := P.pref v0
    exact ne_of_lt (hpref v0)
  have hle1 : maxLoss P a ≤ maxLoss P' ⟨a, ha⟩ := by
    refine maxLoss_le_of_forall_margin_le
      (P := P) (a := a) (k := maxLoss P' ⟨a, ha⟩) ?_
    intro b
    by_cases hbd : b = d
    · subst b
      have hdom : margin P d a ≤ margin P c a :=
        margin_dominated_le (P := P) (c := c) (d := d) (a := a) hpref
      have hca_eq : margin P c a = margin P' ⟨c, hcd⟩ ⟨a, ha⟩ := by
        simpa [P'] using
          (margin_eq_margin_restrictCandidates
            (P := P) (p := fun x => x ≠ d)
            (a := ⟨c, hcd⟩) (b := ⟨a, ha⟩))
      have hca_le : margin P' ⟨c, hcd⟩ ⟨a, ha⟩ ≤ maxLoss P' ⟨a, ha⟩ :=
        margin_le_maxLoss (P := P') (a := ⟨a, ha⟩) (b := ⟨c, hcd⟩)
      calc
        margin P d a ≤ margin P c a := hdom
        _ = margin P' ⟨c, hcd⟩ ⟨a, ha⟩ := hca_eq
        _ ≤ maxLoss P' ⟨a, ha⟩ := hca_le
    · have hb : b ≠ d := hbd
      have hmargin_eq : margin P b a = margin P' ⟨b, hb⟩ ⟨a, ha⟩ := by
        simpa [P'] using
          (margin_eq_margin_restrictCandidates
            (P := P) (p := fun x => x ≠ d)
            (a := ⟨b, hb⟩) (b := ⟨a, ha⟩))
      have hle := margin_le_maxLoss (P := P') (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
      simpa [hmargin_eq] using hle
  have hle2 : maxLoss P' ⟨a, ha⟩ ≤ maxLoss P a := by
    refine maxLoss_le_of_forall_margin_le
      (P := P') (a := ⟨a, ha⟩) (k := maxLoss P a) ?_
    intro b
    have hmargin_eq : margin P' b ⟨a, ha⟩ = margin P b a := by
      simpa [P'] using
        (margin_eq_margin_restrictCandidates
          (P := P) (p := fun x => x ≠ d)
          (a := b) (b := ⟨a, ha⟩)).symm
    calc
      margin P' b ⟨a, ha⟩ = margin P b a := hmargin_eq
      _ ≤ maxLoss P a := margin_le_maxLoss (P := P) (a := a) (b := b)
  exact le_antisymm hle1 hle2

private lemma minimaxScore_restrict_eq_of_dominated {V A : Type}
    [Fintype V] [Fintype A] [DecidableEq A] [Nonempty V]
    (P : Profile V A) (c d : A) (hpref : ∀ v : V, Prefers P v c d) :
    minimaxScore (restrictCandidates P (fun x => x ≠ d)) = minimaxScore P := by
  classical
  let P' : Profile V {x : A // x ≠ d} := restrictCandidates P (fun x => x ≠ d)
  have hcd : c ≠ d := by
    rcases Classical.choice (inferInstance : Nonempty V) with v0
    let _ := P.pref v0
    exact ne_of_lt (hpref v0)
  let : Nonempty A := ⟨c⟩
  let : Nonempty {x : A // x ≠ d} := ⟨⟨c, hcd⟩⟩
  have hA' : (Finset.univ : Finset {x : A // x ≠ d}).Nonempty := by
    exact ⟨⟨c, hcd⟩, by simp⟩
  have hle1 : minimaxScore P ≤ minimaxScore P' := by
    refine le_minimaxScore_of_forall
      (P := P') (k := minimaxScore P) (hA := hA') ?_
    intro a'
    have hmin : minimaxScore P ≤ maxLoss P a'.1 :=
      minimaxScore_le_of_candidate (P := P) (a := a'.1)
    have hmax_eq : maxLoss P a'.1 = maxLoss P' a' :=
      maxLoss_restrict_eq_of_dominated
        (P := P) (c := c) (d := d) (a := a'.1) (ha := a'.2) hpref
    simpa [hmax_eq] using hmin
  have hd_not : d ∉ minimax P :=
    minimax_pareto_efficiency (P := P) (c := c) (d := d) hpref
  have hminimax_nonempty : (minimax P).Nonempty :=
    minimax_isVotingRule (P := P)
  rcases hminimax_nonempty with ⟨w, hw⟩
  have hwd : w ≠ d := by
    intro hEq
    apply hd_not
    simpa [hEq] using hw
  have hw_eq : maxLoss P w = minimaxScore P :=
    (mem_minimax_iff (P := P) (a := w)).1 hw
  have hle2 : minimaxScore P' ≤ minimaxScore P := by
    have hmin_w : minimaxScore P' ≤ maxLoss P' ⟨w, hwd⟩ :=
      minimaxScore_le_of_candidate (P := P') (a := ⟨w, hwd⟩)
    have hmax_eq : maxLoss P w = maxLoss P' ⟨w, hwd⟩ :=
      maxLoss_restrict_eq_of_dominated
        (P := P) (c := c) (d := d) (a := w) (ha := hwd) hpref
    calc
      minimaxScore P' ≤ maxLoss P' ⟨w, hwd⟩ := hmin_w
      _ = maxLoss P w := hmax_eq.symm
      _ = minimaxScore P := hw_eq
  exact le_antisymm hle2 hle1

/-- Minimax satisfies independence of dominated alternatives. -/
theorem minimax_independenceOfDominated : IndependenceOfDominated minimax := by
  intro V A _ _ _ _ P c d hpref
  classical
  let P' : Profile V {x : A // x ≠ d} := restrictCandidates P (fun x => x ≠ d)
  have hcd : c ≠ d := by
    rcases Classical.choice (inferInstance : Nonempty V) with v0
    let _ := P.pref v0
    exact ne_of_lt (hpref v0)
  let : Nonempty A := ⟨c⟩
  let : Nonempty {x : A // x ≠ d} := ⟨⟨c, hcd⟩⟩
  have hd_not : d ∉ minimax P :=
    minimax_pareto_efficiency (P := P) (c := c) (d := d) hpref
  have hscore_eq : minimaxScore P' = minimaxScore P :=
    minimaxScore_restrict_eq_of_dominated (P := P) (c := c) (d := d) hpref
  apply Finset.ext
  intro a
  by_cases had : a = d
  · constructor
    · intro ha
      subst a
      have hnot : d ∉ liftWinners (minimax P') := by
        simp [liftWinners, P']
      exact (hnot ha).elim
    · intro ha
      subst a
      exact (hd_not ha).elim
  · constructor
    · intro ha
      have ha' : (⟨a, had⟩ : {x : A // x ≠ d}) ∈ minimax P' :=
        (mem_liftWinners_iff (s := minimax P') (a := a) (ha := had)).1 ha
      have hEq' : maxLoss P' ⟨a, had⟩ = minimaxScore P' :=
        (mem_minimax_iff (P := P') (a := ⟨a, had⟩)).1 ha'
      have hmax_eq : maxLoss P a = maxLoss P' ⟨a, had⟩ :=
        maxLoss_restrict_eq_of_dominated
          (P := P) (c := c) (d := d) (a := a) (ha := had) hpref
      have hEq : maxLoss P a = minimaxScore P := by
        calc
          maxLoss P a = maxLoss P' ⟨a, had⟩ := hmax_eq
          _ = minimaxScore P' := hEq'
          _ = minimaxScore P := hscore_eq
      exact (mem_minimax_iff (P := P) (a := a)).2 hEq
    · intro ha
      have hEq : maxLoss P a = minimaxScore P :=
        (mem_minimax_iff (P := P) (a := a)).1 ha
      have hmax_eq : maxLoss P a = maxLoss P' ⟨a, had⟩ :=
        maxLoss_restrict_eq_of_dominated
          (P := P) (c := c) (d := d) (a := a) (ha := had) hpref
      have hEq' : maxLoss P' ⟨a, had⟩ = minimaxScore P' := by
        calc
          maxLoss P' ⟨a, had⟩ = maxLoss P a := hmax_eq.symm
          _ = minimaxScore P := hEq
          _ = minimaxScore P' := hscore_eq.symm
      have haSubtype : (⟨a, had⟩ : {x : A // x ≠ d}) ∈ minimax P' :=
        (mem_minimax_iff (P := P') (a := ⟨a, had⟩)).2 hEq'
      exact (mem_liftWinners_iff (s := minimax P') (a := a) (ha := had)).2 haSubtype

end SocialChoice
