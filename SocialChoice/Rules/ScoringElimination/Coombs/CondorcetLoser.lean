import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic
import SocialChoice.Axioms.Condorcet
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.Coombs.Defs
import SocialChoice.Rules.ScoringRules.Plurality.Defs
import SocialChoice.Rules.ScoringRules.Veto.Common

namespace SocialChoice

open Finset
open scoped BigOperators

variable {V A : Type} [Fintype V] [Fintype A]

/-! ### Two-candidate lemmas -/

lemma bottomRank_iff_prefers_of_two
    (P : Profile V A) (hcard : Fintype.card A = 2)
    (c d : A) (hcd : c ≠ d) (v : V) :
    BottomRank P v c ↔ Prefers P v d c := by
  constructor
  · intro hbottom
    exact hbottom d hcd.symm
  · intro hpref e he
    rcases two_elems_eq_or_eq hcard c d hcd e with rfl | rfl
    · exact (he rfl).elim
    · exact hpref

lemma notBottomRank_iff_prefers_of_two
    (P : Profile V A) (hcard : Fintype.card A = 2)
    (c d : A) (hcd : c ≠ d) (v : V) :
    (¬ BottomRank P v c) ↔ Prefers P v c d := by
  constructor
  · intro hnot
    have hnot' : ¬ Prefers P v d c := by
      intro hdc
      exact hnot ((bottomRank_iff_prefers_of_two P hcard c d hcd v).2 hdc)
    let _ := P.pref v
    have hlt_or : Prefers P v c d ∨ Prefers P v d c := lt_or_gt_of_ne hcd
    cases hlt_or with
    | inl h => exact h
    | inr h => exact (hnot' h).elim
  · intro hpref hbottom
    have hdc : Prefers P v d c :=
      (bottomRank_iff_prefers_of_two P hcard c d hcd v).1 hbottom
    let _ : Preorder A := (P.pref v).toPreorder
    exact (lt_asymm hpref hdc).elim

lemma vetoScore_eq_topCount_of_two
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (hcard : Fintype.card A = 2)
    (c d : A) (hcd : c ≠ d) :
    scoreCandidate P (fun r => vetoScore (Fintype.card A) r) c =
      topCount P c := by
  classical
  have hscore :
      scoreCandidate P (fun r => vetoScore (Fintype.card A) r) c =
        ((Finset.univ.filter (fun v => ¬ BottomRank P v c)).card : Int) := by
    simpa [vetoScore] using
      (vetoScore_scoreCandidate_eq_notBottom_card (P := P) (c := c))
  have hvoters :
      (Finset.univ.filter (fun v => ¬ BottomRank P v c)).card =
        (votersPreferring P c d).card := by
    classical
    apply cardinality_lemma2
    intro v
    exact (notBottomRank_iff_prefers_of_two P hcard c d hcd v)
  have htop :
      topCount P c = (votersPreferring P c d).card := by
    have h :=
      congrArg Finset.card
        (votersTop_eq_votersPreferring_of_two (P := P) hcard c d hcd)
    simpa [topCount] using h
  calc
    scoreCandidate P (fun r => vetoScore (Fintype.card A) r) c
        = ((Finset.univ.filter (fun v => ¬ BottomRank P v c)).card : Int) := hscore
    _ = ((votersPreferring P c d).card : Int) := by exact_mod_cast hvoters
    _ = topCount P c := by exact_mod_cast htop.symm

lemma coombs_of_card_two
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (hcard : Fintype.card A = 2) (a b : A) (hab : a ≠ b) :
    a ∈ coombs P ↔ 0 ≤ margin P a b := by
  classical
  let : DecidableEq A := Classical.decEq A
  have hnot_le_one : ¬ Fintype.card A ≤ 1 := by
    omega
  let m := Fintype.card A
  let scoreVec : Nat → Int := fun r => vetoScore m r
  let L : Finset A := lowestScoring P scoreVec
  have haux :
      scoringEliminationAux vetoScore A P =
        L.biUnion (fun c => liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P c))) := by
    simpa [m, scoreVec, L] using
      (scoringEliminationAux_eq_biUnion_of_not_card_le_one
        (score := vetoScore) (P := P) (hcard := hnot_le_one))
  have hA : (Finset.univ : Finset A).Nonempty := by
    have hpos : 0 < Fintype.card A := by omega
    have : Nonempty A := Fintype.card_pos_iff.mp hpos
    exact Finset.univ_nonempty
  have hbL : b ∈ L ↔ topCount P b ≤ topCount P a := by
    constructor
    · intro hb
      have hle :
          scoreCandidate P scoreVec b ≤ scoreCandidate P scoreVec a :=
        (lowestScoring_iff_forall_le (P := P) (score := scoreVec) hA b).1 hb a
      have hscore_b :
          scoreCandidate P scoreVec b = topCount P b := by
        simpa [scoreVec, m] using
          (vetoScore_eq_topCount_of_two (P := P) (hcard := hcard) (c := b) (d := a)
            (hcd := hab.symm))
      have hscore_a :
          scoreCandidate P scoreVec a = topCount P a := by
        simpa [scoreVec, m] using
          (vetoScore_eq_topCount_of_two (P := P) (hcard := hcard) (c := a) (d := b)
            (hcd := hab))
      have hle' : (topCount P b : Int) ≤ topCount P a := by
        simpa [hscore_b, hscore_a] using hle
      exact_mod_cast hle'
    · intro hle
      apply (lowestScoring_iff_forall_le (P := P) (score := scoreVec) hA b).2
      intro d
      rcases two_elems_eq_or_eq hcard a b hab d with rfl | rfl
      · have hle' : (topCount P b : Int) ≤ topCount P d := by
          exact_mod_cast hle
        have hscore_b :
            scoreCandidate P scoreVec b = topCount P b := by
          simpa [scoreVec, m] using
            (vetoScore_eq_topCount_of_two (P := P) (hcard := hcard) (c := b) (d := d)
              (hcd := hab.symm))
        have hscore_a :
            scoreCandidate P scoreVec d = topCount P d := by
          simpa [scoreVec, m] using
            (vetoScore_eq_topCount_of_two (P := P) (hcard := hcard) (c := d) (d := b)
              (hcd := hab))
        simpa [hscore_b, hscore_a] using hle'
      · exact le_rfl
  have ha_mem : a ∈ scoringEliminationAux vetoScore A P ↔ b ∈ L := by
    constructor
    · intro ha
      have ha' := ha
      rw [haux] at ha'
      rcases Finset.mem_biUnion.mp ha' with ⟨c, hcL, ha_in⟩
      have hca : c ≠ a := by
        intro hEq
        have ha_in' : c ∈ liftFinset
            (scoringEliminationAux vetoScore {x : A // x ≠ c} (restrictProfile P c)) := by
          simpa [hEq] using ha_in
        exact (not_mem_liftFinset_removed (c := c) _ ha_in')
      have hcb : c = b := by
        rcases two_elems_eq_or_eq hcard a b hab c with rfl | rfl
        · exact (hca rfl).elim
        · rfl
      simpa [L, hcb] using hcL
    · intro hb
      have hcard_sub_eq : Fintype.card {x : A // x ≠ b} = 1 := by
        simp [card_subtype_ne_eq b, hcard]
      have hcard_sub : Fintype.card {x : A // x ≠ b} ≤ 1 := by
        exact le_of_eq hcard_sub_eq
      have hsub : Subsingleton {x : A // x ≠ b} :=
        (Fintype.card_le_one_iff_subsingleton).1 hcard_sub
      have : Nonempty {x : A // x ≠ b} := by
        have hpos : 0 < Fintype.card {x : A // x ≠ b} := by
          simp [hcard_sub_eq]
        exact Fintype.card_pos_iff.mp hpos
      have hne :
          (scoringEliminationAux vetoScore {x : A // x ≠ b} (restrictProfile P b)).Nonempty := by
        simpa using
          (scoringEliminationAux_nonempty (score := vetoScore) (P := restrictProfile P b))
      rcases hne with ⟨w, hw⟩
      have hw_eq : w = (⟨a, hab⟩ : {x : A // x ≠ b}) := by
        exact Subsingleton.elim _ _
      have ha_in_sub :
          (⟨a, hab⟩ : {x : A // x ≠ b}) ∈
            scoringEliminationAux vetoScore {x : A // x ≠ b} (restrictProfile P b) := by
        simpa [hw_eq] using hw
      have ha_in :
          a ∈ liftFinset (scoringEliminationAux vetoScore {x : A // x ≠ b}
            (restrictProfile P b)) := by
        exact (mem_liftFinset_iff_subtype
          (s := scoringEliminationAux vetoScore {x : A // x ≠ b} (restrictProfile P b))
          (x := a)).2 ⟨hab, ha_in_sub⟩
      have ha' :
          a ∈ L.biUnion (fun c =>
            liftFinset (scoringEliminationAux vetoScore _ (restrictProfile P c))) := by
        refine Finset.mem_biUnion.mpr ?_
        exact ⟨b, hb, ha_in⟩
      simpa [haux] using ha'
  have hmargin : 0 ≤ margin P a b ↔ topCount P b ≤ topCount P a :=
    margin_nonneg_iff_topCount_le_of_two (P := P) hcard hab
  have ha_mem' :
      a ∈ scoringEliminationAux vetoScore A P ↔ 0 ≤ margin P a b :=
    (ha_mem.trans hbL).trans hmargin.symm
  simpa [coombs, scoringEliminationRule] using ha_mem'

/-! ### Main theorem -/

theorem coombs_CondorcetLoser_criterion : CondorcetLoserCriterion coombs := by
  intro V A _ _ P d hloser
  classical
  let : DecidableEq A := Classical.decEq A
  change d ∉ scoringEliminationAux vetoScore A P
  set n : Nat := Fintype.card A
  have aux :
      ∀ n : Nat,
        (∀ m < n,
          ∀ {A : Type} [Fintype A] [DecidableEq A],
            Fintype.card A = m →
              ∀ {V : Type} [Fintype V] (P : Profile V A) (d : A),
                CondorcetLoser P d → d ∉ scoringEliminationAux vetoScore A P) →
        ∀ {A : Type} [Fintype A] [DecidableEq A],
          Fintype.card A = n →
            ∀ {V : Type} [Fintype V] (P : Profile V A) (d : A),
              CondorcetLoser P d → d ∉ scoringEliminationAux vetoScore A P := by
    intro n ih A _ _ hcard V _ P d hloser
    classical
    have hnot_le_one : ¬ Fintype.card A ≤ 1 := by
      intro hle
      have hsubs : Subsingleton A := (Fintype.card_le_one_iff_subsingleton).1 hle
      rcases hloser.2 with ⟨y, hy⟩
      exact hy (Subsingleton.elim y d)
    by_cases htwo : Fintype.card A = 2
    · intro hdmem
      rcases hloser.2 with ⟨y, hyd⟩
      let instDec : DecidableEq A := inferInstance
      have hdmem_coombs : d ∈ coombs P := by
        let : DecidableEq A := Classical.decEq A
        have hcongr :=
          scoringEliminationAux_decidableEq_congr (score := vetoScore) (P := P)
            (inst1 := instDec) (inst2 := Classical.decEq A)
        have hdmem' :
            d ∈ @scoringEliminationAux V _ vetoScore A _ (Classical.decEq A) P := by
          simpa [hcongr] using hdmem
        simpa [coombs, scoringEliminationRule] using hdmem'
      have hnonneg : 0 ≤ margin P d y :=
        (coombs_of_card_two (P := P) (hcard := htwo) (a := d) (b := y)
          (hab := hyd.symm)).1 hdmem_coombs
      have hpos : margin_pos P y d :=
        (CondorcetLoser_iff_margin_pos (P := P) (c := d)).1 hloser |>.1 y hyd.symm
      have hneg : margin P d y < 0 := by
        have hpos' : 0 < margin P y d := by
          simpa [margin_pos] using hpos
        have hskew : margin P d y = - margin P y d := by
          simpa [skew_symmetric] using (margin_antisymmetric (P := P)) d y
        linarith
      exact (not_lt_of_ge hnonneg) hneg
    · have hgt2 : 2 < Fintype.card A := by
        have hne2 : Fintype.card A ≠ 2 := htwo
        have hone : 1 < Fintype.card A := Nat.lt_of_not_ge hnot_le_one
        exact lt_of_le_of_ne (Nat.succ_le_of_lt hone) (Ne.symm hne2)
      have hcard' : ¬ Fintype.card A ≤ 1 := hnot_le_one
      have haux :=
        scoringEliminationAux_eq_biUnion_of_not_card_le_one
          (score := vetoScore) (P := P) (hcard := hcard')
      intro hdmem
      have hdmem' := hdmem
      rw [haux] at hdmem'
      dsimp at hdmem'
      rcases (Finset.mem_biUnion.mp hdmem') with ⟨c, hcL, hd_in⟩
      have hcd : c ≠ d := by
        intro hEq
        subst hEq
        exact (not_mem_liftFinset_removed (c := c) _ hd_in)
      have hdc : d ≠ c := by simpa [eq_comm] using hcd
      have hd_in' : (⟨d, hdc⟩ : {x : A // x ≠ c}) ∈
          scoringEliminationAux vetoScore {x : A // x ≠ c} (restrictProfile P c) := by
        have himage : d ∈ (scoringEliminationAux vetoScore {x : A // x ≠ c} (restrictProfile P c)).image
            (fun x : {x : A // x ≠ c} => (x : A)) := by
          simpa [liftFinset] using hd_in
        rcases Finset.mem_image.mp himage with ⟨x, hx, hxval⟩
        have hx' : x = (⟨d, hdc⟩ : {x : A // x ≠ c}) := by
          ext
          simpa using hxval
        simpa [hx'] using hx
      have hltcard : Fintype.card {x : A // x ≠ c} < n := by
        simpa [hcard] using (card_restrict_lt (A := A) c)
      have hloser' :
          CondorcetLoser (restrictProfile P c) (⟨d, hdc⟩ : {x : A // x ≠ c}) :=
        CondorcetLoser_restrictProfile_of_two_lt_card (P := P) (hdc := hdc) (hcard := hgt2) hloser
      have hnot : (⟨d, hdc⟩ : {x : A // x ≠ c}) ∉
          scoringEliminationAux vetoScore {x : A // x ≠ c} (restrictProfile P c) := by
        have := ih (m := Fintype.card {x : A // x ≠ c}) hltcard
          (A := {x : A // x ≠ c}) (by rfl) (V := V) (P := restrictProfile P c)
          (d := (⟨d, hdc⟩ : {x : A // x ≠ c})) hloser'
        simpa using this
      exact hnot hd_in'
  let Motive : Nat → Prop := fun k =>
    ∀ {A : Type} [Fintype A] [DecidableEq A],
      Fintype.card A = k →
        ∀ {V : Type} [Fintype V] (P : Profile V A) (d : A),
          CondorcetLoser P d → d ∉ scoringEliminationAux vetoScore A P
  have hStrong : Motive n := by
    classical
    refine Nat.strongRecOn (motive := Motive) n (fun k ih => ?_)
    intro A _ _ hcardA V _ P d hloser
    have ihAux :
        ∀ m < k,
          ∀ {A : Type} [Fintype A] [DecidableEq A],
            Fintype.card A = m →
              ∀ {V : Type} [Fintype V] (P : Profile V A) (d : A),
                CondorcetLoser P d → d ∉ scoringEliminationAux vetoScore A P := by
      intro m hm A _ _ hcardm V _ P d hloser
      exact (ih m hm) (by simpa using hcardm) (P := P) (d := d) hloser
    exact aux k ihAux (A := A) (by simpa using hcardA) (V := V) (P := P) (d := d) hloser
  have := hStrong (A := A) (by rfl) (V := V) (P := P) (d := d) hloser
  simpa [Motive, n] using this

end SocialChoice
