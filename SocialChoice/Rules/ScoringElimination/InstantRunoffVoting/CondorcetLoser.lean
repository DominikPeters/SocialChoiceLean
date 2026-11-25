import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringRules.Plurality.Defs
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.Defs
import SocialChoice.Axioms.Condorcet

namespace SocialChoice

open Finset
open scoped BigOperators

/-!
# IRV Satisfies the Condorcet Loser Criterion

This file proves that Instant Runoff Voting (IRV) satisfies the Condorcet loser criterion:
a Condorcet loser (a candidate who loses pairwise to every other candidate) cannot win.

## Proof sketch

Suppose `d` is a Condorcet loser and assume for contradiction that `d` wins IRV.
Then at some point during elimination, there exists a two-candidate set `{c, d}`
where `c` is eliminated (has lower plurality score) and `d` survives to win.

But in a two-candidate race:
- The plurality score of a candidate = number of first-place votes
- Number of first-place votes = number preferring you (since there are only 2)

Since `d` is a Condorcet loser, more voters prefer `c` to `d` than prefer `d` to `c`.
Therefore `c` has higher plurality score, contradicting that `c` was eliminated.
-/

variable {V A : Type} [Fintype V] [Fintype A]

/-! ### Condorcet loser in two-candidate election -/

/-- A Condorcet loser in a 2-candidate election has strictly fewer first-place votes -/
lemma CondorcetLoser_lower_plurality_two (P : Profile V A) (hcard : Fintype.card A = 2)
    (c d : A) (hcd : c ≠ d) (hloser : CondorcetLoser P d) :
    scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) d <
      scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) c := by
  rw [pluralityScore_eq_votersPreferring_of_two P hcard d c (Ne.symm hcd)]
  rw [pluralityScore_eq_votersPreferring_of_two P hcard c d hcd]
  -- hloser says margin_pos P c d (since c ≠ d and d is Condorcet loser)
  have hmargin : margin_pos P c d :=
    (strictMajority_votersPreferring_iff_margin_pos
      (P := P) (c := c) (d := d) (hcd := hcd)).1 (hloser.1 c hcd)
  -- margin_pos means more prefer c > d than d > c
  dsimp [margin_pos, margin] at hmargin
  have hmargin' :
      0 < Int.ofNat (votersPreferring P c d).card -
          Int.ofNat (votersPreferring P d c).card := by
    simpa [votersPreferring, Prefers] using hmargin
  -- The margin inequality rearranges to the desired comparison of counts.
  have hlt :
      (Int.ofNat (votersPreferring P d c).card) <
        Int.ofNat (votersPreferring P c d).card := sub_pos.mp hmargin'
  simpa using hlt

lemma lowestScoring_plurality_iff_forall_le_topCount
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (hA : (Finset.univ : Finset A).Nonempty) (c : A) :
    c ∈ lowestScoring P (fun r => pluralityScore (Fintype.card A) r) ↔
      ∀ d : A, topCount P c ≤ topCount P d := by
  classical
  constructor
  · intro hc d
    have hle :
        scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) c ≤
          scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) d :=
      (lowestScoring_iff_forall_le (P := P)
        (score := fun r => pluralityScore (Fintype.card A) r) hA c).1 hc d
    have hle' : (topCount P c : Int) ≤ topCount P d := by
      simpa [pluralityScore_eq_topCount] using hle
    exact_mod_cast hle'
  · intro hle
    apply (lowestScoring_iff_forall_le (P := P)
      (score := fun r => pluralityScore (Fintype.card A) r) hA c).2
    intro d
    have hle' : (topCount P c : Int) ≤ topCount P d := by
      exact_mod_cast hle d
    simpa [pluralityScore_eq_topCount] using hle'

lemma instantRunoffVoting_of_card_two
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (hcard : Fintype.card A = 2) (a b : A) (hab : a ≠ b) :
    a ∈ instantRunoffVoting P ↔ 0 ≤ margin P a b := by
  classical
  let : DecidableEq A := Classical.decEq A
  have hnot_le_one : ¬ Fintype.card A ≤ 1 := by
    omega
  let m := Fintype.card A
  let scoreVec : Nat → Int := fun r => pluralityScore m r
  let L : Finset A := lowestScoring P scoreVec
  have haux :
      scoringEliminationAux pluralityScore A P =
        L.biUnion (fun c => liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P c))) := by
    simpa [m, scoreVec, L] using
      (scoringEliminationAux_eq_biUnion_of_not_card_le_one
        (score := pluralityScore) (P := P) (hcard := hnot_le_one))
  have hA : (Finset.univ : Finset A).Nonempty := by
    have hpos : 0 < Fintype.card A := by omega
    have : Nonempty A := Fintype.card_pos_iff.mp hpos
    exact Finset.univ_nonempty
  have hbL : b ∈ L ↔ topCount P b ≤ topCount P a := by
    constructor
    · intro hb
      have hb' :=
        (lowestScoring_plurality_iff_forall_le_topCount (P := P) hA (c := b)).1 hb
      exact hb' a
    · intro hle
      apply (lowestScoring_plurality_iff_forall_le_topCount (P := P) hA (c := b)).2
      intro d
      rcases two_elems_eq_or_eq hcard a b hab d with rfl | rfl
      · exact hle
      · exact le_rfl
  have ha_mem : a ∈ scoringEliminationAux pluralityScore A P ↔ b ∈ L := by
    constructor
    · intro ha
      have ha' := ha
      rw [haux] at ha'
      rcases Finset.mem_biUnion.mp ha' with ⟨c, hcL, ha_in⟩
      have hca : c ≠ a := by
        intro hEq
        have ha_in' : c ∈ liftFinset
            (scoringEliminationAux pluralityScore {x : A // x ≠ c} (restrictProfile P c)) := by
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
          (scoringEliminationAux pluralityScore {x : A // x ≠ b} (restrictProfile P b)).Nonempty := by
        simpa using
          (scoringEliminationAux_nonempty (score := pluralityScore) (P := restrictProfile P b))
      rcases hne with ⟨w, hw⟩
      have hw_eq : w = (⟨a, hab⟩ : {x : A // x ≠ b}) := by
        exact Subsingleton.elim _ _
      have ha_in_sub :
          (⟨a, hab⟩ : {x : A // x ≠ b}) ∈
            scoringEliminationAux pluralityScore {x : A // x ≠ b} (restrictProfile P b) := by
        simpa [hw_eq] using hw
      have ha_in :
          a ∈ liftFinset (scoringEliminationAux pluralityScore {x : A // x ≠ b}
            (restrictProfile P b)) := by
        exact (mem_liftFinset_iff_subtype
          (s := scoringEliminationAux pluralityScore {x : A // x ≠ b} (restrictProfile P b))
          (x := a)).2 ⟨hab, ha_in_sub⟩
      have ha' :
          a ∈ L.biUnion (fun c =>
            liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P c))) := by
        refine Finset.mem_biUnion.mpr ?_
        exact ⟨b, hb, ha_in⟩
      simpa [haux] using ha'
  have hmargin : 0 ≤ margin P a b ↔ topCount P b ≤ topCount P a :=
    margin_nonneg_iff_topCount_le_of_two (P := P) hcard hab
  have ha_mem' :
      a ∈ scoringEliminationAux pluralityScore A P ↔ 0 ≤ margin P a b :=
    (ha_mem.trans hbL).trans hmargin.symm
  simpa [instantRunoffVoting, scoringEliminationRule] using ha_mem'

/-! ### Main theorem -/

theorem irv_CondorcetLoser_criterion : CondorcetLoserCriterion instantRunoffVoting := by
  intro V A _ _ P d hloser
  classical
  let : DecidableEq A := Classical.decEq A
  -- Reduce to the auxiliary elimination function.
  change d ∉ scoringEliminationAux pluralityScore A P
  -- Strong induction on the number of candidates.
  set n : Nat := Fintype.card A
  have aux :
      ∀ n : Nat,
        (∀ m < n,
          ∀ {A : Type} [Fintype A] [DecidableEq A],
            Fintype.card A = m →
              ∀ {V : Type} [Fintype V] (P : Profile V A) (d : A),
                CondorcetLoser P d → d ∉ scoringEliminationAux pluralityScore A P) →
        ∀ {A : Type} [Fintype A] [DecidableEq A],
          Fintype.card A = n →
            ∀ {V : Type} [Fintype V] (P : Profile V A) (d : A),
              CondorcetLoser P d → d ∉ scoringEliminationAux pluralityScore A P := by
    intro n ih A _ _ hcard V _ P d hloser
    classical
    -- We are never in the base case `card ≤ 1`, since a Condorcet loser requires another candidate.
    have hnot_le_one : ¬ Fintype.card A ≤ 1 := by
      intro hle
      have hsubs : Subsingleton A := (Fintype.card_le_one_iff_subsingleton).1 hle
      rcases hloser.2 with ⟨y, hy⟩
      exact hy (Subsingleton.elim y d)
    -- Split on candidate count.
    by_cases htwo : Fintype.card A = 2
    · -- Two-candidate case: use the 2-candidate IRV characterization.
      intro hdmem
      rcases hloser.2 with ⟨y, hyd⟩
      let instDec : DecidableEq A := inferInstance
      have hdmem_irv : d ∈ instantRunoffVoting P := by
        let : DecidableEq A := Classical.decEq A
        have hcongr :=
          scoringEliminationAux_decidableEq_congr (score := pluralityScore) (P := P)
            (inst1 := instDec) (inst2 := Classical.decEq A)
        have hdmem' :
            d ∈ @scoringEliminationAux V _ pluralityScore A _ (Classical.decEq A) P := by
          simpa [hcongr] using hdmem
        simpa [instantRunoffVoting, scoringEliminationRule] using hdmem'
      have hnonneg : 0 ≤ margin P d y :=
        (instantRunoffVoting_of_card_two (P := P) (hcard := htwo) (a := d) (b := y)
          (hab := hyd.symm)).1 hdmem_irv
      have hpos : margin_pos P y d :=
        (CondorcetLoser_iff_margin_pos (P := P) (c := d)).1 hloser |>.1 y hyd.symm
      have hneg : margin P d y < 0 := by
        have hpos' : 0 < margin P y d := by
          simpa [margin_pos] using hpos
        have hskew : margin P d y = - margin P y d := by
          simpa [skew_symmetric] using (margin_antisymmetric (P := P)) d y
        linarith
      exact (not_lt_of_ge hnonneg) hneg
    · -- Recursive case: at least three candidates.
      have hgt2 : 2 < Fintype.card A := by
        have hne2 : Fintype.card A ≠ 2 := htwo
        have hone : 1 < Fintype.card A := Nat.lt_of_not_ge hnot_le_one
        -- Now exclude `card = 2` to get `2 < card`.
        exact lt_of_le_of_ne (Nat.succ_le_of_lt hone) (Ne.symm hne2)
      have hcard' : ¬ Fintype.card A ≤ 1 := hnot_le_one
      have haux :=
        scoringEliminationAux_eq_biUnion_of_not_card_le_one
          (score := pluralityScore) (P := P) (hcard := hcard')
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
      -- Convert `d ∈ liftFinset ...` into membership of the corresponding subtype element.
      have hd_in' : (⟨d, hdc⟩ : {x : A // x ≠ c}) ∈
          scoringEliminationAux pluralityScore {x : A // x ≠ c} (restrictProfile P c) := by
        -- `liftFinset` is `image Subtype.val`.
        have himage : d ∈ (scoringEliminationAux pluralityScore {x : A // x ≠ c} (restrictProfile P c)).image
            (fun x : {x : A // x ≠ c} => (x : A)) := by
          simpa [liftFinset] using hd_in
        rcases Finset.mem_image.mp himage with ⟨x, hx, hxval⟩
        have hx' : x = (⟨d, hdc⟩ : {x : A // x ≠ c}) := by
          ext
          simpa using hxval
        simpa [hx'] using hx
      -- Apply the induction hypothesis to the restricted election.
      have hltcard : Fintype.card {x : A // x ≠ c} < n := by
        -- Use the strict decrease proved in `ScoringElimination/Defs.lean`.
        simpa [hcard] using (card_restrict_lt (A := A) c)
      have hloser' :
          CondorcetLoser (restrictProfile P c) (⟨d, hdc⟩ : {x : A // x ≠ c}) :=
        CondorcetLoser_restrictProfile_of_two_lt_card (P := P) (hdc := hdc) (hcard := hgt2) hloser
      have hnot : (⟨d, hdc⟩ : {x : A // x ≠ c}) ∉
          scoringEliminationAux pluralityScore {x : A // x ≠ c} (restrictProfile P c) := by
        -- Specialize IH to the restricted type.
        have := ih (m := Fintype.card {x : A // x ≠ c}) hltcard
          (A := {x : A // x ≠ c}) (by rfl) (V := V) (P := restrictProfile P c)
          (d := (⟨d, hdc⟩ : {x : A // x ≠ c})) hloser'
        simpa using this
      exact hnot hd_in'
  -- Finish by invoking `aux` at `n = card A`.
  let Motive : Nat → Prop := fun k =>
    ∀ {A : Type} [Fintype A] [DecidableEq A],
      Fintype.card A = k →
        ∀ {V : Type} [Fintype V] (P : Profile V A) (d : A),
          CondorcetLoser P d → d ∉ scoringEliminationAux pluralityScore A P
  have hStrong : Motive n := by
    classical
    refine Nat.strongRecOn (motive := Motive) n (fun k ih => ?_)
    -- Build the IH required by `aux` from the `strongRecOn` hypothesis `ih`.
    intro A _ _ hcardA V _ P d hloser
    have ihAux :
        ∀ m < k,
          ∀ {A : Type} [Fintype A] [DecidableEq A],
            Fintype.card A = m →
              ∀ {V : Type} [Fintype V] (P : Profile V A) (d : A),
                CondorcetLoser P d → d ∉ scoringEliminationAux pluralityScore A P := by
      intro m hm A _ _ hcardm V _ P d hloser
      -- `ih m hm` is the induction hypothesis at `m`.
      exact (ih m hm) (by simpa using hcardm) (P := P) (d := d) hloser
    exact aux k ihAux (A := A) (by simpa using hcardA) (V := V) (P := P) (d := d) hloser
  have := hStrong (A := A) (by rfl) (V := V) (P := P) (d := d) hloser
  simpa [Motive, n] using this

end SocialChoice
