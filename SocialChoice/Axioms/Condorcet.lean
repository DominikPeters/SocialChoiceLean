import SocialChoice.Profile
import SocialChoice.Margin
import SocialChoice.Cycles
import SocialChoice.Meta

namespace SocialChoice

open Finset

def CondorcetWinner {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) : Prop :=
  ∀ d : A, d ≠ c → StrictMajority (votersPreferring P c d)

def CondorcetLoser {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) : Prop :=
  (∀ d : A, d ≠ c → StrictMajority (votersPreferring P d c)) ∧ ∃ d, d ≠ c

@[scAxiom]
def CondorcetConsistency (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) (c : A),
    CondorcetWinner P c → f P = {c}

@[scAxiom]
def CondorcetLoserCriterion (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) (c : A),
    CondorcetLoser P c → c ∉ f P

theorem condorcetConsistency_preservedUnderRefinement :
    PreservedUnderRefinement CondorcetConsistency := by
  intro f g hf_total _ hfg hZg V A _ _ P c hcw
  classical
  let _ : Nonempty A := ⟨c⟩
  have hsubset : f P ⊆ ({c} : Finset A) := by
    intro x hx
    have hxg : x ∈ g P := hfg P hx
    simpa [hZg P c hcw] using hxg
  have hnonempty : (f P).Nonempty := hf_total P
  rcases hnonempty with ⟨x, hx⟩
  have hx' : x = c := by
    have : x ∈ ({c} : Finset A) := hsubset hx
    simpa using this
  have hc : c ∈ f P := by
    simpa [hx'] using hx
  have hsup : ({c} : Finset A) ⊆ f P := by
    intro y hy
    have hy' : y = c := by
      simpa using hy
    subst hy'
    exact hc
  apply Finset.ext
  intro y
  constructor
  · intro hy
    exact hsubset hy
  · intro hy
    exact hsup hy

theorem condorcetLoserCriterion_preservedUnderRefinement :
    PreservedUnderRefinement CondorcetLoserCriterion := by
  intro f g _ _ hfg hZg V A _ _ P c hloser hc
  exact (hZg P c hloser) (hfg P hc)

lemma strictMajority_votersPreferring_iff_margin_pos {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {c d : A} (hcd : c ≠ d) :
    StrictMajority (votersPreferring P c d) ↔ margin_pos P c d := by
  classical
  let S := votersPreferring P c d
  let T := votersPreferring P d c
  have hdisj : Disjoint S T := by
    refine disjoint_left.2 ?_
    intro v hvS hvT
    have hcdv : Prefers P v c d := (Finset.mem_filter.mp hvS).2
    have hdcv : Prefers P v d c := (Finset.mem_filter.mp hvT).2
    let _ := P.pref v
    exact lt_asymm hcdv hdcv
  have hunion : S ∪ T = (Finset.univ : Finset V) := by
    ext v
    constructor
    · intro _hv
      exact Finset.mem_univ v
    · intro _hv
      have htr : Prefers P v c d ∨ Prefers P v d c := by
        let _ := P.pref v
        simpa [Prefers] using (lt_or_gt_of_ne hcd)
      rcases htr with hcdv | hdcv
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hcdv⟩))
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ v, hdcv⟩))
  have hsum_eq : S.card + T.card = Fintype.card V := by
    have hcard_union : (S ∪ T).card = S.card + T.card := by
      simpa using (Finset.card_union_of_disjoint (s := S) (t := T) hdisj)
    calc
      S.card + T.card = (S ∪ T).card := by symm; exact hcard_union
      _ = (Finset.univ : Finset V).card := by simp [hunion]
      _ = Fintype.card V := by simp [Finset.card_univ]
  constructor
  · intro hmaj
    have hmaj' : Fintype.card V < 2 * S.card := by
      simpa [StrictMajority] using hmaj
    have hlt'' : S.card + T.card < S.card + S.card := by
      have : S.card + T.card < 2 * S.card := by
        simpa [hsum_eq] using hmaj'
      simpa [Nat.two_mul] using this
    have hlt : T.card < S.card := Nat.lt_of_add_lt_add_left hlt''
    have hlt' : (Int.ofNat T.card) < Int.ofNat S.card :=
      Int.ofNat_lt_ofNat_of_lt hlt
    have hmargin :
        0 < Int.ofNat S.card - Int.ofNat T.card := sub_pos.mpr hlt'
    exact hmargin
  · intro hmargin
    have hlt' : (Int.ofNat T.card) < Int.ofNat S.card := by
      have : 0 < Int.ofNat S.card - Int.ofNat T.card := by
        exact hmargin
      exact (sub_pos.mp this)
    have hlt : T.card < S.card := Int.lt_of_ofNat_lt_ofNat hlt'
    have hlt'' : S.card + T.card < S.card + S.card :=
      Nat.add_lt_add_left hlt S.card
    have hmaj' : Fintype.card V < 2 * S.card := by
      have : S.card + T.card < 2 * S.card := by
        simpa [Nat.two_mul] using hlt''
      simpa [hsum_eq] using this
    simpa [StrictMajority] using hmaj'

-- Equivalence between StrictMajority and margin_pos definitions
lemma CondorcetWinner_iff_margin_pos {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) :
    CondorcetWinner P c ↔ ∀ d, c ≠ d → margin_pos P c d := by
  constructor
  · intro h d hne
    have hmaj := h d (Ne.symm hne)
    exact (strictMajority_votersPreferring_iff_margin_pos
      (P := P) (c := c) (d := d) (hcd := hne)).1 hmaj
  · intro h d hne
    have hcd : c ≠ d := by
      exact Ne.symm hne
    have hpos := h d hcd
    exact (strictMajority_votersPreferring_iff_margin_pos
      (P := P) (c := c) (d := d) (hcd := hcd)).2 hpos

lemma CondorcetLoser_iff_margin_pos {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (c : A) :
    CondorcetLoser P c ↔ (∀ d, c ≠ d → margin_pos P d c) ∧ ∃ d, d ≠ c := by
  constructor
  · intro h
    refine ⟨?_, h.2⟩
    intro d hne
    have hmaj := h.1 d (Ne.symm hne)
    exact (strictMajority_votersPreferring_iff_margin_pos
      (P := P) (c := d) (d := c) (hcd := Ne.symm hne)).1 hmaj
  · intro h
    refine ⟨?_, h.2⟩
    intro d hne
    have hpos := h.1 d (Ne.symm hne)
    exact (strictMajority_votersPreferring_iff_margin_pos
      (P := P) (c := d) (d := c) (hcd := hne)).2 hpos

lemma CondorcetLoser_restrictProfile_of_two_lt_card {V A : Type} [Fintype V] [Fintype A]
    [DecidableEq A] (P : Profile V A) {c d : A} (hdc : d ≠ c)
    (hcard : 2 < Fintype.card A) (hloser : CondorcetLoser P d) :
    CondorcetLoser (restrictProfile P c) (⟨d, hdc⟩ : {x : A // x ≠ c}) := by
  classical
  refine ⟨?_, ?_⟩
  · intro y hy
    have hy' : (y : A) ≠ d := by
      intro hEq
      apply hy
      apply Subtype.ext
      exact hEq
    have hmaj := hloser.1 (y : A) (by simpa [eq_comm] using hy')
    simpa [votersPreferring] using hmaj
  · have hsub_eq : Fintype.card {x : A // x ≠ c} = Fintype.card A - 1 :=
      card_subtype_ne_eq (α := A) c
    have hge3 : 3 ≤ Fintype.card A := Nat.succ_le_of_lt hcard
    have hge2 : 2 ≤ Fintype.card A - 1 := by
      have : 2 + 1 ≤ Fintype.card A := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hge3
      exact Nat.le_sub_of_add_le this
    have hlt : 1 < Fintype.card A - 1 :=
      Nat.lt_of_lt_of_le (by decide : 1 < 2) hge2
    have hcard_sub : 1 < Fintype.card {x : A // x ≠ c} := by
      simpa [hsub_eq] using hlt
    rcases Fintype.exists_ne_of_one_lt_card (α := {x : A // x ≠ c}) hcard_sub
      (⟨d, hdc⟩ : {x : A // x ≠ c}) with ⟨y, hy⟩
    exact ⟨y, by simpa using hy⟩

end SocialChoice
