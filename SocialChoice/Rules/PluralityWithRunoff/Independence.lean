import Mathlib.Tactic
import SocialChoice.Axioms.Independence
import SocialChoice.Margin
import SocialChoice.Rules
import SocialChoice.Rules.PluralityWithRunoff.Defs
import SocialChoice.Rules.PluralityWithRunoff.CondorcetLoser
import SocialChoice.Rules.PluralityWithRunoff.EqualsIRVForThreeCandidates
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.Independence
import SocialChoice.Rules.ScoringRules.Plurality.Independence

namespace SocialChoice

open Finset

variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]

lemma mem_pluralityWithRunoff_iff (P : Profile V A) (x : A)
    (hcard : ¬ Fintype.card A ≤ 1) :
    x ∈ pluralityWithRunoff P ↔
      ∃ y : A, ({x, y} : Finset A) ∈ pluralityWithRunoffPairs P ∧ 0 ≤ margin P x y := by
  classical
  have hinst : (inferInstance : DecidableEq A) = Classical.decEq A := by
    apply Subsingleton.elim
  cases hinst
  simp [pluralityWithRunoff, hcard]

lemma lift_plurality_restrict_eq_of_dominated
    [Nonempty V] (P : Profile V A) (c d : A) (hpref : ∀ v : V, Prefers P v c d) :
    liftWinners (plurality (restrictCandidates P (fun a => a ≠ d))) = plurality P := by
  simpa using
    (plurality_independence_of_dominated_nonempty (P := P) (c := c) (d := d) hpref)

lemma dominated_not_mem_plurality
    [Nonempty V] (P : Profile V A) (c d : A) (hpref : ∀ v : V, Prefers P v c d) :
    d ∉ plurality P := by
  classical
  have h :=
    lift_plurality_restrict_eq_of_dominated (P := P) (c := c) (d := d) hpref
  have hd' : d ∉ liftWinners (plurality (restrictCandidates P (fun a => a ≠ d))) := by
    simp [liftWinners]
  intro hd
  have : d ∈ liftWinners (plurality (restrictCandidates P (fun a => a ≠ d))) := by
    simpa [h] using hd
  exact hd' this

lemma topRank_of_topCount_zero_outside
    [Nonempty V] [Nonempty A]
    (P : Profile V A) (S : Finset A) (s : A)
    (hS : S = {s})
    (hzero : ∀ e, e ∉ S → topCount P e = 0) :
    ∀ v, TopRank P v s := by
  classical
  intro v
  let t0 : A := topChoice P v
  have ht0 : TopRank P v t0 := by
    simpa [t0] using (topChoice_topRank (P := P) (v := v))
  by_cases hts : t0 = s
  · simpa [hts] using ht0
  · exfalso
    have ht0S : t0 ∉ S := by
      intro ht0S
      have : t0 = s := by simpa [hS] using ht0S
      exact hts this
    have hle0 : topCount P t0 ≤ 0 := by
      exact le_of_eq (hzero t0 ht0S)
    have hv : v ∈ votersTop P t0 := by
      exact Finset.mem_filter.mpr ⟨by simp, ht0⟩
    have hpos : 1 ≤ topCount P t0 := by
      have : 1 ≤ (votersTop P t0).card := Finset.one_le_card.mpr ⟨v, hv⟩
      simpa [topCount] using this
    have hzero' : topCount P t0 = 0 := Nat.eq_zero_of_le_zero hle0
    have hpos' : (1 : Nat) ≤ 0 := by
      simp [hzero'] at hpos
    exact (by decide : ¬ (1 : Nat) ≤ 0) hpos'

/-! ## Core lemmas for PWR independence (placeholders) -/

-- Case 1: plurality has at least two top candidates.
lemma pwr_independence_of_dominated_ge_two
    [Nonempty V]
    (P : Profile V A) (c d : A) (hpref : ∀ v : V, Prefers P v c d)
    (hS : (plurality P).card ≥ 2) :
    liftWinners (pluralityWithRunoff (restrictCandidates P (fun a => a ≠ d))) =
      pluralityWithRunoff P := by
  classical
  have hinst : (inferInstance : DecidableEq A) = Classical.decEq A := by
    apply Subsingleton.elim
  cases hinst
  letI : Nonempty A := ⟨c⟩
  let P' := restrictCandidates P (fun a => a ≠ d)
  let S : Finset A := plurality P
  let S' : Finset {a : A // a ≠ d} := plurality P'
  have hLift : liftWinners S' = S :=
    lift_plurality_restrict_eq_of_dominated (P := P) (c := c) (d := d) hpref
  have hdS : d ∉ S :=
    dominated_not_mem_plurality (P := P) (c := c) (d := d) hpref

  -- Step 1: show S' has at least two elements.
  have hS'ge2 : S'.card ≥ 2 := by
    have h1 : 1 < S.card := lt_of_lt_of_le (by decide : 1 < 2) hS
    rcases Finset.one_lt_card.mp h1 with ⟨a, haS, b, hbS, hab⟩
    have haLift : a ∈ liftWinners S' := by
      simpa [S, hLift] using haS
    have hbLift : b ∈ liftWinners S' := by
      simpa [S, hLift] using hbS
    rcases Finset.mem_image.mp haLift with ⟨xa, hxa, hxa_val⟩
    rcases Finset.mem_image.mp hbLift with ⟨xb, hxb, hxb_val⟩
    have hneq : xa ≠ xb := by
      intro hEq
      have hval : (xa : A) = (xb : A) := by
        simpa using congrArg Subtype.val hEq
      have : a = b := by
        simpa [hxa_val, hxb_val] using hval
      exact hab this
    have h1' : 1 < S'.card := by
      refine Finset.one_lt_card.mpr ?_
      exact ⟨xa, hxa, xb, hxb, hneq⟩
    exact Nat.succ_le_iff.mp h1'

  -- Step 2: relate membership between S and S' for candidates ≠ d.
  have mem_S'_of_mem_S :
      ∀ {a : A} (ha : a ≠ d), a ∈ S → (⟨a, ha⟩ : {x : A // x ≠ d}) ∈ S' := by
    intro a ha haS
    have : a ∈ liftWinners S' := by
      simpa [hLift] using haS
    rcases Finset.mem_image.mp this with ⟨x, hx, hxa⟩
    have hx' : x = ⟨a, ha⟩ := by
      ext
      simpa using hxa
    simpa [hx'] using hx
  have mem_S_of_mem_S' :
      ∀ {a : A} (ha : a ≠ d), (⟨a, ha⟩ : {x : A // x ≠ d}) ∈ S' → a ∈ S := by
    intro a ha haS'
    have : a ∈ liftWinners S' := by
      exact Finset.mem_image.mpr ⟨⟨a, ha⟩, haS', rfl⟩
    simpa [hLift] using this

  -- Step 3: main ext proof with case split on a = d.
  apply Finset.ext
  intro a
  by_cases had : a = d
  · subst had
    have hleft : a ∉ liftWinners (pluralityWithRunoff P') := by
      intro ha
      rcases Finset.mem_image.mp ha with ⟨x, _hx, hxa⟩
      exact x.2 (by simpa using hxa)
    have hright : a ∉ pluralityWithRunoff P := by
      intro ha
      have hcardA : ¬ Fintype.card A ≤ 1 := by
        have hA_ge2 : 2 ≤ Fintype.card A := le_trans hS (Finset.card_le_univ S)
        omega
      rcases (mem_pluralityWithRunoff_iff (P := P) (x := a) hcardA).1 ha with
        ⟨y, hpair, _hmargin⟩
      have hpair' : ({a, y} : Finset A) ∈ S.powersetCard 2 := by
        simpa [pluralityWithRunoffPairs, hS, S] using hpair
      have hsubset : ({a, y} : Finset A) ⊆ S := (Finset.mem_powersetCard.mp hpair').1
      exact (hdS (hsubset (by simp))).elim
    constructor
    · intro ha
      exact (hleft ha).elim
    · intro ha
      exact (hright ha).elim
  · -- show equivalence for a ≠ d using pair correspondence and margin restriction
    have ha' : a ≠ d := had
    constructor
    · intro haL
      -- liftWinners -> winner in P'
      rcases Finset.mem_image.mp haL with ⟨x, hx, hxa⟩
      have hx' : x = ⟨a, ha'⟩ := by
        ext
        simpa using hxa
      have hxP' : (⟨a, ha'⟩ : {x : A // x ≠ d}) ∈ pluralityWithRunoff P' := by
        simpa [hx'] using hx
      have hcardA' : ¬ Fintype.card {x : A // x ≠ d} ≤ 1 := by
        have hA'_ge2 : 2 ≤ Fintype.card {x : A // x ≠ d} :=
          le_trans hS'ge2 (Finset.card_le_univ S')
        omega
      rcases
          (mem_pluralityWithRunoff_iff (P := P')
            (x := (⟨a, ha'⟩ : {x : A // x ≠ d})) hcardA').1 hxP'
        with ⟨y, hpair, hmargin⟩
      have hpair' :
          ({(⟨a, ha'⟩ : {x : A // x ≠ d}), y} :
              Finset {x : A // x ≠ d}) ∈ S'.powersetCard 2 := by
        simpa [pluralityWithRunoffPairs, hS'ge2, S', P'] using hpair
      have hsubset' :
          ({(⟨a, ha'⟩ : {x : A // x ≠ d}), y} :
              Finset {x : A // x ≠ d}) ⊆ S' :=
        (Finset.mem_powersetCard.mp hpair').1
      have haS' : (⟨a, ha'⟩ : {x : A // x ≠ d}) ∈ S' := hsubset' (by simp)
      have hyS' : y ∈ S' := hsubset' (by simp)
      have haS : a ∈ S := mem_S_of_mem_S' (a := a) (ha := ha') haS'
      have hyS : (y : A) ∈ S := mem_S_of_mem_S' (a := y) (ha := y.2) hyS'
      have hne : a ≠ (y : A) := by
        intro hEq
        have hEq' : (⟨a, ha'⟩ : {x : A // x ≠ d}) = y := by
          ext
          simpa using hEq
        have hcard' :
            ({(⟨a, ha'⟩ : {x : A // x ≠ d}), y} :
                Finset {x : A // x ≠ d}).card = 2 :=
          (Finset.mem_powersetCard.mp hpair').2
        have : (1 : Nat) = 2 := by
          simp [hEq'] at hcard'
        exact (by decide : (1 : Nat) ≠ 2) this
      have hsubset : ({a, (y : A)} : Finset A) ⊆ S := by
        intro z hz
        simp [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact haS
        · exact hyS
      have hcardpair : ({a, (y : A)} : Finset A).card = 2 := Finset.card_pair hne
      have hpairS : ({a, (y : A)} : Finset A) ∈ S.powersetCard 2 :=
        Finset.mem_powersetCard.mpr ⟨hsubset, hcardpair⟩
      have hpairP : ({a, (y : A)} : Finset A) ∈ pluralityWithRunoffPairs P := by
        simpa [pluralityWithRunoffPairs, hS, S] using hpairS
      have hmargin' :
          0 ≤ margin P a (y : A) := by
        have hmargin'' :
            margin P a (y : A) =
              margin P' (⟨a, ha'⟩ : {x : A // x ≠ d}) y := by
          simpa [P'] using
            (margin_eq_margin_restrictCandidates (P := P)
              (p := fun a => a ≠ d)
              (a := (⟨a, ha'⟩ : {x : A // x ≠ d})) (b := y))
        simpa [hmargin''] using hmargin
      have hcardA : ¬ Fintype.card A ≤ 1 := by
        have hA_ge2 : 2 ≤ Fintype.card A := le_trans hS (Finset.card_le_univ S)
        omega
      exact (mem_pluralityWithRunoff_iff (P := P) (x := a) hcardA).2
        ⟨(y : A), hpairP, hmargin'⟩
    · intro haP
      have hcardA : ¬ Fintype.card A ≤ 1 := by
        have hA_ge2 : 2 ≤ Fintype.card A := le_trans hS (Finset.card_le_univ S)
        omega
      rcases (mem_pluralityWithRunoff_iff (P := P) (x := a) hcardA).1 haP with
        ⟨y, hpair, hmargin⟩
      have hpairS : ({a, y} : Finset A) ∈ S.powersetCard 2 := by
        simpa [pluralityWithRunoffPairs, hS, S] using hpair
      have hsubset : ({a, y} : Finset A) ⊆ S := (Finset.mem_powersetCard.mp hpairS).1
      have haS : a ∈ S := hsubset (by simp)
      have hyS : y ∈ S := hsubset (by simp)
      have hyne : y ≠ d := by
        intro hEq
        subst hEq
        exact (hdS hyS).elim
      have haS' : (⟨a, ha'⟩ : {x : A // x ≠ d}) ∈ S' :=
        mem_S'_of_mem_S (a := a) (ha := ha') haS
      have hyS' : (⟨y, hyne⟩ : {x : A // x ≠ d}) ∈ S' :=
        mem_S'_of_mem_S (a := y) (ha := hyne) hyS
      have hne : a ≠ y := by
        intro hEq
        have hcard' : ({a, y} : Finset A).card = 2 :=
          (Finset.mem_powersetCard.mp hpairS).2
        have : (1 : Nat) = 2 := by
          simp [hEq] at hcard'
        exact (by decide : (1 : Nat) ≠ 2) this
      have hsubset' :
          ({(⟨a, ha'⟩ : {x : A // x ≠ d}), (⟨y, hyne⟩ : {x : A // x ≠ d})} :
              Finset {x : A // x ≠ d}) ⊆ S' := by
        intro z hz
        simp [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact haS'
        · exact hyS'
      have hcardpair' :
          ({(⟨a, ha'⟩ : {x : A // x ≠ d}), (⟨y, hyne⟩ : {x : A // x ≠ d})} :
              Finset {x : A // x ≠ d}).card = 2 := by
        have hne' :
            (⟨a, ha'⟩ : {x : A // x ≠ d}) ≠ (⟨y, hyne⟩ : {x : A // x ≠ d}) := by
          intro hEq
          have : a = y := by
            simpa using congrArg Subtype.val hEq
          exact hne this
        exact Finset.card_pair hne'
      have hpairS' :
          ({(⟨a, ha'⟩ : {x : A // x ≠ d}), (⟨y, hyne⟩ : {x : A // x ≠ d})} :
              Finset {x : A // x ≠ d}) ∈ S'.powersetCard 2 :=
        Finset.mem_powersetCard.mpr ⟨hsubset', hcardpair'⟩
      have hpair' :
          ({(⟨a, ha'⟩ : {x : A // x ≠ d}), (⟨y, hyne⟩ : {x : A // x ≠ d})} :
              Finset {x : A // x ≠ d}) ∈ pluralityWithRunoffPairs P' := by
        simpa [pluralityWithRunoffPairs, hS'ge2, S', P'] using hpairS'
      have hmargin' :
          0 ≤ margin P' (⟨a, ha'⟩ : {x : A // x ≠ d}) (⟨y, hyne⟩ : {x : A // x ≠ d}) := by
        have hmargin'' :
            margin P a y =
              margin P' (⟨a, ha'⟩ : {x : A // x ≠ d}) (⟨y, hyne⟩ : {x : A // x ≠ d}) := by
          simpa [P'] using
            (margin_eq_margin_restrictCandidates (P := P)
              (p := fun a => a ≠ d)
              (a := (⟨a, ha'⟩ : {x : A // x ≠ d}))
              (b := (⟨y, hyne⟩ : {x : A // x ≠ d})))
        simpa [hmargin''] using hmargin
      have hcardA' : ¬ Fintype.card {x : A // x ≠ d} ≤ 1 := by
        have hA'_ge2 : 2 ≤ Fintype.card {x : A // x ≠ d} :=
          le_trans hS'ge2 (Finset.card_le_univ S')
        omega
      have haP' :
          (⟨a, ha'⟩ : {x : A // x ≠ d}) ∈ pluralityWithRunoff P' := by
        exact (mem_pluralityWithRunoff_iff (P := P')
          (x := (⟨a, ha'⟩ : {x : A // x ≠ d})) hcardA').2
          ⟨⟨y, hyne⟩, hpair', hmargin'⟩
      exact Finset.mem_image.mpr ⟨⟨a, ha'⟩, haP', rfl⟩

-- Case 2: plurality has at most one top candidate.
lemma pwr_independence_of_dominated_le_one
    [Nonempty V]
    (P : Profile V A) (c d : A) (hpref : ∀ v : V, Prefers P v c d)
    (hS : (plurality P).card ≤ 1)
    (hcard2 : ¬ Fintype.card A ≤ 2) :
    liftWinners (pluralityWithRunoff (restrictCandidates P (fun a => a ≠ d))) =
      pluralityWithRunoff P := by
  classical
  have hinst : (inferInstance : DecidableEq A) = Classical.decEq A := by
    apply Subsingleton.elim
  cases hinst
  letI : Nonempty A := ⟨c⟩
  let P' := restrictCandidates P (fun a => a ≠ d)
  let S : Finset A := plurality P
  let S' : Finset {a : A // a ≠ d} := plurality P'
  have hLift : liftWinners S' = S :=
    lift_plurality_restrict_eq_of_dominated (P := P) (c := c) (d := d) hpref
  have hdS : d ∉ S :=
    dominated_not_mem_plurality (P := P) (c := c) (d := d) hpref
  have hSnonempty : S.Nonempty := plurality_nonempty (P := P)
  have hScard : S.card = 1 := Nat.le_antisymm hS (Finset.one_le_card.mpr hSnonempty)
  rcases Finset.card_eq_one.mp hScard with ⟨s, hsS⟩
  have hsS' : s ∈ S := by simp [hsS]
  have hsne : s ≠ d := by
    intro hEq
    subst hEq
    exact (hdS hsS').elim
  have hcardA' : ¬ Fintype.card {x : A // x ≠ d} ≤ 1 := by
    have hA'card : Fintype.card {x : A // x ≠ d} = Fintype.card A - 1 :=
      card_subtype_ne_eq d
    intro hle
    have hle' : Fintype.card A - 1 ≤ 1 := by
      simpa [hA'card] using hle
    have hleA : Fintype.card A ≤ 2 := by
      omega
    exact hcard2 hleA

  -- Step 1: lift s into S'
  have hsS' : (⟨s, hsne⟩ : {x : A // x ≠ d}) ∈ S' := by
    have : s ∈ liftWinners S' := by
      simpa [S, hLift] using hsS'
    rcases Finset.mem_image.mp this with ⟨x, hx, hxs⟩
    have hx' : x = ⟨s, hsne⟩ := by
      ext
      simpa using hxs
    simpa [hx'] using hx

  -- Step 2: characterize PWR winners when S is singleton.
  let T : Finset A := secondPluralitySet P S
  let T' : Finset {x : A // x ≠ d} := secondPluralitySet P' S'
  have hS'eq : S' = ({⟨s, hsne⟩} : Finset {x : A // x ≠ d}) := by
    apply Finset.ext
    intro x
    constructor
    · intro hx
      have hxLift : (x : A) ∈ liftWinners S' :=
        Finset.mem_image.mpr ⟨x, hx, rfl⟩
      have hxS : (x : A) ∈ S := by
        simpa [S, hLift] using hxLift
      have hxval : (x : A) = s := by
        simpa [hsS] using hxS
      have hx' : x = ⟨s, hsne⟩ := by
        ext
        simp [hxval]
      simp [hx']
    · intro hx
      have hx' : x = ⟨s, hsne⟩ := by
        simpa using hx
      simpa [hx'] using hsS'
  have hS'le1 : S'.card ≤ 1 := by
    simp [hS'eq]

  have mem_pwr_card_one :
      ∀ {a : A},
        a ∈ pluralityWithRunoff P ↔
          (a = s ∧ ∃ t ∈ T, 0 ≤ margin P s t) ∨
          (a ∈ T ∧ 0 ≤ margin P a s) := by
    -- unfold pluralityWithRunoffPairs in the S.card ≤ 1 branch (S = {s})
    -- any pair is {s, t} with t ∈ T
    intro a
    have hcardA : ¬ Fintype.card A ≤ 1 := by
      intro hcard
      have hforall : ∀ a b : A, a = b := (Fintype.card_le_one_iff).1 hcard
      rcases Classical.choice (inferInstance : Nonempty V) with v0
      let _ := P.pref v0
      have hcd : c ≠ d := by
        exact ne_of_lt (hpref v0)
      exact hcd (hforall c d)
    have hSge2 : ¬ S.card ≥ 2 := by
      intro hge
      have hlt : S.card < 2 := lt_of_le_of_lt hS (by decide : 1 < 2)
      exact (not_lt_of_ge hge) hlt
    constructor
    · intro ha
      rcases (mem_pluralityWithRunoff_iff (P := P) (x := a) hcardA).1 ha with
        ⟨y, hpair, hmargin⟩
      have hpair' :
          ({a, y} : Finset A) ∈
            (S.product T).image (fun p => ({p.1, p.2} : Finset A)) := by
        simpa [pluralityWithRunoffPairs, hSge2, S, T] using hpair
      rcases Finset.mem_image.mp hpair' with ⟨p, hp, hp_eq⟩
      rcases Finset.mem_product.mp hp with ⟨hpS, hpT⟩
      have hp1 : p.1 = s := by
        simpa [hsS] using hpS
      have hpair_card : ({a, y} : Finset A).card = 2 :=
        mem_pluralityWithRunoffPairs_card (P := P) (s := {a, y}) hpair
      have hne_ay : a ≠ y := by
        intro hEq
        have hcard1 : ({a, y} : Finset A).card = 1 := by
          simp [hEq]
        have : (1 : Nat) = 2 := by
          calc
            (1 : Nat) = ({a, y} : Finset A).card := by
              exact hcard1.symm
            _ = 2 := hpair_card
        exact (by decide : (1 : Nat) ≠ 2) this
      have ha_mem : a ∈ ({p.1, p.2} : Finset A) := by
        simp [hp_eq]
      have ha_cases : a = p.1 ∨ a = p.2 := by
        simp [Finset.mem_insert, Finset.mem_singleton] at ha_mem
        exact ha_mem
      cases ha_cases with
      | inl h_a_p1 =>
          left
          have h_a_s : a = s := by
            simpa [hp1] using h_a_p1
          have hy_mem : y ∈ ({p.1, p.2} : Finset A) := by
            simp [hp_eq]
          have hy_cases : y = p.1 ∨ y = p.2 := by
            simpa [Finset.mem_insert, Finset.mem_singleton] using hy_mem
          have hy_p2 : y = p.2 := by
            cases hy_cases with
            | inl hy_p1 =>
                have : y = a := by
                  simpa [h_a_p1] using hy_p1
                exact (hne_ay this.symm).elim
            | inr hy_p2 => exact hy_p2
          refine ⟨h_a_s, ?_⟩
          refine ⟨p.2, hpT, ?_⟩
          simpa [h_a_s, hy_p2] using hmargin
      | inr h_a_p2 =>
          right
          have haT : a ∈ T := by
            simpa [h_a_p2] using hpT
          have hy_mem : y ∈ ({p.1, p.2} : Finset A) := by
            simp [hp_eq]
          have hy_cases : y = p.1 ∨ y = p.2 := by
            simpa [Finset.mem_insert, Finset.mem_singleton] using hy_mem
          have hy_p1 : y = p.1 := by
            cases hy_cases with
            | inl hy_p1 => exact hy_p1
            | inr hy_p2 =>
                have : y = a := by
                  simpa [h_a_p2] using hy_p2
                exact (hne_ay this.symm).elim
          have hmargin' : 0 ≤ margin P a s := by
            simpa [hy_p1, hp1] using hmargin
          exact ⟨haT, hmargin'⟩
    · intro ha
      rcases ha with ⟨h_as, ⟨t, htT, hmargin⟩⟩ | ⟨haT, hmargin⟩
      · have hpair' :
            ({s, t} : Finset A) ∈
              (S.product T).image (fun p => ({p.1, p.2} : Finset A)) := by
          refine Finset.mem_image.mpr ?_
          refine ⟨(s, t), ?_, rfl⟩
          refine Finset.mem_product.mpr ?_
          have hsS' : s ∈ S := by
            simp [hsS]
          exact ⟨hsS', htT⟩
        have hpair : ({s, t} : Finset A) ∈ pluralityWithRunoffPairs P := by
          simpa [pluralityWithRunoffPairs, hSge2, S, T] using hpair'
        have ha' :
            ∃ y : A, ({a, y} : Finset A) ∈ pluralityWithRunoffPairs P ∧
              0 ≤ margin P a y := by
          refine ⟨t, ?_, ?_⟩
          · simpa [h_as] using hpair
          · simpa [h_as] using hmargin
        exact (mem_pluralityWithRunoff_iff (P := P) (x := a) hcardA).2 ha'
      · have hpair' :
            ({s, a} : Finset A) ∈
              (S.product T).image (fun p => ({p.1, p.2} : Finset A)) := by
          refine Finset.mem_image.mpr ?_
          refine ⟨(s, a), ?_, rfl⟩
          refine Finset.mem_product.mpr ?_
          have hsS' : s ∈ S := by
            simp [hsS]
          exact ⟨hsS', haT⟩
        have hpair_sa : ({s, a} : Finset A) ∈ pluralityWithRunoffPairs P := by
          simpa [pluralityWithRunoffPairs, hSge2, S, T] using hpair'
        have hpair : ({a, s} : Finset A) ∈ pluralityWithRunoffPairs P := by
          simpa [Finset.pair_comm] using hpair_sa
        have ha' :
            ∃ y : A, ({a, y} : Finset A) ∈ pluralityWithRunoffPairs P ∧
              0 ≤ margin P a y := by
          refine ⟨s, hpair, ?_⟩
          exact hmargin
        exact (mem_pluralityWithRunoff_iff (P := P) (x := a) hcardA).2 ha'

  have mem_pwr_card_one' :
      ∀ {a : A} (ha : a ≠ d),
        (⟨a, ha⟩ : {x : A // x ≠ d}) ∈ pluralityWithRunoff P' ↔
          (a = s ∧ ∃ t ∈ T', 0 ≤ margin P' (⟨s, hsne⟩ : {x : A // x ≠ d}) t) ∨
          ((⟨a, ha⟩ : {x : A // x ≠ d}) ∈ T' ∧
            0 ≤ margin P' (⟨a, ha⟩ : {x : A // x ≠ d}) (⟨s, hsne⟩ : {x : A // x ≠ d})) := by
    -- same characterization for P' in the nontrivial agenda case
    intro a ha
    have hS'ge2 : ¬ S'.card ≥ 2 := by
      intro hge
      have hlt : S'.card < 2 := lt_of_le_of_lt hS'le1 (by decide : 1 < 2)
      exact (not_lt_of_ge hge) hlt
    constructor
    · intro haP'
      rcases (mem_pluralityWithRunoff_iff (P := P')
        (x := (⟨a, ha⟩ : {x : A // x ≠ d})) hcardA').1 haP' with
        ⟨y, hpair, hmargin⟩
      have hpair' :
          ({(⟨a, ha⟩ : {x : A // x ≠ d}), y} : Finset {x : A // x ≠ d}) ∈
            (S'.product T').image (fun p => ({p.1, p.2} : Finset {x : A // x ≠ d})) := by
        simpa [pluralityWithRunoffPairs, hS'ge2, S', T'] using hpair
      rcases Finset.mem_image.mp hpair' with ⟨p, hp, hp_eq⟩
      rcases Finset.mem_product.mp hp with ⟨hpS, hpT⟩
      have hp1 : p.1 = (⟨s, hsne⟩ : {x : A // x ≠ d}) := by
        have : p.1 ∈ S' := hpS
        simpa [hS'eq] using this
      have hpair_card :
          ({(⟨a, ha⟩ : {x : A // x ≠ d}), y} : Finset {x : A // x ≠ d}).card = 2 :=
        mem_pluralityWithRunoffPairs_card (P := P') (s := {⟨a, ha⟩, y}) hpair
      have hne_ay : (⟨a, ha⟩ : {x : A // x ≠ d}) ≠ y := by
        intro hEq
        have hcard1 :
            ({(⟨a, ha⟩ : {x : A // x ≠ d}), y} :
              Finset {x : A // x ≠ d}).card = 1 := by
          simp [hEq]
        have : (1 : Nat) = 2 := by
          calc
            (1 : Nat) =
                ({(⟨a, ha⟩ : {x : A // x ≠ d}), y} :
                  Finset {x : A // x ≠ d}).card := by
                  exact hcard1.symm
            _ = 2 := hpair_card
        exact (by decide : (1 : Nat) ≠ 2) this
      have ha_mem :
          (⟨a, ha⟩ : {x : A // x ≠ d}) ∈ ({p.1, p.2} : Finset {x : A // x ≠ d}) := by
        simp [hp_eq]
      have ha_cases :
          (⟨a, ha⟩ : {x : A // x ≠ d}) = p.1 ∨
            (⟨a, ha⟩ : {x : A // x ≠ d}) = p.2 := by
        simp [Finset.mem_insert, Finset.mem_singleton] at ha_mem
        exact ha_mem
      cases ha_cases with
      | inl h_a_p1 =>
          left
          have h_a_s' :
              (⟨a, ha⟩ : {x : A // x ≠ d}) = (⟨s, hsne⟩ : {x : A // x ≠ d}) := by
            simpa [hp1] using h_a_p1
          have h_a_s : a = s := by
            exact congrArg Subtype.val h_a_s'
          have hy_mem : y ∈ ({p.1, p.2} : Finset {x : A // x ≠ d}) := by
            simp [hp_eq]
          have hy_cases : y = p.1 ∨ y = p.2 := by
            simpa [Finset.mem_insert, Finset.mem_singleton] using hy_mem
          have hy_p2 : y = p.2 := by
            cases hy_cases with
            | inl hy_p1 =>
                have : y = (⟨a, ha⟩ : {x : A // x ≠ d}) := by
                  simpa [h_a_p1] using hy_p1
                exact (hne_ay this.symm).elim
            | inr hy_p2 => exact hy_p2
          refine ⟨h_a_s, ?_⟩
          refine ⟨p.2, hpT, ?_⟩
          simpa [h_a_s', hy_p2] using hmargin
      | inr h_a_p2 =>
          right
          have haT : (⟨a, ha⟩ : {x : A // x ≠ d}) ∈ T' := by
            simpa [h_a_p2] using hpT
          have hy_mem : y ∈ ({p.1, p.2} : Finset {x : A // x ≠ d}) := by
            simp [hp_eq]
          have hy_cases : y = p.1 ∨ y = p.2 := by
            simpa [Finset.mem_insert, Finset.mem_singleton] using hy_mem
          have hy_p1 : y = p.1 := by
            cases hy_cases with
            | inl hy_p1 => exact hy_p1
            | inr hy_p2 =>
                have : y = (⟨a, ha⟩ : {x : A // x ≠ d}) := by
                  simpa [h_a_p2] using hy_p2
                exact (hne_ay this.symm).elim
          have hmargin' :
              0 ≤ margin P' (⟨a, ha⟩ : {x : A // x ≠ d})
                (⟨s, hsne⟩ : {x : A // x ≠ d}) := by
            simpa [hy_p1, hp1] using hmargin
          exact ⟨haT, hmargin'⟩
    · intro haP'
      rcases haP' with ⟨h_as, ⟨t, htT, hmargin⟩⟩ | ⟨haT, hmargin⟩
      · have hpair' :
            ({(⟨s, hsne⟩ : {x : A // x ≠ d}), t} : Finset {x : A // x ≠ d}) ∈
              (S'.product T').image (fun p => ({p.1, p.2} : Finset {x : A // x ≠ d})) := by
          refine Finset.mem_image.mpr ?_
          refine ⟨(⟨s, hsne⟩, t), ?_, rfl⟩
          refine Finset.mem_product.mpr ?_
          have hsS'' : (⟨s, hsne⟩ : {x : A // x ≠ d}) ∈ S' := by
            simp [hS'eq]
          exact ⟨hsS'', htT⟩
        have hpair :
            ({(⟨s, hsne⟩ : {x : A // x ≠ d}), t} : Finset {x : A // x ≠ d}) ∈
              pluralityWithRunoffPairs P' := by
          simpa [pluralityWithRunoffPairs, hS'ge2, S', T'] using hpair'
        have ha' :
            ∃ y : {x : A // x ≠ d},
              ({(⟨a, ha⟩ : {x : A // x ≠ d}), y} : Finset {x : A // x ≠ d}) ∈
                pluralityWithRunoffPairs P' ∧
                0 ≤ margin P' (⟨a, ha⟩ : {x : A // x ≠ d}) y := by
          refine ⟨t, ?_, ?_⟩
          · simpa [h_as] using hpair
          · simpa [h_as] using hmargin
        exact (mem_pluralityWithRunoff_iff (P := P')
          (x := (⟨a, ha⟩ : {x : A // x ≠ d})) hcardA').2 ha'
      · have hpair' :
            ({(⟨s, hsne⟩ : {x : A // x ≠ d}), (⟨a, ha⟩ : {x : A // x ≠ d})} :
              Finset {x : A // x ≠ d}) ∈
              (S'.product T').image (fun p => ({p.1, p.2} : Finset {x : A // x ≠ d})) := by
          refine Finset.mem_image.mpr ?_
          refine ⟨(⟨s, hsne⟩, (⟨a, ha⟩ : {x : A // x ≠ d})), ?_, rfl⟩
          refine Finset.mem_product.mpr ?_
          have hsS'' : (⟨s, hsne⟩ : {x : A // x ≠ d}) ∈ S' := by
            simp [hS'eq]
          exact ⟨hsS'', haT⟩
        have hpair_sa :
            ({(⟨s, hsne⟩ : {x : A // x ≠ d}), (⟨a, ha⟩ : {x : A // x ≠ d})} :
              Finset {x : A // x ≠ d}) ∈
              pluralityWithRunoffPairs P' := by
          simpa [pluralityWithRunoffPairs, hS'ge2, S', T'] using hpair'
        have hpair :
            ({(⟨a, ha⟩ : {x : A // x ≠ d}), (⟨s, hsne⟩ : {x : A // x ≠ d})} :
              Finset {x : A // x ≠ d}) ∈
              pluralityWithRunoffPairs P' := by
          simpa [Finset.pair_comm] using hpair_sa
        have ha' :
            ∃ y : {x : A // x ≠ d},
              ({(⟨a, ha⟩ : {x : A // x ≠ d}), y} :
                Finset {x : A // x ≠ d}) ∈
                pluralityWithRunoffPairs P' ∧
                0 ≤ margin P' (⟨a, ha⟩ : {x : A // x ≠ d}) y := by
          refine ⟨(⟨s, hsne⟩ : {x : A // x ≠ d}), hpair, ?_⟩
          exact hmargin
        exact (mem_pluralityWithRunoff_iff (P := P')
          (x := (⟨a, ha⟩ : {x : A // x ≠ d})) hcardA').2 ha'

  -- Step 3: relate T and T' via topCount invariance (d is never top).
  have topCount_d_zero : topCount P d = 0 :=
    topCount_eq_zero_of_dominated (P := P) (c := c) (d := d) hpref
  have hnot_top_d : ∀ v, ¬ TopRank P v d :=
    no_top_of_topCount_zero (P := P) (d := d) topCount_d_zero

  have mem_T_iff :
      ∀ {a : A} (ha : a ≠ d),
        a ∈ T ↔ (⟨a, ha⟩ : {x : A // x ≠ d}) ∈ T' := by
    -- use topCount_restrictProfile_eq with hnot_top_d to show secondPluralitySet preserved
    intro a ha
    classical
    let R : Finset A := Finset.univ.filter (fun c => c ∉ S)
    let R' : Finset {x : A // x ≠ d} := Finset.univ.filter (fun c => c ∉ S')
    have hR : R.Nonempty := by
      refine ⟨d, ?_⟩
      exact Finset.mem_filter.mpr ⟨by simp, hdS⟩
    have hcardA'_ge2 : 2 ≤ Fintype.card {x : A // x ≠ d} := by
      have h1 : 1 < Fintype.card {x : A // x ≠ d} := lt_of_not_ge hcardA'
      exact Nat.succ_le_iff.mp h1
    have hcard_univ :
        2 ≤ (Finset.univ : Finset {x : A // x ≠ d}).card := by
      simpa [Finset.card_univ] using hcardA'_ge2
    have hcard_univ' :
        1 < (Finset.univ : Finset {x : A // x ≠ d}).card := by
      exact lt_of_lt_of_le (by decide : 1 < 2) hcard_univ
    have hR' : R'.Nonempty := by
      rcases
          Finset.exists_mem_ne (s := (Finset.univ : Finset {x : A // x ≠ d}))
            hcard_univ' (⟨s, hsne⟩ : {x : A // x ≠ d}) with
        ⟨t, ht, hts⟩
      have htS' : t ∉ S' := by
        simp [hS'eq, hts]
      exact ⟨t, Finset.mem_filter.mpr ⟨ht, htS'⟩⟩
    have hS_iff :
        a ∈ S ↔ (⟨a, ha⟩ : {x : A // x ≠ d}) ∈ S' := by
      constructor
      · intro haS
        have ha_eq : a = s := by
          simpa [hsS] using haS
        subst ha_eq
        simp [hS'eq]
      · intro haS'
        have haLift : a ∈ liftWinners S' := by
          exact Finset.mem_image.mpr ⟨⟨a, ha⟩, haS', rfl⟩
        simpa [S, hLift] using haLift
    have hR_iff :
        a ∈ R ↔ (⟨a, ha⟩ : {x : A // x ≠ d}) ∈ R' := by
      simp [R, R', hS_iff]
    have hR_iff' :
        ∀ {b : A} (hb : b ≠ d),
          b ∈ R ↔ (⟨b, hb⟩ : {x : A // x ≠ d}) ∈ R' := by
      intro b hb
      have hS_iff' :
          b ∈ S ↔ (⟨b, hb⟩ : {x : A // x ≠ d}) ∈ S' := by
        constructor
        · intro hbS
          have hb_eq : b = s := by
            simpa [hsS] using hbS
          subst hb_eq
          simp [hS'eq]
        · intro hbS'
          have hbLift : b ∈ liftWinners S' := by
            exact Finset.mem_image.mpr ⟨⟨b, hb⟩, hbS', rfl⟩
          simpa [S, hLift] using hbLift
      simp [R, R', hS_iff']
    have hcount_eq :
        ∀ {b : A} (hb : b ≠ d),
          topCount P b = topCount P' (⟨b, hb⟩ : {x : A // x ≠ d}) := by
      intro b hb
      change topCount P b = topCount (restrictProfile P d) (⟨b, hb⟩ : {x : A // x ≠ d})
      exact (topCount_restrictProfile_eq (P := P) (d := d) hnot_top_d b hb).symm
    constructor
    · intro haT
      have haT' := (mem_secondPluralitySet_iff_forall_le (P := P) (S := S) hR).1 haT
      refine (mem_secondPluralitySet_iff_forall_le (P := P') (S := S') hR').2 ?_
      refine ⟨(hR_iff).1 haT'.1, ?_⟩
      intro e' he'
      have heR : (e' : A) ∈ R := (hR_iff' (hb := e'.property)).2 he'
      have hle : topCount P (e' : A) ≤ topCount P a := haT'.2 _ heR
      have hcount_e :
          topCount P (e' : A) = topCount P' e' := hcount_eq (hb := e'.property)
      have hcount_a :
          topCount P a = topCount P' (⟨a, ha⟩ : {x : A // x ≠ d}) := hcount_eq (hb := ha)
      simpa [hcount_e, hcount_a] using hle
    · intro haT
      have haT' :=
        (mem_secondPluralitySet_iff_forall_le (P := P') (S := S') hR').1 haT
      refine (mem_secondPluralitySet_iff_forall_le (P := P) (S := S) hR).2 ?_
      refine ⟨(hR_iff).2 haT'.1, ?_⟩
      intro e he
      by_cases heq : e = d
      · subst e
        calc
          topCount P d = 0 := topCount_d_zero
          _ ≤ topCount P a := Nat.zero_le _
      · have heR' : (⟨e, heq⟩ : {x : A // x ≠ d}) ∈ R' :=
          (hR_iff' (hb := heq)).1 he
        have hle :
            topCount P' (⟨e, heq⟩ : {x : A // x ≠ d}) ≤
              topCount P' (⟨a, ha⟩ : {x : A // x ≠ d}) := haT'.2 _ heR'
        have hcount_e :
            topCount P e = topCount P' (⟨e, heq⟩ : {x : A // x ≠ d}) :=
          hcount_eq (hb := heq)
        have hcount_a :
            topCount P a = topCount P' (⟨a, ha⟩ : {x : A // x ≠ d}) := hcount_eq (hb := ha)
        simpa [hcount_e, hcount_a] using hle

  -- Step 4: margins preserved under restriction
  have margin_eq :
      ∀ {a : A} (ha : a ≠ d),
        margin P a s =
          margin P' (⟨a, ha⟩ : {x : A // x ≠ d}) (⟨s, hsne⟩ : {x : A // x ≠ d}) := by
    intro a ha
    simpa [P'] using
      (margin_eq_margin_restrictCandidates (P := P)
        (p := fun a => a ≠ d)
        (a := (⟨a, ha⟩ : {x : A // x ≠ d}))
        (b := (⟨s, hsne⟩ : {x : A // x ≠ d})))

  -- Step 5: finish by ext using the characterizations and mem_T_iff.
  -- This is a straightforward (but lengthy) case analysis on a = d and the two disjuncts in
  -- mem_pwr_card_one / mem_pwr_card_one', transferring membership in T via mem_T_iff and
  -- margins via margin_eq.
  letI : Fintype {x : A // x ≠ d} := Subtype.fintype (fun a => a ≠ d)
  have left_disjunct_iff :
      ∀ {a : A} (ha : a ≠ d),
        (a = s ∧ ∃ t ∈ T', 0 ≤ margin P' (⟨s, hsne⟩ : {x : A // x ≠ d}) t) ↔
          (a = s ∧ ∃ t ∈ T, 0 ≤ margin P s t) := by
    intro a ha
    constructor
    · intro h
      rcases h with ⟨h_as, ⟨t, htT', hmargin⟩⟩
      refine ⟨h_as, ?_⟩
      refine ⟨t.1, ?_, ?_⟩
      · have htT : t.1 ∈ T := (mem_T_iff (ha := t.2)).2 htT'
        simpa using htT
      · have hskew' :
            margin P' t (⟨s, hsne⟩ : {x : A // x ≠ d}) =
              - margin P' (⟨s, hsne⟩ : {x : A // x ≠ d}) t := by
          simpa [skew_symmetric] using
            (margin_antisymmetric (P := P') t (⟨s, hsne⟩ : {x : A // x ≠ d}))
        have hle' :
            margin P' t (⟨s, hsne⟩ : {x : A // x ≠ d}) ≤ 0 := by
          have : - margin P' (⟨s, hsne⟩ : {x : A // x ≠ d}) t ≤ 0 :=
            neg_nonpos.mpr hmargin
          simpa [hskew'] using this
        have hcount :
            margin P t.1 s =
              margin P' (⟨t.1, t.2⟩ : {x : A // x ≠ d})
                (⟨s, hsne⟩ : {x : A // x ≠ d}) := by
          simpa using (margin_eq (a := t.1) (ha := t.2))
        have hle'' : margin P t.1 s ≤ 0 := by
          simpa [hcount] using hle'
        have hskewP : margin P s t.1 = - margin P t.1 s := by
          simpa [skew_symmetric] using (margin_antisymmetric (P := P) s t.1)
        have : 0 ≤ - margin P t.1 s := neg_nonneg.mpr hle''
        simpa [hskewP] using this
    · intro h
      rcases h with ⟨h_as, ⟨t, htT, hmargin⟩⟩
      by_cases htd : t = d
      · subst t
        -- choose a different candidate r ∈ T with r ≠ d
        let R : Finset A := Finset.univ.filter (fun c => c ∉ S)
        have hR : R.Nonempty := by
          refine ⟨d, ?_⟩
          exact Finset.mem_filter.mpr ⟨by simp, hdS⟩
        have hdT' :=
          (mem_secondPluralitySet_iff_forall_le (P := P) (S := S) hR).1 htT
        have hR_eq : R = (Finset.univ.erase s) := by
          ext x
          simp [R, S, hsS]
        have hRcard :
            R.card = (Finset.univ : Finset A).card - 1 := by
          have hs_univ : s ∈ (Finset.univ : Finset A) := by simp
          have hcard :
              (Finset.univ.erase s).card = (Finset.univ : Finset A).card - 1 :=
            Finset.card_erase_of_mem (s := (Finset.univ : Finset A)) (a := s) hs_univ
          calc
            R.card = (Finset.univ.erase s).card := by simp [hR_eq]
            _ = (Finset.univ : Finset A).card - 1 := hcard
        have hRcard_gt : 1 < R.card := by
          have hcardA : 2 < Fintype.card A := lt_of_not_ge hcard2
          have hRcard' : R.card = Fintype.card A - 1 := by
            calc
              R.card = (Finset.univ : Finset A).card - 1 := hRcard
              _ = Fintype.card A - 1 := by simp [Finset.card_univ]
          omega
        rcases Finset.exists_mem_ne (s := R) hRcard_gt d with ⟨r, hrR, hrd⟩
        have hrS : r ≠ s := by
          have : r ∉ S := (Finset.mem_filter.mp hrR).2
          simpa [hsS] using this
        have htop_le0 : ∀ e ∈ R, topCount P e ≤ 0 := by
          intro e he
          have hle : topCount P e ≤ topCount P d := hdT'.2 _ he
          simpa [topCount_d_zero] using hle
        have htop_r : topCount P r = 0 := Nat.eq_zero_of_le_zero (htop_le0 r hrR)
        have htop_le' : ∀ e ∈ R, topCount P e ≤ topCount P r := by
          intro e he
          simpa [htop_r] using htop_le0 e he
        have hrT : r ∈ T :=
          (mem_secondPluralitySet_iff_forall_le (P := P) (S := S) hR).2 ⟨hrR, htop_le'⟩
        have hzero_outside : ∀ e, e ∉ S → topCount P e = 0 := by
          intro e heS
          have heR : e ∈ R := Finset.mem_filter.mpr ⟨by simp, heS⟩
          exact Nat.eq_zero_of_le_zero (htop_le0 e heR)
        have htop_all : ∀ v, TopRank P v s :=
          topRank_of_topCount_zero_outside (P := P) (S := S) (s := s) hsS hzero_outside
        have hall : ∀ v, Prefers P v s r := by
          intro v
          exact (htop_all v) r hrS
        have hmargin_pos : 0 < margin P s r :=
          unanimous_margin (P := P) s r hall
        have hmargin_nonneg : 0 ≤ margin P s r := le_of_lt hmargin_pos
        have hrT' : (⟨r, hrd⟩ : {x : A // x ≠ d}) ∈ T' :=
          (mem_T_iff (ha := hrd)).1 hrT
        -- transfer margin to P'
        have hskewP : margin P r s = - margin P s r := by
          simpa [skew_symmetric] using (margin_antisymmetric (P := P) r s)
        have hle' : margin P r s ≤ 0 := by
          have : - margin P s r ≤ 0 := neg_nonpos.mpr hmargin_nonneg
          simpa [hskewP] using this
        have hcount :
            margin P r s =
              margin P' (⟨r, hrd⟩ : {x : A // x ≠ d})
                (⟨s, hsne⟩ : {x : A // x ≠ d}) := by
          simpa using (margin_eq (a := r) (ha := hrd))
        have hle'' :
            margin P' (⟨r, hrd⟩ : {x : A // x ≠ d})
              (⟨s, hsne⟩ : {x : A // x ≠ d}) ≤ 0 := by
          simpa [hcount] using hle'
        have hskew' :
            margin P' (⟨s, hsne⟩ : {x : A // x ≠ d})
              (⟨r, hrd⟩ : {x : A // x ≠ d}) =
                - margin P' (⟨r, hrd⟩ : {x : A // x ≠ d})
                    (⟨s, hsne⟩ : {x : A // x ≠ d}) := by
          simpa [skew_symmetric] using
            (margin_antisymmetric (P := P')
              (⟨s, hsne⟩ : {x : A // x ≠ d})
              (⟨r, hrd⟩ : {x : A // x ≠ d}))
        have hmargin' :
            0 ≤ margin P' (⟨s, hsne⟩ : {x : A // x ≠ d})
              (⟨r, hrd⟩ : {x : A // x ≠ d}) := by
          have : 0 ≤
              - margin P' (⟨r, hrd⟩ : {x : A // x ≠ d})
                  (⟨s, hsne⟩ : {x : A // x ≠ d}) := neg_nonneg.mpr hle''
          simpa [hskew'] using this
        exact ⟨h_as, ⟨⟨r, hrd⟩, hrT', hmargin'⟩⟩
      · have htT' : (⟨t, htd⟩ : {x : A // x ≠ d}) ∈ T' :=
          (mem_T_iff (ha := htd)).1 htT
        have hskewP : margin P t s = - margin P s t := by
          simpa [skew_symmetric] using (margin_antisymmetric (P := P) t s)
        have hle' : margin P t s ≤ 0 := by
          have : - margin P s t ≤ 0 := neg_nonpos.mpr hmargin
          simpa [hskewP] using this
        have hcount :
            margin P t s =
              margin P' (⟨t, htd⟩ : {x : A // x ≠ d})
                (⟨s, hsne⟩ : {x : A // x ≠ d}) := by
          simpa using (margin_eq (a := t) (ha := htd))
        have hle'' :
            margin P' (⟨t, htd⟩ : {x : A // x ≠ d})
              (⟨s, hsne⟩ : {x : A // x ≠ d}) ≤ 0 := by
          simpa [hcount] using hle'
        have hskew' :
            margin P' (⟨s, hsne⟩ : {x : A // x ≠ d})
              (⟨t, htd⟩ : {x : A // x ≠ d}) =
                - margin P' (⟨t, htd⟩ : {x : A // x ≠ d})
                    (⟨s, hsne⟩ : {x : A // x ≠ d}) := by
          simpa [skew_symmetric] using
            (margin_antisymmetric (P := P')
              (⟨s, hsne⟩ : {x : A // x ≠ d})
              (⟨t, htd⟩ : {x : A // x ≠ d}))
        have hmargin' :
            0 ≤ margin P' (⟨s, hsne⟩ : {x : A // x ≠ d})
              (⟨t, htd⟩ : {x : A // x ≠ d}) := by
          have : 0 ≤
              - margin P' (⟨t, htd⟩ : {x : A // x ≠ d})
                  (⟨s, hsne⟩ : {x : A // x ≠ d}) := neg_nonneg.mpr hle''
          simpa [hskew'] using this
        exact ⟨h_as, ⟨⟨t, htd⟩, htT', hmargin'⟩⟩
  have right_disjunct_iff :
      ∀ {a : A} (ha : a ≠ d),
        ((⟨a, ha⟩ : {x : A // x ≠ d}) ∈ T' ∧
            0 ≤ margin P' (⟨a, ha⟩ : {x : A // x ≠ d}) (⟨s, hsne⟩ : {x : A // x ≠ d})) ↔
          (a ∈ T ∧ 0 ≤ margin P a s) := by
    intro a ha
    constructor
    · intro h
      rcases h with ⟨haT', hmargin⟩
      have haT : a ∈ T := (mem_T_iff (ha := ha)).2 haT'
      have hmargin' : 0 ≤ margin P a s := by
        simpa [margin_eq (ha := ha)] using hmargin
      exact ⟨haT, hmargin'⟩
    · intro h
      rcases h with ⟨haT, hmargin⟩
      have haT' : (⟨a, ha⟩ : {x : A // x ≠ d}) ∈ T' := (mem_T_iff (ha := ha)).1 haT
      have hmargin' :
          0 ≤ margin P' (⟨a, ha⟩ : {x : A // x ≠ d}) (⟨s, hsne⟩ : {x : A // x ≠ d}) := by
        simpa [margin_eq (ha := ha)] using hmargin
      exact ⟨haT', hmargin'⟩
  have d_not_mem : d ∉ pluralityWithRunoff P := by
    intro hd
    have hdisj := (mem_pwr_card_one (a := d)).1 hd
    cases hdisj with
    | inl hleft =>
        rcases hleft with ⟨hds, _⟩
        exact (hsne hds.symm).elim
    | inr hright =>
        rcases hright with ⟨hdT, hmargin⟩
        let R : Finset A := Finset.univ.filter (fun c => c ∉ S)
        have hR : R.Nonempty := by
          refine ⟨d, ?_⟩
          exact Finset.mem_filter.mpr ⟨by simp, hdS⟩
        have hdT' :=
          (mem_secondPluralitySet_iff_forall_le (P := P) (S := S) hR).1 hdT
        have htop_le0 : ∀ e ∈ R, topCount P e ≤ 0 := by
          intro e he
          have hle : topCount P e ≤ topCount P d := hdT'.2 _ he
          simpa [topCount_d_zero] using hle
        have hzero_outside : ∀ e, e ∉ S → topCount P e = 0 := by
          intro e heS
          have heR : e ∈ R := Finset.mem_filter.mpr ⟨by simp, heS⟩
          exact Nat.eq_zero_of_le_zero (htop_le0 e heR)
        have htop_all : ∀ v, TopRank P v s :=
          topRank_of_topCount_zero_outside (P := P) (S := S) (s := s) hsS hzero_outside
        have hall : ∀ v, Prefers P v s d := by
          intro v
          exact (htop_all v) d (Ne.symm hsne)
        have hmargin_pos : 0 < margin P s d :=
          unanimous_margin (P := P) s d hall
        have hskew : margin P d s = - margin P s d := by
          simpa [skew_symmetric] using (margin_antisymmetric (P := P)) d s
        have hneg : margin P d s < 0 := by
          nlinarith [hmargin_pos, hskew]
        exact (not_le_of_gt hneg) hmargin
  apply Finset.ext
  intro a
  by_cases ha : a = d
  · subst a
    constructor
    · intro hmem
      have hnot :
          d ∉ liftWinners (pluralityWithRunoff (restrictCandidates P (fun a => a ≠ d))) := by
            intro hd
            rcases Finset.mem_image.mp hd with ⟨x, _hx, hxd⟩
            have : (x : A) = d := by
              simpa using hxd
            exact x.property (by simp [this])
      exact (hnot hmem).elim
    · intro hmem
      exact (d_not_mem hmem).elim
  · have hmem_lift :
        a ∈ liftWinners (pluralityWithRunoff (restrictCandidates P (fun a => a ≠ d))) ↔
          (⟨a, ha⟩ : {x : A // x ≠ d}) ∈ pluralityWithRunoff P' := by
        classical
        simp [P', liftWinners, Finset.mem_image, ha]
    constructor
    · intro hmem
      have hmem' : (⟨a, ha⟩ : {x : A // x ≠ d}) ∈ pluralityWithRunoff P' :=
        (hmem_lift).1 hmem
      have hdisj := (mem_pwr_card_one' (a := a) ha).1 hmem'
      cases hdisj with
      | inl hleft =>
          have hleft' := (left_disjunct_iff (ha := ha)).1 hleft
          exact (mem_pwr_card_one (a := a)).2 (Or.inl hleft')
      | inr hright =>
          have hright' := (right_disjunct_iff (ha := ha)).1 hright
          exact (mem_pwr_card_one (a := a)).2 (Or.inr hright')
    · intro hmem
      have hdisj := (mem_pwr_card_one (a := a)).1 hmem
      cases hdisj with
      | inl hleft =>
          have hleft' := (left_disjunct_iff (ha := ha)).2 hleft
          have hmem' :
              (⟨a, ha⟩ : {x : A // x ≠ d}) ∈ pluralityWithRunoff P' :=
            (mem_pwr_card_one' (a := a) ha).2 (Or.inl hleft')
          exact (hmem_lift).2 hmem'
      | inr hright =>
          have hright' := (right_disjunct_iff (ha := ha)).2 hright
          have hmem' :
              (⟨a, ha⟩ : {x : A // x ≠ d}) ∈ pluralityWithRunoff P' :=
            (mem_pwr_card_one' (a := a) ha).2 (Or.inr hright')
          exact (hmem_lift).2 hmem'

lemma pwr_independence_of_dominated_card_le_two
    [Nonempty V]
    (P : Profile V A) (c d : A) (hpref : ∀ v : V, Prefers P v c d)
    (hcard : Fintype.card A ≤ 2) :
    liftWinners (pluralityWithRunoff (restrictCandidates P (fun a => a ≠ d))) =
      pluralityWithRunoff P := by
  classical
  have hIRV :
      liftWinners (instantRunoffVoting (restrictCandidates P (fun a => a ≠ d))) =
        instantRunoffVoting P := by
    simpa using
      (instantRunoffVoting_independenceOfDominated (P := P) (c := c) (d := d) hpref)
  let P' := restrictCandidates P (fun a => a ≠ d)
  letI : Fintype {x : A // x ≠ d} := Subtype.fintype (fun a => a ≠ d)
  have hcard' : Fintype.card {x : A // x ≠ d} ≤ 2 := by
    have hle : Fintype.card {x : A // x ≠ d} ≤ Fintype.card A :=
      Fintype.card_subtype_le (p := fun a => a ≠ d)
    exact le_trans hle hcard
  have hEqP' :
      instantRunoffVoting P' = pluralityWithRunoff P' :=
    instantRunoffVoting_eq_pluralityWithRunoff_of_card_le_two (P := P') hcard'
  have hEqP :
      instantRunoffVoting P = pluralityWithRunoff P :=
    instantRunoffVoting_eq_pluralityWithRunoff_of_card_le_two (P := P) hcard
  calc
    liftWinners (pluralityWithRunoff P') =
        liftWinners (instantRunoffVoting P') := by
          simp [hEqP'.symm]
    _ = instantRunoffVoting P := hIRV
    _ = pluralityWithRunoff P := by
          simp [hEqP]

theorem pluralityWithRunoff_independenceOfDominated :
    IndependenceOfDominated pluralityWithRunoff := by
  intro V A _ _ _ _ P c d hpref
  classical
  by_cases hcard : Fintype.card A ≤ 1
  · -- This case contradicts domination (no distinct candidates).
    rcases Classical.choice (inferInstance : Nonempty V) with v0
    let _ := P.pref v0
    have hcd : c ≠ d := by
      intro hEq
      subst hEq
      exact (lt_irrefl _ (hpref v0))
    have hforall : ∀ a b : A, a = b := (Fintype.card_le_one_iff).1 hcard
    exact (hcd (hforall c d)).elim
  · by_cases hcard2 : Fintype.card A ≤ 2
    · exact pwr_independence_of_dominated_card_le_two (P := P) (c := c) (d := d) hpref hcard2
    · by_cases hS : (plurality P).card ≥ 2
      · exact pwr_independence_of_dominated_ge_two (P := P) (c := c) (d := d) hpref hS
      · have hS' : (plurality P).card ≤ 1 := by
          have hlt : (plurality P).card < 2 := lt_of_not_ge hS
          exact Nat.lt_succ_iff.mp hlt
        exact pwr_independence_of_dominated_le_one (P := P) (c := c) (d := d) hpref hS' hcard2

end SocialChoice
