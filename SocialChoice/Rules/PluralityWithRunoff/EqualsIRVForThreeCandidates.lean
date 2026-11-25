import Mathlib.Tactic
import SocialChoice.Rules.PluralityWithRunoff.CondorcetLoser
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.CondorcetLoser

namespace SocialChoice

/-!
# IRV = Plurality with Runoff for candidate sets of size at most 3
-/

theorem instantRunoffVoting_eq_pluralityWithRunoff_of_card_le_two
    {V A : Type} [Fintype V] [Fintype A]
    (hcard : Fintype.card A ≤ 2) (P : Profile V A) :
    instantRunoffVoting P = pluralityWithRunoff P := by
  classical
  by_cases hcard_le_one : Fintype.card A ≤ 1
  · simp [instantRunoffVoting, scoringEliminationRule, scoringEliminationAux,
      pluralityWithRunoff, hcard_le_one]
  have hcard2 : Fintype.card A = 2 := by
    omega
  have hcard_univ : (Finset.univ : Finset A).card = 2 := by
    simpa [Finset.card_univ] using hcard2
  rcases Finset.card_eq_two.mp hcard_univ with ⟨a, b, hab, hab_univ⟩
  apply Finset.ext
  intro x
  have hx : x = a ∨ x = b := by
    have hxmem : x ∈ (Finset.univ : Finset A) := by
      simp
    simpa [hab_univ] using hxmem
  cases hx with
  | inl hx =>
      subst hx
      have hirv :
          x ∈ instantRunoffVoting P ↔ 0 ≤ margin P x b :=
        instantRunoffVoting_of_card_two (P := P) hcard2 x b hab
      have hpwr :
          x ∈ pluralityWithRunoff P ↔ 0 ≤ margin P x b :=
        pluralityWithRunoff_of_card_two (P := P) hcard2 x b hab
      exact hirv.trans hpwr.symm
  | inr hx =>
      subst hx
      have hirv :
            x ∈ instantRunoffVoting P ↔ 0 ≤ margin P x a :=
        instantRunoffVoting_of_card_two (P := P) hcard2 x a (Ne.symm hab)
      have hpwr :
          x ∈ pluralityWithRunoff P ↔ 0 ≤ margin P x a :=
        pluralityWithRunoff_of_card_two (P := P) hcard2 x a (Ne.symm hab)
      exact hirv.trans hpwr.symm

/-! ### Card = 3 helper lemmas (placeholders) -/

private lemma exists_pair_eq_univ_erase_of_card_three
    {A : Type} [Fintype A] [DecidableEq A]
    (hcard : Fintype.card A = 3) {c x : A} (hcx : x ≠ c) :
    ∃ y : A, ({x, y} : Finset A) = (Finset.univ.erase c) := by
  classical
  have hcard_univ : (Finset.univ : Finset A).card = 3 := by
    simp [Finset.card_univ, hcard]
  have hmem : c ∈ (Finset.univ : Finset A) := by simp
  have hcard_erase : (Finset.univ.erase c : Finset A).card = 2 := by
    calc
      (Finset.univ.erase c : Finset A).card
          = (Finset.univ : Finset A).card - 1 :=
            Finset.card_erase_of_mem (s := (Finset.univ : Finset A)) (a := c) hmem
      _ = 2 := by
            simp [hcard_univ]
  have hxmem : x ∈ (Finset.univ.erase c : Finset A) := by
    simp [hcx]
  have hcard_pos : 1 < (Finset.univ.erase c : Finset A).card := by
    simp [hcard_erase]
  rcases Finset.exists_mem_ne (s := (Finset.univ.erase c : Finset A)) hcard_pos x with
    ⟨y, hy, hyx⟩
  have hsubset : ({x, y} : Finset A) ⊆ (Finset.univ.erase c : Finset A) := by
    intro z hz
    simp [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxmem
    · exact hy
  have hcard_pair : ({x, y} : Finset A).card = 2 := Finset.card_pair hyx.symm
  refine ⟨y, ?_⟩
  apply Finset.eq_of_subset_of_card_le hsubset
  simp [hcard_pair, hcard_erase]

private lemma irv_branch_iff_margin_of_card_three
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (hcard : Fintype.card A = 3) {c x y : A}
    (hpair : ({x, y} : Finset A) = (Finset.univ.erase c)) :
    x ∈ liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P c)) ↔
      0 ≤ margin P x y := by
  classical
  have hxmem : x ∈ (Finset.univ.erase c : Finset A) := by
    have hxmem' : x ∈ ({x, y} : Finset A) := by simp
    simpa [hpair] using hxmem'
  have hymem : y ∈ (Finset.univ.erase c : Finset A) := by
    have hymem' : y ∈ ({x, y} : Finset A) := by simp
    simpa [hpair] using hymem'
  have hxne : x ≠ c := (Finset.mem_erase.mp hxmem).1
  have hyne : y ≠ c := (Finset.mem_erase.mp hymem).1
  have hcard_univ : (Finset.univ : Finset A).card = 3 := by
    simp [Finset.card_univ, hcard]
  have hmemc : c ∈ (Finset.univ : Finset A) := by simp
  have hcard_erase : (Finset.univ.erase c : Finset A).card = 2 := by
    calc
      (Finset.univ.erase c : Finset A).card
          = (Finset.univ : Finset A).card - 1 :=
            Finset.card_erase_of_mem (s := (Finset.univ : Finset A)) (a := c) hmemc
      _ = 2 := by
            simp [hcard_univ]
  have hcard_pair : ({x, y} : Finset A).card = 2 := by
    simpa [hpair] using hcard_erase
  have hxy : x ≠ y := by
    intro hxy
    subst hxy
    simp at hcard_pair
  have hcard_sub : Fintype.card {z : A // z ≠ c} = 2 := by
    simp [card_subtype_ne_eq c, hcard]
  have hxy_sub : (⟨x, hxne⟩ : {z : A // z ≠ c}) ≠ ⟨y, hyne⟩ := by
    intro hEq
    have : x = y := by
      simpa using congrArg Subtype.val hEq
    exact hxy this
  have hx_lift :
      x ∈ liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P c)) ↔
        (⟨x, hxne⟩ : {z : A // z ≠ c}) ∈
          scoringEliminationAux pluralityScore _ (restrictProfile P c) := by
    constructor
    · intro hxmem'
      rcases (mem_liftFinset_iff_subtype
        (s := scoringEliminationAux pluralityScore _ (restrictProfile P c)) (x := x)).1 hxmem' with
        ⟨hxne', hxmem''⟩
      have hx_eq : (⟨x, hxne'⟩ : {z : A // z ≠ c}) = ⟨x, hxne⟩ := by
        ext
        rfl
      simpa [hx_eq] using hxmem''
    · intro hxmem'
      exact (mem_liftFinset_iff_subtype
        (s := scoringEliminationAux pluralityScore _ (restrictProfile P c)) (x := x)).2
        ⟨hxne, hxmem'⟩
  have hirv_sub' :
      (⟨x, hxne⟩ : {z : A // z ≠ c}) ∈
          @scoringEliminationAux V _ pluralityScore {z : A // z ≠ c} _ (Classical.decEq _)
            (restrictProfile P c) ↔
        0 ≤ margin (restrictProfile P c) ⟨x, hxne⟩ ⟨y, hyne⟩ := by
    let : DecidableEq {z : A // z ≠ c} := Classical.decEq _
    simpa [instantRunoffVoting, scoringEliminationRule] using
      (instantRunoffVoting_of_card_two (P := restrictProfile P c) (hcard := hcard_sub)
        (a := (⟨x, hxne⟩ : {z : A // z ≠ c}))
        (b := (⟨y, hyne⟩ : {z : A // z ≠ c})) (hab := hxy_sub))
  have hcongr :=
    scoringEliminationAux_decidableEq_congr (score := pluralityScore) (P := restrictProfile P c)
      (inst1 := Classical.decEq {z : A // z ≠ c}) (inst2 := inferInstance)
  have hirv_sub :
      (⟨x, hxne⟩ : {z : A // z ≠ c}) ∈
          scoringEliminationAux pluralityScore _ (restrictProfile P c) ↔
        0 ≤ margin (restrictProfile P c) ⟨x, hxne⟩ ⟨y, hyne⟩ := by
    simpa [hcongr] using hirv_sub'
  have hmargin_eq :
      margin (restrictProfile P c) ⟨x, hxne⟩ ⟨y, hyne⟩ = margin P x y := by
    simpa using
      (margin_eq_margin_restrictProfile (P := P) (c := c)
        (a := (⟨x, hxne⟩ : {z : A // z ≠ c}))
        (b := (⟨y, hyne⟩ : {z : A // z ≠ c}))).symm
  exact hx_lift.trans (by simpa [hmargin_eq] using hirv_sub)

private lemma exists_c_of_pair_card_two
    {A : Type} [Fintype A] [DecidableEq A]
    (hcard : Fintype.card A = 3) {s : Finset A} (hs : s.card = 2) :
    ∃ c : A, s = (Finset.univ.erase c : Finset A) := by
  classical
  rcases Finset.card_eq_two.mp hs with ⟨x, y, hxy, hs_eq⟩
  have hcard_univ : (Finset.univ : Finset A).card = 3 := by
    simp [Finset.card_univ, hcard]
  have hmemx : x ∈ (Finset.univ : Finset A) := by simp
  have hcard_erase_x : (Finset.univ.erase x : Finset A).card = 2 := by
    calc
      (Finset.univ.erase x : Finset A).card
          = (Finset.univ : Finset A).card - 1 :=
            Finset.card_erase_of_mem (s := (Finset.univ : Finset A)) (a := x) hmemx
      _ = 2 := by
            simp [hcard_univ]
  have hcard_pos : 1 < (Finset.univ.erase x : Finset A).card := by
    simp [hcard_erase_x]
  rcases Finset.exists_mem_ne (s := (Finset.univ.erase x : Finset A)) hcard_pos y with
    ⟨c, hc_mem, hcy⟩
  have hcx : c ≠ x := (Finset.mem_erase.mp hc_mem).1
  have hsubset : s ⊆ (Finset.univ.erase c : Finset A) := by
    intro z hz
    have hz' : z = x ∨ z = y := by
      have : z ∈ ({x, y} : Finset A) := by
        simpa [hs_eq] using hz
      simpa [Finset.mem_insert, Finset.mem_singleton] using this
    rcases hz' with rfl | rfl
    · have hzc : z ≠ c := Ne.symm hcx
      simp [hzc]
    · have hzc : z ≠ c := Ne.symm hcy
      simp [hzc]
  have hcard_erase_c : (Finset.univ.erase c : Finset A).card = 2 := by
    have hmemc : c ∈ (Finset.univ : Finset A) := by simp
    calc
      (Finset.univ.erase c : Finset A).card
          = (Finset.univ : Finset A).card - 1 :=
            Finset.card_erase_of_mem (s := (Finset.univ : Finset A)) (a := c) hmemc
      _ = 2 := by
            simp [hcard_univ]
  refine ⟨c, ?_⟩
  apply Finset.eq_of_subset_of_card_le hsubset
  simp [hs, hcard_erase_c]

private lemma pluralityWithRunoffPairs_pair_iff_lowest_of_card_three_ge_two
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (hcard : Fintype.card A = 3) {c : A}
    (hS : (plurality P).card ≥ 2) :
    (Finset.univ.erase c : Finset A) ∈ pluralityWithRunoffPairs P ↔
      c ∈ lowestScoring P (fun r => pluralityScore (Fintype.card A) r) := by
  classical
  let S : Finset A := plurality P
  have hA : (Finset.univ : Finset A).Nonempty := by
    have hpos : 0 < Fintype.card A := by
      simp [hcard]
    exact Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hpos)
  have hmax_of_memS : ∀ {x : A} (hx : x ∈ S), ∀ d : A, topCount P d ≤ topCount P x := by
    intro x hx d
    have hx' :
        x ∈ (Finset.univ.filter (fun c => ∀ d : A, topCount P d ≤ topCount P c)) := by
      simpa [S, plurality] using hx
    exact (Finset.mem_filter.mp hx').2 d
  have hcard_univ : (Finset.univ : Finset A).card = 3 := by
    simp [Finset.card_univ, hcard]
  have hcard_erase : (Finset.univ.erase c : Finset A).card = 2 := by
    have hmem : c ∈ (Finset.univ : Finset A) := by simp
    calc
      (Finset.univ.erase c : Finset A).card
          = (Finset.univ : Finset A).card - 1 :=
            Finset.card_erase_of_mem (s := (Finset.univ : Finset A)) (a := c) hmem
      _ = 2 := by
            simp [hcard_univ]
  have hmem_pairs :
      (Finset.univ.erase c : Finset A) ∈ pluralityWithRunoffPairs P ↔
        (Finset.univ.erase c : Finset A) ⊆ S := by
    constructor
    · intro hmem
      have hmem' :
          (Finset.univ.erase c : Finset A) ∈ S.powersetCard 2 := by
        simpa [pluralityWithRunoffPairs, hS, S] using hmem
      exact (Finset.mem_powersetCard.mp hmem').1
    · intro hsubset
      have hmem' :
          (Finset.univ.erase c : Finset A) ∈ S.powersetCard 2 := by
        exact Finset.mem_powersetCard.mpr ⟨hsubset, hcard_erase⟩
      simpa [pluralityWithRunoffPairs, hS, S] using hmem'
  constructor
  · intro hmem
    have hsubset := (hmem_pairs.mp hmem)
    apply (lowestScoring_plurality_iff_forall_le_topCount (P := P) hA (c := c)).2
    intro d
    by_cases hdc : d = c
    · subst hdc
      exact le_rfl
    · have hd_in : d ∈ (Finset.univ.erase c : Finset A) := by
        simp [hdc]
      have hdS : d ∈ S := hsubset hd_in
      exact (hmax_of_memS hdS) c
  · intro hcL
    have hmin : ∀ d : A, topCount P c ≤ topCount P d :=
      (lowestScoring_plurality_iff_forall_le_topCount (P := P) hA (c := c)).1 hcL
    by_cases hcS : c ∈ S
    · have hmax : ∀ d : A, topCount P d ≤ topCount P c := (hmax_of_memS hcS)
      have hEq : ∀ d : A, topCount P d = topCount P c := by
        intro d
        exact le_antisymm (hmax d) (hmin d)
      have hsubset_univ : (Finset.univ : Finset A) ⊆ S := by
        intro d _hd
        have hmax' : ∀ e : A, topCount P e ≤ topCount P d := by
          intro e
          simp [hEq e, hEq d]
        exact Finset.mem_filter.mpr ⟨by simp, hmax'⟩
      have hS_univ' : (Finset.univ : Finset A) = S := by
        apply Finset.eq_of_subset_of_card_le hsubset_univ
        simpa [Finset.card_univ] using (Finset.card_le_univ (s := S))
      have hS_univ : S = (Finset.univ : Finset A) := hS_univ'.symm
      have hsubset : (Finset.univ.erase c : Finset A) ⊆ S := by
        intro d hd
        simp [hS_univ]
      exact (hmem_pairs.mpr hsubset)
    · have hsubsetS : S ⊆ (Finset.univ.erase c : Finset A) := by
        intro d hdS
        have hdc : d ≠ c := by
          intro hdc
          exact hcS (by simpa [hdc] using hdS)
        simp [hdc]
      have hS_eq : S = (Finset.univ.erase c : Finset A) := by
        apply Finset.eq_of_subset_of_card_le hsubsetS
        simpa [hcard_erase] using hS
      have hsubset : (Finset.univ.erase c : Finset A) ⊆ S := by
        intro d hd
        simpa [hS_eq] using hd
      exact (hmem_pairs.mpr hsubset)

private lemma pluralityWithRunoffPairs_pair_iff_lowest_of_card_three_eq_one
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (hcard : Fintype.card A = 3) {c : A}
    (hS : (plurality P).card = 1) :
    (Finset.univ.erase c : Finset A) ∈ pluralityWithRunoffPairs P ↔
      c ∈ lowestScoring P (fun r => pluralityScore (Fintype.card A) r) := by
  classical
  let S : Finset A := plurality P
  have hS' : S.card = 1 := by
    simpa [S] using hS
  have hA : (Finset.univ : Finset A).Nonempty := by
    have hpos : 0 < Fintype.card A := by
      simp [hcard]
    exact Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hpos)
  have hmax_of_memS : ∀ {x : A} (hx : x ∈ S), ∀ d : A, topCount P d ≤ topCount P x := by
    intro x hx d
    have hx' :
        x ∈ (Finset.univ.filter (fun c => ∀ d : A, topCount P d ≤ topCount P c)) := by
      simpa [S, plurality] using hx
    exact (Finset.mem_filter.mp hx').2 d
  rcases Finset.card_eq_one.mp hS' with ⟨s, hS_eq⟩
  have hS_eq' : S = {s} := by
    simpa using hS_eq
  let R : Finset A := Finset.univ.filter (fun u => u ∉ S)
  have hR_eq : R = (Finset.univ.erase s : Finset A) := by
    ext u
    simp [R, hS_eq']
  have hAcard : 1 < (Finset.univ : Finset A).card := by
    simp [Finset.card_univ, hcard]
  rcases Finset.exists_mem_ne (s := (Finset.univ : Finset A)) hAcard s with
    ⟨t0, ht0, ht0s⟩
  have hR_nonempty : R.Nonempty := by
    refine ⟨t0, ?_⟩
    have ht0_notS : t0 ∉ S := by
      simp [hS_eq', ht0s]
    exact Finset.mem_filter.mpr ⟨ht0, ht0_notS⟩
  let T : Finset A := secondPluralitySet P S
  have hmem_second :
      ∀ d : A,
        d ∈ T ↔ d ∈ R ∧ ∀ e ∈ R, topCount P e ≤ topCount P d := by
    intro d
    simpa [R] using (mem_secondPluralitySet_iff_forall_le (P := P) (S := S) hR_nonempty)
  have hS_ge2 : ¬ S.card ≥ 2 := by
    omega
  by_cases hcs : c = s
  · subst hcs
    have hpair_false :
        (Finset.univ.erase c : Finset A) ∉ pluralityWithRunoffPairs P := by
      intro hmem
      have hmem' :
          (Finset.univ.erase c : Finset A) ∈
            (S.product T).image (fun p => ({p.1, p.2} : Finset A)) := by
        simpa [pluralityWithRunoffPairs, hS_ge2, S] using hmem
      rcases Finset.mem_image.mp hmem' with ⟨p, hp, hp_eq⟩
      rcases Finset.mem_product.mp hp with ⟨hpS, _hpT⟩
      have hp1 : p.1 = c := by
        simpa [hS_eq'] using hpS
      have hc_mem : p.1 ∈ (Finset.univ.erase c : Finset A) := by
        have : p.1 ∈ ({p.1, p.2} : Finset A) := by simp
        simpa [hp_eq] using this
      have hc_mem' : c ∈ (Finset.univ.erase c : Finset A) := by
        simp [hp1] at hc_mem
      simp at hc_mem'
    have hnotL :
        c ∉ lowestScoring P (fun r => pluralityScore (Fintype.card A) r) := by
      intro hcL
      have hmin : ∀ d : A, topCount P c ≤ topCount P d :=
        (lowestScoring_plurality_iff_forall_le_topCount (P := P) hA (c := c)).1 hcL
      have hcS : c ∈ S := by
        simp [hS_eq']
      have hmax : ∀ d : A, topCount P d ≤ topCount P c := hmax_of_memS hcS
      have hEq : ∀ d : A, topCount P d = topCount P c := by
        intro d
        exact le_antisymm (hmax d) (hmin d)
      have hsubset_univ : (Finset.univ : Finset A) ⊆ S := by
        intro d _hd
        have hmax' : ∀ e : A, topCount P e ≤ topCount P d := by
          intro e
          simp [hEq e, hEq d]
        exact Finset.mem_filter.mpr ⟨by simp, hmax'⟩
      have hS_univ : S = (Finset.univ : Finset A) := by
        have hS_univ' : (Finset.univ : Finset A) = S := by
          apply Finset.eq_of_subset_of_card_le hsubset_univ
          simpa [Finset.card_univ] using (Finset.card_le_univ (s := S))
        exact hS_univ'.symm
      have hS_card : S.card = 3 := by
        simpa [hcard] using congrArg Finset.card hS_univ
      exact (by omega : False)
    constructor
    · intro hmem
      exact (hpair_false hmem).elim
    · intro hcL
      exact (hnotL hcL).elim
  ·
    have hpair : ∃ t : A, ({s, t} : Finset A) = (Finset.univ.erase c) := by
      have hcs' : s ≠ c := Ne.symm hcs
      exact exists_pair_eq_univ_erase_of_card_three (hcard := hcard) (c := c) (x := s) hcs'
    rcases hpair with ⟨t, hpair⟩
    have hcard_univ : (Finset.univ : Finset A).card = 3 := by
      simp [Finset.card_univ, hcard]
    have hcard_erase_c : (Finset.univ.erase c : Finset A).card = 2 := by
      have hmemc : c ∈ (Finset.univ : Finset A) := by simp
      calc
        (Finset.univ.erase c : Finset A).card
            = (Finset.univ : Finset A).card - 1 :=
              Finset.card_erase_of_mem (s := (Finset.univ : Finset A)) (a := c) hmemc
        _ = 2 := by
              simp [hcard_univ]
    have hts : t ≠ s := by
      intro hts
      subst hts
      have hcard_pair : ({t, t} : Finset A).card = 2 := by
        simpa [hpair] using hcard_erase_c
      simp at hcard_pair
    have ht_mem : t ∈ (Finset.univ.erase c : Finset A) := by
      have : t ∈ ({s, t} : Finset A) := by simp
      simpa [hpair] using this
    have hct' : t ≠ c := (Finset.mem_erase.mp ht_mem).1
    have hct : c ≠ t := Ne.symm hct'
    have hcR : c ∈ R := by
      have : c ∈ (Finset.univ.erase s : Finset A) := by
        simp [hcs]
      simpa [hR_eq] using this
    have htR : t ∈ R := by
      have : t ∈ (Finset.univ.erase s : Finset A) := by
        simp [hts]
      simpa [hR_eq] using this
    have hcard_erase_s : (Finset.univ.erase s : Finset A).card = 2 := by
      have hmems : s ∈ (Finset.univ : Finset A) := by simp
      calc
        (Finset.univ.erase s : Finset A).card
            = (Finset.univ : Finset A).card - 1 :=
              Finset.card_erase_of_mem (s := (Finset.univ : Finset A)) (a := s) hmems
        _ = 2 := by
              simp [hcard_univ]
    have hcard_R : R.card = 2 := by
      simpa [hR_eq] using hcard_erase_s
    have hsubset_ct : ({c, t} : Finset A) ⊆ R := by
      intro z hz
      simp [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hcR
      · exact htR
    have hcard_pair_ct : ({c, t} : Finset A).card = 2 := Finset.card_pair hct
    have hR_eq_ct : R = ({c, t} : Finset A) := by
      have hR_eq_ct' : ({c, t} : Finset A) = R := by
        apply Finset.eq_of_subset_of_card_le hsubset_ct
        simp [hcard_R, hcard_pair_ct]
      exact hR_eq_ct'.symm
    have hpair_mem_iff :
        (Finset.univ.erase c : Finset A) ∈ pluralityWithRunoffPairs P ↔ t ∈ T := by
      constructor
      · intro hmem
        have hmem' :
            (Finset.univ.erase c : Finset A) ∈
              (S.product T).image (fun p => ({p.1, p.2} : Finset A)) := by
          simpa [pluralityWithRunoffPairs, hS_ge2, S] using hmem
        rcases Finset.mem_image.mp hmem' with ⟨p, hp, hp_eq⟩
        rcases Finset.mem_product.mp hp with ⟨hpS, hpT⟩
        have hp1 : p.1 = s := by
          simpa [hS_eq'] using hpS
        have hp2_mem : p.2 ∈ ({s, t} : Finset A) := by
          have : p.2 ∈ ({p.1, p.2} : Finset A) := by simp
          have hset : ({p.1, p.2} : Finset A) = ({s, t} : Finset A) := by
            calc
              ({p.1, p.2} : Finset A) = (Finset.univ.erase c : Finset A) := hp_eq
              _ = ({s, t} : Finset A) := hpair.symm
          exact hset ▸ this
        have hp2_not_s : p.2 ≠ s := by
          have hp2_notS : p.2 ∉ S := mem_secondPluralitySet_not_mem (P := P) (S := S) hpT
          intro hps
          apply hp2_notS
          simp [hS_eq', hps]
        have hp2 : p.2 = t := by
          simp [Finset.mem_insert, Finset.mem_singleton] at hp2_mem
          rcases hp2_mem with hps | hpt
          · exact (hp2_not_s hps).elim
          · exact hpt
        simpa [hp2] using hpT
      · intro htT
        have hmem' :
            ({s, t} : Finset A) ∈
              (S.product T).image (fun p => ({p.1, p.2} : Finset A)) := by
          refine Finset.mem_image.mpr ?_
          refine ⟨(s, t), ?_, rfl⟩
          refine Finset.mem_product.mpr ?_
          have hsS : s ∈ S := by
            simp [hS_eq']
          exact ⟨hsS, htT⟩
        have hmem : ({s, t} : Finset A) ∈ pluralityWithRunoffPairs P := by
          simpa [pluralityWithRunoffPairs, hS_ge2, S] using hmem'
        simpa [hpair] using hmem
    have hsecond_iff :
        t ∈ T ↔ topCount P c ≤ topCount P t := by
      constructor
      · intro htT
        have htT' := (hmem_second t).1 htT
        exact (htT'.2 c hcR)
      · intro hle
        apply (hmem_second t).2
        refine ⟨htR, ?_⟩
        intro e he
        have he' : e = c ∨ e = t := by
          have : e ∈ ({c, t} : Finset A) := by
            simpa [hR_eq_ct] using he
          simpa [Finset.mem_insert, Finset.mem_singleton] using this
        rcases he' with rfl | rfl
        · exact hle
        · exact le_rfl
    have hmin_iff :
        c ∈ lowestScoring P (fun r => pluralityScore (Fintype.card A) r) ↔
          topCount P c ≤ topCount P t := by
      constructor
      · intro hcL
        have hmin : ∀ d : A, topCount P c ≤ topCount P d :=
          (lowestScoring_plurality_iff_forall_le_topCount (P := P) hA (c := c)).1 hcL
        exact hmin t
      · intro hle
        apply (lowestScoring_plurality_iff_forall_le_topCount (P := P) hA (c := c)).2
        intro d
        by_cases hdc : d = c
        · subst hdc
          exact le_rfl
        · have hd_in : d ∈ (Finset.univ.erase c : Finset A) := by
            simp [hdc]
          have hd' : d = s ∨ d = t := by
            have : d ∈ ({s, t} : Finset A) := by
              simpa [hpair] using hd_in
            simpa [Finset.mem_insert, Finset.mem_singleton] using this
          rcases hd' with rfl | rfl
          · have hdS : d ∈ S := by
              simp [hS_eq']
            have hmax_d : ∀ d' : A, topCount P d' ≤ topCount P d := hmax_of_memS hdS
            exact hmax_d c
          · exact hle
    exact (hpair_mem_iff.trans hsecond_iff).trans hmin_iff.symm

private lemma pluralityWithRunoffPairs_eq_image_lowest_of_card_three
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (hcard : Fintype.card A = 3) :
    pluralityWithRunoffPairs P =
      (lowestScoring P (fun r => pluralityScore (Fintype.card A) r)).image
        (fun c => (Finset.univ.erase c : Finset A)) := by
  classical
  let scoreVec : Nat → Int := fun r => pluralityScore (Fintype.card A) r
  let L : Finset A := lowestScoring P scoreVec
  have hA_pos : 0 < Fintype.card A := by
    simp [hcard]
  have : Nonempty A := Fintype.card_pos_iff.mp hA_pos
  have hpair_iff : ∀ c : A,
      (Finset.univ.erase c : Finset A) ∈ pluralityWithRunoffPairs P ↔ c ∈ L := by
    intro c
    by_cases hS : (plurality P).card ≥ 2
    ·
      simpa [L, scoreVec] using
        (pluralityWithRunoffPairs_pair_iff_lowest_of_card_three_ge_two
          (P := P) (hcard := hcard) (c := c) hS)
    ·
      have hS_nonempty : (plurality P).Nonempty := plurality_nonempty (P := P)
      have hS_le : (plurality P).card ≤ 1 := by
        have hS_lt : (plurality P).card < 2 := Nat.lt_of_not_ge hS
        exact Nat.lt_succ_iff.mp hS_lt
      have hS_eq_one : (plurality P).card = 1 :=
        Nat.le_antisymm hS_le (Finset.one_le_card.mpr hS_nonempty)
      simpa [L, scoreVec] using
        (pluralityWithRunoffPairs_pair_iff_lowest_of_card_three_eq_one
          (P := P) (hcard := hcard) (c := c) hS_eq_one)
  apply Finset.ext
  intro s
  constructor
  · intro hs
    have hs_card : s.card = 2 := mem_pluralityWithRunoffPairs_card (P := P) hs
    rcases exists_c_of_pair_card_two (hcard := hcard) (s := s) hs_card with ⟨c, hs_eq⟩
    have hcL : c ∈ L := (hpair_iff c).1 (by simpa [hs_eq] using hs)
    exact Finset.mem_image.mpr ⟨c, hcL, by simp [hs_eq]⟩
  · intro hs
    rcases Finset.mem_image.mp hs with ⟨c, hcL, hs_eq⟩
    have hmem : (Finset.univ.erase c : Finset A) ∈ pluralityWithRunoffPairs P :=
      (hpair_iff c).2 hcL
    simpa [hs_eq] using hmem

theorem instantRunoffVoting_eq_pluralityWithRunoff_of_card_le_three
    {V A : Type} [Fintype V] [Fintype A]
    (hcard : Fintype.card A ≤ 3) (P : Profile V A) :
    instantRunoffVoting P = pluralityWithRunoff P := by
  classical
  by_cases hcard_le_two : Fintype.card A ≤ 2
  · exact instantRunoffVoting_eq_pluralityWithRunoff_of_card_le_two (P := P) hcard_le_two
  have hcard3 : Fintype.card A = 3 := by
    omega
  let scoreVec : Nat → Int := fun r => pluralityScore (Fintype.card A) r
  let L : Finset A := lowestScoring P scoreVec
  have hnot_le_one : ¬ Fintype.card A ≤ 1 := by omega
  have haux :
      scoringEliminationAux pluralityScore A P =
        L.biUnion (fun c =>
          liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P c))) := by
    simpa [scoreVec, L] using
      (scoringEliminationAux_eq_biUnion_of_not_card_le_one
        (score := pluralityScore) (P := P) (hcard := hnot_le_one))
  apply Finset.ext
  intro x
  constructor
  · intro hx
    have hx' :
        x ∈ L.biUnion (fun c =>
          liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P c))) := by
      simpa [instantRunoffVoting, scoringEliminationRule, haux] using hx
    rcases Finset.mem_biUnion.mp hx' with ⟨c, hcL, hxmem⟩
    have hcx : x ≠ c := by
      exact (liftFinset_subset_of_prop
        (s := scoringEliminationAux pluralityScore _ (restrictProfile P c)) x hxmem)
    rcases exists_pair_eq_univ_erase_of_card_three (hcard := hcard3) (c := c) (x := x) hcx with
      ⟨y, hpair⟩
    have hmargin :
        0 ≤ margin P x y := by
      exact (irv_branch_iff_margin_of_card_three (P := P) (hcard := hcard3)
        (c := c) (x := x) (y := y) (hpair := hpair)).1 hxmem
    have hpair_mem :
        ({x, y} : Finset A) ∈ pluralityWithRunoffPairs P := by
      have hpair_mem' :
          ({x, y} : Finset A) ∈
            L.image (fun c => (Finset.univ.erase c : Finset A)) := by
        exact Finset.mem_image.mpr ⟨c, hcL, by simp [hpair]⟩
      simpa [pluralityWithRunoffPairs_eq_image_lowest_of_card_three (P := P) (hcard := hcard3)]
        using hpair_mem'
    have hnot_le_one' : ¬ Fintype.card A ≤ 1 := by omega
    have : x ∈ pluralityWithRunoff P := by
      simp [pluralityWithRunoff, hnot_le_one']
      exact ⟨y, hpair_mem, hmargin⟩
    exact this
  · intro hx
    have hnot_le_one' : ¬ Fintype.card A ≤ 1 := by omega
    rcases (by
      simpa [pluralityWithRunoff, hnot_le_one'] using hx
      : ∃ y : A, ({x, y} : Finset A) ∈ pluralityWithRunoffPairs P ∧ 0 ≤ margin P x y) with
      ⟨y, hpair_mem, hmargin⟩
    have hpair_mem' :
        ({x, y} : Finset A) ∈
          L.image (fun c => (Finset.univ.erase c : Finset A)) := by
      simpa [pluralityWithRunoffPairs_eq_image_lowest_of_card_three (P := P) (hcard := hcard3)]
        using hpair_mem
    rcases Finset.mem_image.mp hpair_mem' with ⟨c, hcL, hpair⟩
    have hxmem :
        x ∈ liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P c)) := by
      exact (irv_branch_iff_margin_of_card_three (P := P) (hcard := hcard3)
        (c := c) (x := x) (y := y) (hpair := hpair.symm)).2 hmargin
    have : x ∈ instantRunoffVoting P := by
      have hx' :
          x ∈ L.biUnion (fun c =>
            liftFinset (scoringEliminationAux pluralityScore _ (restrictProfile P c))) := by
        exact Finset.mem_biUnion.mpr ⟨c, hcL, hxmem⟩
      simpa [instantRunoffVoting, scoringEliminationRule, haux] using hx'
    exact this

end SocialChoice
