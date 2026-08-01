import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import SocialChoice.Margin
import SocialChoice.Rules.ScoringRules.Plurality.Defs
import SocialChoice.Meta

namespace SocialChoice

open Finset

noncomputable def secondPluralitySet {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (S : Finset A) : Finset A := by
  classical
  let R := Finset.univ.filter (fun c => c ∉ S)
  by_cases hR : R.Nonempty
  · let maxScore : Nat :=
      (R.image (fun c => topCount P c)).max' (by
        simpa [Finset.Nonempty] using hR.image (fun c => topCount P c))
    exact R.filter (fun c => topCount P c = maxScore)
  · exact ∅

/-- `secondPluralitySet` is an instance of the generic `argmaxSet`, over the
candidates outside `S`. -/
lemma secondPluralitySet_eq_argmaxSet {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (S : Finset A) :
    secondPluralitySet P S =
      argmaxSet (Finset.univ.filter (fun c => c ∉ S)) (topCount P) := by
  classical
  unfold secondPluralitySet argmaxSet
  by_cases hR : (Finset.univ.filter (fun c : A => c ∉ S)).Nonempty <;> simp [hR]

noncomputable def pluralityWithRunoffPairs {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) : Finset (Finset A) := by
  classical
  let S := plurality P
  by_cases hS : S.card ≥ 2
  · exact S.powersetCard 2
  · let T := secondPluralitySet P S
    exact (S.product T).image (fun p => ({p.1, p.2} : Finset A))

@[scRule]
noncomputable def pluralityWithRunoff : VotingRule :=
  fun {V A} _ _ (P : Profile V A) => by
    classical
    by_cases hcard : Fintype.card A ≤ 1
    · exact (Finset.univ : Finset A)
    · let pairs := pluralityWithRunoffPairs P
      exact
        (Finset.univ.filter (fun x =>
          ∃ y : A, ({x, y} : Finset A) ∈ pairs ∧ 0 ≤ margin P x y))

lemma pluralityWithRunoffPairs_decEq_congr
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (inst1 inst2 : DecidableEq A) :
    @pluralityWithRunoffPairs V A _ _ inst1 P =
      @pluralityWithRunoffPairs V A _ _ inst2 P := by
  classical
  cases Subsingleton.elim inst1 inst2
  rfl

lemma mem_pluralityWithRunoffPairs_decEq_congr
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (inst1 inst2 : DecidableEq A) (s : Finset A) :
    s ∈ @pluralityWithRunoffPairs V A _ _ inst1 P ↔
      s ∈ @pluralityWithRunoffPairs V A _ _ inst2 P := by
  classical
  cases Subsingleton.elim inst1 inst2
  simp

theorem plurality_with_runoff_nonempty
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A] [Nonempty A]
    (P : Profile V A) : (pluralityWithRunoff P).Nonempty := by
  classical
  letI := Classical.decEq A
  by_cases hcard : Fintype.card A ≤ 1
  · simp [pluralityWithRunoff, hcard]
  · let S := plurality P
    have hSnonempty : S.Nonempty := plurality_nonempty (P := P)
    by_cases hS : S.card ≥ 2
    · have h1 : 1 < S.card := lt_of_lt_of_le (by decide : 1 < 2) hS
      rcases Finset.one_lt_card.mp h1 with ⟨a, ha, b, hb, hab⟩
      have hsubset : ({a, b} : Finset A) ⊆ S := by
        intro x hx
        simp [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have hcardpair : ({a, b} : Finset A).card = 2 := by
        exact (Finset.card_eq_two.mpr ⟨a, b, hab, rfl⟩)
      have hpair : ({a, b} : Finset A) ∈ pluralityWithRunoffPairs P := by
        simp [pluralityWithRunoffPairs, hS, S, hsubset, hcardpair]
      have hle : 0 ≤ margin P a b ∨ 0 ≤ margin P b a := by
        have htotal := le_total 0 (margin P a b)
        cases htotal with
        | inl h0 => exact Or.inl h0
        | inr h0 =>
            have hskew : margin P b a = - margin P a b := by
              simpa [skew_symmetric] using (margin_antisymmetric (P := P)) b a
            have hnonneg : 0 ≤ - margin P a b := by
              exact neg_nonneg.mpr h0
            exact Or.inr (by simpa [hskew] using hnonneg)
      cases hle with
      | inl hleab =>
          refine ⟨a, ?_⟩
          simp [pluralityWithRunoff, hcard]
          exact ⟨b, hpair, hleab⟩
      | inr hleba =>
          refine ⟨b, ?_⟩
          simp [pluralityWithRunoff, hcard]
          exact ⟨a, by simpa [Finset.pair_comm] using hpair, hleba⟩
    · have hSle : S.card ≤ 1 := by
        have hlt : S.card < 2 := lt_of_not_ge hS
        exact Nat.lt_succ_iff.mp hlt
      have hSge : 1 ≤ S.card := (Finset.one_le_card.mpr hSnonempty)
      have hScard : S.card = 1 := Nat.le_antisymm hSle hSge
      rcases Finset.card_eq_one.mp hScard with ⟨s, hs⟩
      have hAcard : 1 < (Finset.univ : Finset A).card := by
        simp [Finset.card_univ]
        exact Nat.lt_of_not_ge hcard
      have hRnonempty :
          (Finset.univ.filter (fun c => c ∉ S)).Nonempty := by
        have hs' : s ∈ (Finset.univ : Finset A) := by simp
        rcases Finset.exists_mem_ne (s := (Finset.univ : Finset A)) hAcard s with
          ⟨t, ht, hts⟩
        refine ⟨t, ?_⟩
        have htnot : t ∉ S := by
          simp [hs, hts]
        exact Finset.mem_filter.mpr ⟨ht, htnot⟩
      let R : Finset A := Finset.univ.filter (fun c => c ∉ S)
      have hRne : R.Nonempty := by
        simp [R]
        exact hRnonempty
      let scoreSet : Finset Nat := R.image (fun c => topCount P c)
      have hscoreSet : scoreSet.Nonempty := hRne.image (fun c => topCount P c)
      let maxScore : Nat := scoreSet.max' hscoreSet
      have hmaxmem : maxScore ∈ scoreSet := Finset.max'_mem scoreSet hscoreSet
      rcases Finset.mem_image.mp hmaxmem with ⟨t, ht, htScore⟩
      have htT : t ∈ secondPluralitySet P S := by
        have ht' : t ∈ R.filter (fun c => topCount P c = maxScore) := by
          exact Finset.mem_filter.mpr ⟨ht, htScore⟩
        have hRne' : (Finset.univ.filter (fun c => c ∉ S)).Nonempty := hRnonempty
        simp [R] at ht'
        dsimp [secondPluralitySet]
        simp [hRne']
        exact ht'
      have hsS : s ∈ S := by
        simp [hs]
      have hpair : ({s, t} : Finset A) ∈ pluralityWithRunoffPairs P := by
        simp [pluralityWithRunoffPairs, hS, S]
        exact ⟨s, t, ⟨hsS, htT⟩, rfl⟩
      have hle : 0 ≤ margin P s t ∨ 0 ≤ margin P t s := by
        have htotal := le_total 0 (margin P s t)
        cases htotal with
        | inl h0 => exact Or.inl h0
        | inr h0 =>
            have hskew : margin P t s = - margin P s t := by
              simpa [skew_symmetric] using (margin_antisymmetric (P := P)) t s
            have hnonneg : 0 ≤ - margin P s t := by
              exact neg_nonneg.mpr h0
            exact Or.inr (by simpa [hskew] using hnonneg)
      cases hle with
      | inl hle_st =>
          refine ⟨s, ?_⟩
          simp [pluralityWithRunoff, hcard]
          exact ⟨t, hpair, hle_st⟩
      | inr hle_ts =>
          refine ⟨t, ?_⟩
          simp [pluralityWithRunoff, hcard]
          exact ⟨s, by simpa [Finset.pair_comm] using hpair, hle_ts⟩

theorem pluralityWithRunoff_isVotingRule : IsVotingRule pluralityWithRunoff := by
  intro V A _ _ _ P
  classical
  simpa using (plurality_with_runoff_nonempty (P := P))

end SocialChoice
