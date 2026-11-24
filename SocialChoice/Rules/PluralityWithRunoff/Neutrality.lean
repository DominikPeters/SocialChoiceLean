import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Image
import SocialChoice.Axioms.Neutrality
import SocialChoice.Margin
import SocialChoice.Rules
import SocialChoice.Rules.ScoringRules.Plurality.Derived
import SocialChoice.Rules.PluralityWithRunoff.Defs

namespace SocialChoice

lemma topRank_permuteCandidates_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) (v : V) (a : A) :
    TopRank (permuteCandidates P σ) v a ↔ TopRank P v (σ.symm a) := by
  constructor
  · intro h d hd
    have hd' : σ d ≠ a := by
      intro hda
      apply hd
      simpa using congrArg σ.symm hda
    have hpref : Prefers (permuteCandidates P σ) v a (σ d) := h (σ d) hd'
    have hpref' :
        Prefers P v (σ.symm a) (σ.symm (σ d)) := by
      simpa using (prefers_permuteCandidates_iff (P := P) (σ := σ) (v := v)
        (a := a) (b := σ d)).1 hpref
    simpa using hpref'
  · intro h d hd
    have hd' : σ.symm d ≠ σ.symm a := by
      intro hda
      apply hd
      simpa using congrArg σ hda
    have hpref : Prefers P v (σ.symm a) (σ.symm d) := h (σ.symm d) hd'
    have hpref' :
        Prefers (permuteCandidates P σ) v a d := by
      simpa using (prefers_permuteCandidates_iff (P := P) (σ := σ) (v := v)
        (a := a) (b := d)).2 hpref
    exact hpref'

@[simp] lemma votersTop_permuteCandidates {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) (a : A) :
    votersTop (permuteCandidates P σ) a = votersTop P (σ.symm a) := by
  classical
  ext v
  simp [votersTop, topRank_permuteCandidates_iff]

@[simp] lemma topCount_permuteCandidates {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) (a : A) :
    topCount (permuteCandidates P σ) a = topCount P (σ.symm a) := by
  classical
  simp [topCount]

@[simp] lemma map_pair {A B : Type} [DecidableEq A] [DecidableEq B]
    (f : A ↪ B) (a b : A) :
    ({a, b} : Finset A).map f = {f a, f b} := by
  simp [Finset.map_insert, Finset.map_singleton]

lemma secondPluralitySet_permuteCandidates {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (σ : Equiv.Perm A) (S : Finset A) :
    secondPluralitySet (permuteCandidates P σ) (S.map σ.toEmbedding) =
      (secondPluralitySet P S).map σ.toEmbedding := by
  classical
  let R : Finset A := Finset.univ.filter fun c => c ∉ S
  let R' : Finset A := Finset.univ.filter fun c => c ∉ S.map σ.toEmbedding
  have hRmap : R' = R.map σ.toEmbedding := by
    apply Finset.ext
    intro a
    simp [R, R', Finset.mem_map_equiv]
  by_cases hR : R.Nonempty
  · have hR' : R'.Nonempty := by simpa [hRmap] using hR
    have hR0 : (Finset.univ.filter (fun c => c ∉ S)).Nonempty := by
      simpa [R] using hR
    have himage :
        (R'.image (fun c => topCount P (σ.symm c))) =
          (R.image (fun c => topCount P c)) := by
      apply Finset.ext
      intro m
      constructor
      · intro hm
        rcases Finset.mem_image.mp hm with ⟨a, ha, rfl⟩
        have haR : σ.symm a ∈ R := by
          have : a ∈ R.map σ.toEmbedding := by simpa [hRmap] using ha
          simpa [Finset.mem_map_equiv] using this
        exact Finset.mem_image.mpr ⟨σ.symm a, haR, by simp⟩
      · intro hm
        rcases Finset.mem_image.mp hm with ⟨a, ha, rfl⟩
        have haR' : σ a ∈ R' := by
          have : σ a ∈ R.map σ.toEmbedding := by
            exact Finset.mem_map.mpr ⟨a, ha, by simp⟩
          simpa [hRmap] using this
        exact Finset.mem_image.mpr ⟨σ a, haR', by simp⟩
    have hmax :
        (R'.image (fun c => topCount P (σ.symm c))).max' (hR'.image _) =
          (R.image (fun c => topCount P c)).max' (hR.image _) := by
      simp [himage]
    have hR'' :
        (Finset.univ.filter (fun c => σ.symm c ∉ S)).Nonempty := by
      simpa [R', Finset.mem_map_equiv] using hR'
    apply Finset.ext
    intro a
    constructor
    · intro ha
      have ha' :
          a ∈ R'.filter (fun c =>
            topCount P (σ.symm c) =
              (R'.image (fun c => topCount P (σ.symm c))).max' (hR'.image _)) := by
        simpa [secondPluralitySet, hR'', topCount_permuteCandidates, R', Finset.mem_map_equiv] using ha
      have haR : a ∈ R' := (Finset.mem_filter.mp ha').1
      have haR' : σ.symm a ∈ R := by
        have : a ∈ R.map σ.toEmbedding := by simpa [hRmap] using haR
        simpa [Finset.mem_map_equiv] using this
      have haEq :
          topCount P (σ.symm a) =
            (R.image (fun c => topCount P c)).max' (hR.image _) := by
        have haEq' := (Finset.mem_filter.mp ha').2
        simpa [hmax] using haEq'
      have : σ.symm a ∈ secondPluralitySet P S := by
        have : σ.symm a ∈ R.filter (fun c =>
            topCount P c =
              (R.image (fun c => topCount P c)).max' (hR.image _)) :=
          Finset.mem_filter.mpr ⟨haR', haEq⟩
        simpa [secondPluralitySet, hR0, R] using this
      simpa [Finset.mem_map_equiv] using this
    · intro ha
      have ha' : σ.symm a ∈ secondPluralitySet P S := by
        simpa [Finset.mem_map_equiv] using ha
      have ha'' : σ.symm a ∈
          R.filter (fun c => topCount P c =
            (R.image (fun c => topCount P c)).max' (hR.image _)) := by
        simpa [secondPluralitySet, hR0, R] using ha'
      have haR : σ.symm a ∈ R := (Finset.mem_filter.mp ha'').1
      have haR' : a ∈ R' := by
        have : a ∈ R.map σ.toEmbedding := by
          exact Finset.mem_map.mpr ⟨σ.symm a, haR, by simp⟩
        simpa [hRmap] using this
      have haEq :
          topCount P (σ.symm a) =
            (R'.image (fun c => topCount P (σ.symm c))).max' (hR'.image _) := by
        have haEq' := (Finset.mem_filter.mp ha'').2
        simpa [hmax] using haEq'
      have : a ∈ R'.filter (fun c =>
          topCount P (σ.symm c) =
            (R'.image (fun c => topCount P (σ.symm c))).max' (hR'.image _)) :=
        Finset.mem_filter.mpr ⟨haR', haEq⟩
      have : a ∈ secondPluralitySet (permuteCandidates P σ) (S.map σ.toEmbedding) := by
        simpa [secondPluralitySet, hR'', topCount_permuteCandidates, R', Finset.mem_map_equiv] using this
      simpa [Finset.mem_map_equiv] using this
  · have hR' : ¬ R'.Nonempty := by
      intro hne
      have : R.Nonempty := by
        rcases hne with ⟨a, ha⟩
        have : a ∈ R.map σ.toEmbedding := by simpa [hRmap] using ha
        have : σ.symm a ∈ R := by simpa [Finset.mem_map_equiv] using this
        exact ⟨σ.symm a, this⟩
      exact hR this
    have hR0 : ¬ (Finset.univ.filter (fun c => c ∉ S)).Nonempty := by
      simpa [R] using hR
    have hR'' :
        ¬ (Finset.univ.filter (fun c => σ.symm c ∉ S)).Nonempty := by
      simpa [R', Finset.mem_map_equiv] using hR'
    apply Finset.ext
    intro a
    simp [secondPluralitySet, hR'', hR0, Finset.mem_map_equiv]

lemma pluralityWithRunoffPairs_permuteCandidates {V A : Type} [Fintype V] [Fintype A]
    [DecidableEq A] (P : Profile V A) (σ : Equiv.Perm A) :
    pluralityWithRunoffPairs (permuteCandidates P σ) =
      (pluralityWithRunoffPairs P).map (Finset.mapEmbedding σ.toEmbedding).toEmbedding := by
  classical
  let S := plurality P
  let S' := plurality (permuteCandidates P σ)
  have hS' : S' = S.map σ.toEmbedding := by
    have h := (plurality_neutral (P := P) (σ := σ))
    simpa [S, S', permuteWinners] using h.symm
  by_cases hS : S.card ≥ 2
  · have hS'card : S'.card ≥ 2 := by simpa [hS'] using hS
    have hSmap :
        S'.powersetCard 2 =
          (S.powersetCard 2).map (Finset.mapEmbedding σ.toEmbedding).toEmbedding := by
      simpa [hS'] using (Finset.powersetCard_map (f := σ.toEmbedding) (n := 2) (s := S))
    simp [pluralityWithRunoffPairs, S, S', hS, hS'card, hSmap]
  · have hS'card : ¬ S'.card ≥ 2 := by
      simpa [hS'] using hS
    let T := secondPluralitySet P S
    have hT' :
        secondPluralitySet (permuteCandidates P σ) S' = T.map σ.toEmbedding := by
      simpa [T, S', hS'] using
        (secondPluralitySet_permuteCandidates (P := P) (σ := σ) (S := S))
    let pair : A × A → Finset A := fun p => ({p.1, p.2} : Finset A)
    let pairσ : A × A → Finset A := fun p => ({σ p.1, σ p.2} : Finset A)
    have hprod :
        S'.product (T.map σ.toEmbedding) =
          (S.product T).map (σ.toEmbedding.prodMap σ.toEmbedding) := by
      simpa [hS'] using
        (Finset.prodMap_map_product (f := σ.toEmbedding) (g := σ.toEmbedding)
          (s := S) (t := T)).symm
    have hpairσ : pair ∘ Prod.map (fun x => σ x) (fun x => σ x) = pairσ := by
      funext p
      cases p
      rfl
    have hpair_map : (Finset.mapEmbedding σ.toEmbedding) ∘ pair = pairσ := by
      funext p
      cases p
      simp [pair, pairσ, Finset.mapEmbedding_apply]
    calc
      pluralityWithRunoffPairs (permuteCandidates P σ)
          = (S'.product (T.map σ.toEmbedding)).image pair := by
              simp [pluralityWithRunoffPairs, S', hS'card, hT', pair, T]
      _ = ((S.product T).map (σ.toEmbedding.prodMap σ.toEmbedding)).image pair := by
              simpa using congrArg (fun s => s.image pair) hprod
      _ = (S.product T).image (pair ∘ (σ.toEmbedding.prodMap σ.toEmbedding)) := by
              simp [Finset.map_eq_image, Finset.image_image]
      _ = (S.product T).image pairσ := by
              simp [hpairσ]
      _ = (pluralityWithRunoffPairs P).map (Finset.mapEmbedding σ.toEmbedding).toEmbedding := by
              symm
              simp [pluralityWithRunoffPairs, S, hS, pair, pairσ, T,
                Finset.map_eq_image, Finset.image_image, hpair_map]

lemma pair_mem_pluralityWithRunoffPairs_permuteCandidates_iff
    {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    (P : Profile V A) (σ : Equiv.Perm A) (c y : A) :
    ({c, y} : Finset A) ∈ pluralityWithRunoffPairs (permuteCandidates P σ) ↔
      ({σ.symm c, σ.symm y} : Finset A) ∈ pluralityWithRunoffPairs P := by
  classical
  -- Use `finsetCongr` to treat `mapEmbedding σ` as an equivalence on finsets and apply `mem_map_equiv`.
  have hmap :
      pluralityWithRunoffPairs (permuteCandidates P σ) =
        (pluralityWithRunoffPairs P).map (σ.finsetCongr.toEmbedding) := by
    simpa [Equiv.finsetCongr_toEmbedding] using
      (pluralityWithRunoffPairs_permuteCandidates (P := P) (σ := σ))
  constructor
  · intro h
    have h' := h
    rw [hmap] at h'
    have h'' :
        σ.finsetCongr.symm ({c, y} : Finset A) ∈ pluralityWithRunoffPairs P := by
      simpa using
        (Finset.mem_map_equiv (s := pluralityWithRunoffPairs P) (f := σ.finsetCongr)
          (b := ({c, y} : Finset A))).1 h'
    simpa [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, map_pair] using h''
  · intro h
    have h' :
        σ.finsetCongr.symm ({c, y} : Finset A) ∈ pluralityWithRunoffPairs P := by
      simpa [Equiv.finsetCongr_symm, Equiv.finsetCongr_apply, map_pair] using h
    have h'' :
        ({c, y} : Finset A) ∈
          (pluralityWithRunoffPairs P).map (σ.finsetCongr.toEmbedding) := by
      exact
        (Finset.mem_map_equiv (s := pluralityWithRunoffPairs P) (f := σ.finsetCongr)
          (b := ({c, y} : Finset A))).2 h'
    simpa [hmap] using h''

lemma mem_pluralityWithRunoff_permuteCandidates_iff {V A : Type} [Fintype V] [Fintype A]
    [DecidableEq A] (P : Profile V A) (σ : Equiv.Perm A) (c : A) :
    c ∈ pluralityWithRunoff (permuteCandidates P σ) ↔
      σ.symm c ∈ pluralityWithRunoff P := by
  classical
  let := Classical.decEq A
  by_cases hcard : Fintype.card A ≤ 1
  · simp [pluralityWithRunoff, hcard]
  · constructor
    · intro hc
      simp [pluralityWithRunoff, hcard] at hc
      rcases hc with ⟨y, hpair, hmargin⟩
      have hpair' :
          ({σ.symm c, σ.symm y} : Finset A) ∈ pluralityWithRunoffPairs P :=
        (pair_mem_pluralityWithRunoffPairs_permuteCandidates_iff (P := P) (σ := σ)
          (c := c) (y := y)).1 hpair
      have hmargin' :
          0 ≤ margin P (σ.symm c) (σ.symm y) := by
        simpa [margin_permuteCandidates] using hmargin
      simp [pluralityWithRunoff, hcard]
      exact ⟨σ.symm y, hpair', hmargin'⟩
    · intro hc
      simp [pluralityWithRunoff, hcard] at hc
      rcases hc with ⟨y, hpair, hmargin⟩
      have hpair' :
          ({c, σ y} : Finset A) ∈ pluralityWithRunoffPairs (permuteCandidates P σ) :=
        (pair_mem_pluralityWithRunoffPairs_permuteCandidates_iff (P := P) (σ := σ)
          (c := c) (y := σ y)).2 (by simpa using hpair)
      have hmargin' :
          0 ≤ margin (permuteCandidates P σ) c (σ y) := by
        simpa [margin_permuteCandidates] using hmargin
      simp [pluralityWithRunoff, hcard]
      exact ⟨σ y, hpair', hmargin'⟩

theorem plurality_with_runoff_neutral : Neutrality pluralityWithRunoff := by
  intro V A _ _ P σ
  classical
  apply Finset.ext
  intro c
  constructor
  · intro hc
    have : σ.symm c ∈ pluralityWithRunoff P := by
      simpa [permuteWinners] using hc
    simpa [mem_pluralityWithRunoff_permuteCandidates_iff (P := P) (σ := σ)] using this
  · intro hc
    have hc' :
        σ.symm c ∈ pluralityWithRunoff P := by
      simpa [mem_pluralityWithRunoff_permuteCandidates_iff (P := P) (σ := σ)] using hc
    have : c ∈ permuteWinners σ (pluralityWithRunoff P) := by
      simpa [permuteWinners] using hc'
    simpa [permuteWinners] using this

end SocialChoice
