import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import SocialChoice.Axioms.Majority
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.Defs
import SocialChoice.Rules.ScoringElimination.InstantRunoffVoting.CondorcetLoser

namespace SocialChoice

open Finset

variable {V A : Type} [Fintype V] [Fintype A]

lemma strictMajority_of_subset {S T : Finset V} (hS : StrictMajority S) (hsub : S ⊆ T) :
    StrictMajority T := by
  unfold StrictMajority at *
  have hcard : S.card ≤ T.card := Finset.card_le_card hsub
  have hmul : 2 * S.card ≤ 2 * T.card := Nat.mul_le_mul_left 2 hcard
  exact lt_of_lt_of_le hS hmul

lemma votersTop_subset_of_singleton (P : Profile V A) (S : Finset V) (c : A)
    (h : ∀ v ∈ S, ∀ a ∈ ({c} : Finset A), ∀ b ∉ ({c} : Finset A), Prefers P v a b) :
    S ⊆ votersTop P c := by
  classical
  intro v hv
  have htop : TopRank P v c := by
    intro d hd
    have hpref := h v hv c (by simp) d (by simp [hd])
    simpa using hpref
  exact Finset.mem_filter.mpr ⟨by simp, htop⟩

lemma votersTop_card_lt_of_strictMajority (P : Profile V A) {c d : A}
    (hmaj : StrictMajority (votersTop P c)) (hcd : d ≠ c) :
    (votersTop P d).card < (votersTop P c).card := by
  classical
  have hdisj : Disjoint (votersTop P c) (votersTop P d) := by
    refine disjoint_left.2 ?_
    intro v hv1 hv2
    have hc : TopRank P v c := (mem_filter.mp hv1).2
    have hd : TopRank P v d := (mem_filter.mp hv2).2
    have hcd' : Prefers P v c d := hc d hcd
    have hdc : Prefers P v d c := hd c (by simpa [eq_comm] using hcd)
    let _ : Preorder A := (P.pref v).toPreorder
    exact (lt_asymm hcd') hdc
  have hsubset : votersTop P c ∪ votersTop P d ⊆ (Finset.univ : Finset V) := by
    intro v _
    exact mem_univ v
  have hcard : (votersTop P c ∪ votersTop P d).card ≤ (Finset.univ : Finset V).card :=
    Finset.card_le_card hsubset
  have hsum : (votersTop P c).card + (votersTop P d).card ≤ Fintype.card V := by
    have hcard' :
        (votersTop P c ∪ votersTop P d).card =
          (votersTop P c).card + (votersTop P d).card := by
      simpa using
        (Finset.card_union_of_disjoint (s := votersTop P c) (t := votersTop P d) hdisj)
    have hcard'' :
        (votersTop P c).card + (votersTop P d).card ≤ (Finset.univ : Finset V).card := by
      simpa [hcard'] using hcard
    simpa [Finset.card_univ] using hcard''
  have hmaj' : Fintype.card V < 2 * (votersTop P c).card := by
    simpa [StrictMajority] using hmaj
  have hlt' :
      (votersTop P c).card + (votersTop P d).card < 2 * (votersTop P c).card :=
    lt_of_le_of_lt hsum hmaj'
  have hlt'' :
      (votersTop P c).card + (votersTop P d).card <
        (votersTop P c).card + (votersTop P c).card := by
    simpa [Nat.two_mul] using hlt'
  exact Nat.lt_of_add_lt_add_left hlt''

lemma not_lowestScoring_of_strictMajority_top
    [DecidableEq A] (P : Profile V A) (c : A)
    (hmaj : StrictMajority (votersTop P c)) (hcard : 1 < Fintype.card A) :
    c ∉ lowestScoring P (fun r => pluralityScore (Fintype.card A) r) := by
  classical
  rcases Fintype.exists_ne_of_one_lt_card hcard c with ⟨d, hdc⟩
  have hlt_card : (votersTop P d).card < (votersTop P c).card :=
    votersTop_card_lt_of_strictMajority (P := P) (hmaj := hmaj) hdc
  have hlt_int : ((votersTop P d).card : Int) < (votersTop P c).card := by
    exact_mod_cast hlt_card
  have hd :
      scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) d =
        (votersTop P d).card := by
    simpa [pluralityScore] using (pluralityScore_eq_votersTop_card (P := P) (c := d))
  have hc :
      scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) c =
        (votersTop P c).card := by
    simpa [pluralityScore] using (pluralityScore_eq_votersTop_card (P := P) (c := c))
  have hlt_score :
      scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) d <
        scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) c := by
    simpa [hd, hc] using hlt_int
  intro hcL
  have hle :
      scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) c ≤
        scoreCandidate P (fun r => pluralityScore (Fintype.card A) r) d :=
    scoreCandidate_le_of_mem_lowestScoring (P := P)
      (score := fun r => pluralityScore (Fintype.card A) r) (c := c) (e := d) hcL
  exact (not_lt_of_ge hle) hlt_score

theorem irv_mutual_majority_criterion : MutualMajorityCriterion instantRunoffVoting := by
  intro V A _ _ P S T hmaj hTne hpref
  classical
  let : DecidableEq A := Classical.decEq A
  change scoringEliminationAux pluralityScore A P ⊆ T
  set n : Nat := Fintype.card A
  let Motive : Nat → Prop := fun k =>
    ∀ {A : Type} [Fintype A] [DecidableEq A],
      Fintype.card A = k →
        ∀ {V : Type} [Fintype V]
          (P : Profile V A) (S : Finset V) (T : Finset A),
          StrictMajority S →
          T.Nonempty →
          (∀ v ∈ S, ∀ a ∈ T, ∀ b ∉ T, Prefers P v a b) →
          scoringEliminationAux pluralityScore A P ⊆ T
  have hStrong : Motive n := by
    classical
    refine Nat.strongRecOn (motive := Motive) n (fun k ih => ?_)
    intro A _ _ hcard V _ P S T hmaj hTne hpref
    by_cases hle : Fintype.card A ≤ 1
    · have hsub : Subsingleton A := (Fintype.card_le_one_iff_subsingleton).1 hle
      intro x hx
      rcases hTne with ⟨t, ht⟩
      have hx' : x = t := Subsingleton.elim _ _
      simpa [hx'] using ht
    · have haux :=
        scoringEliminationAux_eq_biUnion_of_not_card_le_one
          (score := pluralityScore) (P := P) (hcard := hle)
      let m := Fintype.card A
      let scoreVec : Nat → Int := fun r => pluralityScore m r
      let L : Finset A := lowestScoring P scoreVec
      have haux' :
          scoringEliminationAux pluralityScore A P =
            L.biUnion (fun c => liftFinset
              (scoringEliminationAux pluralityScore _ (restrictProfile P c))) := by
        simpa [m, scoreVec, L] using haux
      intro x hx
      have hx' : x ∈
          L.biUnion (fun c => liftFinset
            (scoringEliminationAux pluralityScore _ (restrictProfile P c))) := by
        simpa [haux'] using hx
      rcases Finset.mem_biUnion.mp hx' with ⟨c, hcL, hxbranch⟩
      rcases (mem_liftFinset_iff_subtype
        (s := scoringEliminationAux pluralityScore {x : A // x ≠ c} (restrictProfile P c))
        (x := x)).1 hxbranch with ⟨hxc, hxsub⟩
      let T' : Finset {x : A // x ≠ c} := Finset.subtype (fun x => x ≠ c) T
      by_cases hcT : c ∈ T
      · by_cases hcardT : T.card = 1
        · have hT_eq : T = {c} := by
            rcases (Finset.card_eq_one.mp hcardT) with ⟨a, ha⟩
            have hac : c = a := by
              have : c ∈ ({a} : Finset A) := by simpa [ha] using hcT
              simpa using this
            simp [ha, hac]
          have hSsub : S ⊆ votersTop P c := by
            apply votersTop_subset_of_singleton (P := P) (S := S) (c := c)
            simpa [hT_eq] using hpref
          have hmaj_top : StrictMajority (votersTop P c) :=
            strictMajority_of_subset hmaj hSsub
          have hcardA : 1 < Fintype.card A := Nat.lt_of_not_ge hle
          have hnot_lowest : c ∉ L := by
            have hnot :=
              not_lowestScoring_of_strictMajority_top (P := P) (c := c) hmaj_top hcardA
            simpa [L, scoreVec, m] using hnot
          exact (False.elim (hnot_lowest hcL))
        · have hpos : 0 < T.card := Finset.card_pos.mpr hTne
          have hge : 1 ≤ T.card := Nat.succ_le_iff.mp hpos
          have hlt : 1 < T.card := lt_of_le_of_ne hge (Ne.symm hcardT)
          rcases Finset.exists_mem_ne hlt c with ⟨t, htT, htne⟩
          have hT'ne : T'.Nonempty := by
            refine ⟨⟨t, htne⟩, ?_⟩
            exact Finset.mem_subtype.mpr htT
          have hpref' :
              ∀ v ∈ S, ∀ a ∈ T', ∀ b ∉ T',
                Prefers (restrictProfile P c) v a b := by
            intro v hv a ha b hb
            have ha' : (a : A) ∈ T := (Finset.mem_subtype.mp ha)
            have hb' : (b : A) ∉ T := by
              intro hbT
              exact hb (Finset.mem_subtype.mpr hbT)
            have hpref' := hpref v hv a ha' b hb'
            simpa using hpref'
          have hltcard : Fintype.card {x : A // x ≠ c} < k := by
            have hltcard' := card_restrict_lt (A := A) c
            simpa [hcard] using hltcard'
          have hrec :
              scoringEliminationAux pluralityScore {x : A // x ≠ c} (restrictProfile P c) ⊆ T' := by
            have := ih (m := Fintype.card {x : A // x ≠ c}) hltcard
              (A := {x : A // x ≠ c}) (by rfl) (V := V) (P := restrictProfile P c)
              (S := S) (T := T') hmaj hT'ne hpref'
            simpa using this
          have hxT' : (⟨x, hxc⟩ : {x : A // x ≠ c}) ∈ T' := hrec hxsub
          exact (Finset.mem_subtype.mp hxT')
      · rcases hTne with ⟨t, htT⟩
        have htne : t ≠ c := by
          intro hEq
          subst hEq
          exact hcT htT
        have hT'ne : T'.Nonempty := by
          refine ⟨⟨t, htne⟩, ?_⟩
          exact Finset.mem_subtype.mpr htT
        have hpref' :
            ∀ v ∈ S, ∀ a ∈ T', ∀ b ∉ T',
              Prefers (restrictProfile P c) v a b := by
          intro v hv a ha b hb
          have ha' : (a : A) ∈ T := (Finset.mem_subtype.mp ha)
          have hb' : (b : A) ∉ T := by
            intro hbT
            exact hb (Finset.mem_subtype.mpr hbT)
          have hpref' := hpref v hv a ha' b hb'
          simpa using hpref'
        have hltcard : Fintype.card {x : A // x ≠ c} < k := by
          have hltcard' := card_restrict_lt (A := A) c
          simpa [hcard] using hltcard'
        have hrec :
            scoringEliminationAux pluralityScore {x : A // x ≠ c} (restrictProfile P c) ⊆ T' := by
          have := ih (m := Fintype.card {x : A // x ≠ c}) hltcard
            (A := {x : A // x ≠ c}) (by rfl) (V := V) (P := restrictProfile P c)
            (S := S) (T := T') hmaj hT'ne hpref'
          simpa using this
        have hxT' : (⟨x, hxc⟩ : {x : A // x ≠ c}) ∈ T' := hrec hxsub
        exact (Finset.mem_subtype.mp hxT')
  have := hStrong (A := A) (by rfl) (V := V) (P := P) (S := S) (T := T) hmaj hTne hpref
  simpa [Motive, n] using this

end SocialChoice
