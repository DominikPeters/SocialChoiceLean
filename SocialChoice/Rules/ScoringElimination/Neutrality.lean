import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Union
import SocialChoice.Axioms.Neutrality
import SocialChoice.Rules.ScoringElimination.Basic
import SocialChoice.Rules.ScoringRules.Neutrality

namespace SocialChoice

open Finset
open scoped BigOperators

lemma relabelProfile_perm {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) :
    relabelProfile P σ = permuteCandidates P σ := by
  rfl

lemma rank_relabelBallotEquiv_symm {A B : Type} [Fintype A] [Fintype B] (r : LinearOrder A)
    (e : A ≃ B) (c : A) :
    rank (relabelBallotEquiv r e) (e c) = rank r c := by
  classical
  have hlt :
      ∀ {a b : B}, (relabelBallotEquiv r e).lt a b ↔ r.lt (e.symm a) (e.symm b) := by
    intro a b
    rfl
  have hcard :
      (Finset.univ.filter (fun d : B => r.lt (e.symm d) c)).card =
        (Finset.univ.filter (fun d : A => r.lt d c)).card := by
    refine Finset.card_bij
      (s := Finset.univ.filter (fun d : B => r.lt (e.symm d) c))
      (t := Finset.univ.filter (fun d : A => r.lt d c))
      (i := fun a _ => e.symm a) ?_ ?_ ?_
    · intro a ha
      have ha' : r.lt (e.symm a) c := (Finset.mem_filter.mp ha).2
      exact Finset.mem_filter.mpr ⟨by simp, ha'⟩
    · intro a1 ha1 a2 ha2 h
      exact e.symm.injective h
    · intro b hb
      refine ⟨e b, ?_, by simp⟩
      have hb' : r.lt b c := (Finset.mem_filter.mp hb).2
      exact Finset.mem_filter.mpr ⟨by simp, by simpa using hb'⟩
  simpa [rank, hlt] using hcard

lemma scoreCandidate_relabelProfile {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
    (P : Profile V A) (e : A ≃ B) (score : Nat → Int) (c : A) :
    scoreCandidate (relabelProfile P e) score (e c) = scoreCandidate P score c := by
  classical
  unfold scoreCandidate
  refine Finset.sum_congr rfl ?_
  intro v hv
  have hrank :
      rank (relabelBallotEquiv (P.pref v) e) (e c) = rank (P.pref v) c := by
    simpa using (rank_relabelBallotEquiv_symm (r := P.pref v) (e := e) (c := c))
  simp [relabelProfile, hrank]

lemma scoreCandidate_relabelProfile_symm {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
    (P : Profile V A) (e : A ≃ B) (score : Nat → Int) (c : B) :
    scoreCandidate (relabelProfile P e) score c =
      scoreCandidate P score (e.symm c) := by
  classical
  have h := scoreCandidate_relabelProfile (P := P) (e := e) (score := score) (c := e.symm c)
  simpa using h

lemma mem_relabelWinners {A B : Type} [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (s : Finset A) (b : B) :
    b ∈ s.map e.toEmbedding ↔ e.symm b ∈ s := by
  classical
  constructor
  · intro hb
    rcases Finset.mem_map.mp hb with ⟨a, ha, rfl⟩
    simpa using ha
  · intro hb
    exact Finset.mem_map.mpr ⟨e.symm b, hb, by simp⟩

lemma lowestScoring_relabelProfile {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (P : Profile V A) (e : A ≃ B) (score : Nat → Int) :
    lowestScoring (relabelProfile P e) score = (lowestScoring P score).map e.toEmbedding := by
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  ·
    have hB : (Finset.univ : Finset B).Nonempty := by
      rcases hA with ⟨a, ha⟩
      exact ⟨e a, by simp⟩
    -- Compare score sets.
    let scoreSetA : Finset Int :=
      (Finset.univ.image (fun c => scoreCandidate P score c))
    let scoreSetB : Finset Int :=
      (Finset.univ.image (fun c => scoreCandidate (relabelProfile P e) score c))
    have hscoreSet :
        scoreSetB = scoreSetA := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨c, _hc, rfl⟩
        refine Finset.mem_image.mpr ?_
        refine ⟨e.symm c, by simp, ?_⟩
        simpa using
          (scoreCandidate_relabelProfile_symm (P := P) (e := e) (score := score) (c := c)).symm
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨c, _hc, rfl⟩
        refine Finset.mem_image.mpr ?_
        refine ⟨e c, by simp, ?_⟩
        simpa using (scoreCandidate_relabelProfile (P := P) (e := e) (score := score) (c := c))
    -- Compare mins via the same score set.
    let minScore : Int := scoreSetA.min' (by
      simpa [scoreSetA, Finset.Nonempty] using hA.image (fun c => scoreCandidate P score c))
    have hminScore :
        scoreSetB.min' (by
          simpa [scoreSetB, Finset.Nonempty] using hB.image
            (fun c => scoreCandidate (relabelProfile P e) score c)) = minScore := by
      simp [scoreSetA, scoreSetB, minScore, hscoreSet]
    -- Set equality via membership characterization.
    apply Finset.ext
    intro b
    constructor
    · intro hb
      have hb' :
          scoreCandidate (relabelProfile P e) score b = minScore := by
        simpa [lowestScoring, hB, scoreSetB, minScore, hminScore] using hb
      have hb'' :
          scoreCandidate P score (e.symm b) = minScore := by
        calc
          scoreCandidate P score (e.symm b) =
              scoreCandidate (relabelProfile P e) score b := by
                symm
                simpa using
                  (scoreCandidate_relabelProfile_symm (P := P) (e := e) (score := score) (c := b))
          _ = minScore := hb'
      have hb0 : e.symm b ∈ lowestScoring P score := by
        simpa [lowestScoring, hA, scoreSetA, minScore] using hb''
      exact (mem_relabelWinners e (lowestScoring P score) b).2 hb0
    · intro hb
      have hb0 : e.symm b ∈ lowestScoring P score :=
        (mem_relabelWinners e (lowestScoring P score) b).1 hb
      have hb' :
          scoreCandidate P score (e.symm b) = minScore := by
        simpa [lowestScoring, hA, scoreSetA, minScore] using hb0
      have hb'' :
          scoreCandidate (relabelProfile P e) score b = minScore := by
        calc
          scoreCandidate (relabelProfile P e) score b =
              scoreCandidate P score (e.symm b) := by
                simpa using
                  (scoreCandidate_relabelProfile_symm (P := P) (e := e) (score := score) (c := b))
          _ = minScore := hb'
      simpa [lowestScoring, hB, scoreSetB, minScore, hminScore] using hb''
  ·
    -- Empty agenda.
    have hB : ¬ (Finset.univ : Finset B).Nonempty := by
      intro hB
      apply hA
      rcases hB with ⟨b, hb⟩
      exact ⟨e.symm b, by simp⟩
    simp [lowestScoring, hA, hB]

@[implicit_reducible] def subtypeEquiv {A B : Type} (e : A ≃ B) (a : A) :
    {x : A // x ≠ a} ≃ {y : B // y ≠ e a} := by
  classical
  refine
    { toFun := fun x => ⟨e x, ?_⟩
      invFun := fun y => ⟨e.symm y, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro hEq
    exact x.property (by simpa using congrArg e.symm hEq)
  · intro hEq
    have hEq' : e (e.symm y) = e a := by
      simpa using congrArg e hEq
    exact y.property (by simpa using hEq')
  · intro x
    ext
    simp
  · intro y
    ext
    simp

lemma relabelProfile_restrictProfile {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (P : Profile V A) (e : A ≃ B) (a : A) :
    relabelProfile (restrictProfile P a) (subtypeEquiv e a) =
      restrictProfile (relabelProfile P e) (e a) := by
  ext v
  rfl

lemma liftFinset_map_subtypeEquiv {A B : Type} [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (a : A) (s : Finset {x : A // x ≠ a}) :
    liftFinset (s.map (subtypeEquiv e a).toEmbedding) =
      (liftFinset s).map e.toEmbedding := by
  classical
  apply Finset.ext
  intro b
  constructor
  · intro hb
    rcases Finset.mem_image.mp hb with ⟨x, hx, rfl⟩
    rcases Finset.mem_map.mp hx with ⟨y, hy, hxy⟩
    have hb' : (e y : B) = (x : B) := by
      exact congrArg Subtype.val hxy
    refine Finset.mem_map.mpr ?_
    refine ⟨y, ?_, hb'⟩
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  · intro hb
    rcases Finset.mem_map.mp hb with ⟨a', ha', hba⟩
    rcases Finset.mem_image.mp ha' with ⟨y, hy, rfl⟩
    refine Finset.mem_image.mpr ?_
    refine ⟨(subtypeEquiv e a y), ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨y, hy, rfl⟩
    · exact hba

theorem scoringEliminationAux_equiv_card (score : Nat → Nat → Int) :
    ∀ n, ∀ {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
      [DecidableEq A] [DecidableEq B],
      Fintype.card A = n →
      (P : Profile V A) → (e : A ≃ B) →
      scoringEliminationAux score B (relabelProfile P e) =
        (scoringEliminationAux score A P).map e.toEmbedding := by
  intro n
  induction n with
  | zero =>
      intro V A B _ _ _ _ _ hcard P e
      have hcard_le : Fintype.card A ≤ 1 := by simp [hcard]
      have hcard_le' : Fintype.card B ≤ 1 := by
        simpa [Fintype.card_congr e] using hcard_le
      simp [scoringEliminationAux, hcard_le, hcard_le', relabelProfile]
  | succ n ih =>
      intro V A B _ _ _ _ _ hcard P e
      by_cases hcard_le : Fintype.card A ≤ 1
      ·
        have hcard_le' : Fintype.card B ≤ 1 := by
          simpa [Fintype.card_congr e] using hcard_le
        simp [scoringEliminationAux, hcard_le, hcard_le', relabelProfile]
      ·
        have hcard_le' : ¬ Fintype.card B ≤ 1 := by
          intro hle
          apply hcard_le
          have hle' : Fintype.card A ≤ 1 := by
            simpa [Fintype.card_congr e] using hle
          exact hle'
        -- Unfold the head of the recursion on both sides.
        have hA :=
          scoringEliminationAux_eq_biUnion_of_not_card_le_one
            (score := score) (P := P) hcard_le
        have hB :=
          scoringEliminationAux_eq_biUnion_of_not_card_le_one
            (score := score) (P := relabelProfile P e) hcard_le'
        -- Prepare score vectors and lowest-scoring sets.
        let m := Fintype.card A
        let scoreVec : Nat → Int := fun r => score m r
        have hL :
            lowestScoring (relabelProfile P e) scoreVec =
              (lowestScoring P scoreVec).map e.toEmbedding := by
          simpa [m, scoreVec] using
            (lowestScoring_relabelProfile (P := P) (e := e) (score := scoreVec))
        -- Rewrite and compare via membership.
        apply Finset.ext
        intro b
        constructor
        · intro hb
          have hb' : b ∈
              (lowestScoring (relabelProfile P e) scoreVec).biUnion
                (fun c => liftFinset
                  (scoringEliminationAux score _ (restrictProfile (relabelProfile P e) c))) := by
            simpa [hB, m, scoreVec, Fintype.card_congr e] using hb
          rcases Finset.mem_biUnion.mp hb' with ⟨c, hc, hmem⟩
          have hc' : e.symm c ∈ lowestScoring P scoreVec := by
            have hc'' : c ∈ (lowestScoring P scoreVec).map e.toEmbedding := by
              simpa [hL] using hc
            exact (mem_relabelWinners e (lowestScoring P scoreVec) c).1 hc''
          -- Use IH on the restricted profile.
          have hcard_sub :
              Fintype.card {x : A // x ≠ e.symm c} = n := by
            have hcardA : Fintype.card A = Nat.succ n := hcard
            have hsub := card_subtype_ne_eq (e.symm c)
            -- hsub : card subtype = card A - 1
            have hsub' : Fintype.card {x : A // x ≠ e.symm c} = Nat.succ n - 1 := by
              rw [hcardA] at hsub
              exact hsub
            -- simplify Nat.succ n - 1 to n
            simpa using hsub'
          have hrec0 :=
            ih (A := {x : A // x ≠ e.symm c})
              (B := {y : B // y ≠ e (e.symm c)})
              (P := restrictProfile P (e.symm c))
              (e := subtypeEquiv e (e.symm c))
              (by simpa using hcard_sub)
          have hrec := hrec0
          simp at hrec
          have hc_eq : c = e (e.symm c) := by simp
          -- Map membership through the induction hypothesis.
          have hmem' := hmem
          rw [hc_eq] at hmem'
          rw [← relabelProfile_restrictProfile (P := P) (e := e) (a := e.symm c)] at hmem'
          -- Transfer using the IH and liftFinset map.
          have hmem'' :
              b ∈ (liftFinset
                (scoringEliminationAux score _ (restrictProfile P (e.symm c)))).map e.toEmbedding := by
            -- use IH to rewrite
            have hmem0 := hmem'
            -- rewrite with hrec inside the lift
            rw [hrec] at hmem0
            simpa [liftFinset_map_subtypeEquiv (e := e) (a := e.symm c)] using hmem0
          have : b ∈
              ((lowestScoring P scoreVec).biUnion
                (fun c => liftFinset
                  (scoringEliminationAux score _ (restrictProfile P c)))).map e.toEmbedding := by
            refine Finset.mem_map.mpr ?_
            refine ⟨e.symm b, ?_, by simp⟩
            refine Finset.mem_biUnion.mpr ?_
            refine ⟨e.symm c, hc', ?_⟩
            simpa using (mem_relabelWinners e (liftFinset
              (scoringEliminationAux score _ (restrictProfile P (e.symm c)))) b).1 hmem''
          simpa [hA, m, scoreVec] using this
        · intro hb
          have hb' :
              b ∈ ((lowestScoring P scoreVec).biUnion
                (fun c => liftFinset
                  (scoringEliminationAux score _ (restrictProfile P c)))).map e.toEmbedding := by
            simpa [hA, m, scoreVec] using hb
          rcases Finset.mem_map.mp hb' with ⟨a, ha, rfl⟩
          rcases Finset.mem_biUnion.mp ha with ⟨c, hc, hmem⟩
          have hc' :
              e c ∈ lowestScoring (relabelProfile P e) scoreVec := by
            have hc'' : e c ∈ (lowestScoring P scoreVec).map e.toEmbedding := by
              exact Finset.mem_map.mpr ⟨c, hc, by simp⟩
            simpa [hL] using hc''
          -- IH on restricted profile.
          have hcard_sub :
              Fintype.card {x : A // x ≠ c} = n := by
            have hcardA : Fintype.card A = Nat.succ n := hcard
            have hsub := card_subtype_ne_eq c
            have hsub' : Fintype.card {x : A // x ≠ c} = Nat.succ n - 1 := by
              rw [hcardA] at hsub
              exact hsub
            simpa using hsub'
          have hrec :=
            ih (A := {x : A // x ≠ c})
              (B := {y : B // y ≠ e c})
              (P := restrictProfile P c)
              (e := subtypeEquiv e c)
              (by simpa using hcard_sub)
          have hmem' :
              e a ∈ liftFinset
                (Finset.map (subtypeEquiv e c).toEmbedding
                  (scoringEliminationAux score _ (restrictProfile P c))) := by
            rw [liftFinset_map_subtypeEquiv (e := e) (a := c)]
            exact Finset.mem_map.mpr ⟨a, hmem, by simp⟩
          have hmem'' :
              e a ∈ liftFinset
                (scoringEliminationAux score _ (restrictProfile (relabelProfile P e) (e c))) := by
            -- rewrite via IH
            have hmem0 := hmem'
            rw [← hrec] at hmem0
            rw [relabelProfile_restrictProfile (P := P) (e := e) (a := c)] at hmem0
            exact hmem0
          have : e a ∈
              (lowestScoring (relabelProfile P e) scoreVec).biUnion
                (fun c => liftFinset
                  (scoringEliminationAux score _ (restrictProfile (relabelProfile P e) c))) := by
            exact Finset.mem_biUnion.mpr ⟨e c, hc', hmem''⟩
          simpa [hB, m, scoreVec, Fintype.card_congr e] using this

theorem scoringEliminationAux_equiv (score : Nat → Nat → Int)
    {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (P : Profile V A) (e : A ≃ B) :
    scoringEliminationAux score B (relabelProfile P e) =
      (scoringEliminationAux score A P).map e.toEmbedding := by
  classical
  have hcard : Fintype.card A = Fintype.card A := rfl
  simpa using (scoringEliminationAux_equiv_card (score := score) (n := Fintype.card A)
    (P := P) (e := e) hcard)

theorem scoringEliminationRule_neutral (score : Nat → Nat → Int) :
    Neutrality (scoringEliminationRule score) := by
  intro V A _ _ P σ
  classical
  -- Specialize equivariance to permutations.
  have h :=
    (scoringEliminationAux_equiv (score := score) (P := P) (e := σ)).symm
  simpa [scoringEliminationRule, permuteWinners, relabelProfile_perm] using h

end SocialChoice
