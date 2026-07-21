import Mathlib.Algebra.Order.BigOperators.Group.Finset
import SocialChoice.Axioms.Neutrality
import SocialChoice.Rules.Nanson.Defs

namespace SocialChoice

open Finset
open scoped BigOperators

lemma mem_map_equiv {A B : Type} [DecidableEq A] [DecidableEq B]
    (e : A ≃ B) (s : Finset A) (b : B) :
    b ∈ s.map e.toEmbedding ↔ e.symm b ∈ s := by
  classical
  constructor
  · intro hb
    rcases Finset.mem_map.mp hb with ⟨a, ha, hab⟩
    have ha' : a = e.symm b := by
      simpa using congrArg e.symm hab
    simpa [ha'] using ha
  · intro hb
    exact Finset.mem_map.mpr ⟨e.symm b, hb, by simp⟩

lemma c2BordaScore_relabelProfile {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
    (P : Profile V A) (e : A ≃ B) (x : A) :
    c2BordaScore (relabelProfile P e) (e x) = c2BordaScore P x := by
  classical
  -- Rewrite margins under relabeling, then change variables in the sum using `e`.
  unfold c2BordaScore
  have hsum :
      (∑ y : B, margin P x (e.symm y)) = ∑ y : A, margin P x y := by
    simpa using
      (Fintype.sum_equiv e.symm
        (fun y : B => margin P x (e.symm y))
        (fun y : A => margin P x y) (by intro y; rfl))
  simp [margin_relabelProfile, hsum]

lemma c2BordaScore_relabelProfile_symm {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
    (P : Profile V A) (e : A ≃ B) (x : B) :
    c2BordaScore (relabelProfile P e) x = c2BordaScore P (e.symm x) := by
  classical
  simpa using (c2BordaScore_relabelProfile (P := P) (e := e) (x := e.symm x))

lemma nansonAux_relabelProfile {V A B : Type} [Fintype V]
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (n : Nat) (P : Profile V A) (e : A ≃ B) :
    (nansonAux (V := V) n A P).map e.toEmbedding =
      nansonAux (V := V) n B (relabelProfile P e) := by
  classical
  induction n generalizing A B with
  | zero =>
      ext b
      simp [nansonAux]
  | succ n ih =>
      -- Set up the score functions on `A` and `B`.
      let scoreA : A → Int := fun a => c2BordaScore P a
      let PB : Profile V B := relabelProfile P e
      let scoreB : B → Int := fun b => c2BordaScore PB b
      have hscore : ∀ a : A, scoreB (e a) = scoreA a := by
        intro a
        simpa [scoreA, scoreB, PB] using (c2BordaScore_relabelProfile (P := P) (e := e) (x := a))
      have hall_iff : (∀ a : A, scoreA a = 0) ↔ ∀ b : B, scoreB b = 0 := by
        constructor
        · intro hall b
          have hA0 : scoreA (e.symm b) = 0 := hall (e.symm b)
          have hB : scoreB b = scoreA (e.symm b) := by
            simpa [scoreA, scoreB, PB] using
              (c2BordaScore_relabelProfile_symm (P := P) (e := e) (x := b))
          simpa [hB] using hA0
        · intro hall a
          have : scoreB (e a) = 0 := hall (e a)
          simpa [hscore a] using this
      have hsurv_map :
          (Finset.univ.filter (fun a : A => scoreA a > 0)).map e.toEmbedding =
            (Finset.univ.filter (fun b : B => scoreB b > 0)) := by
        ext b
        simp [scoreA, scoreB, PB, c2BordaScore_relabelProfile_symm]
      -- Split cases exactly as in `nansonAux`.
      by_cases hallA : ∀ a : A, scoreA a = 0
      · have hallB : ∀ b : B, scoreB b = 0 := (hall_iff.mp hallA)
        ext b
        simp [nansonAux, scoreA, scoreB, PB, hallA, hallB]
      · have hallB : ¬ ∀ b : B, scoreB b = 0 := by
          intro hallB
          exact hallA ((hall_iff).2 hallB)
        by_cases hsurvA : (Finset.univ.filter (fun a : A => scoreA a > 0)).Nonempty
        · have hsurvB : (Finset.univ.filter (fun b : B => scoreB b > 0)).Nonempty := by
            simpa [hsurv_map] using hsurvA.map (f := e.toEmbedding)
          -- Define the restricted profiles and the induced equivalence between survivor types.
          let pA : A → Prop := fun a => scoreA a > 0
          let pB : B → Prop := fun b => scoreB b > 0
          letI : DecidableEq {a : A // pA a} := by classical infer_instance
          letI : DecidableEq {b : B // pB b} := by classical infer_instance
          let PA' : Profile V {a : A // pA a} := restrictCandidates P pA
          let PB' : Profile V {b : B // pB b} := restrictCandidates PB pB
          have hp : ∀ a : A, pB (e a) ↔ pA a := by
            intro a
            simp [pA, pB, hscore a]
          let eSub : {a : A // pA a} ≃ {b : B // pB b} :=
            { toFun := fun x => ⟨e x.1, (hp x.1).2 x.2⟩
              invFun := fun y => ⟨e.symm y.1, (hp (e.symm y.1)).1 (by simpa using y.2)⟩
              left_inv := by intro x; ext; simp
              right_inv := by intro y; ext; simp }
          have hprof : relabelProfile PA' eSub = PB' := by
            ext v
            rfl
          have hrec :
              (nansonAux (V := V) n {a : A // pA a} PA').map eSub.toEmbedding =
                nansonAux (V := V) n {b : B // pB b} PB' := by
            simpa [hprof, PB] using (ih (A := {a : A // pA a}) (B := {b : B // pB b}) (P := PA') eSub)
          -- `liftWinners` commutes with relabeling.
          have hlift :
              (liftWinners (nansonAux (V := V) n {a : A // pA a} PA')).map e.toEmbedding =
                liftWinners (nansonAux (V := V) n {b : B // pB b} PB') := by
            classical
            -- `liftWinners` is defined using `Classical.decEq`, so use the same instance here.
            letI : DecidableEq A := Classical.decEq A
            letI : DecidableEq B := Classical.decEq B
            ext b
            constructor
            · intro hb
              -- Unpack membership in the mapped lift.
              have hb' :
                  e.symm b ∈ liftWinners (nansonAux (V := V) n {a : A // pA a} PA') :=
                (mem_map_equiv e (liftWinners (nansonAux (V := V) n {a : A // pA a} PA')) b).1 hb
              -- Unfold `liftWinners` to expose `Finset.image`.
              dsimp [liftWinners] at hb'
              rcases Finset.mem_image.mp hb' with ⟨x, hx, hxval⟩
              have hx' :
                  eSub x ∈ nansonAux (V := V) n {b : B // pB b} PB' := by
                have : eSub x ∈ (nansonAux (V := V) n {a : A // pA a} PA').map eSub.toEmbedding :=
                  Finset.mem_map.mpr ⟨x, hx, rfl⟩
                simpa [hrec] using this
              have hxval' : (eSub x).1 = b := by
                have := congrArg e hxval
                simpa [eSub] using this
              -- Re-fold `liftWinners`.
              show b ∈ liftWinners (nansonAux (V := V) n {b : B // pB b} PB')
              dsimp [liftWinners]
              exact Finset.mem_image.mpr ⟨eSub x, hx', hxval'⟩
            · intro hb
              dsimp [liftWinners] at hb
              rcases Finset.mem_image.mp hb with ⟨y, hy, hyval⟩
              have hy' :
                  y ∈ (nansonAux (V := V) n {a : A // pA a} PA').map eSub.toEmbedding := by
                simpa [hrec] using hy
              have hx :
                  eSub.symm y ∈ nansonAux (V := V) n {a : A // pA a} PA' := by
                exact (mem_map_equiv eSub (nansonAux (V := V) n {a : A // pA a} PA') y).1 hy'
              have hxval : (eSub.symm y).1 = e.symm b := by
                have := congrArg e.symm hyval
                simpa [eSub] using this
              have : e.symm b ∈ liftWinners (nansonAux (V := V) n {a : A // pA a} PA') := by
                dsimp [liftWinners]
                exact Finset.mem_image.mpr ⟨eSub.symm y, hx, hxval⟩
              exact (mem_map_equiv e (liftWinners (nansonAux (V := V) n {a : A // pA a} PA')) b).2 this
          ext b
          simp [nansonAux, scoreA, scoreB, PB, hallA, hallB, hsurvA, hsurvB, pA, pB, PA', PB', hlift]
        · have hsurvB : ¬ (Finset.univ.filter (fun b : B => scoreB b > 0)).Nonempty := by
            intro hsurvB
            have : (Finset.univ.filter (fun a : A => scoreA a > 0)).Nonempty := by
              -- Pull back a witness along `e.symm`.
              rcases hsurvB with ⟨b, hb⟩
              refine ⟨e.symm b, ?_⟩
              have : b ∈ (Finset.univ.filter (fun a : A => scoreA a > 0)).map e.toEmbedding := by
                simpa [hsurv_map] using hb
              simpa [mem_map_equiv] using this
            exact hsurvA this
          ext b
          simp [nansonAux, scoreA, scoreB, PB, hallA, hallB, hsurvA, hsurvB]

theorem nanson_neutral : Neutrality nanson := by
  intro V A _ _ P σ
  classical
  change (nansonAux (Fintype.card A) A P).map σ.toEmbedding =
    nansonAux (Fintype.card A) A (relabelProfile P σ)
  exact nansonAux_relabelProfile (V := V) (A := A) (B := A)
    (n := Fintype.card A) (P := P) (e := σ)

end SocialChoice
