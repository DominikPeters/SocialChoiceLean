import Mathlib.Tactic
import SocialChoice.Axioms.Participation
import SocialChoice.Axioms.Condorcet
import SocialChoice.Margin
import SocialChoice.Impossibilities.Holliday.DefensibleSlack
import SocialChoice.Impossibilities.GibbardSatterthwaite.InductionStepCase2

namespace SocialChoice

open Finset

namespace Holliday

lemma addCopiesProfile_restrict {U A : Type} [DecidableEq U] [Fintype A]
    (V W : Finset U) (P : Profile (Electorate U V) A) (r : LinearOrder A) :
    restrictElectorate (addCopiesProfile V W P r) V (by
      intro x hx
      exact Finset.mem_union.mpr (Or.inl hx)) = P := by
  apply Profile.ext
  intro v
  simp only [restrictElectorate, addCopiesProfile, dif_pos v.2]

lemma addCopiesProfile_pref_of_mem {U A : Type} [DecidableEq U] [Fintype A]
    (V W : Finset U) (P : Profile (Electorate U V) A) (r : LinearOrder A)
    (hVW : Disjoint V W) {w : U} (hw : w ∈ W) :
    (addCopiesProfile V W P r).pref ⟨w, Finset.mem_union.mpr (Or.inr hw)⟩ = r := by
  have hwV : w ∉ V := by
    intro hwV
    exact (Finset.disjoint_left.mp hVW) hwV hw
  simp [addCopiesProfile, hwV]

lemma margin_castProfile {U A : Type} [DecidableEq U] [Fintype A] {S T : Finset U}
    (h : S = T) (P : Profile (Electorate U S) A) (a b : A) :
    margin (castProfile h P) a b = margin P a b := by
  cases h
  simp [castProfile]

lemma margin_addCopies_eq_of_prefers {U A : Type} [DecidableEq U] [Fintype A]
    {V W : Finset U} (hVW : Disjoint V W)
    (P : Profile (Electorate U V) A) (r : LinearOrder A) {a b : A}
    (h : r.lt a b) :
    margin (addCopiesProfile V W P r) a b = margin P a b + (W.card : Int) := by
  classical
  revert hVW
  refine Finset.induction_on W ?base ?step
  · intro _hVW
    have hEq : V ∪ (∅ : Finset U) = V := by simp
    have hP : castProfile hEq (addCopiesProfile V (∅ : Finset U) P r) = P := by
      apply Profile.ext
      intro v
      simp [castProfile, addCopiesProfile]
    have hcast :
        margin (castProfile hEq (addCopiesProfile V (∅ : Finset U) P r)) a b =
          margin (addCopiesProfile V (∅ : Finset U) P r) a b :=
      margin_castProfile (h := hEq) (P := addCopiesProfile V (∅ : Finset U) P r) (a := a) (b := b)
    calc
      margin (addCopiesProfile V (∅ : Finset U) P r) a b =
          margin (castProfile hEq (addCopiesProfile V (∅ : Finset U) P r)) a b := by
            simpa using hcast.symm
      _ = margin P a b := by simp [hP]
      _ = margin P a b + (0 : Int) := by simp
  · intro w s hw ih hVW
    have hVS : Disjoint V s := by
      refine Finset.disjoint_left.mpr ?_
      intro x hxV hxS
      exact (Finset.disjoint_left.mp hVW) hxV (by simp [hxS])
    have hwV : w ∉ V := by
      intro hwV
      exact (Finset.disjoint_left.mp hVW) hwV (by simp)
    have hwV' : w ∉ V ∪ s := by
      intro hwV'
      rcases Finset.mem_union.mp hwV' with hwV' | hwS
      · exact hwV hwV'
      · exact hw hwS
    have hEq : insert w (V ∪ s) = V ∪ insert w s := by
      simp [Finset.union_insert]
    let Qbig : Profile (Electorate U (insert w (V ∪ s))) A :=
      castProfile (S := V ∪ insert w s) (T := insert w (V ∪ s)) hEq.symm
        (addCopiesProfile (V := V) (W := insert w s) P r)
    let Qsmall : Profile (Electorate U (V ∪ s)) A := addCopiesProfile (V := V) (W := s) P r
    have hagree :
        ∀ v : Electorate U (V ∪ s),
          Qbig.pref (liftVoter (u := w) v) = Qsmall.pref v := by
      intro v
      by_cases hv : v.1 ∈ V
      · simp [Qbig, Qsmall, castProfile, addCopiesProfile, liftVoter, hv]
      · simp [Qbig, Qsmall, castProfile, addCopiesProfile, liftVoter, hv]
    have hnew : Qbig.pref (newVoter (u := w) (V := V ∪ s) hwV') = r := by
      simp [Qbig, castProfile, addCopiesProfile, newVoter, hwV]
    have hmargin :
        margin Qbig a b = margin Qsmall a b + 1 := by
      have hpref : (Qbig.pref (newVoter (u := w) (V := V ∪ s) hwV')).lt a b := by
        rw [hnew]
        exact h
      exact margin_add_newVoter_eq_of_prefers (u := w) (V := V ∪ s) hwV' Qsmall Qbig hagree a b
        hpref
    have hIH := ih hVS
    calc
      margin (addCopiesProfile V (insert w s) P r) a b = margin Qbig a b := by
        have hcast :
            margin Qbig a b =
              margin (addCopiesProfile V (insert w s) P r) a b :=
          margin_castProfile (h := hEq.symm)
            (P := addCopiesProfile (V := V) (W := insert w s) P r) (a := a) (b := b)
        simpa [Qbig] using hcast.symm
      _ = margin Qsmall a b + 1 := hmargin
      _ = margin P a b + (s.card : Int) + 1 := by
        simp [Qsmall, hIH, add_assoc]
      _ = margin P a b + ((insert w s).card : Int) := by
        have hcard : ((insert w s).card : Int) = (s.card : Int) + 1 := by
          have hcard' : (insert w s).card = s.card + 1 := by
            simpa using (Finset.card_insert_of_notMem (s := s) (a := w) hw)
          exact congrArg Int.ofNat hcard'
        simp [hcard, add_assoc, add_left_comm, add_comm]

lemma margin_addCopies_eq_of_prefers_rev {U A : Type} [DecidableEq U] [Fintype A]
    {V W : Finset U} (hVW : Disjoint V W)
    (P : Profile (Electorate U V) A) (r : LinearOrder A) {a b : A}
    (h : r.lt b a) :
    margin (addCopiesProfile V W P r) a b = margin P a b - (W.card : Int) := by
  have hswap :
      margin (addCopiesProfile V W P r) b a = margin P b a + (W.card : Int) :=
    margin_addCopies_eq_of_prefers (hVW := hVW) P r (a := b) (b := a) h
  have hskewP : margin P a b = - margin P b a := by
    simpa [skew_symmetric] using (margin_antisymmetric (P := P)) a b
  have hskewQ :
      margin (addCopiesProfile V W P r) a b =
        - margin (addCopiesProfile V W P r) b a := by
    simpa [skew_symmetric] using (margin_antisymmetric (P := addCopiesProfile V W P r)) a b
  calc
    margin (addCopiesProfile V W P r) a b =
        - margin (addCopiesProfile V W P r) b a := hskewQ
    _ = - (margin P b a + (W.card : Int)) := by simp [hswap]
    _ = (- margin P b a) - (W.card : Int) := by ring
    _ = margin P a b - (W.card : Int) := by simp [hskewP]

lemma positiveInvolvement_condorcet_not_winner_of_margin_gap
    {f : VotingRule} (hpos : PositiveInvolvement f) (hcond : CondorcetConsistency f)
    {U A : Type} [DecidableEq U] [Fintype A]
    (hcard : 3 ≤ Fintype.card A)
    {V : Finset U} (P : Profile (Electorate U V) A) {x y : A}
    (hx : x ∈ f P) (hxy : x ≠ y)
    {W : Finset U} (hVW : Disjoint V W)
    (hgap_xy : (W.card : Int) < margin P y x)
    (hgap : ∀ z, margin P z y < (W.card : Int)) :
    False := by
  classical
  have hcard2 : 2 ≤ Fintype.card A := by
    exact le_trans (by decide : 2 ≤ 3) hcard
  let r : LinearOrder A := ballotWithTopTwo (A := A) x y hcard2 hxy
  let Q : Profile (Electorate U (V ∪ W)) A := addCopiesProfile (V := V) (W := W) P r
  have hrest :
      restrictElectorate Q V (by
        intro x hx
        exact Finset.mem_union.mpr (Or.inl hx)) = P := by
    simpa [Q] using (addCopiesProfile_restrict (V := V) (W := W) (P := P) (r := r))
  have hnew :
      ∀ w (hw : w ∈ W),
        Q.pref ⟨w, Finset.mem_union.mpr (Or.inr hw)⟩ = r := by
    intro w hw
    simpa [Q] using
      (addCopiesProfile_pref_of_mem (V := V) (W := W) (P := P) (r := r) hVW hw)
  have htop : BallotTop r x := by
    intro d hd
    exact topRank_ballotWithTopTwo (A := A) x y hcard2 hxy d hd
  have hxQ : x ∈ f Q := by
    apply positiveInvolvement_add_copies (f := f) hpos V W hVW P Q x r
    · exact hrest
    · exact hnew
    · exact htop
    · exact hx
  have hcond_win : CondorcetWinner Q y := by
    apply (CondorcetWinner_iff_margin_pos (P := Q) (c := y)).2
    intro z hz
    by_cases hzx : z = x
    · subst hzx
      have hlt : r.lt z y := htop y hxy.symm
      have hmargin :
          margin Q y z = margin P y z - (W.card : Int) := by
        simpa [Q] using
          (margin_addCopies_eq_of_prefers_rev (hVW := hVW) (P := P) (r := r) (a := y) (b := z)
            hlt)
      have hpos : 0 < margin Q y z := by
        linarith [hmargin, hgap_xy]
      exact hpos
    · have hlt : r.lt y z := by
        exact prefers_second_over_others_ballotWithTopTwo (A := A) x y z hcard hxy hzx hz.symm
      have hmargin :
          margin Q y z = margin P y z + (W.card : Int) := by
        simpa [Q] using
          (margin_addCopies_eq_of_prefers (hVW := hVW) (P := P) (r := r) (a := y) (b := z) hlt)
      have hskew : margin P y z = - margin P z y := by
        simpa [skew_symmetric] using (margin_antisymmetric (P := P)) y z
      have hpos : 0 < margin Q y z := by
        linarith [hmargin, hgap z, hskew]
      exact hpos
  have hfy : f Q = {y} := hcond Q y hcond_win
  have hxQ' : x ∈ ({y} : Finset A) := by
    simpa [hfy] using hxQ
  simp [hxy] at hxQ'

theorem positiveInvolvement_condorcet_refines_defensible_of_gap
    {f : VotingRule} (hpos : PositiveInvolvement f) (hcond : CondorcetConsistency f)
    {U A : Type} [DecidableEq U] [Fintype A]
    (hcard : 3 ≤ Fintype.card A)
    {V : Finset U} (P : Profile (Electorate U V) A)
    (hgap :
      ∀ {x y : A}, x ∈ f P → x ≠ y →
        (∀ z, margin P z y < margin P y x) →
        ∃ W : Finset U, Disjoint V W ∧
          (W.card : Int) < margin P y x ∧
          (∀ z, margin P z y < (W.card : Int))) :
    f P ⊆ defensibleSet P := by
  intro x hx
  classical
  by_contra hxdef
  have hxdef' : ∃ y, ∀ z, margin P z y < margin P y x := by
    have hxdef' : ¬ (∀ y, ∃ z, margin P z y ≥ margin P y x) := by
      simpa [mem_defensibleSet_iff] using hxdef
    classical
    push_neg at hxdef'
    exact hxdef'
  rcases hxdef' with ⟨y, hy⟩
  have hxy : x ≠ y := by
    intro hxy
    subst hxy
    have hcontra := hy x
    simp [self_margin_zero] at hcontra
  rcases hgap (x := x) (y := y) hx hxy hy with ⟨W, hVW, hgap_xy, hgapW⟩
  exact
    positiveInvolvement_condorcet_not_winner_of_margin_gap
      (f := f) hpos hcond hcard P hx hxy hVW hgap_xy hgapW

end Holliday

end SocialChoice
