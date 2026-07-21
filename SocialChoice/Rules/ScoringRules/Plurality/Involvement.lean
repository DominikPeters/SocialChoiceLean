import SocialChoice.Axioms.Participation
import SocialChoice.Rules.ScoringRules.Plurality.Defs
import SocialChoice.Rules

namespace SocialChoice

open Finset

-- Plurality satisfies positive involvement.
theorem plurality_positive_involvement : PositiveInvolvement plurality := by
  intro U A _ _ V u hu P Q c hagree hc htop
  classical
  let ballot := Q.pref (newVoter (u := u) (V := V) hu)
  let P' := Q
  have ballot_not_top : ∀ d : A, d ≠ c → ¬ BallotTop ballot d := by
    intro d hne htopd
    have hcd : ballot.lt c d := htop d hne
    have hdc : ballot.lt d c := htopd c (by simpa [eq_comm] using hne)
    let _ : Preorder A := ballot.toPreorder
    exact (lt_asymm (a := c) (b := d) hcd) hdc
  have topCount_add_newVoter :
      ∀ d : A, topCount Q d = topCount P d + (if BallotTop ballot d then 1 else 0) := by
    intro d
    let S0 : Finset (Electorate U V) := votersTop P d
    let S : Finset (Electorate U (insert u V)) := votersTop Q d
    by_cases htopd : BallotTop ballot d
    · have hS : S =
          insert (newVoter (u := u) (V := V) hu) (S0.image (liftVoter (u := u))) := by
        ext v
        by_cases hv : v = newVoter (u := u) (V := V) hu
        · subst hv
          have hpref : TopRank Q (newVoter (u := u) (V := V) hu) d := by
            exact htopd
          constructor
          · intro _hmem
            simp
          · intro _hmem
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpref⟩
        · have hv' : v.1 ∈ V := by
            have hmem : v.1 ∈ insert u V := v.2
            have hmem' : v.1 = u ∨ v.1 ∈ V := by
              simpa using (Finset.mem_insert.mp hmem)
            cases hmem' with
            | inl h =>
                exact (hv (Subtype.ext h)).elim
            | inr h => exact h
          let v' : Electorate U V := ⟨v.1, hv'⟩
          have hv_eq : v = liftVoter (u := u) v' := by
            apply Subtype.ext
            rfl
          have htop' : TopRank Q v d ↔ TopRank P v' d := by
            unfold TopRank Prefers
            rw [hv_eq, hagree]
          have himage : v ∈ S0.image (liftVoter (u := u)) ↔ v' ∈ S0 := by
            constructor
            · intro hvimg
              rcases Finset.mem_image.mp hvimg with ⟨w, hw, hweq⟩
              have hw' : w = v' := by
                apply (liftVoter_injective (u := u))
                simpa [hv_eq] using hweq
              simpa [hw'] using hw
            · intro hvS0
              exact Finset.mem_image.mpr ⟨v', hvS0, hv_eq.symm⟩
          have hvS : v ∈ S ↔ v' ∈ S0 := by
            constructor
            · intro hvS
              have htopQ : TopRank Q v d := (Finset.mem_filter.mp hvS).2
              have htopP : TopRank P v' d := (htop'.mp htopQ)
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htopP⟩
            · intro hvS0
              have htopP : TopRank P v' d := (Finset.mem_filter.mp hvS0).2
              have htopQ : TopRank Q v d := (htop'.mpr htopP)
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htopQ⟩
          have hinsert :
              v ∈ insert (newVoter (u := u) (V := V) hu) (S0.image (liftVoter (u := u))) ↔
                v ∈ S0.image (liftVoter (u := u)) := by
            simp [hv]
          calc
            v ∈ S ↔ v' ∈ S0 := hvS
            _ ↔ v ∈ S0.image (liftVoter (u := u)) := himage.symm
            _ ↔ v ∈ insert (newVoter (u := u) (V := V) hu) (S0.image (liftVoter (u := u))) :=
              hinsert.symm
      have hnotmem :
          newVoter (u := u) (V := V) hu ∉ S0.image (liftVoter (u := u)) := by
        intro hmem
        rcases Finset.mem_image.mp hmem with ⟨v, _hv, hveq⟩
        exact (liftVoter_ne_newVoter (u := u) (V := V) hu v) hveq
      have hinj :
          Function.Injective (liftVoter (u := u) : Electorate U V → Electorate U (insert u V)) :=
        liftVoter_injective (u := u)
      have hcard :
          S.card = S0.card + 1 := by
        have hcard' :
            (insert (newVoter (u := u) (V := V) hu) (S0.image (liftVoter (u := u)))).card =
              (S0.image (liftVoter (u := u))).card + 1 :=
          Finset.card_insert_of_notMem hnotmem
        calc
          S.card = (S0.image (liftVoter (u := u))).card + 1 := by
            simpa [hS] using hcard'
          _ = S0.card + 1 := by
            simpa using (Finset.card_image_of_injective S0 hinj)
      simp [topCount, S, S0, hcard, htopd]
    · have hS : S = S0.image (liftVoter (u := u)) := by
        ext v
        by_cases hv : v = newVoter (u := u) (V := V) hu
        · subst hv
          have hpref : ¬ TopRank Q (newVoter (u := u) (V := V) hu) d := by
            intro htopQ
            have htopB : BallotTop ballot d := by
              intro x hx
              have hprefQ : Prefers Q (newVoter (u := u) (V := V) hu) d x := htopQ x hx
              simpa [Prefers, ballot] using hprefQ
            exact htopd htopB
          constructor
          · intro hmem
            have hpref' : TopRank Q (newVoter (u := u) (V := V) hu) d :=
              (Finset.mem_filter.mp hmem).2
            exact (hpref hpref').elim
          · intro hmem
            rcases Finset.mem_image.mp hmem with ⟨w, _hw, hweq⟩
            exact (False.elim ((liftVoter_ne_newVoter (u := u) (V := V) hu w) hweq))
        · have hv' : v.1 ∈ V := by
            have hmem : v.1 ∈ insert u V := v.2
            have hmem' : v.1 = u ∨ v.1 ∈ V := by
              simpa using (Finset.mem_insert.mp hmem)
            cases hmem' with
            | inl h =>
                exact (hv (Subtype.ext h)).elim
            | inr h => exact h
          let v' : Electorate U V := ⟨v.1, hv'⟩
          have hv_eq : v = liftVoter (u := u) v' := by
            apply Subtype.ext
            rfl
          have htop' : TopRank Q v d ↔ TopRank P v' d := by
            unfold TopRank Prefers
            rw [hv_eq, hagree]
          have himage : v ∈ S0.image (liftVoter (u := u)) ↔ v' ∈ S0 := by
            constructor
            · intro hvimg
              rcases Finset.mem_image.mp hvimg with ⟨w, hw, hweq⟩
              have hw' : w = v' := by
                apply (liftVoter_injective (u := u))
                simpa [hv_eq] using hweq
              simpa [hw'] using hw
            · intro hvS0
              exact Finset.mem_image.mpr ⟨v', hvS0, hv_eq.symm⟩
          have hvS : v ∈ S ↔ v' ∈ S0 := by
            constructor
            · intro hvS
              have htopQ : TopRank Q v d := (Finset.mem_filter.mp hvS).2
              have htopP : TopRank P v' d := (htop'.mp htopQ)
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htopP⟩
            · intro hvS0
              have htopP : TopRank P v' d := (Finset.mem_filter.mp hvS0).2
              have htopQ : TopRank Q v d := (htop'.mpr htopP)
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, htopQ⟩
          calc
            v ∈ S ↔ v' ∈ S0 := hvS
            _ ↔ v ∈ S0.image (liftVoter (u := u)) := himage.symm
      have hinj :
          Function.Injective (liftVoter (u := u) : Electorate U V → Electorate U (insert u V)) :=
        liftVoter_injective (u := u)
      have hcard :
          S.card = S0.card := by
        calc
          S.card = (S0.image (liftVoter (u := u))).card := by
            simp [hS]
          _ = S0.card := by
            simpa using (Finset.card_image_of_injective S0 hinj)
      simp [topCount, S, S0, hcard, htopd]
  have topCount_c : topCount P' c = topCount P c + 1 := by
    simpa [ballot, htop] using topCount_add_newVoter c
  have topCount_ne : ∀ d : A, d ≠ c → topCount P' d = topCount P d := by
    intro d hne
    have hbt : ¬ BallotTop ballot d := ballot_not_top d hne
    simpa [hbt] using topCount_add_newVoter d
  have hmax_old : ∀ d : A, topCount P d ≤ topCount P c := by
    have hc' : c ∈ (Finset.univ.filter
        (fun c => ∀ d : A, topCount P d ≤ topCount P c)) := by
      simpa [plurality] using hc
    exact (mem_filter.mp hc').2
  have hmax_new : ∀ d : A, topCount P' d ≤ topCount P' c := by
    intro d
    by_cases hne : d = c
    · simp [hne]
    · calc
        topCount P' d = topCount P d := topCount_ne d hne
        _ ≤ topCount P c := hmax_old d
        _ ≤ topCount P c + 1 := Nat.le_succ _
        _ = topCount P' c := topCount_c.symm
  have hc' : c ∈ (Finset.univ.filter
      (fun c => ∀ d : A, topCount P' d ≤ topCount P' c)) := by
    exact mem_filter.mpr ⟨mem_univ _, hmax_new⟩
  simpa [plurality] using hc'

end SocialChoice
