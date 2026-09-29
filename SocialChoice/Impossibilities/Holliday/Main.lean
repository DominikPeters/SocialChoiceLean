import SocialChoice.Impossibilities.Holliday.Profiles
import SocialChoice.Impossibilities.Holliday.Margins
import SocialChoice.Impossibilities.Holliday.CondorcetLosers
import SocialChoice.Impossibilities.Holliday.DefensibleSlack
import SocialChoice.Impossibilities.Holliday.DefensibleSets
import SocialChoice.Impossibilities.Holliday.DefensibleExtensions
import SocialChoice.Impossibilities.Holliday.MarginDifferences
import SocialChoice.Impossibilities.Holliday.GapInstances
import SocialChoice.Impossibilities.Holliday.GapExtensions
import SocialChoice.Impossibilities.Holliday.ResolvabilitySteps
import SocialChoice.Impossibilities.Holliday.Transitions
import SocialChoice.Impossibilities.Holliday.TransitionsExtensions

namespace SocialChoice

namespace Holliday

set_option maxRecDepth 3000 in
set_option maxHeartbeats 150000 in
theorem no_positiveInvolvement_condorcet_resolvability_holliday
    (f : VotingRule) (hf : IsVotingRule f)
    (hpos : PositiveInvolvement f) (hcond : CondorcetConsistency f)
    (hcl : CondorcetLoserCriterion f) (hres : Resolvability f) : False := by
  classical
  -- P1: winners are defensible; d is a Condorcet loser, so a must win.
  obtain ⟨x, hx⟩ := hf P1Profile
  have hxdef : x ∈ defensibleSet P1Profile :=
    (refines_defensible_P1 (f := f) hpos hcond) hx
  have hxad : x ∈ ({a, d} : Finset A5) := by
    simpa [defensibleSet_P1] using hxdef
  have hdnot : d ∉ f P1Profile :=
    hcl P1Profile d P1_condorcetLoser_d
  have hxne_d : x ≠ d := by
    intro hxd
    subst hxd
    exact hdnot hx
  have hxa : x = a := by
    rcases Finset.mem_insert.mp hxad with hx' | hx'
    · exact hx'
    · have hx'' : x = d := by simpa using hx'
      exact (hxne_d hx'').elim
  have haP1 : a ∈ f P1Profile := by
    simpa [hxa] using hx

  -- P1 → P2 by positive involvement on the a-top block.
  have haP2 : a ∈ f P2Profile := mem_P2_of_mem_P1 (hpos := hpos) haP1

  -- Choose a fresh voter u2 and resolve at P2.
  set u2 : U450 := u280
  have hu2 : u2 ∉ votersP2 := by
    intro hu2
    have hIio : u2 ∈ Finset.Iio u280 := votersP2_subset_Iio_u280 hu2
    have hlt : u2 < u280 := by simpa using hIio
    exact (lt_irrefl u280) hlt
  obtain ⟨r2, Q2, hagree2, _hnew2, hQ2⟩ :=
    hres (V := votersP2) (u := u2) (hu := hu2) (P := P2Profile) (x := a) haP2
  have hdQ2 : d ∉ f Q2 := by
    simpa [hQ2] using (by decide : d ∉ ({a} : Finset A5))

  -- Restrict to P3 + S2 and push d ∉ winners back to P3 + S2.
  let V3 : Finset U450 := insert u2 votersP3
  have hV3 : V3 ⊆ insert u2 votersP2 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxP3
    · exact Finset.mem_insert.mpr (Or.inl rfl)
    · have hxP2 : x ∈ votersP2 := by
        have h := congrArg (fun s => x ∈ s) votersP2_eq_union_votersP3_votersP1_2
        exact Eq.mp h (Finset.mem_union.mpr (Or.inl hxP3))
      exact Finset.mem_insert.mpr (Or.inr hxP2)
  let Q3 : Profile (Electorate U450 V3) A5 := restrictElectorate Q2 V3 hV3
  have hdQ3 : d ∉ f Q3 := by
    simpa [V3, Q3] using
      (not_mem_P3_add_newVoter_of_not_mem_P2_add_newVoter (f := f) hpos (u := u2) (hu := hu2)
        (Q2 := Q2) (hagree2 := hagree2) (hd := hdQ2))
  have hagree3 :
      ∀ v : Electorate U450 votersP3,
        Q3.pref (liftVoter (u := u2) v) = P3Profile.pref v := by
    intro v
    have hvP2 : v.1 ∈ votersP2 := by
      have h := congrArg (fun s => v.1 ∈ s) votersP2_eq_union_votersP3_votersP1_2
      exact Eq.mp h (Finset.mem_union.mpr (Or.inl v.2))
    let vP2 : Electorate U450 votersP2 := ⟨v.1, hvP2⟩
    have h := hagree2 vP2
    have hP2 : P2Profile.pref vP2 = (ballotsAll v.1).toLinearOrder := by
      rfl
    have hP3 : P3Profile.pref v = (ballotsAll v.1).toLinearOrder := by
      rfl
    have hQ2pref :
        Q2.pref (liftVoter (u := u2) vP2) = (ballotsAll v.1).toLinearOrder := by
      have h' := h
      rw [hP2] at h'
      exact h'
    have hQ3pref :
        Q3.pref (liftVoter (u := u2) v) = (ballotsAll v.1).toLinearOrder := by
      change
        Q2.pref ⟨(liftVoter (u := u2) v).1, hV3 (liftVoter (u := u2) v).2⟩ =
          (ballotsAll v.1).toLinearOrder
      have hsub :
          (⟨(liftVoter (u := u2) v).1, hV3 (liftVoter (u := u2) v).2⟩ :
            Electorate U450 (insert u2 votersP2)) =
            liftVoter (u := u2) vP2 := by
        rfl
      rw [hsub]
      exact hQ2pref
    rw [hP3]
    exact hQ3pref

  have hsubset_Q3 : f Q3 ⊆ ({b, d} : Finset A5) := by
    have href : f Q3 ⊆ defensibleSet Q3 :=
      refines_defensible_P3_add_newVoter (hpos := hpos) (hcond := hcond)
        (hu := by
          intro hu
          have hIio : u2 ∈ Finset.Iio u280 := votersP3_subset_Iio_u280 hu
          have hlt : u2 < u280 := by simpa using hIio
          exact (lt_irrefl u280) hlt) (Q := Q3) hagree3
    have hdef : defensibleSet Q3 ⊆ ({b, d} : Finset A5) :=
      defensibleSet_P3_add_newVoter_subset (hu := by
        intro hu
        have hIio : u2 ∈ Finset.Iio u280 := votersP3_subset_Iio_u280 hu
        have hlt : u2 < u280 := by simpa using hIio
        exact (lt_irrefl u280) hlt) (Q := Q3) hagree3
    exact Finset.Subset.trans href hdef
  obtain ⟨x3, hx3⟩ := hf Q3
  have hx3_bd : x3 ∈ ({b, d} : Finset A5) := hsubset_Q3 hx3
  have hx3_ne_d : x3 ≠ d := by
    intro hxd
    subst hxd
    exact hdQ3 hx3
  have hbQ3 : b ∈ f Q3 := by
    rcases Finset.mem_insert.mp hx3_bd with hx3' | hx3'
    · simpa [hx3'] using hx3
    · have hx3'' : x3 = d := by simpa using hx3'
      exact (hx3_ne_d hx3'').elim

  -- P3 + S2 → P4 + S2 by positive involvement on the b-top block.
  have hdisj3_10 : Disjoint V3 votersP1_10 := by
    refine Finset.disjoint_left.2 ?_
    intro v hvV hv10
    rcases Finset.mem_insert.mp hvV with rfl | hvP3
    · have hmem : u2 ∈ votersP1_10 := hv10
      have hcontra : ¬ (280 : Nat) < p1_cut10 := by decide
      have hmem' : p1_cut9 ≤ 280 ∧ 280 < p1_cut10 := by
        simpa [u2, votersP1_10, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut9_fin,
          p1_cut10_fin] using hmem
      have hmem'' : (280 : Nat) < p1_cut10 := hmem'.2
      exact (hcontra hmem'').elim
    · exact (Finset.disjoint_left.mp votersP3_disjoint_votersP1_10) hvP3 hv10
  let Q4raw : Profile (Electorate U450 (V3 ∪ votersP1_10)) A5 :=
    addCopiesProfile (V := V3) (W := votersP1_10) Q3 ballot_bdeac.toLinearOrder
  have hbQ4raw : b ∈ f Q4raw :=
    positiveInvolvement_addCopiesProfile (f := f) hpos V3 votersP1_10 hdisj3_10 Q3
      ballot_bdeac.toLinearOrder b ballot_bdeac_top_b hbQ3
  have hset4 :
      V3 ∪ votersP1_10 = insert u2 votersP4 := by
    have h' : votersP3 ∪ votersP1_10 = votersP4 := votersP4_eq_union_votersP3_votersP1_10
    unfold V3
    rw [Finset.insert_union, h']
  let Q4base : Profile (Electorate U450 (insert u2 votersP4)) A5 :=
    castProfile (h := hset4) Q4raw
  have hbQ4base : b ∈ f Q4base := by
    have hcast := votingRule_castProfile (f := f) (h := hset4) (P := Q4raw)
    rw [hcast]
    exact hbQ4raw

  -- Resolve at P4 + S2, then push d out of P5 + S2 + S4.
  set u4 : U450 := u449
  have hu4P4 : u4 ∉ votersP4 := by
    intro hu4P4
    have hIio : u4 ∈ Finset.Iio u280 := votersP4_subset_Iio_u280 hu4P4
    have hlt : u4 < u280 := by simpa using hIio
    have hcontra : ¬ u4 < u280 := by decide
    exact (hcontra hlt).elim
  have hu4' : u4 ∉ insert u2 votersP4 := by
    intro hu4'
    rcases Finset.mem_insert.mp hu4' with h | h
    · have : u4 ≠ u2 := by decide
      exact (this h).elim
    · exact hu4P4 h
  obtain ⟨r4, Q4', hagree4', _hnew4, hQ4'⟩ :=
    hres (V := insert u2 votersP4) (u := u4) (hu := hu4') (P := Q4base) (x := b) hbQ4base
  have hdQ4' : d ∉ f Q4' := by
    simpa [hQ4'] using (by decide : d ∉ ({b} : Finset A5))

  -- Q4raw agrees with P4 on votersP4.
  have hagree4P4 :
      ∀ v : Electorate U450 votersP4,
        ∀ hv_union : v.1 ∈ V3 ∪ votersP1_10,
          Q4raw.pref ⟨v.1, hv_union⟩ = P4Profile.pref v := by
    have hu2P4 : u2 ∉ votersP4 := by
      intro hu2P4
      have hIio : u2 ∈ Finset.Iio u280 := votersP4_subset_Iio_u280 hu2P4
      have hlt : u2 < u280 := by simpa using hIio
      have hcontra : ¬ u2 < u280 := by decide
      exact (hcontra hlt).elim
    have h :=
      hagree_Q4raw_P4 (u2 := u2) (hu2 := hu2P4) (Q3 := Q3)
        (hagree3 := hagree3) (hdisj := hdisj3_10)
    exact h

  have hagree4base :
      ∀ v : Electorate U450 votersP4,
        Q4base.pref (liftVoter (u := u2) v) = P4Profile.pref v := by
    intro v
    have hv_union : v.1 ∈ V3 ∪ votersP1_10 := by
      have hv_union' : v.1 ∈ votersP3 ∪ votersP1_10 := by
        rw [show votersP3 ∪ votersP1_10 = votersP4 from
          votersP4_eq_union_votersP3_votersP1_10]
        exact v.2
      rcases Finset.mem_union.mp hv_union' with hvP3 | hvP10
      · have hvV3 : v.1 ∈ V3 := Finset.mem_insert.mpr (Or.inr hvP3)
        exact Finset.mem_union.mpr (Or.inl hvV3)
      · exact Finset.mem_union.mpr (Or.inr hvP10)
    have hQ4pref : Q4raw.pref ⟨v.1, hv_union⟩ = P4Profile.pref v :=
      hagree4P4 v hv_union
    have hv_union_cast : v.1 ∈ V3 ∪ votersP1_10 := by
      have h := congrArg (fun s => v.1 ∈ s) hset4.symm
      exact Eq.mp h (liftVoter (u := u2) v).2
    have hsub :
        (⟨(liftVoter (u := u2) v).1, by
            exact hv_union_cast⟩ : Electorate U450 (V3 ∪ votersP1_10)) =
          ⟨v.1, hv_union⟩ := by
      apply Subtype.ext
      rfl
    have hcast :
        Q4base.pref (liftVoter (u := u2) v) =
          Q4raw.pref ⟨(liftVoter (u := u2) v).1, hv_union_cast⟩ := by
      rfl
    rw [hcast, hsub]
    exact hQ4pref

  have hagree4P4' :
      ∀ v : Electorate U450 votersP4,
        Q4'.pref (liftVoter (u := u4) (liftVoter (u := u2) v)) = P4Profile.pref v := by
    intro v
    have h := hagree4' (liftVoter (u := u2) v)
    have hQ4base : Q4base.pref (liftVoter (u := u2) v) = P4Profile.pref v :=
      hagree4base v
    simpa [hQ4base] using h

  -- Restrict to P5 + S2 + S4.
  let V5 : Finset U450 := insert u4 (insert u2 votersP5)
  have hV5 : V5 ⊆ insert u4 (insert u2 votersP4) := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Finset.mem_insert.mpr (Or.inl rfl)
    rcases Finset.mem_insert.mp hv with rfl | hvP5
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl rfl)))
    · have hvP4 : v ∈ votersP4 := by
        have h := congrArg (fun s => v ∈ s) votersP4_eq_union_votersP5_votersP1_7
        exact Eq.mp h (Finset.mem_union.mpr (Or.inl hvP5))
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr hvP4)))
  let Q5 : Profile (Electorate U450 V5) A5 := restrictElectorate Q4' V5 hV5
  have hdQ5 : d ∉ f Q5 := by
    have hu2P4 : u2 ∉ votersP4 := by
      intro hu2P4
      have hIio : u2 ∈ Finset.Iio u280 := votersP4_subset_Iio_u280 hu2P4
      have hlt : u2 < u280 := by simpa using hIio
      have hcontra : ¬ u2 < u280 := by decide
      exact (hcontra hlt).elim
    simpa [V5, Q5] using
      (not_mem_P5_add_twoVoters_of_not_mem_P4_add_twoVoters (f := f) hpos
        (u2 := u2) (u4 := u4) (hu2 := hu2P4) (hu4 := hu4P4) (Q4 := Q4')
        (hagree4 := hagree4P4') (hd := hdQ4'))

  -- Defensible refinement on P5 + S2 + S4 forces d to be the only possible winner.
  have hsubset_u2P5 : insert u2 votersP5 ⊆ insert u2 votersP4 := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hvP5
    · exact Finset.mem_insert.mpr (Or.inl rfl)
    · have hvP4 : v ∈ votersP4 := by
        have h := congrArg (fun s => v ∈ s) votersP4_eq_union_votersP5_votersP1_7
        exact Eq.mp h (Finset.mem_union.mpr (Or.inl hvP5))
      exact Finset.mem_insert.mpr (Or.inr hvP4)
  let Q2' : Profile (Electorate U450 (insert u2 votersP5)) A5 :=
    restrictElectorate Q4base (insert u2 votersP5) hsubset_u2P5
  have hagree2P5 :
      ∀ v : Electorate U450 votersP5,
        Q2'.pref (liftVoter (u := u2) v) = P5Profile.pref v := by
    intro v
    have hvP4 : v.1 ∈ votersP4 := by
      have h := congrArg (fun s => v.1 ∈ s) votersP4_eq_union_votersP5_votersP1_7
      exact Eq.mp h (Finset.mem_union.mpr (Or.inl v.2))
    have hP5 : P5Profile.pref v = (ballotsAll v.1).toLinearOrder := by
      rfl
    have hP4 : P4Profile.pref ⟨v.1, hvP4⟩ = (ballotsAll v.1).toLinearOrder := by
      rfl
    have hQ4pref :
        Q4base.pref (liftVoter (u := u2) ⟨v.1, hvP4⟩) = P4Profile.pref ⟨v.1, hvP4⟩ :=
      hagree4base ⟨v.1, hvP4⟩
    have hQ2pref :
        Q2'.pref (liftVoter (u := u2) v) = (ballotsAll v.1).toLinearOrder := by
      have hQ4pref' :
          Q4base.pref (liftVoter (u := u2) ⟨v.1, hvP4⟩) =
            (ballotsAll v.1).toLinearOrder := by
        rw [hQ4pref, hP4]
      have hv_ins : v.1 ∈ insert u2 votersP4 :=
        Finset.mem_insert.mpr (Or.inr hvP4)
      have hsub :
          (⟨(liftVoter (u := u2) v).1, by
              exact hv_ins⟩ : Electorate U450 (insert u2 votersP4)) =
            liftVoter (u := u2) ⟨v.1, hvP4⟩ := by
        apply Subtype.ext
        rfl
      have hrest :
          Q2'.pref (liftVoter (u := u2) v) =
            Q4base.pref ⟨(liftVoter (u := u2) v).1, hsubset_u2P5 (liftVoter (u := u2) v).2⟩ := by
        rfl
      rw [hrest, hsub]
      exact hQ4pref'
    simpa [hP5] using hQ2pref
  have hagree4P5 :
      ∀ v : Electorate U450 (insert u2 votersP5),
        Q5.pref (liftVoter (u := u4) v) = Q2'.pref v := by
    intro v
    have hv_ins : v.1 ∈ insert u2 votersP4 := by
      rcases Finset.mem_insert.mp v.2 with h | hvP5
      · exact Finset.mem_insert.mpr (Or.inl h)
      · have hvP4 : v.1 ∈ votersP4 := by
          have h := congrArg (fun s => v.1 ∈ s) votersP4_eq_union_votersP5_votersP1_7
          exact Eq.mp h (Finset.mem_union.mpr (Or.inl hvP5))
        exact Finset.mem_insert.mpr (Or.inr hvP4)
    let vP4 : Electorate U450 (insert u2 votersP4) := ⟨v.1, hv_ins⟩
    have hQ4'pref : Q4'.pref (liftVoter (u := u4) vP4) = Q4base.pref vP4 := by
      exact hagree4' vP4
    have hleft : Q5.pref (liftVoter (u := u4) v) = Q4'.pref (liftVoter (u := u4) vP4) := by
      have hsub :
          (⟨(liftVoter (u := u4) v).1, by
              exact hV5 (liftVoter (u := u4) v).2⟩ :
            Electorate U450 (insert u4 (insert u2 votersP4))) =
            liftVoter (u := u4) vP4 := by
        apply Subtype.ext
        rfl
      have hrest :
          Q5.pref (liftVoter (u := u4) v) =
            Q4'.pref ⟨(liftVoter (u := u4) v).1, hV5 (liftVoter (u := u4) v).2⟩ := by
        rfl
      rw [hrest, hsub]
    have hright : Q2'.pref v = Q4base.pref vP4 := by
      have hsub :
          (⟨v.1, hsubset_u2P5 v.2⟩ : Electorate U450 (insert u2 votersP4)) = vP4 := by
        apply Subtype.ext
        rfl
      have hrest :
          Q2'.pref v = Q4base.pref ⟨v.1, hsubset_u2P5 v.2⟩ := by
        rfl
      rw [hrest, hsub]
    calc
      Q5.pref (liftVoter (u := u4) v)
          = Q4'.pref (liftVoter (u := u4) vP4) := hleft
      _ = Q4base.pref vP4 := hQ4'pref
      _ = Q2'.pref v := by symm; exact hright

  have hsubset_Q5 : f Q5 ⊆ ({d} : Finset A5) := by
    have href : f Q5 ⊆ defensibleSet Q5 :=
      refines_defensible_P5_add_twoVoters (hpos := hpos) (hcond := hcond)
        (hu2 := by
          intro hu2P5
          have hIio : u2 ∈ Finset.Iio u280 := votersP5_subset_Iio_u280 hu2P5
          have hlt : u2 < u280 := by simpa using hIio
          exact (lt_irrefl u280) hlt)
        (hu4 := by
          intro hu4P5
          rcases Finset.mem_insert.mp hu4P5 with h | h
          · have : u4 ≠ u2 := by decide
            exact (this h).elim
          · have hIio : u4 ∈ Finset.Iio u280 := votersP5_subset_Iio_u280 h
            have hlt : u4 < u280 := by simpa using hIio
            have hcontra : ¬ u4 < u280 := by decide
            exact (hcontra hlt).elim)
        (Q2 := Q2') (Q := Q5) (hagree2 := hagree2P5) (hagree4 := hagree4P5)
    have hdef : defensibleSet Q5 ⊆ ({d} : Finset A5) :=
      defensibleSet_P5_add_twoVoters_subset (hu2 := by
        intro hu2P5
        have hIio : u2 ∈ Finset.Iio u280 := votersP5_subset_Iio_u280 hu2P5
        have hlt : u2 < u280 := by simpa using hIio
        exact (lt_irrefl u280) hlt)
        (hu4 := by
          intro hu4P5
          rcases Finset.mem_insert.mp hu4P5 with h | h
          · have : u4 ≠ u2 := by decide
            exact (this h).elim
          · have hIio : u4 ∈ Finset.Iio u280 := votersP5_subset_Iio_u280 h
            have hlt : u4 < u280 := by simpa using hIio
            have hcontra : ¬ u4 < u280 := by decide
            exact (hcontra hlt).elim)
        (Q2 := Q2') (Q := Q5) (hagree2 := hagree2P5) (hagree4 := hagree4P5)
    exact Finset.Subset.trans href hdef
  obtain ⟨x5, hx5⟩ := hf Q5
  have hx5_d : x5 = d := by
    have hx5' : x5 ∈ ({d} : Finset A5) := hsubset_Q5 hx5
    simpa using hx5'
  subst hx5_d
  exact hdQ5 hx5

end Holliday

end SocialChoice
