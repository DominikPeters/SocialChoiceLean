import Mathlib.Tactic
import SocialChoice.Axioms.Participation
import SocialChoice.Impossibilities.Holliday.Profiles
import SocialChoice.Impossibilities.Holliday.Transitions

namespace SocialChoice

open Finset

namespace Holliday

lemma not_mem_add_copies_of_not_mem {f : VotingRule} (hpos : PositiveInvolvement f)
    {U A : Type} [DecidableEq U] [Fintype A]
    (V W : Finset U) (hVW : Disjoint V W)
    (P : Profile (Electorate U V) A)
    (Q : Profile (Electorate U (V ∪ W)) A) (c : A) (r : LinearOrder A)
    (hrest :
      restrictElectorate Q V (by intro x hx; exact Finset.mem_union.mpr (Or.inl hx)) = P)
    (hnew :
      ∀ w (hw : w ∈ W),
        Q.pref ⟨w, Finset.mem_union.mpr (Or.inr hw)⟩ = r)
    (htop : BallotTop r c) :
    c ∉ f Q → c ∉ f P := by
  intro hnot hc
  have hmem :
      c ∈ f Q :=
    positiveInvolvement_add_copies (f := f) hpos V W hVW P Q c r hrest hnew htop hc
  exact hnot hmem

lemma not_mem_P3_add_newVoter_of_not_mem_P2_add_newVoter {f : VotingRule} (hpos : PositiveInvolvement f)
    {u : U450} (hu : u ∉ votersP2)
    (Q2 : Profile (Electorate U450 (insert u votersP2)) A5)
    (hagree2 : ∀ v : Electorate U450 votersP2, Q2.pref (liftVoter (u := u) v) = P2Profile.pref v)
    (hd : d ∉ f Q2) :
    let V : Finset U450 := insert u votersP3
    let hV : V ⊆ insert u votersP2 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxP3
      · exact Finset.mem_insert.mpr (Or.inl rfl)
      · have hxP2 : x ∈ votersP2 := by
          have h := congrArg (fun s => x ∈ s) votersP2_eq_union_votersP3_votersP1_2
          exact (Eq.mp h (Finset.mem_union.mpr (Or.inl hxP3)))
        exact Finset.mem_insert.mpr (Or.inr hxP2)
    let Q3 : Profile (Electorate U450 V) A5 :=
      restrictElectorate Q2 V hV
    d ∉ f Q3 := by
  classical
  intro V hV Q3
  have hu12 : u ∉ votersP1_2 := by
    intro hu12
    exact hu (votersP1_2_subset_votersP2 hu12)
  have hVW : Disjoint V votersP1_2 := by
    refine Finset.disjoint_left.2 ?_
    intro x hxV hx12
    rcases Finset.mem_insert.mp hxV with rfl | hxP3
    · exact hu12 hx12
    · exact (Finset.disjoint_left.mp votersP3_disjoint_votersP1_2) hxP3 hx12
  have hset :
      V ∪ votersP1_2 = insert u votersP2 := by
    have h' : votersP3 ∪ votersP1_2 = votersP2 := votersP2_eq_union_votersP3_votersP1_2
    calc
      V ∪ votersP1_2 = insert u (votersP3 ∪ votersP1_2) := by
        simp [V, Finset.insert_union]
      _ = insert u votersP2 := by simp [h']
  let Q2' : Profile (Electorate U450 (V ∪ votersP1_2)) A5 :=
    castProfile (h := hset.symm) Q2
  have hnot : d ∉ f Q2' := by
    have hcast : f Q2' = f Q2 := by
      dsimp [Q2']
      exact votingRule_castProfile (f := f) (h := hset.symm) (P := Q2)
    rw [hcast]
    exact hd
  have hrest :
      restrictElectorate Q2' V (by intro x hx; exact Finset.mem_union.mpr (Or.inl hx)) = Q3 := by
    ext v
    rfl
  have hnew :
      ∀ w (hw : w ∈ votersP1_2),
        Q2'.pref ⟨w, Finset.mem_union.mpr (Or.inr hw)⟩ = ballot_daceb.toLinearOrder := by
    intro w hw
    have hwP2 : w ∈ votersP2 := votersP1_2_subset_votersP2 hw
    have hballot : ballotsAll w = ballot_daceb :=
      ballotsAll_eq_ballot_daceb_of_mem_votersP1_2 hw
    have hP2pref :
        P2Profile.pref ⟨w, hwP2⟩ = ballot_daceb.toLinearOrder := by
      change (ballotsAll w).toLinearOrder = ballot_daceb.toLinearOrder
      rw [hballot]
    have hQ2pref :
        Q2.pref (liftVoter (u := u) ⟨w, hwP2⟩) = ballot_daceb.toLinearOrder := by
      have h := hagree2 ⟨w, hwP2⟩
      rw [hP2pref] at h
      exact h
    simp only [Q2', castProfile]
    rw [show (⟨w, _⟩ : Electorate U450 (insert u votersP2)) =
      liftVoter (u := u) ⟨w, hwP2⟩ by apply Subtype.ext; rfl]
    exact hQ2pref
  exact
    not_mem_add_copies_of_not_mem (f := f) hpos V votersP1_2 hVW Q3 Q2' d
      ballot_daceb.toLinearOrder hrest hnew ballot_daceb_top_d hnot

lemma not_mem_P3_add_newVoter_of_not_mem_P4_add_newVoter {f : VotingRule} (hpos : PositiveInvolvement f)
    {u : U450} (hu : u ∉ votersP4)
    (Q4 : Profile (Electorate U450 (insert u votersP4)) A5)
    (hagree4 : ∀ v : Electorate U450 votersP4, Q4.pref (liftVoter (u := u) v) = P4Profile.pref v)
    (hb : b ∉ f Q4) :
    let V : Finset U450 := insert u votersP3
    let hV : V ⊆ insert u votersP4 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxP3
      · exact Finset.mem_insert.mpr (Or.inl rfl)
      · have hxP4 : x ∈ votersP4 := by
          have h := congrArg (fun s => x ∈ s) votersP4_eq_union_votersP3_votersP1_10
          exact Eq.mp h (Finset.mem_union.mpr (Or.inl hxP3))
        exact Finset.mem_insert.mpr (Or.inr hxP4)
    let Q3 : Profile (Electorate U450 V) A5 :=
      restrictElectorate Q4 V hV
    b ∉ f Q3 := by
  classical
  intro V hV Q3
  have hu10 : u ∉ votersP1_10 := by
    intro hu10
    have hu4 : u ∈ votersP4 := by
      have h := congrArg (fun s => u ∈ s) votersP4_eq_union_votersP3_votersP1_10
      exact Eq.mp h (Finset.mem_union.mpr (Or.inr hu10))
    exact hu hu4
  have hVW : Disjoint V votersP1_10 := by
    refine Finset.disjoint_left.2 ?_
    intro x hxV hx10
    rcases Finset.mem_insert.mp hxV with rfl | hxP3
    · exact hu10 hx10
    · exact (Finset.disjoint_left.mp votersP3_disjoint_votersP1_10) hxP3 hx10
  have hset :
      V ∪ votersP1_10 = insert u votersP4 := by
    have h' : votersP3 ∪ votersP1_10 = votersP4 := votersP4_eq_union_votersP3_votersP1_10
    calc
      V ∪ votersP1_10 = insert u (votersP3 ∪ votersP1_10) := by
        simp [V, Finset.insert_union]
      _ = insert u votersP4 := by simp [h']
  let Q4' : Profile (Electorate U450 (V ∪ votersP1_10)) A5 :=
    castProfile (h := hset.symm) Q4
  have hnot : b ∉ f Q4' := by
    have hcast : f Q4' = f Q4 := by
      dsimp [Q4']
      exact votingRule_castProfile (f := f) (h := hset.symm) (P := Q4)
    rw [hcast]
    exact hb
  have hrest :
      restrictElectorate Q4' V (by intro x hx; exact Finset.mem_union.mpr (Or.inl hx)) = Q3 := by
    ext v
    rfl
  have hnew :
      ∀ w (hw : w ∈ votersP1_10),
        Q4'.pref ⟨w, Finset.mem_union.mpr (Or.inr hw)⟩ = ballot_bdeac.toLinearOrder := by
    intro w hw
    have hwP4 : w ∈ votersP4 := by
      have h := congrArg (fun s => w ∈ s) votersP4_eq_union_votersP3_votersP1_10
      exact Eq.mp h (Finset.mem_union.mpr (Or.inr hw))
    have hballot : ballotsAll w = ballot_bdeac :=
      ballotsAll_eq_ballot_bdeac_of_mem_votersP1_10 hw
    have hP4pref :
        P4Profile.pref ⟨w, hwP4⟩ = ballot_bdeac.toLinearOrder := by
      change (ballotsAll w).toLinearOrder = ballot_bdeac.toLinearOrder
      rw [hballot]
    have hQ4pref :
        Q4.pref (liftVoter (u := u) ⟨w, hwP4⟩) = ballot_bdeac.toLinearOrder := by
      have h := hagree4 ⟨w, hwP4⟩
      rw [hP4pref] at h
      exact h
    simp only [Q4', castProfile]
    rw [show (⟨w, _⟩ : Electorate U450 (insert u votersP4)) =
      liftVoter (u := u) ⟨w, hwP4⟩ by apply Subtype.ext; rfl]
    exact hQ4pref
  exact
    not_mem_add_copies_of_not_mem (f := f) hpos V votersP1_10 hVW Q3 Q4' b
      ballot_bdeac.toLinearOrder hrest hnew ballot_bdeac_top_b hnot

lemma not_mem_P5_add_newVoter_of_not_mem_P4_add_newVoter {f : VotingRule} (hpos : PositiveInvolvement f)
    {u : U450} (hu : u ∉ votersP4)
    (Q4 : Profile (Electorate U450 (insert u votersP4)) A5)
    (hagree4 : ∀ v : Electorate U450 votersP4, Q4.pref (liftVoter (u := u) v) = P4Profile.pref v)
    (hd : d ∉ f Q4) :
    let V : Finset U450 := insert u votersP5
    let hV : V ⊆ insert u votersP4 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxP5
      · exact Finset.mem_insert.mpr (Or.inl rfl)
      · have hxP4 : x ∈ votersP4 := by
          have h := congrArg (fun s => x ∈ s) votersP4_eq_union_votersP5_votersP1_7
          exact Eq.mp h (Finset.mem_union.mpr (Or.inl hxP5))
        exact Finset.mem_insert.mpr (Or.inr hxP4)
    let Q5 : Profile (Electorate U450 V) A5 :=
      restrictElectorate Q4 V hV
    d ∉ f Q5 := by
  classical
  intro V hV Q5
  have hu17 : u ∉ votersP1_7 := by
    intro hu17
    have hu4 : u ∈ votersP4 := by
      have h := congrArg (fun s => u ∈ s) votersP4_eq_union_votersP5_votersP1_7
      exact Eq.mp h (Finset.mem_union.mpr (Or.inr hu17))
    exact hu hu4
  have hVW : Disjoint V votersP1_7 := by
    refine Finset.disjoint_left.2 ?_
    intro x hxV hx17
    rcases Finset.mem_insert.mp hxV with rfl | hxP5
    · exact hu17 hx17
    · exact (Finset.disjoint_left.mp votersP5_disjoint_votersP1_7) hxP5 hx17
  have hset :
      V ∪ votersP1_7 = insert u votersP4 := by
    have h' : votersP5 ∪ votersP1_7 = votersP4 := votersP4_eq_union_votersP5_votersP1_7
    calc
      V ∪ votersP1_7 = insert u (votersP5 ∪ votersP1_7) := by
        simp [V, Finset.insert_union]
      _ = insert u votersP4 := by simp [h']
  let Q4' : Profile (Electorate U450 (V ∪ votersP1_7)) A5 :=
    castProfile (h := hset.symm) Q4
  have hnot : d ∉ f Q4' := by
    have hcast : f Q4' = f Q4 := by
      dsimp [Q4']
      exact votingRule_castProfile (f := f) (h := hset.symm) (P := Q4)
    rw [hcast]
    exact hd
  have hrest :
      restrictElectorate Q4' V (by intro x hx; exact Finset.mem_union.mpr (Or.inl hx)) = Q5 := by
    ext v
    rfl
  have hnew :
      ∀ w (hw : w ∈ votersP1_7),
        Q4'.pref ⟨w, Finset.mem_union.mpr (Or.inr hw)⟩ = ballot_dbace.toLinearOrder := by
    intro w hw
    have hwP4 : w ∈ votersP4 := by
      have h := congrArg (fun s => w ∈ s) votersP4_eq_union_votersP5_votersP1_7
      exact Eq.mp h (Finset.mem_union.mpr (Or.inr hw))
    have hballot : ballotsAll w = ballot_dbace :=
      ballotsAll_eq_ballot_dbace_of_mem_votersP1_7 hw
    have hP4pref :
        P4Profile.pref ⟨w, hwP4⟩ = ballot_dbace.toLinearOrder := by
      change (ballotsAll w).toLinearOrder = ballot_dbace.toLinearOrder
      rw [hballot]
    have hQ4pref :
        Q4.pref (liftVoter (u := u) ⟨w, hwP4⟩) = ballot_dbace.toLinearOrder := by
      have h := hagree4 ⟨w, hwP4⟩
      rw [hP4pref] at h
      exact h
    simp only [Q4', castProfile]
    rw [show (⟨w, _⟩ : Electorate U450 (insert u votersP4)) =
      liftVoter (u := u) ⟨w, hwP4⟩ by apply Subtype.ext; rfl]
    exact hQ4pref
  exact
    not_mem_add_copies_of_not_mem (f := f) hpos V votersP1_7 hVW Q5 Q4' d
      ballot_dbace.toLinearOrder hrest hnew ballot_dbace_top_d hnot

lemma hagree_Q4raw_P4 {u2 : U450} (hu2 : u2 ∉ votersP4)
    (Q3 : Profile (Electorate U450 (insert u2 votersP3)) A5)
    (hagree3 : ∀ v : Electorate U450 votersP3, Q3.pref (liftVoter (u := u2) v) = P3Profile.pref v)
    (hdisj : Disjoint (insert u2 votersP3) votersP1_10) :
    let V3 : Finset U450 := insert u2 votersP3
    let Q4raw : Profile (Electorate U450 (V3 ∪ votersP1_10)) A5 :=
      addCopiesProfile (V := V3) (W := votersP1_10) Q3 ballot_bdeac.toLinearOrder
    ∀ v : Electorate U450 votersP4,
      ∀ hv_union : v.1 ∈ V3 ∪ votersP1_10,
        Q4raw.pref ⟨v.1, hv_union⟩ = P4Profile.pref v := by
  classical
  intro V3 Q4raw v hv_union
  rcases Finset.mem_union.mp hv_union with hvV3 | hv10
  · rcases Finset.mem_insert.mp hvV3 with h | hvP3
    · have hvP4 : u2 ∈ votersP4 := by
        simpa [h] using v.2
      exact (hu2 hvP4).elim
    · have hP4 : P4Profile.pref v = (ballotsAll v.1).toLinearOrder := by
        rfl
      have hP3 : P3Profile.pref ⟨v.1, hvP3⟩ = (ballotsAll v.1).toLinearOrder := by
        rfl
      have hQ3pref :
          Q3.pref ⟨v.1, by
            have : v.1 ∈ V3 := by
              exact Finset.mem_insert.mpr (Or.inr hvP3)
            exact this⟩ = (ballotsAll v.1).toLinearOrder := by
        have h := hagree3 ⟨v.1, hvP3⟩
        have hvV3' : v.1 ∈ V3 := Finset.mem_insert.mpr (Or.inr hvP3)
        have hsub :
            (liftVoter (u := u2) ⟨v.1, hvP3⟩ : Electorate U450 V3) = ⟨v.1, hvV3'⟩ := by
          apply Subtype.ext
          rfl
        rw [hsub] at h
        rw [hP3] at h
        exact h
      unfold Q4raw
      unfold addCopiesProfile
      change (if h : v.1 ∈ V3 then Q3.pref ⟨v.1, h⟩ else ballot_bdeac.toLinearOrder) =
        P4Profile.pref v
      simp only [dif_pos hvV3, hQ3pref, hP4]
  · have hballot : ballotsAll v.1 = ballot_bdeac :=
      ballotsAll_eq_ballot_bdeac_of_mem_votersP1_10 hv10
    have hP4 : P4Profile.pref v = (ballotsAll v.1).toLinearOrder := by
      rfl
    have hvV3' : v.1 ∉ V3 := by
      intro hvV3'
      exact (Finset.disjoint_left.mp hdisj hvV3' hv10).elim
    unfold Q4raw
    unfold addCopiesProfile
    change (if h : v.1 ∈ V3 then Q3.pref ⟨v.1, h⟩ else ballot_bdeac.toLinearOrder) =
      P4Profile.pref v
    simp only [dif_neg hvV3', hP4, hballot]

lemma not_mem_P5_add_twoVoters_of_not_mem_P4_add_twoVoters {f : VotingRule} (hpos : PositiveInvolvement f)
    {u2 u4 : U450} (hu2 : u2 ∉ votersP4) (hu4 : u4 ∉ votersP4)
    (Q4 : Profile (Electorate U450 (insert u4 (insert u2 votersP4))) A5)
    (hagree4 :
      ∀ v : Electorate U450 votersP4,
        Q4.pref (liftVoter (u := u4) (liftVoter (u := u2) v)) = P4Profile.pref v)
    (hd : d ∉ f Q4) :
    let V : Finset U450 := insert u4 (insert u2 votersP5)
    let hV : V ⊆ insert u4 (insert u2 votersP4) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_insert.mpr (Or.inl rfl)
      rcases Finset.mem_insert.mp hx with rfl | hxP5
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl rfl)))
      · have hxP4 : x ∈ votersP4 := by
          have h := congrArg (fun s => x ∈ s) votersP4_eq_union_votersP5_votersP1_7
          exact Eq.mp h (Finset.mem_union.mpr (Or.inl hxP5))
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr hxP4)))
    let Q5 : Profile (Electorate U450 V) A5 :=
      restrictElectorate Q4 V hV
    d ∉ f Q5 := by
  classical
  intro V hV Q5
  have hu217 : u2 ∉ votersP1_7 := by
    intro hu217
    exact hu2 (votersP1_7_subset_votersP4 hu217)
  have hu417 : u4 ∉ votersP1_7 := by
    intro hu417
    exact hu4 (votersP1_7_subset_votersP4 hu417)
  have hVW : Disjoint V votersP1_7 := by
    refine Finset.disjoint_left.2 ?_
    intro x hxV hx17
    rcases Finset.mem_insert.mp hxV with rfl | hxV
    · exact hu417 hx17
    rcases Finset.mem_insert.mp hxV with rfl | hxP5
    · exact hu217 hx17
    · exact (Finset.disjoint_left.mp votersP5_disjoint_votersP1_7) hxP5 hx17
  have hset :
      V ∪ votersP1_7 = insert u4 (insert u2 votersP4) := by
    have h' : votersP5 ∪ votersP1_7 = votersP4 := votersP4_eq_union_votersP5_votersP1_7
    calc
      V ∪ votersP1_7 = insert u4 ((insert u2 votersP5) ∪ votersP1_7) := by
        simp [V, Finset.insert_union]
      _ = insert u4 (insert u2 (votersP5 ∪ votersP1_7)) := by
        simp [Finset.insert_union]
      _ = insert u4 (insert u2 votersP4) := by simp [h']
  let Q4' : Profile (Electorate U450 (V ∪ votersP1_7)) A5 :=
    castProfile (h := hset.symm) Q4
  have hnot : d ∉ f Q4' := by
    have hcast : f Q4' = f Q4 := by
      dsimp [Q4']
      exact votingRule_castProfile (f := f) (h := hset.symm) (P := Q4)
    rw [hcast]
    exact hd
  have hrest :
      restrictElectorate Q4' V (by intro x hx; exact Finset.mem_union.mpr (Or.inl hx)) = Q5 := by
    ext v
    rfl
  have hnew :
      ∀ w (hw : w ∈ votersP1_7),
        Q4'.pref ⟨w, Finset.mem_union.mpr (Or.inr hw)⟩ = ballot_dbace.toLinearOrder := by
    intro w hw
    have hwP4 : w ∈ votersP4 := votersP1_7_subset_votersP4 hw
    have hballot : ballotsAll w = ballot_dbace :=
      ballotsAll_eq_ballot_dbace_of_mem_votersP1_7 hw
    have hP4pref :
        P4Profile.pref ⟨w, hwP4⟩ = ballot_dbace.toLinearOrder := by
      change (ballotsAll w).toLinearOrder = ballot_dbace.toLinearOrder
      rw [hballot]
    have hQ4pref :
        Q4.pref (liftVoter (u := u4) (liftVoter (u := u2) ⟨w, hwP4⟩)) =
          ballot_dbace.toLinearOrder := by
      have h := hagree4 ⟨w, hwP4⟩
      rw [hP4pref] at h
      exact h
    simp only [Q4', castProfile]
    rw [show (⟨w, _⟩ : Electorate U450 (insert u4 (insert u2 votersP4))) =
      liftVoter (u := u4) (liftVoter (u := u2) ⟨w, hwP4⟩) by
        apply Subtype.ext
        rfl]
    exact hQ4pref
  exact
    not_mem_add_copies_of_not_mem (f := f) hpos V votersP1_7 hVW Q5 Q4' d
      ballot_dbace.toLinearOrder hrest hnew ballot_dbace_top_d hnot

end Holliday

end SocialChoice
