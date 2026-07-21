import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Finset.Fin
import SocialChoice.Impossibilities.Holliday.Profiles

namespace SocialChoice

namespace Holliday

abbrev u280 : U450 := ⟨280, by decide⟩
abbrev u449 : U450 := ⟨449, by decide⟩

def Wpool : Finset U450 := Finset.Icc u280 u449

lemma Wpool_card : Wpool.card = 170 := by
  simp [Wpool, u280, u449]

lemma Wpool_erase_card_ge_169 (u : U450) : 169 ≤ (Wpool.erase u).card := by
  by_cases hu : u ∈ Wpool
  · simp [hu, Wpool_card]
  · simp [hu, Wpool_card]

lemma Wpool_erase_erase_card_ge_168 (u1 u2 : U450) :
    168 ≤ ((Wpool.erase u1).erase u2).card := by
  by_cases h1 : u1 ∈ Wpool
  · have hcard1 : (Wpool.erase u1).card = 169 := by
      simp [h1, Wpool_card]
    by_cases h2 : u2 ∈ Wpool.erase u1
    · simp [h2, hcard1]
    · simp [h2, hcard1]
  · have hcard1 : (Wpool.erase u1).card = 170 := by
      simp [h1, Wpool_card]
    by_cases h2 : u2 ∈ Wpool.erase u1
    · simp [h2, hcard1]
    · simp [h2, hcard1]

private lemma mem_Iio_u280_of_val_lt {v : U450} (hv : v.val < 280) :
    v ∈ Finset.Iio u280 := by
  apply Finset.mem_Iio.mpr
  change v.val < u280.val
  exact hv

lemma disjoint_Iio_u280_Wpool : Disjoint (Finset.Iio u280) Wpool := by
  refine Finset.disjoint_left.2 ?_
  intro v hvIio hvW
  have hvlt : v < u280 := by simpa using hvIio
  have hvge : u280 ≤ v := (Finset.mem_Icc.mp hvW).1
  exact (not_lt_of_ge hvge) hvlt

lemma exists_disjoint_W_of_card_le_170 {V : Finset U450} (hV : V ⊆ Finset.Iio u280)
    {k : ℕ} (hk : k ≤ 170) :
    ∃ W : Finset U450, Disjoint V W ∧ W.card = k := by
  classical
  have hk' : k ≤ Wpool.card := by
    simpa [Wpool_card] using hk
  obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq (s := Wpool) hk'
  refine ⟨W, ?_, hWcard⟩
  refine Finset.disjoint_left.2 ?_
  intro v hvV hvW
  have hvIio : v ∈ Finset.Iio u280 := hV hvV
  have hvWpool : v ∈ Wpool := hWsub hvW
  exact (Finset.disjoint_left.1 disjoint_Iio_u280_Wpool) hvIio hvWpool

lemma exists_disjoint_W_of_int_card_le_170 {V : Finset U450} (hV : V ⊆ Finset.Iio u280)
    {k : Int} (hk0 : 0 ≤ k) (hk : k.toNat ≤ 170) :
    ∃ W : Finset U450, Disjoint V W ∧ (W.card : Int) = k := by
  obtain ⟨W, hdisj, hcard⟩ := exists_disjoint_W_of_card_le_170 (V := V) hV hk
  refine ⟨W, hdisj, ?_⟩
  have hk' : (k.toNat : Int) = k := by
    simp [hk0]
  calc
    (W.card : Int) = (k.toNat : Int) := by simp [hcard]
    _ = k := hk'

lemma exists_disjoint_W_insert_of_int_card_le_168 {V : Finset U450}
    (hV : V ⊆ Finset.Iio u280) {u : U450}
    {k : Int} (hk0 : 0 ≤ k) (hk : k.toNat ≤ 168) :
    ∃ W : Finset U450, Disjoint (insert u V) W ∧ (W.card : Int) = k := by
  classical
  have hk' : k.toNat ≤ (Wpool.erase u).card := by
    have hcard : 168 ≤ (Wpool.erase u).card := by
      exact le_trans (by decide : 168 ≤ 169) (Wpool_erase_card_ge_169 u)
    exact le_trans hk hcard
  obtain ⟨W, hWsub, hcard⟩ := Finset.exists_subset_card_eq (s := Wpool.erase u) hk'
  refine ⟨W, ?_, ?_⟩
  · refine Finset.disjoint_left.2 ?_
    intro v hvins hvW
    rcases Finset.mem_insert.mp hvins with rfl | hvV
    · have : v ∉ Wpool.erase v := by simp
      exact this (hWsub hvW)
    · have hvIio : v ∈ Finset.Iio u280 := hV hvV
      have hsub : Wpool.erase u ⊆ Wpool := Finset.erase_subset u Wpool
      have hvWpool : v ∈ Wpool := hsub (hWsub hvW)
      exact (Finset.disjoint_left.1 disjoint_Iio_u280_Wpool) hvIio hvWpool
  · have hk' : (k.toNat : Int) = k := by
      simp [hk0]
    calc
      (W.card : Int) = (k.toNat : Int) := by simp [hcard]
      _ = k := hk'

lemma exists_disjoint_W_insert_insert_of_int_card_le_168 {V : Finset U450}
    (hV : V ⊆ Finset.Iio u280) {u1 u2 : U450}
    {k : Int} (hk0 : 0 ≤ k) (hk : k.toNat ≤ 168) :
    ∃ W : Finset U450, Disjoint (insert u1 (insert u2 V)) W ∧ (W.card : Int) = k := by
  classical
  have hk' : k.toNat ≤ ((Wpool.erase u1).erase u2).card := by
    have hcard : 168 ≤ ((Wpool.erase u1).erase u2).card :=
      Wpool_erase_erase_card_ge_168 u1 u2
    exact le_trans hk hcard
  obtain ⟨W, hWsub, hcard⟩ :=
    Finset.exists_subset_card_eq (s := (Wpool.erase u1).erase u2) hk'
  refine ⟨W, ?_, ?_⟩
  · refine Finset.disjoint_left.2 ?_
    intro v hvins hvW
    rcases Finset.mem_insert.mp hvins with rfl | hvins
    · have : v ∉ (Wpool.erase v).erase u2 := by simp
      exact this (hWsub hvW)
    rcases Finset.mem_insert.mp hvins with rfl | hvV
    · have : v ∉ (Wpool.erase u1).erase v := by simp
      exact this (hWsub hvW)
    · have hvIio : v ∈ Finset.Iio u280 := hV hvV
      have hsub1 : (Wpool.erase u1).erase u2 ⊆ Wpool.erase u1 :=
        Finset.erase_subset u2 (Wpool.erase u1)
      have hsub2 : Wpool.erase u1 ⊆ Wpool := Finset.erase_subset u1 Wpool
      have hsub : (Wpool.erase u1).erase u2 ⊆ Wpool := by
        intro w hw
        exact hsub2 (hsub1 hw)
      have hvWpool : v ∈ Wpool := hsub (hWsub hvW)
      exact (Finset.disjoint_left.1 disjoint_Iio_u280_Wpool) hvIio hvWpool
  · have hk' : (k.toNat : Int) = k := by
      simp [hk0]
    calc
      (W.card : Int) = (k.toNat : Int) := by simp [hcard]
      _ = k := hk'

lemma votersP1_subset_Iio_u280 : votersP1 ⊆ Finset.Iio u280 := by
  intro v hv
  have hv' : v.val < p1_cut8 := (Finset.mem_filter.mp hv).2
  have hv'' : v.val < 280 := lt_of_lt_of_le hv' (by decide : p1_cut8 ≤ 280)
  exact mem_Iio_u280_of_val_lt hv''

lemma votersP2_subset_Iio_u280 : votersP2 ⊆ Finset.Iio u280 := by
  intro v hv
  have hv' : v.val < p1_cut9 := (Finset.mem_filter.mp hv).2
  have hv'' : v.val < 280 := lt_of_lt_of_le hv' (by decide : p1_cut9 ≤ 280)
  exact mem_Iio_u280_of_val_lt hv''

lemma votersP3_subset_Iio_u280 : votersP3 ⊆ Finset.Iio u280 := by
  intro v hv
  have hv' :
      v.val < p1_cut1 ∨ (p1_cut2 ≤ v.val ∧ v.val < p1_cut9) := (Finset.mem_filter.mp hv).2
  have hvlt : v.val < p1_cut9 := by
    rcases hv' with hlt | hmid
    · exact lt_of_lt_of_le hlt (by decide : p1_cut1 ≤ p1_cut9)
    · exact hmid.2
  have hv'' : v.val < 280 := lt_of_lt_of_le hvlt (by decide : p1_cut9 ≤ 280)
  exact mem_Iio_u280_of_val_lt hv''

lemma votersP4_subset_Iio_u280 : votersP4 ⊆ Finset.Iio u280 := by
  intro v hv
  have hv' :
      v.val < p1_cut1 ∨ (p1_cut2 ≤ v.val ∧ v.val < p1_cut10) := (Finset.mem_filter.mp hv).2
  have hvlt : v.val < p1_cut10 := by
    rcases hv' with hlt | hmid
    · exact lt_of_lt_of_le hlt (by decide : p1_cut1 ≤ p1_cut10)
    · exact hmid.2
  have hv'' : v.val < 280 := lt_of_lt_of_le hvlt (by decide : p1_cut10 ≤ 280)
  exact mem_Iio_u280_of_val_lt hv''

lemma votersP5_subset_Iio_u280 : votersP5 ⊆ Finset.Iio u280 := by
  intro v hv
  have hv' :
      v.val < p1_cut1 ∨
        (p1_cut2 ≤ v.val ∧ v.val < p1_cut6) ∨
        (p1_cut7 ≤ v.val ∧ v.val < p1_cut10) := (Finset.mem_filter.mp hv).2
  have hvlt : v.val < p1_cut10 := by
    rcases hv' with hlt | hmid | hhigh
    · exact lt_of_lt_of_le hlt (by decide : p1_cut1 ≤ p1_cut10)
    · exact lt_of_lt_of_le hmid.2 (by decide : p1_cut6 ≤ p1_cut10)
    · exact hhigh.2
  have hv'' : v.val < 280 := lt_of_lt_of_le hvlt (by decide : p1_cut10 ≤ 280)
  exact mem_Iio_u280_of_val_lt hv''

end Holliday

end SocialChoice
