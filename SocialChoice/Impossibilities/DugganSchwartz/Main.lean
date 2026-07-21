import SocialChoice.Impossibilities.DugganSchwartz.DictatingSet
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find

namespace SocialChoice

open Finset

variable {V A : Type} [Fintype V] [Fintype A] [Nonempty A]

section BallotTopSet

variable [DecidableEq A]

noncomputable def ballotTopSetList (S : Finset A) (a : A) : List A :=
  a :: (S.erase a).toList ++ (Finset.univ \ S).toList

omit [Nonempty A] in
lemma ballotTopSetList_nodup (S : Finset A) (a : A) (ha : a ∈ S) :
    (ballotTopSetList S a).Nodup := by
  classical
  have hnodup_erase : (S.erase a).toList.Nodup := by
    simpa using (S.erase a).nodup_toList
  have hnodup_rest : (Finset.univ \ S).toList.Nodup := by
    simpa using (Finset.univ \ S).nodup_toList
  have ha_not_erase : a ∉ (S.erase a).toList := by
    have : a ∉ (S.erase a) := by simp
    simp [Finset.mem_toList, this]
  have ha_not_rest : a ∉ (Finset.univ \ S).toList := by
    have : a ∉ (Finset.univ \ S) := by
      simp [ha]
    simpa [Finset.mem_toList] using this
  have hdisjoint :
      List.Disjoint (S.erase a).toList (Finset.univ \ S).toList := by
    refine List.disjoint_left.2 ?_
    intro x hxS hxR
    have hxS' : x ∈ (S.erase a) := by
      simpa [Finset.mem_toList] using hxS
    have hxR' : x ∈ (Finset.univ \ S) := by
      simpa [Finset.mem_toList] using hxR
    have hxS_in : x ∈ S := (Finset.mem_erase.mp hxS').2
    have hxR_not : x ∉ S := (Finset.mem_sdiff.mp hxR').2
    exact (hxR_not hxS_in).elim
  have htail :
      ((S.erase a).toList ++ (Finset.univ \ S).toList).Nodup := by
    exact List.Nodup.append hnodup_erase hnodup_rest hdisjoint
  have ha_not_tail :
      a ∉ (S.erase a).toList ++ (Finset.univ \ S).toList := by
    intro hmem
    have hmem' :
        a ∈ (S.erase a).toList ∨ a ∈ (Finset.univ \ S).toList := by
      simpa [List.mem_append] using hmem
    cases hmem' with
    | inl h => exact ha_not_erase h
    | inr h => exact ha_not_rest h
  have hnodup :
      (a :: (S.erase a).toList ++ (Finset.univ \ S).toList).Nodup := by
    exact List.nodup_cons.2 ⟨ha_not_tail, htail⟩
  simpa [ballotTopSetList] using hnodup

omit [Nonempty A] in
lemma ballotTopSetList_complete (S : Finset A) (a : A) (ha : a ∈ S) :
    ∀ x : A, x ∈ ballotTopSetList S a := by
  classical
  intro x
  by_cases hx : x = a
  · subst hx
    simp [ballotTopSetList]
  by_cases hxS : x ∈ S
  · have hx' : x ∈ S.erase a := by
      simp [Finset.mem_erase, hx, hxS]
    have hx_list : x ∈ (S.erase a).toList := by
      simpa [Finset.mem_toList] using hx'
    simp [ballotTopSetList, hx, hx_list]
  · have hx' : x ∈ (Finset.univ \ S) := by
      have hx_univ : x ∈ (Finset.univ : Finset A) := by simp
      exact Finset.mem_sdiff.mpr ⟨hx_univ, hxS⟩
    have hx_list : x ∈ (Finset.univ \ S).toList := by
      simpa [Finset.mem_toList] using hx'
    simp [ballotTopSetList, hx, hxS, hx_list]

@[reducible] noncomputable def ballotTopSet
    (S : Finset A) (a : A) (ha : a ∈ S) : LinearOrder A := by
  classical
  exact linearOrderOfList (ballotTopSetList S a)
    (ballotTopSetList_nodup S a ha)
    (ballotTopSetList_complete S a ha)

omit [Nonempty A] in
lemma ballotTopSet_topSet (S : Finset A) (a : A) (ha : a ∈ S) :
    BallotTopSet (ballotTopSet S a ha) S := by
  classical
  intro x y hx hy
  let lS : List A := a :: (S.erase a).toList
  let lT : List A := (Finset.univ \ S).toList
  let l : List A := lS ++ lT
  have hx_in_lS : x ∈ lS := by
    by_cases hxa : x = a
    · subst hxa
      simp [lS]
    · have hx' : x ∈ S.erase a := by
        simp [Finset.mem_erase, hx, hxa]
      have hx_list : x ∈ (S.erase a).toList := by
        simpa [Finset.mem_toList] using hx'
      simp [lS, hxa, hx_list]
  have hy_not_lS : y ∉ lS := by
    intro hy_lS
    have hy_cases : y = a ∨ y ∈ (S.erase a).toList := by
      simpa [lS, List.mem_cons, List.mem_append] using hy_lS
    cases hy_cases with
    | inl hy_eq =>
        subst hy_eq
        exact hy ha
    | inr hy_mem =>
        have hy_mem' : y ∈ S.erase a := by
          simpa [Finset.mem_toList] using hy_mem
        have hyS : y ∈ S := (Finset.mem_erase.mp hy_mem').2
        exact hy hyS
  have hx_idx_lt : l.idxOf x < lS.length := by
    have hx_lt : lS.idxOf x < lS.length := List.idxOf_lt_length_of_mem hx_in_lS
    have hx_idx : l.idxOf x = lS.idxOf x := by
      simpa [l] using (List.idxOf_append_of_mem (l₁ := lS) (l₂ := lT) hx_in_lS)
    simpa [hx_idx] using hx_lt
  have hy_idx_ge : lS.length ≤ l.idxOf y := by
    have hy_idx : l.idxOf y = lS.length + lT.idxOf y := by
      simpa [l] using (List.idxOf_append_of_notMem (l₁ := lS) (l₂ := lT) hy_not_lS)
    have hle : lS.length ≤ lS.length + lT.idxOf y := Nat.le_add_right _ _
    simp [hy_idx, hle]
  have hlt : l.idxOf x < l.idxOf y := lt_of_lt_of_le hx_idx_lt hy_idx_ge
  have hlt' :
      (linearOrderOfList l (ballotTopSetList_nodup S a ha)
        (ballotTopSetList_complete S a ha)).lt x y := by
    exact (linearOrderOfList_lt_iff_idxOf (l := l)
      (hnodup := ballotTopSetList_nodup S a ha)
      (hcomplete := ballotTopSetList_complete S a ha) x y).2 hlt
  change
    (linearOrderOfList (ballotTopSetList S a)
      (ballotTopSetList_nodup S a ha) (ballotTopSetList_complete S a ha)).lt x y
  have hl : l = ballotTopSetList S a := by
    simp only [l, lS, lT, ballotTopSetList]
  subst l
  exact hlt'

omit [Nonempty A] in
lemma ballotTopSet_prefers_top (S : Finset A) (a b : A) (ha : a ∈ S) (hb : b ≠ a) :
    (ballotTopSet S a ha).lt a b := by
  classical
  let l := ballotTopSetList S a
  let tail := (S.erase a).toList ++ (Finset.univ \ S).toList
  have hidxa : l.idxOf a = 0 := by
    simp [ballotTopSetList, l]
  have hidxb : l.idxOf b = Nat.succ (tail.idxOf b) := by
    simpa [l, ballotTopSetList, tail] using
      (List.idxOf_cons_ne (a := b) (b := a) (l := tail) hb.symm)
  have hlt : l.idxOf a < l.idxOf b := by
    simp [hidxa, hidxb]
  have hlt' :
      (linearOrderOfList l (ballotTopSetList_nodup S a ha)
        (ballotTopSetList_complete S a ha)).lt a b := by
    exact (linearOrderOfList_lt_iff_idxOf (l := l)
      (hnodup := ballotTopSetList_nodup S a ha)
      (hcomplete := ballotTopSetList_complete S a ha) a b).2 hlt
  simpa [ballotTopSet, l] using hlt'

end BallotTopSet

omit [Nonempty A] in
lemma winners_subset_of_ballotTopSet_update (f : VotingRule)
    (hf_pess : PessimistStrategyproof f)
    (P : Profile V A) (v : V) (ballot : LinearOrder A) (S : Finset A)
    (hsubset : f P ⊆ S)
    (hBallot : BallotTopSet ballot S) :
    f (updateProfile P v ballot) ⊆ S := by
  classical
  intro y hy
  by_contra hyS
  let P' := updateProfile P v ballot
  have hback : updateProfile P' v (P.pref v) = P := by
    apply Profile.ext
    intro u
    unfold P' updateProfile
    by_cases h : u = v
    · subst u
      simp only [if_true]
    · simp only [if_neg h]
  have hmanip :
      ∃ x ∈ f P', ∀ y' ∈ f (updateProfile P' v (P.pref v)), Prefers P' v y' x := by
    refine ⟨y, hy, ?_⟩
    intro y' hy'
    have hy'_P : y' ∈ f P := by
      simpa [hback] using hy'
    have hy'_S : y' ∈ S := hsubset hy'_P
    have hlt : ballot.lt y' y := hBallot y' y hy'_S hyS
    unfold Prefers
    rw [show P'.pref v = ballot by simp only [P', updateProfile, if_true]]
    exact hlt
  exact (hf_pess P' v (P.pref v)) hmanip

omit [Nonempty A] in
lemma singleton_winner_of_topSet (f : VotingRule)
    (hf_total : IsVotingRule f)
    (hf_opt : OptimistStrategyproof f)
    (hf_pess : PessimistStrategyproof f)
    (hviable : Viable f)
    (P : Profile V A) (a : A)
    (hTop : TopSet P {a}) :
    f P = {a} := by
  classical
  have hmono_singleton : DownMonotonicitySingleton f :=
    downMonotonicity_of_opt_pess_sp f hf_total hf_opt hf_pess
  have hmono : DownMonotonicity f :=
    downMonotonicity_of_singleton (f := f) hmono_singleton
  obtain ⟨P_a, hPa⟩ := hviable (V := V) (A := A) a
  have hdown : DownObtainable (V := V) (A := A) a P_a P := by
    intro v b hpb
    have hb_ne : b ≠ a := by
      intro hb
      subst hb
      let _ := P_a.pref v
      simp [Prefers] at hpb
    have htop : TopRank P v a :=
      (topSet_singleton_iff_topRank (P := P) (c := a)).1 hTop v
    exact htop b hb_ne
  exact hmono P_a P a hPa hdown

/-! ## Duggan-Schwartz Theorem (Taylor 2002, Thm 2.2) -/

theorem duggan_schwartz
    (f : VotingRule)
    (hf_total : IsVotingRule f)
    (hf_opt : OptimistStrategyproof f)
    (hf_pess : PessimistStrategyproof f)
    (hviable : Viable f)
    (hcard : 3 ≤ Fintype.card A) :
    ∃ i : V, ∀ P : Profile V A, topChoice P i ∈ f P := by
  classical
  letI := Classical.decEq V
  letI := Classical.decEq A
  obtain ⟨i, hi⟩ :=
    exists_voter_topRank_of_singleton_winner (V := V) (A := A) (f := f) (hf_total := hf_total)
      (hf_opt := hf_opt) (hf_pess := hf_pess) (hviable := hviable) (hcard := hcard)
  refine ⟨i, ?_⟩
  by_contra hbad
  have hbad' : ∃ P : Profile V A, topChoice P i ∉ f P := by
    simpa [not_forall] using hbad
  let bad_card : Nat → Prop := fun n =>
    ∃ P : Profile V A, topChoice P i ∉ f P ∧ (f P).card = n
  have hbad_card : ∃ n, bad_card n := by
    rcases hbad' with ⟨P, hP⟩
    exact ⟨(f P).card, ⟨P, hP, rfl⟩⟩
  let m := Nat.find hbad_card
  have hm_spec : bad_card m := Nat.find_spec hbad_card
  rcases hm_spec with ⟨P0, hP0_bad, hP0_card⟩
  let x := topChoice P0 i
  let S : Finset A := f P0
  have hx_not : x ∉ S := by simpa [x, S] using hP0_bad
  have hS_card : S.card = m := by simpa [S] using hP0_card
  have hS_nonempty : S.Nonempty := hf_total P0
  have hcard_ge2 : 2 ≤ S.card := by
    by_contra hcard
    have hcard_lt2 : S.card < 2 := lt_of_not_ge hcard
    have hcard_pos : 0 < S.card := Finset.card_pos.mpr hS_nonempty
    have hle1 : S.card ≤ 1 := Nat.lt_succ_iff.mp hcard_lt2
    have hge1 : 1 ≤ S.card := Nat.succ_le_iff.mpr hcard_pos
    have hcard1 : S.card = 1 := Nat.le_antisymm hle1 hge1
    obtain ⟨a, haS⟩ := (Finset.card_eq_one).1 hcard1
    have hfa : f P0 = {a} := by simp [S, haS]
    have htop : TopRank P0 i a := hi P0 a hfa
    have hx_eq : x = a := by
      have h := eq_topChoice_of_topRank (P := P0) (v := i) (c := a) htop
      simpa [x] using h.symm
    have hx_mem : x ∈ f P0 := by
      simp [x, hx_eq, hfa]
    exact (hx_not hx_mem).elim
  letI := P0.pref i
  let a := Finset.min' S hS_nonempty
  have ha_mem : a ∈ S := Finset.min'_mem S hS_nonempty
  have h_pref_min : ∀ b ∈ S, b ≠ a → Prefers P0 i a b := by
    intro b hb hbne
    have hle : a ≤ b := Finset.min'_le S b hb
    have hlt : a < b := lt_of_le_of_ne hle (Ne.symm hbne)
    simpa [Prefers] using hlt
  let ballot := ballotTopSet S a ha_mem
  let P_top : Profile V A := { pref := fun _ => ballot }
  let others : Finset V := Finset.univ.erase i
  let P1 : Profile V A := profileUpdateSet P0 P_top others
  have hpref_i : P1.pref i = P0.pref i := by
    simp [P1, profileUpdateSet, others]
  have htop_x : TopRank P0 i x := topChoice_topRank (P := P0) (v := i)
  have htop_x' : TopRank P1 i x := by
    intro d hd
    have h := htop_x d hd
    unfold Prefers at h ⊢
    rw [hpref_i]
    exact h
  have hx_eq_P1 : topChoice P1 i = x := by
    have h := eq_topChoice_of_topRank (P := P1) (v := i) (c := x) htop_x'
    simpa using h.symm
  have hsubset_updates :
      f (profileUpdateSet P0 P_top others) ⊆ S := by
    refine Finset.induction_on (s := others) ?base ?step
    · simp [profileUpdateSet_empty, S]
    · intro v T hv hT
      let Q := profileUpdateSet P0 P_top T
      have hBallot : BallotTopSet ballot S :=
        ballotTopSet_topSet (S := S) (a := a) ha_mem
      have hsubset' :
          f (updateProfile Q v ballot) ⊆ S :=
        winners_subset_of_ballotTopSet_update (f := f) (hf_pess := hf_pess)
          (P := Q) (v := v) (ballot := ballot) (S := S) hT hBallot
      have hupdate :=
        profileUpdateSet_insert (P := P0) (P' := P_top) (S := T) (v := v) hv
      have hupdate' :
          profileUpdateSet P0 P_top (insert v T) =
            updateProfile Q v ballot := by
        simpa [Q, P_top, ballot] using hupdate
      simpa [hupdate'] using hsubset'
  have hsubset_P1 : f P1 ⊆ S := by
    simpa [P1] using hsubset_updates
  have hx_not_P1 : topChoice P1 i ∉ f P1 := by
    have hx_not' : x ∉ f P1 := by
      intro hx_mem
      exact hx_not (hsubset_P1 hx_mem)
    simpa [hx_eq_P1] using hx_not'
  have hmin_le : m ≤ (f P1).card :=
    Nat.find_min' hbad_card ⟨P1, hx_not_P1, rfl⟩
  have hcard_ge : S.card ≤ (f P1).card := by
    simpa [hS_card] using hmin_le
  have hP1_eq : f P1 = S :=
    Finset.eq_of_subset_of_card_le hsubset_P1 hcard_ge
  have hcard_gt1 : 1 < S.card := lt_of_lt_of_le (by decide : 1 < 2) hcard_ge2
  obtain ⟨b, hbS, hbne⟩ :=
    Finset.exists_mem_ne (s := S) (by simpa using hcard_gt1) a
  have h_pref_ab : Prefers P1 i a b := by
    have h := h_pref_min b hbS hbne
    unfold Prefers at h ⊢
    rw [hpref_i]
    exact h
  have hTop_a : TopSet P_top {a} := by
    refine (topSet_singleton_iff_topRank (P := P_top) (c := a)).2 ?_
    intro v d hd
    have h := ballotTopSet_prefers_top (S := S) (a := a) (b := d) ha_mem hd
    simpa [P_top, Prefers] using h
  have hPtop : f P_top = {a} :=
    singleton_winner_of_topSet (f := f) (hf_total := hf_total) (hf_opt := hf_opt)
      (hf_pess := hf_pess) (hviable := hviable) (P := P_top) (a := a) hTop_a
  have hupdate : updateProfile P1 i ballot = P_top := by
    apply Profile.ext
    intro u
    unfold updateProfile
    by_cases hu : u = i
    · subst u
      simp only [if_true]
      rfl
    · have hu' : u ∈ others := by
        simp [others, hu]
      simp only [if_neg hu]
      change (if u ∈ others then P_top.pref u else P0.pref u) = P_top.pref u
      rw [if_pos hu']
  have hmanip :
      ∃ x ∈ f P1, ∀ y ∈ f (updateProfile P1 i ballot), Prefers P1 i y x := by
    refine ⟨b, ?_, ?_⟩
    · simpa [hP1_eq] using hbS
    · intro y hy
      have hy' : y = a := by
        have : y ∈ f P_top := by simpa [hupdate] using hy
        have : y ∈ ({a} : Finset A) := by simpa [hPtop] using this
        simpa using this
      subst hy'
      exact h_pref_ab
  exact (hf_pess P1 i ballot) hmanip

end SocialChoice
