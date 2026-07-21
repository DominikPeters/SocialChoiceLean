import SocialChoice.Impossibilities.DugganSchwartz.TopSet
import SocialChoice.Impossibilities.DugganSchwartz.DownMonotonicity
import SocialChoice.Impossibilities.DugganSchwartz.Viable

namespace SocialChoice

open Finset

variable {V A : Type} [Fintype V] [Fintype A]

/-! ## aXb and Dictating Sets -/

/-- `aXb` means that whenever everyone in `X` prefers `a` to `b`,
    the unique winner cannot be `b`. -/
def aXb (f : VotingRule) (X : Finset V) (a b : A) : Prop :=
  ∀ P : Profile V A, (∀ v : V, v ∈ X → Prefers P v a b) → f P ≠ {b}

/-- A dictating set `X` blocks every distinct `b` from being the unique winner
    whenever `X` prefers `a` to `b`. -/
def DictatingSet (f : VotingRule) (X : Finset V) : Prop :=
  ∀ a b : A, a ≠ b → aXb (V := V) (A := A) f X a b

/-! ## Lemma 2.6 (Taylor 2002) -/

variable [DecidableEq V] [DecidableEq A]

@[reducible] noncomputable def ballotTopAB (a b : A) (hab : a ≠ b) : LinearOrder A := by
  classical
  let rest : Finset A := (Finset.univ.erase a).erase b
  let l : List A := a :: b :: rest.toList
  have hrest_nodup : rest.toList.Nodup := by
    simpa using rest.nodup_toList
  have ha_rest : a ∉ rest.toList := by
    have : a ∉ rest := by simp [rest]
    simpa [Finset.mem_toList] using this
  have hb_rest : b ∉ rest.toList := by
    have : b ∉ rest := by simp [rest]
    simpa [Finset.mem_toList] using this
  have hnodup_b : (b :: rest.toList).Nodup := by
    exact List.nodup_cons.2 ⟨hb_rest, hrest_nodup⟩
  have hnodup : l.Nodup := by
    apply List.nodup_cons.2
    refine ⟨?_, hnodup_b⟩
    simp [ha_rest, hab]
  have hcomplete : ∀ x : A, x ∈ l := by
    intro x
    by_cases hxa : x = a
    · subst hxa
      simp [l]
    by_cases hxb : x = b
    · subst hxb
      simp [l, hxa]
    have hx_mem : x ∈ rest := by
      simp [rest, hxa, hxb]
    have hx_mem' : x ∈ rest.toList := by
      simpa [Finset.mem_toList] using hx_mem
    simp [l, hxa, hxb, hx_mem']
  exact linearOrderOfList l hnodup hcomplete

@[reducible] noncomputable def profileTopAB (a b : A) (hab : a ≠ b) : Profile V A :=
  { pref := fun _ => ballotTopAB (A := A) a b hab }

/-! ## Three-Alternative Top Ballots -/

@[reducible] noncomputable def ballotTopABC (a b c : A)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    LinearOrder A := by
  classical
  let rest : Finset A := ((Finset.univ.erase a).erase b).erase c
  let l : List A := a :: b :: c :: rest.toList
  have hrest_nodup : rest.toList.Nodup := by
    simpa using rest.nodup_toList
  have ha_rest : a ∉ rest.toList := by
    have : a ∉ rest := by simp [rest]
    simpa [Finset.mem_toList] using this
  have hb_rest : b ∉ rest.toList := by
    have : b ∉ rest := by simp [rest]
    simpa [Finset.mem_toList] using this
  have hc_rest : c ∉ rest.toList := by
    have : c ∉ rest := by simp [rest]
    simpa [Finset.mem_toList] using this
  have hnodup_c : (c :: rest.toList).Nodup := by
    exact List.nodup_cons.2 ⟨hc_rest, hrest_nodup⟩
  have hnodup_b : (b :: c :: rest.toList).Nodup := by
    apply List.nodup_cons.2
    refine ⟨?_, hnodup_c⟩
    simp [hb_rest, hbc]
  have hnodup : l.Nodup := by
    apply List.nodup_cons.2
    refine ⟨?_, hnodup_b⟩
    simp [ha_rest, hab, hac]
  have hcomplete : ∀ x : A, x ∈ l := by
    intro x
    by_cases hxa : x = a
    · subst hxa
      simp [l]
    by_cases hxb : x = b
    · subst hxb
      simp [l, hxa]
    by_cases hxc : x = c
    · subst hxc
      simp [l, hxa, hxb]
    have hx_mem : x ∈ rest := by
      simp [rest, hxa, hxb, hxc]
    have hx_mem' : x ∈ rest.toList := by
      simpa [Finset.mem_toList] using hx_mem
    simp [l, hxa, hxb, hxc, hx_mem']
  exact linearOrderOfList l hnodup hcomplete

@[reducible] noncomputable def profileTopABC (a b c : A)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Profile V A :=
  { pref := fun _ => ballotTopABC (A := A) a b c hab hac hbc }

lemma ballotTopABC_prefers_first_second (a b c : A) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (ballotTopABC (A := A) a b c hab hac hbc).lt a b := by
  classical
  let rest : Finset A := ((Finset.univ.erase a).erase b).erase c
  let l : List A := a :: b :: c :: rest.toList
  have hrest_nodup : rest.toList.Nodup := by
    simpa using rest.nodup_toList
  have ha_rest : a ∉ rest.toList := by
    have : a ∉ rest := by simp [rest]
    simpa [Finset.mem_toList] using this
  have hb_rest : b ∉ rest.toList := by
    have : b ∉ rest := by simp [rest]
    simpa [Finset.mem_toList] using this
  have hc_rest : c ∉ rest.toList := by
    have : c ∉ rest := by simp [rest]
    simpa [Finset.mem_toList] using this
  have hnodup_c : (c :: rest.toList).Nodup := by
    exact List.nodup_cons.2 ⟨hc_rest, hrest_nodup⟩
  have hnodup_b : (b :: c :: rest.toList).Nodup := by
    apply List.nodup_cons.2
    refine ⟨?_, hnodup_c⟩
    simp [hb_rest, hbc]
  have hnodup : l.Nodup := by
    apply List.nodup_cons.2
    refine ⟨?_, hnodup_b⟩
    simp [ha_rest, hab, hac]
  have hcomplete : ∀ x : A, x ∈ l := by
    intro x
    by_cases hxa : x = a
    · subst hxa
      simp [l]
    by_cases hxb : x = b
    · subst hxb
      simp [l, hxa]
    by_cases hxc : x = c
    · subst hxc
      simp [l, hxa, hxb]
    have hx_mem : x ∈ rest := by
      simp [rest, hxa, hxb, hxc]
    have hx_mem' : x ∈ rest.toList := by
      simpa [Finset.mem_toList] using hx_mem
    simp [l, hxa, hxb, hxc, hx_mem']
  have hlt :
      l.idxOf a < l.idxOf b := by
    have hidxa : l.idxOf a = 0 := by
      simp [l]
    have hidxb : l.idxOf b = 1 := by
      simp [l, List.idxOf_cons_ne _ hab]
    simp [hidxa, hidxb]
  exact (linearOrderOfList_lt_iff_idxOf (l := l) (hnodup := hnodup) (hcomplete := hcomplete) a b).2 hlt

lemma ballotTopABC_prefers_second_third (a b c : A) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (ballotTopABC (A := A) a b c hab hac hbc).lt b c := by
  classical
  let rest : Finset A := ((Finset.univ.erase a).erase b).erase c
  let l : List A := a :: b :: c :: rest.toList
  have hrest_nodup : rest.toList.Nodup := by
    simpa using rest.nodup_toList
  have ha_rest : a ∉ rest.toList := by
    have : a ∉ rest := by simp [rest]
    simpa [Finset.mem_toList] using this
  have hb_rest : b ∉ rest.toList := by
    have : b ∉ rest := by simp [rest]
    simpa [Finset.mem_toList] using this
  have hc_rest : c ∉ rest.toList := by
    have : c ∉ rest := by simp [rest]
    simpa [Finset.mem_toList] using this
  have hnodup_c : (c :: rest.toList).Nodup := by
    exact List.nodup_cons.2 ⟨hc_rest, hrest_nodup⟩
  have hnodup_b : (b :: c :: rest.toList).Nodup := by
    apply List.nodup_cons.2
    refine ⟨?_, hnodup_c⟩
    simp [hb_rest, hbc]
  have hnodup : l.Nodup := by
    apply List.nodup_cons.2
    refine ⟨?_, hnodup_b⟩
    simp [ha_rest, hab, hac]
  have hcomplete : ∀ x : A, x ∈ l := by
    intro x
    by_cases hxa : x = a
    · subst hxa
      simp [l]
    by_cases hxb : x = b
    · subst hxb
      simp [l, hxa]
    by_cases hxc : x = c
    · subst hxc
      simp [l, hxa, hxb]
    have hx_mem : x ∈ rest := by
      simp [rest, hxa, hxb, hxc]
    have hx_mem' : x ∈ rest.toList := by
      simpa [Finset.mem_toList] using hx_mem
    simp [l, hxa, hxb, hxc, hx_mem']
  have hlt :
      l.idxOf b < l.idxOf c := by
    have hidxb : l.idxOf b = 1 := by
      simp [l, List.idxOf_cons_ne _ hab]
    have hidxc : l.idxOf c = 2 := by
      simp [l, List.idxOf_cons_ne _ hac, List.idxOf_cons_ne _ hbc]
    simp [hidxb, hidxc]
  exact (linearOrderOfList_lt_iff_idxOf (l := l) (hnodup := hnodup) (hcomplete := hcomplete) b c).2 hlt

lemma ballotTopABC_prefers_first_third (a b c : A) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (ballotTopABC (A := A) a b c hab hac hbc).lt a c := by
  classical
  let rest : Finset A := ((Finset.univ.erase a).erase b).erase c
  let l : List A := a :: b :: c :: rest.toList
  have hrest_nodup : rest.toList.Nodup := by
    simpa using rest.nodup_toList
  have ha_rest : a ∉ rest.toList := by
    have : a ∉ rest := by simp [rest]
    simpa [Finset.mem_toList] using this
  have hb_rest : b ∉ rest.toList := by
    have : b ∉ rest := by simp [rest]
    simpa [Finset.mem_toList] using this
  have hc_rest : c ∉ rest.toList := by
    have : c ∉ rest := by simp [rest]
    simpa [Finset.mem_toList] using this
  have hnodup_c : (c :: rest.toList).Nodup := by
    exact List.nodup_cons.2 ⟨hc_rest, hrest_nodup⟩
  have hnodup_b : (b :: c :: rest.toList).Nodup := by
    apply List.nodup_cons.2
    refine ⟨?_, hnodup_c⟩
    simp [hb_rest, hbc]
  have hnodup : l.Nodup := by
    apply List.nodup_cons.2
    refine ⟨?_, hnodup_b⟩
    simp [ha_rest, hab, hac]
  have hcomplete : ∀ x : A, x ∈ l := by
    intro x
    by_cases hxa : x = a
    · subst hxa
      simp [l]
    by_cases hxb : x = b
    · subst hxb
      simp [l, hxa]
    by_cases hxc : x = c
    · subst hxc
      simp [l, hxa, hxb]
    have hx_mem : x ∈ rest := by
      simp [rest, hxa, hxb, hxc]
    have hx_mem' : x ∈ rest.toList := by
      simpa [Finset.mem_toList] using hx_mem
    simp [l, hxa, hxb, hxc, hx_mem']
  have hlt :
      l.idxOf a < l.idxOf c := by
    have hidxa : l.idxOf a = 0 := by
      simp [l]
    have hidxc : l.idxOf c = 2 := by
      simp [l, List.idxOf_cons_ne _ hac, List.idxOf_cons_ne _ hbc]
    simp [hidxa, hidxc]
  exact (linearOrderOfList_lt_iff_idxOf (l := l) (hnodup := hnodup) (hcomplete := hcomplete) a c).2 hlt

lemma ballotTopABC_topSet (a b c : A) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    BallotTopSet (ballotTopABC (A := A) a b c hab hac hbc) (insert a (insert b {c})) := by
  classical
  intro x y hx hy
  have hxa : x = a ∨ x = b ∨ x = c := by
    simpa [Finset.mem_insert, Finset.mem_singleton, or_left_comm, or_assoc] using hx
  have hya : y ≠ a := by
    intro h
    apply hy
    simp [h]
  have hyb : y ≠ b := by
    intro h
    apply hy
    simp [h]
  have hyc : y ≠ c := by
    intro h
    apply hy
    simp [h]
  let rest : Finset A := ((Finset.univ.erase a).erase b).erase c
  let l : List A := a :: b :: c :: rest.toList
  have hrest_nodup : rest.toList.Nodup := by
    simpa using rest.nodup_toList
  have ha_rest : a ∉ rest.toList := by
    have : a ∉ rest := by simp [rest]
    simpa [Finset.mem_toList] using this
  have hb_rest : b ∉ rest.toList := by
    have : b ∉ rest := by simp [rest]
    simpa [Finset.mem_toList] using this
  have hc_rest : c ∉ rest.toList := by
    have : c ∉ rest := by simp [rest]
    simpa [Finset.mem_toList] using this
  have hnodup_c : (c :: rest.toList).Nodup := by
    exact List.nodup_cons.2 ⟨hc_rest, hrest_nodup⟩
  have hnodup_b : (b :: c :: rest.toList).Nodup := by
    apply List.nodup_cons.2
    refine ⟨?_, hnodup_c⟩
    simp [hb_rest, hbc]
  have hnodup : l.Nodup := by
    apply List.nodup_cons.2
    refine ⟨?_, hnodup_b⟩
    simp [ha_rest, hab, hac]
  have hcomplete : ∀ z : A, z ∈ l := by
    intro z
    by_cases hza : z = a
    · subst hza
      simp [l]
    by_cases hzb : z = b
    · subst hzb
      simp [l, hza]
    by_cases hzc : z = c
    · subst hzc
      simp [l, hza, hzb]
    have hz_mem : z ∈ rest := by
      simp [rest, hza, hzb, hzc]
    have hz_mem' : z ∈ rest.toList := by
      simpa [Finset.mem_toList] using hz_mem
    simp [l, hza, hzb, hzc, hz_mem']
  have hy_succ1 :
      l.idxOf y = Nat.succ (List.idxOf y (b :: c :: rest.toList)) := by
    simpa [l] using
      (List.idxOf_cons_ne (a := y) (b := a) (l := b :: c :: rest.toList) hya.symm)
  have hy_succ2 :
      List.idxOf y (b :: c :: rest.toList) = Nat.succ (List.idxOf y (c :: rest.toList)) := by
    simpa using
      (List.idxOf_cons_ne (a := y) (b := b) (l := c :: rest.toList) hyb.symm)
  have hy_succ3 :
      List.idxOf y (c :: rest.toList) = Nat.succ (List.idxOf y rest.toList) := by
    simpa using
      (List.idxOf_cons_ne (a := y) (b := c) (l := rest.toList) hyc.symm)
  have hy_ge :
      l.idxOf y = Nat.succ (Nat.succ (Nat.succ (List.idxOf y rest.toList))) := by
    calc
      l.idxOf y = Nat.succ (List.idxOf y (b :: c :: rest.toList)) := hy_succ1
      _ = Nat.succ (Nat.succ (List.idxOf y (c :: rest.toList))) := by
          simpa using hy_succ2
      _ = Nat.succ (Nat.succ (Nat.succ (List.idxOf y rest.toList))) := by
          simpa using hy_succ3
  have hlt_a : l.idxOf a < l.idxOf y := by
    have hidxa : l.idxOf a = 0 := by
      simp [l]
    have : 0 < l.idxOf y := by
      simp [hy_ge]
    exact by simpa [hidxa] using this
  have hlt_b : l.idxOf b < l.idxOf y := by
    have hidxb : l.idxOf b = 1 := by
      simp [l, List.idxOf_cons_ne _ hab]
    have : 1 < l.idxOf y := by
      simp [hy_ge]
    exact by simpa [hidxb] using this
  have hlt_c : l.idxOf c < l.idxOf y := by
    have hidxc : l.idxOf c = 2 := by
      simp [l, List.idxOf_cons_ne _ hac, List.idxOf_cons_ne _ hbc]
    have : 2 < l.idxOf y := by
      simp [hy_ge]
    exact by simpa [hidxc] using this
  cases hxa with
  | inl hxa' =>
      subst hxa'
      exact (linearOrderOfList_lt_iff_idxOf (l := l) (hnodup := hnodup)
        (hcomplete := hcomplete) x y).2 hlt_a
  | inr hxb' =>
      cases hxb' with
      | inl hxb'' =>
          subst hxb''
          exact (linearOrderOfList_lt_iff_idxOf (l := l) (hnodup := hnodup)
            (hcomplete := hcomplete) x y).2 hlt_b
      | inr hxc' =>
          subst hxc'
          exact (linearOrderOfList_lt_iff_idxOf (l := l) (hnodup := hnodup)
            (hcomplete := hcomplete) x y).2 hlt_c

lemma ballotTopABC_topSet_first_second (a b c : A) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    BallotTopSet (ballotTopABC (A := A) a b c hab hac hbc) (insert a {b}) := by
  classical
  intro x y hx hy
  have hxa : x = a ∨ x = b := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hx
  by_cases hyc : y = c
  · subst hyc
    cases hxa with
    | inl hxa' =>
        subst x
        have h := ballotTopABC_prefers_first_third (A := A) a b y hab hac hbc
        simpa using h
    | inr hxb' =>
        subst x
        have h := ballotTopABC_prefers_second_third (A := A) a b y hab hac hbc
        simpa using h
  · have hya : y ≠ a := by
      intro h
      apply hy
      simp [h]
    have hyb : y ≠ b := by
      intro h
      apply hy
      simp [h]
    have hy_not : y ∉ (insert a (insert b {c}) : Finset A) := by
      simp [hya, hyb, hyc]
    have hxabc : x ∈ (insert a (insert b {c}) : Finset A) := by
      cases hxa with
      | inl hxa' =>
          subst hxa'
          simp
      | inr hxb' =>
          subst hxb'
          simp
    have htop := ballotTopABC_topSet (A := A) a b c hab hac hbc
    exact htop x y hxabc hy_not

omit [DecidableEq V] in
lemma topRank_profileTopABC (a b c : A) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ v : V, TopRank (profileTopABC (V := V) (A := A) a b c hab hac hbc) v a := by
  classical
  intro v d hd
  by_cases hdb : d = b
  · subst d
    have h := ballotTopABC_prefers_first_second (A := A) (a := a) (b := b) (c := c) hab hac hbc
    simpa [profileTopABC, Prefers] using h
  · by_cases hdc : d = c
    · subst d
      have h := ballotTopABC_prefers_first_third (A := A) (a := a) (b := b) (c := c) hab hac hbc
      simpa [profileTopABC, Prefers] using h
    · have hd_not : d ∉ (insert a (insert b {c}) : Finset A) := by
        simp [hd, hdb, hdc]
      have ha_mem : a ∈ (insert a (insert b {c}) : Finset A) := by simp
      have htop := ballotTopABC_topSet (A := A) a b c hab hac hbc
      have h := htop a d ha_mem hd_not
      simpa [profileTopABC, Prefers] using h

lemma ballotTopAB_prefers (a b : A) (hab : a ≠ b) :
    (ballotTopAB (A := A) a b hab).lt a b := by
  classical
  let rest : Finset A := (Finset.univ.erase a).erase b
  let l : List A := a :: b :: rest.toList
  have hrest_nodup : rest.toList.Nodup := by
    simpa using rest.nodup_toList
  have ha_rest : a ∉ rest.toList := by
    have : a ∉ rest := by simp [rest]
    simpa [Finset.mem_toList] using this
  have hb_rest : b ∉ rest.toList := by
    have : b ∉ rest := by simp [rest]
    simpa [Finset.mem_toList] using this
  have hnodup_b : (b :: rest.toList).Nodup := by
    exact List.nodup_cons.2 ⟨hb_rest, hrest_nodup⟩
  have hnodup : l.Nodup := by
    apply List.nodup_cons.2
    refine ⟨?_, hnodup_b⟩
    simp [ha_rest, hab]
  have hcomplete : ∀ x : A, x ∈ l := by
    intro x
    by_cases hxa : x = a
    · subst hxa
      simp [l]
    by_cases hxb : x = b
    · subst hxb
      simp [l, hxa]
    have hx_mem : x ∈ rest := by
      simp [rest, hxa, hxb]
    have hx_mem' : x ∈ rest.toList := by
      simpa [Finset.mem_toList] using hx_mem
    simp [l, hxa, hxb, hx_mem']
  have hlt :
      l.idxOf a < l.idxOf b := by
    have hidxa : l.idxOf a = 0 := by
      simp [l]
    have hidxb : l.idxOf b = 1 := by
      simp [l, List.idxOf_cons_ne _ hab]
    simp [hidxa, hidxb]
  exact (linearOrderOfList_lt_iff_idxOf (l := l) (hnodup := hnodup) (hcomplete := hcomplete) a b).2 hlt

lemma ballotTopAB_topSet (a b : A) (hab : a ≠ b) :
    BallotTopSet (ballotTopAB (A := A) a b hab) (insert a {b}) := by
  classical
  intro x y hx hy
  have hxa : x = a ∨ x = b := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hx
  have hya : y ≠ a := by
    intro h
    apply hy
    simp [h]
  have hyb : y ≠ b := by
    intro h
    apply hy
    simp [h]
  let rest : Finset A := (Finset.univ.erase a).erase b
  let l : List A := a :: b :: rest.toList
  have hrest_nodup : rest.toList.Nodup := by
    simpa using rest.nodup_toList
  have ha_rest : a ∉ rest.toList := by
    have : a ∉ rest := by simp [rest]
    simpa [Finset.mem_toList] using this
  have hb_rest : b ∉ rest.toList := by
    have : b ∉ rest := by simp [rest]
    simpa [Finset.mem_toList] using this
  have hnodup_b : (b :: rest.toList).Nodup := by
    exact List.nodup_cons.2 ⟨hb_rest, hrest_nodup⟩
  have hnodup : l.Nodup := by
    apply List.nodup_cons.2
    refine ⟨?_, hnodup_b⟩
    simp [ha_rest, hab]
  have hcomplete : ∀ z : A, z ∈ l := by
    intro z
    by_cases hza : z = a
    · subst hza
      simp [l]
    by_cases hzb : z = b
    · subst hzb
      simp [l, hza]
    have hz_mem : z ∈ rest := by
      simp [rest, hza, hzb]
    have hz_mem' : z ∈ rest.toList := by
      simpa [Finset.mem_toList] using hz_mem
    simp [l, hza, hzb, hz_mem']
  have hlt_a : l.idxOf a < l.idxOf y := by
    have hidxa : l.idxOf a = 0 := by
      simp [l]
    have hy_succ : l.idxOf y = Nat.succ (List.idxOf y (b :: rest.toList)) := by
      simpa [l] using
        (List.idxOf_cons_ne (a := y) (b := a) (l := b :: rest.toList) hya.symm)
    have : 0 < l.idxOf y := by
      simp [hy_succ]
    simp [hidxa]
    exact this
  have hlt_b : l.idxOf b < l.idxOf y := by
    have hidxb : l.idxOf b = 1 := by
      simp [l, List.idxOf_cons_ne _ hab]
    have hy_succ : l.idxOf y = Nat.succ (List.idxOf y (b :: rest.toList)) := by
      simpa [l] using
        (List.idxOf_cons_ne (a := y) (b := a) (l := b :: rest.toList) hya.symm)
    have hy_succ2 : List.idxOf y (b :: rest.toList) = Nat.succ (List.idxOf y rest.toList) := by
      simpa using (List.idxOf_cons_ne (a := y) (b := b) (l := rest.toList) hyb.symm)
    have hy_ge : l.idxOf y = Nat.succ (Nat.succ (List.idxOf y rest.toList)) := by
      calc
        l.idxOf y = Nat.succ (List.idxOf y (b :: rest.toList)) := hy_succ
        _ = Nat.succ (Nat.succ (List.idxOf y rest.toList)) := by
            simpa using hy_succ2
    have : 1 < l.idxOf y := by
      simp [hy_ge]
    simp [hidxb]
    exact this
  cases hxa with
  | inl hxa' =>
      subst hxa'
      exact (linearOrderOfList_lt_iff_idxOf (l := l) (hnodup := hnodup) (hcomplete := hcomplete) x y).2 hlt_a
  | inr hxb' =>
      subst hxb'
      exact (linearOrderOfList_lt_iff_idxOf (l := l) (hnodup := hnodup) (hcomplete := hcomplete) x y).2 hlt_b

omit [DecidableEq V] in
lemma topRank_profileTopAB (a b : A) (hab : a ≠ b) :
    ∀ v : V, TopRank (profileTopAB (V := V) (A := A) a b hab) v a := by
  classical
  intro v c hc
  by_cases hcb : c = b
  · have h := ballotTopAB_prefers (A := A) (a := a) (b := b) hab
    simpa [hcb, profileTopAB, Prefers] using h
  · have hc_not : c ∉ (insert a ({b} : Finset A)) := by
      simp [hc, hcb]
    have ha_mem : a ∈ (insert a ({b} : Finset A)) := by simp
    have htop := ballotTopAB_topSet (A := A) a b hab
    have h := htop a c ha_mem hc_not
    simpa [profileTopAB, Prefers] using h

omit [DecidableEq V] in
lemma prefers_b_profileTopAB_of_ne (a b c : A) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    ∀ v : V, Prefers (profileTopAB (V := V) (A := A) a b hab) v b c := by
  classical
  intro v
  have hc_not : c ∉ (insert a ({b} : Finset A)) := by
    simp [hca, hcb]
  have hb_mem : b ∈ (insert a ({b} : Finset A)) := by simp
  have htop := ballotTopAB_topSet (A := A) a b hab
  have h := htop b c hb_mem hc_not
  simpa [profileTopAB, Prefers] using h

lemma aXb_of_topSet_profile (f : VotingRule) (hf : DownMonotonicitySingleton f)
    (X : Finset V) (a b : A) (hab : a ≠ b)
    (P : Profile V A)
    (hTop : TopSet P (insert a {b}))
    (_hX : ∀ v : V, v ∈ X → Prefers P v a b)
    (hnotX : ∀ v : V, v ∉ X → Prefers P v b a)
    (ha : a ∈ f P) :
    aXb (V := V) (A := A) f X a b := by
  classical
  intro P' hX' hfb
  have hdown : DownObtainable (V := V) (A := A) b P' P := by
    intro v c hbc
    by_cases hc_a : c = a
    · subst hc_a
      by_cases hv : v ∈ X
      · have hX'v : Prefers P' v c b := hX' v hv
        let _ := P'.pref v
        have : False := lt_asymm (by simpa [Prefers] using hbc) (by simpa [Prefers] using hX'v)
        exact (False.elim this)
      · exact hnotX v hv
    · by_cases hc_b : c = b
      · subst hc_b
        let _ := P'.pref v
        simp [Prefers] at hbc
      · have hc_not : c ∉ (insert a ({b} : Finset A)) := by
          simp [hc_a, hc_b]
        have hb_mem : b ∈ (insert a ({b} : Finset A)) := by simp
        exact hTop v b c hb_mem hc_not
  have hmono : DownMonotonicity f := SocialChoice.downMonotonicity_of_singleton (f := f) hf
  have hfb' : f P = {b} := hmono P' P b hfb hdown
  have ha' : a ∈ ({b} : Finset A) := by simpa [hfb'] using ha
  have hab' : a = b := by simpa using ha'
  exact hab hab'

/-- Lemma 2.6 in the "exists profile" form. -/
lemma aXb_of_exists_profile (f : VotingRule) (hf : DownMonotonicitySingleton f)
    (X : Finset V) (a b : A) (hab : a ≠ b)
    (hP : ∃ P : Profile V A,
      TopSet P (insert a {b}) ∧
      (∀ v : V, v ∈ X → Prefers P v a b) ∧
      (∀ v : V, v ∉ X → Prefers P v b a) ∧
      a ∈ f P) :
    aXb (V := V) (A := A) f X a b := by
  rcases hP with ⟨P, hTop, hX, hnotX, ha⟩
  exact aXb_of_topSet_profile (f := f) (hf := hf) (X := X) (a := a) (b := b)
    (hab := hab) (P := P) hTop hX hnotX ha

/-! Lemma 2.7 (Taylor 2002) -/
omit [DecidableEq V] in
lemma dictatingSet_univ_of_downMonotonicitySingleton_viable
    (f : VotingRule) (hf : DownMonotonicitySingleton f) (hviable : Viable f) :
    DictatingSet (V := V) (A := A) f (Finset.univ : Finset V) := by
  classical
  intro a b hab P hall hfb
  obtain ⟨P_a, hPa⟩ := hviable (V := V) (A := A) a
  let Q := profileTopAB (V := V) (A := A) a b hab
  have hmono : DownMonotonicity f := downMonotonicity_of_singleton (f := f) hf
  have hdown_a : DownObtainable (V := V) (A := A) a P_a Q := by
    intro v c hpc
    have hc_ne : c ≠ a := by
      intro hca
      let _ := P_a.pref v
      simp [Prefers, hca] at hpc
    have htop := topRank_profileTopAB (V := V) (A := A) a b hab v c hc_ne
    simpa [Prefers] using htop
  have hQ_a : f Q = {a} := hmono P_a Q a hPa hdown_a
  have hdown_b : DownObtainable (V := V) (A := A) b P Q := by
    intro v c hbc
    have hc_ne_b : c ≠ b := by
      intro hcb
      let _ := P.pref v
      simp [Prefers, hcb] at hbc
    have hc_ne_a : c ≠ a := by
      intro hca
      have hba : Prefers P v b a := by simpa [hca] using hbc
      have hab' : Prefers P v a b := hall v (by simp)
      let _ := P.pref v
      exact lt_asymm hba hab'
    have htop := prefers_b_profileTopAB_of_ne (V := V) (A := A) a b c hab hc_ne_a hc_ne_b v
    simp [Prefers] at htop
    exact htop
  have hQ_b : f Q = {b} := hmono P Q b hfb hdown_b
  have haQ : a ∈ f Q := by simp [hQ_a]
  have haQ' : a ∈ ({b} : Finset A) := by simpa [hQ_b] using haQ
  have hab' : a = b := by simpa using haQ'
  exact hab hab'

/-! Lemma 2.8 (Taylor 2002) -/

omit [DecidableEq A] in
lemma updateProfileList_map_const (P : Profile V A) (l : List V) (ballot : LinearOrder A) :
    updateProfileList P (l.map (fun v => (v, ballot))) =
      { pref := fun v => if v ∈ l then ballot else P.pref v } := by
  classical
  induction l generalizing P with
  | nil =>
      apply Profile.ext
      intro v
      simp [updateProfileList]
  | cons v rest ih =>
      apply Profile.ext
      intro u
      by_cases hmem : u ∈ rest
      · have ih' := ih (P := updateProfile P v ballot)
        have ihu := congrArg (fun P => P.pref u) ih'
        have h1 :
            (updateProfileList (updateProfile P v ballot) (List.map (fun v => (v, ballot)) rest)).pref
                u =
              ballot := by
          simpa [hmem] using ihu
        simpa [updateProfileList, List.mem_cons, hmem] using h1
      · by_cases huv : u = v
        · subst huv
          have ih' := ih (P := updateProfile P u ballot)
          have ihu := congrArg (fun P => P.pref u) ih'
          have h1 :
              (updateProfileList (updateProfile P u ballot) (List.map (fun v => (v, ballot)) rest)).pref
                  u =
                ballot := by
            simpa [hmem, updateProfile] using ihu
          simpa [updateProfileList, List.mem_cons, hmem] using h1
        · have ih' := ih (P := updateProfile P v ballot)
          have ihu := congrArg (fun P => P.pref u) ih'
          have h1 :
              (updateProfileList (updateProfile P v ballot) (List.map (fun v => (v, ballot)) rest)).pref
                  u =
                P.pref u := by
            simpa [hmem, updateProfile, huv] using ihu
          simpa [updateProfileList, List.mem_cons, hmem, huv] using h1

lemma winner_preserved_of_optimist_top (f : VotingRule) (hf_opt : OptimistStrategyproof f)
    (P : Profile V A) (v : V) (ballot : LinearOrder A) (a : A)
    (ha : a ∈ f P)
    (htop : TopRank (updateProfile P v ballot) v a) :
    a ∈ f (updateProfile P v ballot) := by
  classical
  by_contra ha'
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
      ∃ y ∈ f (updateProfile P' v (P.pref v)),
        ∀ x ∈ f P', Prefers P' v y x := by
    refine ⟨a, ?_, ?_⟩
    · simpa [hback] using ha
    · intro x hx
      have hx_ne : x ≠ a := by
        intro h
        subst h
        exact ha' hx
      exact htop x hx_ne
  exact hf_opt P' v (P.pref v) hmanip

omit [DecidableEq V] in
lemma winner_preserved_of_pessimist_pref (f : VotingRule) (hf_pess : PessimistStrategyproof f)
    (P : Profile V A) (v : V) (ballot : LinearOrder A) (a : A)
    (ha : a ∈ f P)
    (hbetter : ∀ y ∈ f (updateProfile P v ballot), y ≠ a → Prefers P v y a) :
    a ∈ f (updateProfile P v ballot) := by
  classical
  by_contra ha'
  have hmanip :
      ∃ x ∈ f P, ∀ y ∈ f (updateProfile P v ballot), Prefers P v y x := by
    refine ⟨a, ha, ?_⟩
    intro y hy
    have hy_ne : y ≠ a := by
      intro h
      subst h
      exact ha' hy
    exact hbetter y hy hy_ne
  exact hf_pess P v ballot hmanip

lemma aXb_partition_of_opt_pess_viable (f : VotingRule)
    (hf_total : IsVotingRule f)
    (hf_opt : OptimistStrategyproof f)
    (hf_pess : PessimistStrategyproof f)
    (hviable : Viable f)
    (X Y Z : Finset V) (a b c : A)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hX : aXb (V := V) (A := A) f X a b)
    (hYZ : Disjoint Y Z) (hunion : Y ∪ Z = X) :
    aXb (V := V) (A := A) f Y a c ∨ aXb (V := V) (A := A) f Z c b := by
  classical
  let abc : Finset A := insert a (insert b {c})
  let r_abc := ballotTopABC (A := A) a b c hab hac hbc
  let r_cab := ballotTopABC (A := A) c a b hac.symm hbc.symm hab
  let r_bca := ballotTopABC (A := A) b c a hbc hab.symm hac.symm
  let r_acb := ballotTopABC (A := A) a c b hac hab hbc.symm
  let r_cba := ballotTopABC (A := A) c b a hbc.symm hac.symm hab.symm
  have abc_eq_acb : (insert a (insert c {b}) : Finset A) = abc := by
    ext x
    simp [abc, Finset.mem_insert, Finset.mem_singleton, or_comm]
  have abc_eq_cab : (insert c (insert a {b}) : Finset A) = abc := by
    ext x
    simp [abc, Finset.mem_insert, Finset.mem_singleton, or_left_comm, or_comm]
  have abc_eq_bca : (insert b (insert c {a}) : Finset A) = abc := by
    ext x
    simp [abc, Finset.mem_insert, Finset.mem_singleton, or_left_comm, or_comm]
  have abc_eq_cba : (insert c (insert b {a}) : Finset A) = abc := by
    ext x
    simp [abc, Finset.mem_insert, Finset.mem_singleton, or_left_comm, or_comm]
  let P : Profile V A :=
    { pref := fun v =>
        if v ∈ Y then r_abc else if v ∈ Z then r_cab else r_bca }
  have hTopP : TopSet P abc := by
    intro v
    by_cases hvY : v ∈ Y
    · simpa [P, hvY, abc] using
        (ballotTopABC_topSet (A := A) a b c hab hac hbc)
    · by_cases hvZ : v ∈ Z
      · simpa [P, hvY, hvZ, r_cab, abc_eq_cab] using
          (ballotTopABC_topSet (A := A) c a b hac.symm hbc.symm hab)
      · simpa [P, hvY, hvZ, r_bca, abc_eq_bca] using
          (ballotTopABC_topSet (A := A) b c a hbc hab.symm hac.symm)
  have hmono_singleton : DownMonotonicitySingleton f :=
    downMonotonicity_of_opt_pess_sp f hf_total hf_opt hf_pess
  have hmono : DownMonotonicity f :=
    downMonotonicity_of_singleton (f := f) hmono_singleton
  obtain ⟨P_a, hPa⟩ := hviable (V := V) (A := A) a
  let P_top := profileTopABC (V := V) (A := A) a b c hab hac hbc
  have hdown_a : DownObtainable (V := V) (A := A) a P_a P_top := by
    intro v d hpd
    have hd_ne : d ≠ a := by
      intro hda
      let _ := P_a.pref v
      simp [Prefers, hda] at hpd
    have htop := topRank_profileTopABC (V := V) (A := A) a b c hab hac hbc v d hd_ne
    simpa [profileTopABC, Prefers] using htop
  have hPtop : f P_top = {a} := hmono P_a P_top a hPa hdown_a
  have hsubset_top : f P_top ⊆ abc := by
    intro x hx
    have hx' : x = a := by
      have : x ∈ ({a} : Finset A) := by simpa [hPtop] using hx
      simpa using this
    subst hx'
    simp [abc]
  let updates : List (V × LinearOrder A) :=
    (Finset.univ.toList.map (fun v => (v, r_abc)))
  have hupdate_const_raw :
      ∀ Q : Profile V A, updateProfileList Q updates = { pref := fun _ => r_abc } := by
    intro Q
    simpa [updates] using
      (updateProfileList_map_const (P := Q) (l := Finset.univ.toList) (ballot := r_abc))
  have hupdate_const : ∀ Q : Profile V A, updateProfileList Q updates = P_top := by
    intro Q
    have h := hupdate_const_raw Q
    simpa [P_top, profileTopABC] using h
  have hBallots : ∀ u ∈ updates, BallotTopSet u.2 abc := by
    intro u hu
    rcases List.mem_map.1 hu with ⟨v, hv, rfl⟩
    simpa [abc] using (ballotTopABC_topSet (A := A) a b c hab hac hbc)
  have hsubset_topset : ∀ Q : Profile V A, TopSet Q abc → f Q ⊆ abc := by
    intro Q hTopQ
    have hsubset_final : f (updateProfileList Q updates) ⊆ abc := by
      have hupdate := hupdate_const Q
      simpa [hupdate] using hsubset_top
    exact topSet_subset_of_pessimist_updates (f := f) (hf_pess := hf_pess)
      (P := Q) (updates := updates) (X := abc) hTopQ hBallots hsubset_final
  have hsubsetP : f P ⊆ abc := hsubset_topset P hTopP
  have hXpref : ∀ v : V, v ∈ X → Prefers P v a b := by
    intro v hvX
    have hvYZ : v ∈ Y ∪ Z := by
      simpa [hunion] using hvX
    rcases (Finset.mem_union.1 hvYZ) with hvY | hvZ
    · have h := ballotTopABC_prefers_first_second (A := A) a b c hab hac hbc
      unfold Prefers
      rw [show P.pref v = ballotTopABC (A := A) a b c hab hac hbc by
        simp only [P, hvY, if_true, r_abc]]
      exact h
    · have hvY : v ∉ Y := by
        intro hvY
        exact (Finset.disjoint_left.1 hYZ hvY hvZ).elim
      have h := ballotTopABC_prefers_second_third (A := A) c a b hac.symm hbc.symm hab
      unfold Prefers
      rw [show P.pref v = ballotTopABC (A := A) c a b hac.symm hbc.symm hab by
        simp only [P, hvY, hvZ, if_false, if_true, r_cab]]
      exact h
  have hnotb : f P ≠ {b} := hX P hXpref
  have hAorC : a ∈ f P ∨ c ∈ f P := by
    by_contra h
    have ha' : a ∉ f P := by
      intro ha
      exact h (Or.inl ha)
    have hc' : c ∉ f P := by
      intro hc
      exact h (Or.inr hc)
    let _ : Nonempty A := ⟨a⟩
    obtain ⟨x, hx⟩ := hf_total P
    have hxabc : x ∈ abc := hsubsetP hx
    have hx' : x = a ∨ x = b ∨ x = c := by
      simpa [abc] using hxabc
    have hxB : x = b := by
      rcases hx' with hx' | hx' | hx'
      · subst hx'
        exact (ha' hx).elim
      · exact hx'
      · subst hx'
        exact (hc' hx).elim
    have hb_mem : b ∈ f P := by
      subst hxB
      exact hx
    have hfb : f P = {b} := by
      ext y
      constructor
      · intro hy
        have hyabc : y ∈ abc := hsubsetP hy
        have hy' : y = a ∨ y = b ∨ y = c := by
          simpa [abc] using hyabc
        rcases hy' with hy' | hy' | hy'
        · subst hy'
          exact (ha' hy).elim
        · subst hy'
          simp
        · subst hy'
          exact (hc' hy).elim
      · intro hy
        have hy' : y = b := by simpa using hy
        subst hy'
        exact hb_mem
    exact hnotb hfb
  cases hAorC with
  | inl ha =>
      let P_acb : Profile V A := { pref := fun _ => r_acb }
      let P_cab : Profile V A := { pref := fun _ => r_cab }
      have hP1 :
          a ∈ f (profileUpdateSet P P_acb Y) ∧
            TopSet (profileUpdateSet P P_acb Y) abc := by
        refine Finset.induction ?base ?step Y
        · simp [profileUpdateSet_empty, ha, hTopP]
        · intro v S hv hS
          let Q := profileUpdateSet P P_acb S
          have haQ : a ∈ f Q := hS.1
          have hTopQ : TopSet Q abc := hS.2
          have hTopBallot :
              TopRank (updateProfile Q v (P_acb.pref v)) v a := by
            intro d hd
            have htop :=
              topRank_profileTopABC (V := V) (A := A) a c b hac hab hbc.symm v d hd
            unfold Prefers
            rw [show (updateProfile Q v (P_acb.pref v)).pref v = P_acb.pref v by
              simp only [updateProfile, if_true]]
            change (profileTopABC (V := V) (A := A) a c b hac hab hbc.symm).pref v |>.lt a d
            exact htop
          have haQ' : a ∈ f (updateProfile Q v (P_acb.pref v)) :=
            winner_preserved_of_optimist_top (f := f) (hf_opt := hf_opt)
              (P := Q) (v := v) (ballot := P_acb.pref v) (a := a) haQ hTopBallot
          have hBallot : BallotTopSet (P_acb.pref v) abc := by
            simpa [P_acb, abc_eq_acb] using
              (ballotTopABC_topSet (A := A) a c b hac hab hbc.symm)
          have hTopQ' :
              TopSet (updateProfile Q v (P_acb.pref v)) abc :=
            topSet_updateProfile (P := Q) (v := v) (ballot := P_acb.pref v) (X := abc) hTopQ hBallot
          have hupdate :=
            profileUpdateSet_insert (P := P) (P' := P_acb) (S := S) (v := v) hv
          have haInsert : a ∈ f (profileUpdateSet P P_acb (insert v S)) := by
            simpa [hupdate] using haQ'
          have hTopInsert : TopSet (profileUpdateSet P P_acb (insert v S)) abc := by
            simpa [hupdate] using hTopQ'
          exact ⟨haInsert, hTopInsert⟩
      have haP1 : a ∈ f (profileUpdateSet P P_acb Y) := hP1.1
      have hTopP1 : TopSet (profileUpdateSet P P_acb Y) abc := hP1.2
      let others : Finset V := Finset.univ \ X
      have hP2 :
          ∀ S : Finset V, S ⊆ others →
            a ∈ f (profileUpdateSet (profileUpdateSet P P_acb Y) P_cab S) ∧
              TopSet (profileUpdateSet (profileUpdateSet P P_acb Y) P_cab S) abc := by
        intro S hsub
        induction S using Finset.induction_on with
        | empty =>
            simpa [profileUpdateSet_empty] using ⟨haP1, hTopP1⟩
        | @insert v S hv hS =>
          have hsubS : S ⊆ others := by
            intro u hu
            exact hsub (Finset.mem_insert_of_mem hu)
          have hv_other : v ∈ others := hsub (by simp [hv])
          let Q := profileUpdateSet (profileUpdateSet P P_acb Y) P_cab S
          have hS' := hS hsubS
          have haQ : a ∈ f Q := hS'.1
          have hTopQ : TopSet Q abc := hS'.2
          have hBallot : BallotTopSet (P_cab.pref v) abc := by
            simpa [P_cab, abc_eq_cab] using
              (ballotTopABC_topSet (A := A) c a b hac.symm hbc.symm hab)
          have hTopQ' :
              TopSet (updateProfile Q v (P_cab.pref v)) abc :=
            topSet_updateProfile (P := Q) (v := v) (ballot := P_cab.pref v) (X := abc) hTopQ hBallot
          have hsubset_next : f (updateProfile Q v (P_cab.pref v)) ⊆ abc :=
            hsubset_topset _ hTopQ'
          have hv_notX : v ∉ X := (Finset.mem_sdiff.mp hv_other).2
          have hv_notY : v ∉ Y := by
            intro hvY
            have hvX : v ∈ X := by
              have : v ∈ Y ∪ Z := by
                exact Finset.mem_union.mpr (Or.inl hvY)
              simpa [hunion] using this
            exact hv_notX hvX
          have hv_notZ : v ∉ Z := by
            intro hvZ
            have hvX : v ∈ X := by
              have : v ∈ Y ∪ Z := by
                exact Finset.mem_union.mpr (Or.inr hvZ)
              simpa [hunion] using this
            exact hv_notX hvX
          have hbetter :
              ∀ y ∈ f (updateProfile Q v (P_cab.pref v)), y ≠ a → Prefers Q v y a := by
            intro y hy hy_ne
            have hyabc : y ∈ abc := hsubset_next hy
            have hy' : y = a ∨ y = b ∨ y = c := by
              simpa [abc] using hyabc
            rcases hy' with hy' | hy' | hy'
            · exact (hy_ne hy').elim
            · subst y
              have h := ballotTopABC_prefers_first_third (A := A) b c a hbc hab.symm hac.symm
              unfold Prefers
              rw [show Q.pref v = ballotTopABC (A := A) b c a hbc hab.symm hac.symm by
                simp only [Q, profileUpdateSet, hv, if_false, P, hv_notY, hv_notZ, r_bca]]
              exact h
            · subst y
              have h := ballotTopABC_prefers_second_third (A := A) b c a hbc hab.symm hac.symm
              unfold Prefers
              rw [show Q.pref v = ballotTopABC (A := A) b c a hbc hab.symm hac.symm by
                simp only [Q, profileUpdateSet, hv, if_false, P, hv_notY, hv_notZ, r_bca]]
              exact h
          have haQ' :
              a ∈ f (updateProfile Q v (P_cab.pref v)) :=
            winner_preserved_of_pessimist_pref (f := f) (hf_pess := hf_pess)
              (P := Q) (v := v) (ballot := P_cab.pref v) (a := a) haQ hbetter
          have hupdate :=
            profileUpdateSet_insert (P := profileUpdateSet P P_acb Y) (P' := P_cab) (S := S) (v := v) hv
          have haInsert :
              a ∈ f (profileUpdateSet (profileUpdateSet P P_acb Y) P_cab (insert v S)) := by
            simpa [hupdate] using haQ'
          have hTopInsert :
              TopSet (profileUpdateSet (profileUpdateSet P P_acb Y) P_cab (insert v S)) abc := by
            simpa [hupdate] using hTopQ'
          exact ⟨haInsert, hTopInsert⟩
      have haP2 :
          a ∈ f (profileUpdateSet (profileUpdateSet P P_acb Y) P_cab others) :=
        (hP2 others (by intro u hu; exact hu)).1
      let P2 := profileUpdateSet (profileUpdateSet P P_acb Y) P_cab others
      have hPrefY : ∀ v : V, v ∈ Y → P2.pref v = r_acb := by
        intro v hvY
        have hvX : v ∈ X := by
          have : v ∈ Y ∪ Z := by
            exact Finset.mem_union.mpr (Or.inl hvY)
          simpa [hunion] using this
        have hv_notOther : v ∉ others := by
          intro hvOther
          exact (Finset.mem_sdiff.mp hvOther).2 hvX
        simp [P2, profileUpdateSet, hv_notOther, profileUpdateSet, hvY, P_acb]
      have hPrefNotY : ∀ v : V, v ∉ Y → P2.pref v = r_cab := by
        intro v hvY
        by_cases hvOther : v ∈ others
        · simp [P2, profileUpdateSet, hvOther, P_cab]
        · have hvX : v ∈ X := by
            have hv_univ : v ∈ (Finset.univ : Finset V) := by simp
            by_contra hvX
            have : v ∈ others := by
              exact Finset.mem_sdiff.mpr ⟨hv_univ, hvX⟩
            exact hvOther this
          have hvZ : v ∈ Z := by
            have : v ∈ Y ∪ Z := by
              simpa [hunion] using hvX
            rcases Finset.mem_union.1 this with hvY' | hvZ
            · exact (hvY hvY').elim
            · exact hvZ
          simp [P2, profileUpdateSet, hvOther, profileUpdateSet, hvY, P, hvZ, P_cab]
      have hTopP2_ac : TopSet P2 (insert a {c}) := by
        intro v
        by_cases hvY : v ∈ Y
        · have h :=
            ballotTopABC_topSet_first_second (A := A) a c b hac hab hbc.symm
          simpa [hPrefY v hvY] using h
        · have h :=
            ballotTopABC_topSet_first_second (A := A) c a b hac.symm hbc.symm hab
          have h' : BallotTopSet (ballotTopABC (A := A) c a b hac.symm hbc.symm hab) (insert a {c}) := by
            simpa [Finset.pair_comm] using h
          simpa [hPrefNotY v hvY, r_cab] using h'
      have hP2prefsY : ∀ v : V, v ∈ Y → Prefers P2 v a c := by
        intro v hvY
        have h := ballotTopABC_prefers_first_second (A := A) a c b hac hab hbc.symm
        unfold Prefers
        rw [hPrefY v hvY]
        exact h
      have hP2prefsNotY : ∀ v : V, v ∉ Y → Prefers P2 v c a := by
        intro v hvY
        have h := ballotTopABC_prefers_first_second (A := A) c a b hac.symm hbc.symm hab
        unfold Prefers
        rw [hPrefNotY v hvY]
        exact h
      left
      exact aXb_of_exists_profile (f := f) (hf := hmono_singleton) (X := Y) (a := a) (b := c)
        (hab := hac) ⟨P2, hTopP2_ac, hP2prefsY, hP2prefsNotY, haP2⟩
  | inr hc =>
      let P_cba : Profile V A := { pref := fun _ => r_cba }
      let P_bca : Profile V A := { pref := fun _ => r_bca }
      have hP1 :
          c ∈ f (profileUpdateSet P P_cba Z) ∧
            TopSet (profileUpdateSet P P_cba Z) abc := by
        refine Finset.induction ?_ ?_ Z
        · simp [profileUpdateSet_empty, hc, hTopP]
        · intro v S hv hS
          let Q := profileUpdateSet P P_cba S
          have hcQ : c ∈ f Q := hS.1
          have hTopQ : TopSet Q abc := hS.2
          have hTopBallot :
              TopRank (updateProfile Q v (P_cba.pref v)) v c := by
            intro d hd
            have htop :=
              topRank_profileTopABC (V := V) (A := A) c b a hbc.symm hac.symm hab.symm v d hd
            unfold Prefers
            rw [show (updateProfile Q v (P_cba.pref v)).pref v = P_cba.pref v by
              simp only [updateProfile, if_true]]
            change (profileTopABC (V := V) (A := A) c b a hbc.symm hac.symm hab.symm).pref v |>.lt c d
            exact htop
          have hcQ' : c ∈ f (updateProfile Q v (P_cba.pref v)) :=
            winner_preserved_of_optimist_top (f := f) (hf_opt := hf_opt)
              (P := Q) (v := v) (ballot := P_cba.pref v) (a := c) hcQ hTopBallot
          have hBallot : BallotTopSet (P_cba.pref v) abc := by
            simpa [P_cba, abc_eq_cba] using
              (ballotTopABC_topSet (A := A) c b a hbc.symm hac.symm hab.symm)
          have hTopQ' :
              TopSet (updateProfile Q v (P_cba.pref v)) abc :=
            topSet_updateProfile (P := Q) (v := v) (ballot := P_cba.pref v) (X := abc) hTopQ hBallot
          have hupdate :=
            profileUpdateSet_insert (P := P) (P' := P_cba) (S := S) (v := v) hv
          have hcInsert : c ∈ f (profileUpdateSet P P_cba (insert v S)) := by
            simpa [hupdate] using hcQ'
          have hTopInsert : TopSet (profileUpdateSet P P_cba (insert v S)) abc := by
            simpa [hupdate] using hTopQ'
          exact ⟨hcInsert, hTopInsert⟩
      have hcP1 : c ∈ f (profileUpdateSet P P_cba Z) := hP1.1
      have hTopP1 : TopSet (profileUpdateSet P P_cba Z) abc := hP1.2
      have hP2 :
          ∀ S : Finset V, S ⊆ Y →
            c ∈ f (profileUpdateSet (profileUpdateSet P P_cba Z) P_bca S) ∧
              TopSet (profileUpdateSet (profileUpdateSet P P_cba Z) P_bca S) abc := by
        intro S hsub
        induction S using Finset.induction_on with
        | empty =>
            simpa [profileUpdateSet_empty] using ⟨hcP1, hTopP1⟩
        | @insert v S hv hS =>
            have hsubS : S ⊆ Y := by
              intro u hu
              exact hsub (Finset.mem_insert_of_mem hu)
            have hvY : v ∈ Y := hsub (by simp [hv])
            have hv_notZ : v ∉ Z := by
              intro hvZ
              exact (Finset.disjoint_left.1 hYZ hvY hvZ).elim
            let Q := profileUpdateSet (profileUpdateSet P P_cba Z) P_bca S
            have hS' := hS hsubS
            have hcQ : c ∈ f Q := hS'.1
            have hTopQ : TopSet Q abc := hS'.2
            have hBallot : BallotTopSet (P_bca.pref v) abc := by
              simpa [P_bca, abc_eq_bca] using
                (ballotTopABC_topSet (A := A) b c a hbc hab.symm hac.symm)
            have hTopQ' :
                TopSet (updateProfile Q v (P_bca.pref v)) abc :=
              topSet_updateProfile (P := Q) (v := v) (ballot := P_bca.pref v) (X := abc) hTopQ hBallot
            have hsubset_next : f (updateProfile Q v (P_bca.pref v)) ⊆ abc :=
              hsubset_topset _ hTopQ'
            have hbetter :
                ∀ y ∈ f (updateProfile Q v (P_bca.pref v)), y ≠ c → Prefers Q v y c := by
              intro y hy hy_ne
              have hyabc : y ∈ abc := hsubset_next hy
              have hy' : y = a ∨ y = b ∨ y = c := by
                simpa [abc] using hyabc
              rcases hy' with hy' | hy' | hy'
              · subst y
                unfold Prefers
                rw [show Q.pref v = ballotTopABC (A := A) a b c hab hac hbc by
                  simp only [Q, profileUpdateSet, hv, if_false, P, hvY, if_true, hv_notZ, r_abc]]
                exact ballotTopABC_prefers_first_third (A := A) a b c hab hac hbc
              · subst y
                unfold Prefers
                rw [show Q.pref v = ballotTopABC (A := A) a b c hab hac hbc by
                  simp only [Q, profileUpdateSet, hv, if_false, P, hvY, if_true, hv_notZ, r_abc]]
                exact ballotTopABC_prefers_second_third (A := A) a b c hab hac hbc
              · subst y
                exact (hy_ne rfl).elim
            have hcQ' :
                c ∈ f (updateProfile Q v (P_bca.pref v)) :=
              winner_preserved_of_pessimist_pref (f := f) (hf_pess := hf_pess)
                (P := Q) (v := v) (ballot := P_bca.pref v) (a := c) hcQ hbetter
            have hupdate :=
              profileUpdateSet_insert (P := profileUpdateSet P P_cba Z) (P' := P_bca) (S := S) (v := v) hv
            have hcInsert :
                c ∈ f (profileUpdateSet (profileUpdateSet P P_cba Z) P_bca (insert v S)) := by
              simpa [hupdate] using hcQ'
            have hTopInsert :
                TopSet (profileUpdateSet (profileUpdateSet P P_cba Z) P_bca (insert v S)) abc := by
              simpa [hupdate] using hTopQ'
            exact ⟨hcInsert, hTopInsert⟩
      have hcP2 :
          c ∈ f (profileUpdateSet (profileUpdateSet P P_cba Z) P_bca Y) :=
        (hP2 Y (by intro u hu; exact hu)).1
      let P2 := profileUpdateSet (profileUpdateSet P P_cba Z) P_bca Y
      have hPrefZ : ∀ v : V, v ∈ Z → P2.pref v = r_cba := by
        intro v hvZ
        have hv_notY : v ∉ Y := by
          intro hvY
          exact (Finset.disjoint_left.1 hYZ hvY hvZ).elim
        simp [P2, profileUpdateSet, hv_notY, profileUpdateSet, hvZ, P_cba]
      have hPrefNotZ : ∀ v : V, v ∉ Z → P2.pref v = r_bca := by
        intro v hvZ
        by_cases hvY : v ∈ Y
        · simp [P2, profileUpdateSet, hvY, P_bca]
        · simp [P2, profileUpdateSet, hvY, hvZ, profileUpdateSet, P, P_bca]
      have hTopP2_cb : TopSet P2 (insert c {b}) := by
        intro v
        by_cases hvZ : v ∈ Z
        · have h :=
            ballotTopABC_topSet_first_second (A := A) c b a hbc.symm hac.symm hab.symm
          simpa [hPrefZ v hvZ, r_cba] using h
        · have h :=
            ballotTopABC_topSet_first_second (A := A) b c a hbc hab.symm hac.symm
          have h' :
              BallotTopSet (ballotTopABC (A := A) b c a hbc hab.symm hac.symm) (insert c {b}) := by
            simpa [Finset.pair_comm] using h
          simpa [hPrefNotZ v hvZ, r_bca] using h'
      have hP2prefsZ : ∀ v : V, v ∈ Z → Prefers P2 v c b := by
        intro v hvZ
        have h := ballotTopABC_prefers_first_second (A := A) c b a hbc.symm hac.symm hab.symm
        unfold Prefers
        rw [hPrefZ v hvZ]
        exact h
      have hP2prefsNotZ : ∀ v : V, v ∉ Z → Prefers P2 v b c := by
        intro v hvZ
        have h := ballotTopABC_prefers_first_second (A := A) b c a hbc hab.symm hac.symm
        unfold Prefers
        rw [hPrefNotZ v hvZ]
        exact h
      right
      exact aXb_of_exists_profile (f := f) (hf := hmono_singleton) (X := Z) (a := c) (b := b)
        (hab := hbc.symm) ⟨P2, hTopP2_cb, hP2prefsZ, hP2prefsNotZ, hcP2⟩

/-! Lemma 2.9 (Taylor 2002) -/

omit [DecidableEq V] [DecidableEq A] in
lemma not_aXb_empty_of_viable (f : VotingRule) (hviable : Viable f) (a b : A) :
    ¬ aXb (V := V) (A := A) f (∅ : Finset V) a b := by
  classical
  intro h
  obtain ⟨P, hP⟩ := hviable (V := V) (A := A) b
  have h' : f P ≠ {b} := by
    apply h P
    intro v hv
    have : False := by simp at hv
    exact this.elim
  exact h' hP

lemma exists_ne_of_three_le_card (a b : A) (hab : a ≠ b) (hcard : 3 ≤ Fintype.card A) :
    ∃ c : A, c ≠ a ∧ c ≠ b := by
  classical
  have hcard_sub : 1 < Fintype.card {x : A // x ≠ a} := by
    have hcard_sub' : 1 < Fintype.card A - 1 := by
      omega
    simpa [card_subtype_ne_eq (α := A) (x := a)] using hcard_sub'
  obtain ⟨z, hz⟩ :=
    Fintype.exists_ne_of_one_lt_card (α := {x : A // x ≠ a}) hcard_sub ⟨b, Ne.symm hab⟩
  refine ⟨z.1, z.property, ?_⟩
  intro hzb
  apply hz
  apply Subtype.ext
  simp [hzb]

lemma aXb_left_right_of_opt_pess_viable (f : VotingRule)
    (hf_total : IsVotingRule f)
    (hf_opt : OptimistStrategyproof f)
    (hf_pess : PessimistStrategyproof f)
    (hviable : Viable f)
    (X : Finset V) (a b : A) (hab : a ≠ b)
    (hX : aXb (V := V) (A := A) f X a b) :
    (∀ c : A, c ≠ a → aXb (V := V) (A := A) f X a c) ∧
      (∀ c : A, c ≠ b → aXb (V := V) (A := A) f X c b) := by
  classical
  refine ⟨?left, ?right⟩
  · intro c hac
    by_cases hbc : b = c
    · subst hbc
      exact hX
    · have hpart :=
        aXb_partition_of_opt_pess_viable (f := f) (hf_total := hf_total) (hf_opt := hf_opt)
          (hf_pess := hf_pess) (hviable := hviable) (X := X) (Y := X) (Z := ∅)
          (a := a) (b := b) (c := c) (hab := hab) (hac := Ne.symm hac) (hbc := hbc) (hX := hX)
          (hYZ := by simp) (hunion := by simp)
      cases hpart with
      | inl h => exact h
      | inr h =>
          have : False :=
            (not_aXb_empty_of_viable (f := f) (hviable := hviable) (a := c) (b := b)) h
          exact this.elim
  · intro c hcb
    by_cases hca : c = a
    · subst hca
      exact hX
    · have hpart :=
        aXb_partition_of_opt_pess_viable (f := f) (hf_total := hf_total) (hf_opt := hf_opt)
          (hf_pess := hf_pess) (hviable := hviable) (X := X) (Y := ∅) (Z := X)
          (a := a) (b := b) (c := c) (hab := hab) (hac := Ne.symm hca) (hbc := Ne.symm hcb)
          (hX := hX)
          (hYZ := by simp) (hunion := by simp)
      cases hpart with
      | inl h =>
          have : False :=
            (not_aXb_empty_of_viable (f := f) (hviable := hviable) (a := a) (b := c)) h
          exact this.elim
      | inr h => exact h

/-! Lemma 2.10 (Taylor 2002) -/

lemma dictatingSet_of_aXb_of_opt_pess_viable (f : VotingRule)
    (hf_total : IsVotingRule f)
    (hf_opt : OptimistStrategyproof f)
    (hf_pess : PessimistStrategyproof f)
    (hviable : Viable f)
    (hcard : 3 ≤ Fintype.card A)
    (X : Finset V) (a b : A) (hab : a ≠ b)
    (hX : aXb (V := V) (A := A) f X a b) :
    DictatingSet (V := V) (A := A) f X := by
  classical
  intro x y hxy
  obtain ⟨hleft, hright⟩ :=
    aXb_left_right_of_opt_pess_viable (f := f) (hf_total := hf_total) (hf_opt := hf_opt)
      (hf_pess := hf_pess) (hviable := hviable) (X := X) (a := a) (b := b) (hab := hab) hX
  by_cases hya : y = a
  · subst y
    by_cases hxb : x = b
    · subst x
      obtain ⟨z, hz1, hz2⟩ := exists_ne_of_three_le_card (a := a) (b := b) hab hcard
      have hAz : aXb (V := V) (A := A) f X a z := hleft z hz1
      have hBz : aXb (V := V) (A := A) f X b z := by
        have h' :=
          aXb_left_right_of_opt_pess_viable (f := f) (hf_total := hf_total) (hf_opt := hf_opt)
            (hf_pess := hf_pess) (hviable := hviable) (X := X) (a := a) (b := z)
            (hab := Ne.symm hz1) hAz
        exact h'.2 b (Ne.symm hz2)
      have hBa : aXb (V := V) (A := A) f X b a := by
        have h' :=
          aXb_left_right_of_opt_pess_viable (f := f) (hf_total := hf_total) (hf_opt := hf_opt)
            (hf_pess := hf_pess) (hviable := hviable) (X := X) (a := b) (b := z)
            (hab := Ne.symm hz2) hBz
        exact h'.1 a hab
      exact hBa
    · have hXb : aXb (V := V) (A := A) f X x b := hright x hxb
      have h' :=
        aXb_left_right_of_opt_pess_viable (f := f) (hf_total := hf_total) (hf_opt := hf_opt)
          (hf_pess := hf_pess) (hviable := hviable) (X := X) (a := x) (b := b)
          (hab := hxb) hXb
      exact h'.1 a (Ne.symm hxy)
  · have hay : a ≠ y := by exact Ne.symm hya
    have hAy : aXb (V := V) (A := A) f X a y := hleft y hya
    have h' :=
      aXb_left_right_of_opt_pess_viable (f := f) (hf_total := hf_total) (hf_opt := hf_opt)
        (hf_pess := hf_pess) (hviable := hviable) (X := X) (a := a) (b := y)
        (hab := hay) hAy
    exact h'.2 x hxy

/-! Lemma 2.11 (Taylor 2002) -/

lemma dictatingSet_partition_of_opt_pess_viable (f : VotingRule)
    (hf_total : IsVotingRule f)
    (hf_opt : OptimistStrategyproof f)
    (hf_pess : PessimistStrategyproof f)
    (hviable : Viable f)
    (hcard : 3 ≤ Fintype.card A)
    (X Y Z : Finset V)
    (hX : DictatingSet (V := V) (A := A) f X)
    (hYZ : Disjoint Y Z) (hunion : Y ∪ Z = X) :
    DictatingSet (V := V) (A := A) f Y ∨ DictatingSet (V := V) (A := A) f Z := by
  classical
  have hcard1 : 1 < Fintype.card A := by
    exact lt_of_lt_of_le (by decide : 1 < 3) hcard
  obtain ⟨a, b, hab⟩ := exists_pair_of_one_lt_card (α := A) hcard1
  obtain ⟨c, hac, hbc⟩ := exists_ne_of_three_le_card (a := a) (b := b) hab hcard
  have hXab : aXb (V := V) (A := A) f X a b := hX a b hab
  have hpart :=
    aXb_partition_of_opt_pess_viable (f := f) (hf_total := hf_total) (hf_opt := hf_opt)
      (hf_pess := hf_pess) (hviable := hviable) (X := X) (Y := Y) (Z := Z) (a := a) (b := b)
      (c := c) (hab := hab) (hac := Ne.symm hac) (hbc := Ne.symm hbc) (hX := hXab)
      (hYZ := hYZ) (hunion := hunion)
  cases hpart with
  | inl hY =>
      left
      exact dictatingSet_of_aXb_of_opt_pess_viable (f := f) (hf_total := hf_total) (hf_opt := hf_opt)
        (hf_pess := hf_pess) (hviable := hviable) (hcard := hcard) (X := Y) (a := a) (b := c)
        (hab := Ne.symm hac) hY
  | inr hZ =>
      right
      exact dictatingSet_of_aXb_of_opt_pess_viable (f := f) (hf_total := hf_total) (hf_opt := hf_opt)
        (hf_pess := hf_pess) (hviable := hviable) (hcard := hcard) (X := Z) (a := c) (b := b)
        (hab := hbc) hZ

/-! Lemma 2.12 (Taylor 2002) -/

lemma exists_voter_topRank_of_singleton_winner (f : VotingRule)
    (hf_total : IsVotingRule f)
    (hf_opt : OptimistStrategyproof f)
    (hf_pess : PessimistStrategyproof f)
    (hviable : Viable f)
    (hcard : 3 ≤ Fintype.card A) :
    ∃ i : V, ∀ P : Profile V A, ∀ a : A, f P = {a} → TopRank P i a := by
  classical
  have hmono_singleton : DownMonotonicitySingleton f :=
    downMonotonicity_of_opt_pess_sp f hf_total hf_opt hf_pess
  have hdict_univ : DictatingSet (V := V) (A := A) f (Finset.univ : Finset V) :=
    dictatingSet_univ_of_downMonotonicitySingleton_viable (f := f) hmono_singleton hviable
  have hsingleton :
      ∃ i ∈ (Finset.univ : Finset V),
        DictatingSet (V := V) (A := A) f ({i} : Finset V) := by
    have hsubset :
        ∀ X : Finset V, DictatingSet (V := V) (A := A) f X →
          ∃ i ∈ X, DictatingSet (V := V) (A := A) f ({i} : Finset V) := by
      intro X hX
      revert hX
      refine Finset.induction_on (s := X) ?base ?step
      · intro hX
        have hcard1 : 1 < Fintype.card A := by
          exact lt_of_lt_of_le (by decide : 1 < 3) hcard
        obtain ⟨a, b, hab⟩ := exists_pair_of_one_lt_card (α := A) hcard1
        have hax : aXb (V := V) (A := A) f (∅ : Finset V) a b := hX a b hab
        have : False :=
          (not_aXb_empty_of_viable (f := f) (hviable := hviable) (a := a) (b := b)) hax
        exact this.elim
      · intro v S hv hS hX
        have hYZ : Disjoint ({v} : Finset V) S := by
          refine Finset.disjoint_left.2 ?_
          intro u hu huS
          have hu' : u = v := by simpa using hu
          subst hu'
          exact hv huS
        have hunion : ({v} : Finset V) ∪ S = insert v S := by
          ext u
          by_cases huv : u = v
          · subst huv
            simp
          · simp [Finset.mem_insert, huv]
        have hpart :=
          dictatingSet_partition_of_opt_pess_viable (f := f) (hf_total := hf_total) (hf_opt := hf_opt)
            (hf_pess := hf_pess) (hviable := hviable) (hcard := hcard) (X := insert v S)
            (Y := {v}) (Z := S) (hX := hX) (hYZ := hYZ) (hunion := hunion)
        cases hpart with
        | inl hY =>
            refine ⟨v, ?_, hY⟩
            simp
        | inr hZ =>
            rcases hS hZ with ⟨i, hiS, hiDict⟩
            refine ⟨i, ?_, hiDict⟩
            simp [hiS]
    exact hsubset (Finset.univ : Finset V) hdict_univ
  rcases hsingleton with ⟨i, _hi, hdict⟩
  refine ⟨i, ?_⟩
  intro P a hfa d hd
  have hnot : ¬ Prefers P i d a := by
    intro hda
    have hXda : aXb (V := V) (A := A) f ({i} : Finset V) d a := hdict d a hd
    have hXda' : f P ≠ {a} := by
      apply hXda P
      intro v hv
      have hv' : v = i := by simpa using hv
      subst hv'
      exact hda
    exact hXda' hfa
  let _ := P.pref i
  have hlt_or : Prefers P i a d ∨ Prefers P i d a := by
    simpa [Prefers] using (lt_or_gt_of_ne (a := a) (b := d) hd.symm)
  cases hlt_or with
  | inl hlt => exact hlt
  | inr hgt => exact (hnot hgt).elim

end SocialChoice
