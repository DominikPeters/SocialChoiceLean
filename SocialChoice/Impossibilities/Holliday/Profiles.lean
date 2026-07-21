import SocialChoice.Impossibilities.Holliday.Blocks

namespace SocialChoice

open Finset
open scoped BigOperators

namespace Holliday

/-! ### P1 on a single electorate (Fin 450) -/

abbrev U450 := Fin 450

def p1_cut1 : Nat := 62
def p1_cut2 : Nat := 69
def p1_cut3 : Nat := 133
def p1_cut4 : Nat := 179
def p1_cut5 : Nat := 199
def p1_cut6 : Nat := 210
def p1_cut7 : Nat := 217
def p1_cut8 : Nat := 219
def p1_cut9 : Nat := 245
def p1_cut10 : Nat := 268

def p1_cut1_fin : U450 := ⟨p1_cut1, by decide⟩
def p1_cut2_fin : U450 := ⟨p1_cut2, by decide⟩
def p1_cut3_fin : U450 := ⟨p1_cut3, by decide⟩
def p1_cut4_fin : U450 := ⟨p1_cut4, by decide⟩
def p1_cut5_fin : U450 := ⟨p1_cut5, by decide⟩
def p1_cut6_fin : U450 := ⟨p1_cut6, by decide⟩
def p1_cut7_fin : U450 := ⟨p1_cut7, by decide⟩
def p1_cut8_fin : U450 := ⟨p1_cut8, by decide⟩
def p1_cut9_fin : U450 := ⟨p1_cut9, by decide⟩
def p1_cut10_fin : U450 := ⟨p1_cut10, by decide⟩

def votersP1_1 : Finset U450 := Finset.Ico 0 p1_cut1_fin
def votersP1_2 : Finset U450 := Finset.Ico p1_cut1_fin p1_cut2_fin
def votersP1_3 : Finset U450 := Finset.Ico p1_cut2_fin p1_cut3_fin
def votersP1_4 : Finset U450 := Finset.Ico p1_cut3_fin p1_cut4_fin
def votersP1_5 : Finset U450 := Finset.Ico p1_cut4_fin p1_cut5_fin
def votersP1_6 : Finset U450 := Finset.Ico p1_cut5_fin p1_cut6_fin
def votersP1_7 : Finset U450 := Finset.Ico p1_cut6_fin p1_cut7_fin
def votersP1_8 : Finset U450 := Finset.Ico p1_cut7_fin p1_cut8_fin
def votersP1_9 : Finset U450 := Finset.Ico p1_cut8_fin p1_cut9_fin
def votersP1_10 : Finset U450 := Finset.Ico p1_cut9_fin p1_cut10_fin

def ballotsAllCuts : List (Nat × ListBallot 5) :=
  [(p1_cut1, ballot_daceb), (p1_cut2, ballot_daceb), (p1_cut3, ballot_ebacd),
   (p1_cut4, ballot_bcaed), (p1_cut5, ballot_cdeba), (p1_cut6, ballot_dbace),
   (p1_cut7, ballot_dbace), (p1_cut8, ballot_edcba), (p1_cut9, ballot_adbec),
   (p1_cut10, ballot_bdeac)]

def ballotByCuts : List (Nat × ListBallot 5) → Nat → ListBallot 5
  | [], _ => ballot_bdeac
  | (cut, ballot) :: tail, n => if n < cut then ballot else ballotByCuts tail n

lemma ballotByCuts_eq_of_lt {cut : Nat} {ballot : ListBallot 5} {tail : List (Nat × ListBallot 5)}
    {n : Nat} (h : n < cut) :
    ballotByCuts ((cut, ballot) :: tail) n = ballot := by
  simp [ballotByCuts, h]

lemma ballotByCuts_eq_of_ge {cut : Nat} {ballot : ListBallot 5} {tail : List (Nat × ListBallot 5)}
    {n : Nat} (h : cut ≤ n) :
    ballotByCuts ((cut, ballot) :: tail) n = ballotByCuts tail n := by
  simp [ballotByCuts, not_lt_of_ge h]

def blocksFromCuts : List (Nat × ListBallot 5) → Nat → List (Nat × Nat × ListBallot 5)
  | [], _ => []
  | (cut, ballot) :: tail, prev => (prev, cut, ballot) :: blocksFromCuts tail cut

def ballotsAllBlocks : List (Nat × Nat × ListBallot 5) :=
  blocksFromCuts ballotsAllCuts 0

@[simp] lemma ballotsAllBlocks_mem_1 : (0, p1_cut1, ballot_daceb) ∈ ballotsAllBlocks := by
  simp [ballotsAllBlocks, blocksFromCuts, ballotsAllCuts]

@[simp] lemma ballotsAllBlocks_mem_2 : (p1_cut1, p1_cut2, ballot_daceb) ∈ ballotsAllBlocks := by
  simp [ballotsAllBlocks, blocksFromCuts, ballotsAllCuts]

@[simp] lemma ballotsAllBlocks_mem_3 : (p1_cut2, p1_cut3, ballot_ebacd) ∈ ballotsAllBlocks := by
  simp [ballotsAllBlocks, blocksFromCuts, ballotsAllCuts]

@[simp] lemma ballotsAllBlocks_mem_4 : (p1_cut3, p1_cut4, ballot_bcaed) ∈ ballotsAllBlocks := by
  simp [ballotsAllBlocks, blocksFromCuts, ballotsAllCuts]

@[simp] lemma ballotsAllBlocks_mem_5 : (p1_cut4, p1_cut5, ballot_cdeba) ∈ ballotsAllBlocks := by
  simp [ballotsAllBlocks, blocksFromCuts, ballotsAllCuts]

@[simp] lemma ballotsAllBlocks_mem_6 : (p1_cut5, p1_cut6, ballot_dbace) ∈ ballotsAllBlocks := by
  simp [ballotsAllBlocks, blocksFromCuts, ballotsAllCuts]

@[simp] lemma ballotsAllBlocks_mem_7 : (p1_cut6, p1_cut7, ballot_dbace) ∈ ballotsAllBlocks := by
  simp [ballotsAllBlocks, blocksFromCuts, ballotsAllCuts]

@[simp] lemma ballotsAllBlocks_mem_8 : (p1_cut7, p1_cut8, ballot_edcba) ∈ ballotsAllBlocks := by
  simp [ballotsAllBlocks, blocksFromCuts, ballotsAllCuts]

@[simp] lemma ballotsAllBlocks_mem_9 : (p1_cut8, p1_cut9, ballot_adbec) ∈ ballotsAllBlocks := by
  simp [ballotsAllBlocks, blocksFromCuts, ballotsAllCuts]

@[simp] lemma ballotsAllBlocks_mem_10 : (p1_cut9, p1_cut10, ballot_bdeac) ∈ ballotsAllBlocks := by
  simp [ballotsAllBlocks, blocksFromCuts, ballotsAllCuts]

lemma blocksFromCuts_lo_ge_prev {cuts : List (Nat × ListBallot 5)} {prev lo hi : Nat}
    {ballot : ListBallot 5} :
    List.IsChain (· ≤ ·) (prev :: cuts.map Prod.fst) →
    (lo, hi, ballot) ∈ blocksFromCuts cuts prev →
    prev ≤ lo := by
  intro hchain hmem
  induction cuts generalizing prev lo hi ballot with
  | nil =>
      cases hmem
  | cons head tail ih =>
      cases head with
      | mk cut ballot' =>
          simp [blocksFromCuts] at hmem
          cases hmem with
          | inl h =>
              rcases h with ⟨rfl, rfl, rfl⟩
              exact le_rfl
          | inr hmem_tail =>
              have hchain' := (List.isChain_cons_cons).1 hchain
              have hprev_le_cut : prev ≤ cut := hchain'.1
              have hchain_tail : List.IsChain (· ≤ ·) (cut :: tail.map Prod.fst) := hchain'.2
              have hcut_le_lo : cut ≤ lo :=
                ih (prev := cut) (lo := lo) (hi := hi) (ballot := ballot) hchain_tail hmem_tail
              exact le_trans hprev_le_cut hcut_le_lo

lemma ballotByCuts_eq_of_mem_blocksFromCuts {cuts : List (Nat × ListBallot 5)} {prev n lo hi : Nat}
    {ballot : ListBallot 5} (hchain : List.IsChain (· ≤ ·) (prev :: cuts.map Prod.fst))
    (hmem : (lo, hi, ballot) ∈ blocksFromCuts cuts prev) (hlo : lo ≤ n) (hhi : n < hi) :
    ballotByCuts cuts n = ballot := by
  induction cuts generalizing prev lo hi ballot with
  | nil =>
      cases hmem
  | cons head tail ih =>
      cases head with
      | mk cut ballot' =>
          simp [blocksFromCuts] at hmem
          cases hmem with
          | inl h =>
              rcases h with ⟨rfl, rfl, rfl⟩
              simp [ballotByCuts, hhi]
          | inr hmem_tail =>
              have hchain' := (List.isChain_cons_cons).1 hchain
              have hchain_tail : List.IsChain (· ≤ ·) (cut :: tail.map Prod.fst) := hchain'.2
              have hcut_le_lo : cut ≤ lo :=
                blocksFromCuts_lo_ge_prev (cuts := tail) (prev := cut) (lo := lo) (hi := hi)
                  (ballot := ballot) hchain_tail hmem_tail
              have hcut_le_n : cut ≤ n := le_trans hcut_le_lo hlo
              have hskip :
                  ballotByCuts ((cut, ballot') :: tail) n = ballotByCuts tail n := by
                simpa using
                  (ballotByCuts_eq_of_ge (cut := cut) (ballot := ballot') (tail := tail) (n := n)
                    hcut_le_n)
              have ih' :=
                ih (prev := cut) (lo := lo) (hi := hi) (ballot := ballot) hchain_tail hmem_tail hlo
                  hhi
              simpa [hskip] using ih'

noncomputable def ballotsAll (v : U450) : ListBallot 5 :=
  ballotByCuts ballotsAllCuts v.val

lemma ballotsAll_eq_of_mem_block {v : U450} {lo hi : Nat} {ballot : ListBallot 5}
    (hmem : (lo, hi, ballot) ∈ ballotsAllBlocks) (hlo : lo ≤ v.val) (hhi : v.val < hi) :
    ballotsAll v = ballot := by
  have hchain : List.IsChain (· ≤ ·) (0 :: ballotsAllCuts.map Prod.fst) := by decide
  simpa [ballotsAll, ballotsAllBlocks] using
    (ballotByCuts_eq_of_mem_blocksFromCuts (cuts := ballotsAllCuts) (prev := 0) (n := v.val)
      hchain hmem hlo hhi)

lemma ballotsAll_eq_ballot_daceb_of_mem_votersP1_2 {v : U450} (hv : v ∈ votersP1_2) :
    ballotsAll v = ballot_daceb := by
  have hv' : p1_cut1 ≤ v.val ∧ v.val < p1_cut2 := by
    simpa [votersP1_2, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut1_fin, p1_cut2_fin] using hv
  exact ballotsAll_eq_of_mem_block (v := v) ballotsAllBlocks_mem_2 hv'.1 hv'.2

lemma ballotsAll_eq_ballot_dbace_of_mem_votersP1_7 {v : U450} (hv : v ∈ votersP1_7) :
    ballotsAll v = ballot_dbace := by
  have hv' : p1_cut6 ≤ v.val ∧ v.val < p1_cut7 := by
    simpa [votersP1_7, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut6_fin, p1_cut7_fin] using hv
  exact ballotsAll_eq_of_mem_block (v := v) ballotsAllBlocks_mem_7 hv'.1 hv'.2

lemma ballotsAll_eq_ballot_adbec_of_mem_votersP1_9 {v : U450} (hv : v ∈ votersP1_9) :
    ballotsAll v = ballot_adbec := by
  have hv' : p1_cut8 ≤ v.val ∧ v.val < p1_cut9 := by
    simpa [votersP1_9, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut8_fin, p1_cut9_fin] using hv
  exact ballotsAll_eq_of_mem_block (v := v) ballotsAllBlocks_mem_9 hv'.1 hv'.2

lemma ballotsAll_eq_ballot_bdeac_of_mem_votersP1_10 {v : U450} (hv : v ∈ votersP1_10) :
    ballotsAll v = ballot_bdeac := by
  have hv' : p1_cut9 ≤ v.val ∧ v.val < p1_cut10 := by
    simpa [votersP1_10, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut9_fin, p1_cut10_fin] using hv
  exact ballotsAll_eq_of_mem_block (v := v) ballotsAllBlocks_mem_10 hv'.1 hv'.2

noncomputable def FullProfile : Profile (Electorate U450 (Finset.univ)) A5 :=
  { pref := fun v => (ballotsAll v.1).toLinearOrder }

def votersP1 : Finset U450 :=
  Finset.univ.filter (fun v => v.val < p1_cut8)

lemma votersP1_eq_Ico : votersP1 = Finset.Ico 0 p1_cut8_fin := by
  ext v
  simp [votersP1, Finset.mem_Ico, Fin.lt_def, p1_cut8_fin]

-- P2 obtained by block 9 joining P1
def votersP2 : Finset U450 :=
  Finset.univ.filter (fun v => v.val < p1_cut9)

lemma votersP2_eq_Ico : votersP2 = Finset.Ico 0 p1_cut9_fin := by
  ext v
  simp [votersP2, Finset.mem_Ico, Fin.lt_def, p1_cut9_fin]

-- P3 obtained by block 2 leaving P2
def votersP3 : Finset U450 :=
  Finset.univ.filter (fun v => v.val < p1_cut1 ∨ (p1_cut2 ≤ v.val ∧ v.val < p1_cut9))

-- P4 obtained by block 10 joining P3
def votersP4 : Finset U450 :=
  Finset.univ.filter (fun v => v.val < p1_cut1 ∨ (p1_cut2 ≤ v.val ∧ v.val < p1_cut10))

-- P5 obtained by block 7 leaving P4
def votersP5 : Finset U450 :=
  Finset.univ.filter (fun v =>
    v.val < p1_cut1 ∨
      (p1_cut2 ≤ v.val ∧ v.val < p1_cut6) ∨
      (p1_cut7 ≤ v.val ∧ v.val < p1_cut10))

noncomputable def P1Profile : Profile (Electorate U450 votersP1) A5 :=
  restrictElectorate FullProfile votersP1 (by intro x hx ; exact Finset.mem_univ x)

noncomputable def P2Profile : Profile (Electorate U450 votersP2) A5 :=
  restrictElectorate FullProfile votersP2 (by intro x hx ; exact Finset.mem_univ x)

noncomputable def P3Profile : Profile (Electorate U450 votersP3) A5 :=
  restrictElectorate FullProfile votersP3 (by intro x hx ; exact Finset.mem_univ x)

noncomputable def P4Profile : Profile (Electorate U450 votersP4) A5 :=
  restrictElectorate FullProfile votersP4 (by intro x hx ; exact Finset.mem_univ x)

noncomputable def P5Profile : Profile (Electorate U450 votersP5) A5 :=
  restrictElectorate FullProfile votersP5 (by intro x hx ; exact Finset.mem_univ x)

lemma sum_Ico_split (a b c : U450) (f : U450 → Int) (hab : a ≤ b) (hbc : b ≤ c) :
    (Finset.Ico a c).sum f = (Finset.Ico a b).sum f + (Finset.Ico b c).sum f := by
  classical
  have hdisj : Disjoint (Finset.Ico a b) (Finset.Ico b c) :=
    Finset.Ico_disjoint_Ico_consecutive a b c
  have hunion : Finset.Ico a b ∪ Finset.Ico b c = Finset.Ico a c :=
    Finset.Ico_union_Ico_eq_Ico hab hbc
  calc
    (Finset.Ico a c).sum f =
        ((Finset.Ico a b ∪ Finset.Ico b c).sum f) := by simp [hunion]
    _ = (Finset.Ico a b).sum f + (Finset.Ico b c).sum f := by
        exact Finset.sum_union hdisj

def p1_cut_list : List U450 :=
  [0, p1_cut1_fin, p1_cut2_fin, p1_cut3_fin, p1_cut4_fin, p1_cut5_fin, p1_cut6_fin,
   p1_cut7_fin, p1_cut8_fin]

def lastOf (a : U450) : List U450 → U450
  | [] => a
  | b :: rest => lastOf b rest

def sum_Ico_chain (a : U450) : List U450 → (U450 → Int) → Int
  | [], _ => 0
  | b :: rest, f => (Finset.Ico a b).sum f + sum_Ico_chain b rest f

lemma le_lastOf_of_chain {a : U450} {rest : List U450} :
    List.IsChain (· ≤ ·) (a :: rest) → a ≤ lastOf a rest := by
  intro hchain
  cases rest with
  | nil =>
      simp [lastOf]
  | cons b rest =>
      have hchain' := (List.isChain_cons_cons).1 hchain
      have hab : a ≤ b := hchain'.1
      have hchain_tail : List.IsChain (· ≤ ·) (b :: rest) := hchain'.2
      have hbc : b ≤ lastOf b rest := le_lastOf_of_chain hchain_tail
      exact le_trans hab hbc

lemma sum_Ico_chain_eq (a : U450) (rest : List U450) (f : U450 → Int)
    (hchain : List.IsChain (· ≤ ·) (a :: rest)) :
    sum_Ico_chain a rest f = (Finset.Ico a (lastOf a rest)).sum f := by
  cases rest with
  | nil =>
      simp [sum_Ico_chain, lastOf]
  | cons b rest =>
      have hchain' := (List.isChain_cons_cons).1 hchain
      have hab : a ≤ b := hchain'.1
      have hchain_tail : List.IsChain (· ≤ ·) (b :: rest) := hchain'.2
      have hbc : b ≤ lastOf b rest := le_lastOf_of_chain hchain_tail
      have ih := sum_Ico_chain_eq (a := b) (rest := rest) (f := f) hchain_tail
      calc
        sum_Ico_chain a (b :: rest) f =
            (Finset.Ico a b).sum f + sum_Ico_chain b rest f := by
              simp [sum_Ico_chain]
        _ = (Finset.Ico a b).sum f + (Finset.Ico b (lastOf b rest)).sum f := by
              simp [ih]
        _ = (Finset.Ico a (lastOf b rest)).sum f := by
              symm
              exact sum_Ico_split (a := a) (b := b) (c := lastOf b rest) f hab hbc
        _ = (Finset.Ico a (lastOf a (b :: rest))).sum f := by
              simp [lastOf]

lemma sum_Ico_chain_p1 (f : U450 → Int) :
    (Finset.Ico (0 : U450) p1_cut8_fin).sum f =
      sum_Ico_chain 0 p1_cut_list.tail f := by
  have hchain : List.IsChain (· ≤ ·) p1_cut_list := by decide
  have hsum :=
    sum_Ico_chain_eq (a := 0) (rest := p1_cut_list.tail) (f := f)
      (by simpa [p1_cut_list] using hchain)
  simpa [p1_cut_list, lastOf] using hsum.symm

lemma sum_Ico_chain_p1_9 (f : U450 → Int) :
    (Finset.Ico (0 : U450) p1_cut9_fin).sum f =
      sum_Ico_chain 0 [p1_cut8_fin, p1_cut9_fin] f := by
  have hchain : List.IsChain (· ≤ ·) ([0, p1_cut8_fin, p1_cut9_fin] : List U450) := by
    decide
  have hsum :=
    sum_Ico_chain_eq (a := 0) (rest := [p1_cut8_fin, p1_cut9_fin]) (f := f)
      (by simpa using hchain)
  simpa [lastOf] using hsum.symm

lemma prefers_restrictElectorate_iff_prefersInList (S : Finset U450)
    (v : Electorate U450 S) (a b : A5) :
    Prefers (restrictElectorate FullProfile S (by intro x _; exact Finset.mem_univ x)) v a b ↔
      prefersInList (ballotsAll v.1).ranking a b = true := by
  unfold Prefers restrictElectorate FullProfile prefersInList
  rw [ListBallot.lt_iff_idxOf]
  simp [decide_eq_true_eq]

lemma votersP1_2_subset_votersP2 : votersP1_2 ⊆ votersP2 := by
  intro v hv
  have hv' : v.val < p1_cut2 := by
    rcases (Finset.mem_Ico.mp hv) with ⟨_hlo, hhi⟩
    exact Fin.lt_def.mp hhi
  have hlt9 : v.val < p1_cut9 := lt_of_lt_of_le hv' (by decide : p1_cut2 ≤ p1_cut9)
  simp [votersP2, hlt9]

lemma votersP3_eq_sdiff : votersP3 = votersP2 \ votersP1_2 := by
  ext v
  constructor
  · intro hv
    have hv' : v.val < p1_cut1 ∨ (p1_cut2 ≤ v.val ∧ v.val < p1_cut9) := by
      simpa [votersP3] using (Finset.mem_filter.mp hv).2
    have hv2 : v ∈ votersP2 := by
      have hlt9 : v.val < p1_cut9 := by
        cases hv' with
        | inl hlt1 =>
            exact lt_of_lt_of_le hlt1 (by decide : p1_cut1 ≤ p1_cut9)
        | inr hge2 =>
            exact hge2.2
      simp [votersP2, hlt9]
    have hv12 : v ∉ votersP1_2 := by
      intro hv12
      rcases (Finset.mem_Ico.mp hv12) with ⟨hlo, hhi⟩
      have hle1 : p1_cut1 ≤ v.val := Fin.le_def.mp hlo
      have hlt2 : v.val < p1_cut2 := Fin.lt_def.mp hhi
      cases hv' with
      | inl hlt1 =>
          exact (not_lt_of_ge hle1) hlt1
      | inr hge2 =>
          exact (not_lt_of_ge hge2.1) hlt2
    exact Finset.mem_sdiff.mpr ⟨hv2, hv12⟩
  · intro hv
    rcases Finset.mem_sdiff.mp hv with ⟨hv2, hv12⟩
    have hv2' : v.val < p1_cut9 := by
      simpa [votersP2] using (Finset.mem_filter.mp hv2).2
    by_cases hlt1 : v.val < p1_cut1
    · exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hlt1⟩)
    · have hge1 : p1_cut1 ≤ v.val := le_of_not_gt hlt1
      have hnot2 : ¬ v.val < p1_cut2 := by
        intro hlt2
        have hv12' : v ∈ votersP1_2 := by
          simpa [votersP1_2, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut1_fin,
            p1_cut2_fin] using And.intro hge1 hlt2
        exact hv12 hv12'
      have hge2 : p1_cut2 ≤ v.val := le_of_not_gt hnot2
      exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨hge2, hv2'⟩⟩)

lemma votersP4_eq_union_sdiff : votersP4 = (votersP2 \ votersP1_2) ∪ votersP1_10 := by
  ext v
  constructor
  · intro hv
    have hv' :
        v.val < p1_cut1 ∨ (p1_cut2 ≤ v.val ∧ v.val < p1_cut10) := by
      simpa [votersP4] using (Finset.mem_filter.mp hv).2
    cases hv' with
    | inl hlt1 =>
        have hlt9 : v.val < p1_cut9 := lt_of_lt_of_le hlt1 (by decide : p1_cut1 ≤ p1_cut9)
        have hv2 : v ∈ votersP2 := by
          simp [votersP2, hlt9]
        have hv12 : v ∉ votersP1_2 := by
          intro hv12
          have hv12' : p1_cut1 ≤ v.val := by
            rcases (Finset.mem_Ico.mp hv12) with ⟨hlo, _hhi⟩
            exact Fin.le_def.mp hlo
          exact (not_lt_of_ge hv12') hlt1
        exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hv2, hv12⟩))
    | inr hge2 =>
        by_cases hlt9 : v.val < p1_cut9
        · have hv2 : v ∈ votersP2 := by
            simp [votersP2, hlt9]
          have hv12 : v ∉ votersP1_2 := by
            intro hv12
            have hv12' : v.val < p1_cut2 := by
              rcases (Finset.mem_Ico.mp hv12) with ⟨_hlo, hhi⟩
              exact Fin.lt_def.mp hhi
            exact (not_lt_of_ge hge2.1) hv12'
          exact Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hv2, hv12⟩))
        · have hge9 : p1_cut9 ≤ v.val := le_of_not_gt hlt9
          have hv10 : v ∈ votersP1_10 := by
            have hlt10 : v.val < p1_cut10 := hge2.2
            simpa [votersP1_10, Finset.mem_Ico, Fin.le_def, Fin.lt_def,
              p1_cut9_fin, p1_cut10_fin] using And.intro hge9 hlt10
          exact Finset.mem_union.mpr (Or.inr hv10)
  · intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_sdiff.mp hv with ⟨hv2, hv10⟩
      have hv2' : v.val < p1_cut9 := by
        simpa [votersP2] using (Finset.mem_filter.mp hv2).2
      by_cases hlt1 : v.val < p1_cut1
      · exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hlt1⟩)
      · have hge1 : p1_cut1 ≤ v.val := le_of_not_gt hlt1
        have hnot2 : ¬ v.val < p1_cut2 := by
          intro hlt2
          have hv12' : v ∈ votersP1_2 := by
            simpa [votersP1_2, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut1_fin,
              p1_cut2_fin] using And.intro hge1 hlt2
          exact hv10 hv12'
        have hge2 : p1_cut2 ≤ v.val := le_of_not_gt hnot2
        exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨hge2, lt_of_lt_of_le hv2'
          (by decide : p1_cut9 ≤ p1_cut10)⟩⟩)
    · have hv10' : p1_cut9 ≤ v.val ∧ v.val < p1_cut10 := by
        simpa [votersP1_10, Finset.mem_Ico, Fin.le_def, Fin.lt_def,
          p1_cut9_fin, p1_cut10_fin] using hv
      exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨
        le_trans (by decide : p1_cut2 ≤ p1_cut9) hv10'.1, hv10'.2⟩⟩)

lemma votersP1_7_subset_votersP4 : votersP1_7 ⊆ votersP4 := by
  intro v hv
  have hv' : p1_cut6 ≤ v.val ∧ v.val < p1_cut7 := by
    simpa [votersP1_7, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut6_fin, p1_cut7_fin] using hv
  have hlt10 : v.val < p1_cut10 := lt_of_lt_of_le hv'.2 (by decide : p1_cut7 ≤ p1_cut10)
  exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨
    le_trans (by decide : p1_cut2 ≤ p1_cut6) hv'.1, hlt10⟩⟩)

lemma votersP5_eq_sdiff : votersP5 = votersP4 \ votersP1_7 := by
  ext v
  constructor
  · intro hv
    have hv' :
        v.val < p1_cut1 ∨ (p1_cut2 ≤ v.val ∧ v.val < p1_cut6) ∨ (p1_cut7 ≤ v.val ∧ v.val < p1_cut10) := by
      simpa [votersP5] using (Finset.mem_filter.mp hv).2
    have hv4 : v ∈ votersP4 := by
      cases hv' with
      | inl hlt1 =>
          exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hlt1⟩)
      | inr hrest =>
          cases hrest with
          | inl hge2lt6 =>
              have hlt10 : v.val < p1_cut10 := lt_of_lt_of_le hge2lt6.2 (by decide : p1_cut6 ≤ p1_cut10)
              exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨hge2lt6.1, hlt10⟩⟩)
          | inr hge7lt10 =>
              exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨
                le_trans (by decide : p1_cut2 ≤ p1_cut7) hge7lt10.1, hge7lt10.2⟩⟩)
    have hv17 : v ∉ votersP1_7 := by
      intro hv17
      have hv17' : p1_cut6 ≤ v.val ∧ v.val < p1_cut7 := by
        simpa [votersP1_7, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut6_fin, p1_cut7_fin] using hv17
      cases hv' with
      | inl hlt1 =>
          have hlt6 : v.val < p1_cut6 := lt_of_lt_of_le hlt1 (by decide : p1_cut1 ≤ p1_cut6)
          exact (not_lt_of_ge hv17'.1) hlt6
      | inr hrest =>
          cases hrest with
          | inl hge2lt6 =>
              exact (not_lt_of_ge hv17'.1) hge2lt6.2
          | inr hge7lt10 =>
              exact (not_lt_of_ge hge7lt10.1) hv17'.2
    exact Finset.mem_sdiff.mpr ⟨hv4, hv17⟩
  · intro hv
    rcases Finset.mem_sdiff.mp hv with ⟨hv4, hv17⟩
    have hv4' : v.val < p1_cut1 ∨ (p1_cut2 ≤ v.val ∧ v.val < p1_cut10) := by
      simpa [votersP4] using (Finset.mem_filter.mp hv4).2
    cases hv4' with
    | inl hlt1 =>
        exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl hlt1⟩)
    | inr hge2lt10 =>
        by_cases hlt6 : v.val < p1_cut6
        · exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Or.inl ⟨hge2lt10.1, hlt6⟩)⟩)
        · have hge6 : p1_cut6 ≤ v.val := le_of_not_gt hlt6
          have hnot7 : ¬ v.val < p1_cut7 := by
            intro hlt7
            have hv17' : v ∈ votersP1_7 := by
              simpa [votersP1_7, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut6_fin, p1_cut7_fin] using
                And.intro hge6 hlt7
            exact hv17 hv17'
          have hge7 : p1_cut7 ≤ v.val := le_of_not_gt hnot7
          exact (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr (Or.inr ⟨hge7, hge2lt10.2⟩)⟩)

lemma votersP1_disjoint_votersP1_9 : Disjoint votersP1 votersP1_9 := by
  refine Finset.disjoint_left.2 ?_
  intro v hv1 hv9
  have hv1' : v.val < p1_cut8 := by
    simpa [votersP1_eq_Ico, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut8_fin] using hv1
  have hv9' : p1_cut8 ≤ v.val := by
    have hv9' : p1_cut8 ≤ v.val ∧ v.val < p1_cut9 := by
      simpa [votersP1_9, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut8_fin, p1_cut9_fin] using hv9
    exact hv9'.1
  exact (not_lt_of_ge hv9') hv1'

lemma votersP3_disjoint_votersP1_2 : Disjoint votersP3 votersP1_2 := by
  refine Finset.disjoint_left.2 ?_
  intro v hv3 hv12
  have hv3' : v ∈ votersP2 ∧ v ∉ votersP1_2 := by
    simpa [votersP3_eq_sdiff] using hv3
  exact hv3'.2 hv12

lemma votersP3_disjoint_votersP1_10 : Disjoint votersP3 votersP1_10 := by
  refine Finset.disjoint_left.2 ?_
  intro v hv3 hv10
  have hv3' : v.val < p1_cut9 := by
    have hv3' : v.val < p1_cut1 ∨ (p1_cut2 ≤ v.val ∧ v.val < p1_cut9) := by
      simpa [votersP3] using (Finset.mem_filter.mp hv3).2
    cases hv3' with
    | inl hlt1 =>
        exact lt_of_lt_of_le hlt1 (by decide : p1_cut1 ≤ p1_cut9)
    | inr hge2 =>
        exact hge2.2
  have hv10' : p1_cut9 ≤ v.val := by
    have hv10' : p1_cut9 ≤ v.val ∧ v.val < p1_cut10 := by
      simpa [votersP1_10, Finset.mem_Ico, Fin.le_def, Fin.lt_def,
        p1_cut9_fin, p1_cut10_fin] using hv10
    exact hv10'.1
  exact (not_lt_of_ge hv10') hv3'

lemma votersP5_disjoint_votersP1_7 : Disjoint votersP5 votersP1_7 := by
  refine Finset.disjoint_left.2 ?_
  intro v hv5 hv17
  have hv5' : v ∈ votersP4 ∧ v ∉ votersP1_7 := by
    simpa [votersP5_eq_sdiff] using hv5
  exact hv5'.2 hv17

lemma votersP2_eq_union_votersP1_votersP1_9 : votersP1 ∪ votersP1_9 = votersP2 := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · have hv' : v.val < p1_cut8 := by
        simpa [votersP1_eq_Ico, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut8_fin] using hv
      have hv'' : v.val < p1_cut9 := lt_of_lt_of_le hv' (by decide : p1_cut8 ≤ p1_cut9)
      simp [votersP2, hv'']
    · have hv' : p1_cut8 ≤ v.val ∧ v.val < p1_cut9 := by
        simpa [votersP1_9, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut8_fin, p1_cut9_fin] using hv
      simp [votersP2, hv'.2]
  · intro hv
    have hv' : v.val < p1_cut9 := by
      simpa [votersP2] using (Finset.mem_filter.mp hv).2
    by_cases hlt8 : v.val < p1_cut8
    · have hv1 : v ∈ votersP1 := by
        simpa [votersP1] using hlt8
      exact Finset.mem_union.mpr (Or.inl hv1)
    · have hge8 : p1_cut8 ≤ v.val := le_of_not_gt hlt8
      have hv9 : v ∈ votersP1_9 := by
        simpa [votersP1_9, Finset.mem_Ico, Fin.le_def, Fin.lt_def, p1_cut8_fin, p1_cut9_fin] using
          And.intro hge8 hv'
      exact Finset.mem_union.mpr (Or.inr hv9)

lemma votersP2_eq_union_votersP3_votersP1_2 : votersP3 ∪ votersP1_2 = votersP2 := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · have hv' : v ∈ votersP2 := by
        have hv' : v ∈ votersP2 \ votersP1_2 := by
          simpa [votersP3_eq_sdiff] using hv
        exact (Finset.mem_sdiff.mp hv').1
      exact hv'
    · exact votersP1_2_subset_votersP2 hv
  · intro hv
    by_cases hv12 : v ∈ votersP1_2
    · exact Finset.mem_union.mpr (Or.inr hv12)
    · have hv3 : v ∈ votersP3 := by
        have hv3' : v ∈ votersP2 \ votersP1_2 := by
          exact Finset.mem_sdiff.mpr ⟨hv, hv12⟩
        simpa [votersP3_eq_sdiff] using hv3'
      exact Finset.mem_union.mpr (Or.inl hv3)

lemma votersP4_eq_union_votersP3_votersP1_10 : votersP3 ∪ votersP1_10 = votersP4 := by
  simpa [votersP3_eq_sdiff] using votersP4_eq_union_sdiff.symm

lemma votersP4_eq_union_votersP5_votersP1_7 : votersP5 ∪ votersP1_7 = votersP4 := by
  ext v
  constructor
  · intro hv
    rcases Finset.mem_union.mp hv with hv | hv
    · have hv' : v ∈ votersP4 := by
        have hv' : v ∈ votersP4 \ votersP1_7 := by
          simpa [votersP5_eq_sdiff] using hv
        exact (Finset.mem_sdiff.mp hv').1
      exact hv'
    · exact votersP1_7_subset_votersP4 hv
  · intro hv
    by_cases hv17 : v ∈ votersP1_7
    · exact Finset.mem_union.mpr (Or.inr hv17)
    · have hv5 : v ∈ votersP5 := by
        have hv5' : v ∈ votersP4 \ votersP1_7 := by
          exact Finset.mem_sdiff.mpr ⟨hv, hv17⟩
        simpa [votersP5_eq_sdiff] using hv5'
      exact Finset.mem_union.mpr (Or.inl hv5)

lemma P2Profile_eq_addCopiesProfile_P1 :
    P2Profile =
      castProfile (h := votersP2_eq_union_votersP1_votersP1_9)
        (addCopiesProfile (V := votersP1) (W := votersP1_9) P1Profile
          ballot_adbec.toLinearOrder) := by
  classical
  apply Profile.ext
  intro v
  by_cases hv : v.1 ∈ votersP1
  ·
    unfold P2Profile P1Profile FullProfile restrictElectorate castProfile addCopiesProfile
    simp [hv]
  · have hv2 : v.1 ∈ votersP2 := v.2
    have hv_union : v.1 ∈ votersP1 ∪ votersP1_9 := by
      have h :=
        congrArg (fun s => v.1 ∈ s) votersP2_eq_union_votersP1_votersP1_9
      exact (Eq.mp h.symm hv2)
    have hv9 : v.1 ∈ votersP1_9 := by
      rcases Finset.mem_union.mp hv_union with hv1 | hv9
      · exact (False.elim (hv hv1))
      · exact hv9
    have hballot : ballotsAll v.1 = ballot_adbec :=
      ballotsAll_eq_ballot_adbec_of_mem_votersP1_9 hv9
    unfold P2Profile FullProfile restrictElectorate castProfile addCopiesProfile
    simp [hv, hballot]

lemma P2Profile_eq_addCopiesProfile_P3 :
    P2Profile =
      castProfile (h := votersP2_eq_union_votersP3_votersP1_2)
        (addCopiesProfile (V := votersP3) (W := votersP1_2) P3Profile
          ballot_daceb.toLinearOrder) := by
  classical
  apply Profile.ext
  intro v
  by_cases hv : v.1 ∈ votersP3
  ·
    unfold P2Profile P3Profile FullProfile restrictElectorate castProfile addCopiesProfile
    simp [hv]
  · have hv2 : v.1 ∈ votersP2 := v.2
    have hv_union : v.1 ∈ votersP3 ∪ votersP1_2 := by
      have h :=
        congrArg (fun s => v.1 ∈ s) votersP2_eq_union_votersP3_votersP1_2
      exact (Eq.mp h.symm hv2)
    have hv12 : v.1 ∈ votersP1_2 := by
      rcases Finset.mem_union.mp hv_union with hv3 | hv12
      · exact (False.elim (hv hv3))
      · exact hv12
    have hballot : ballotsAll v.1 = ballot_daceb :=
      ballotsAll_eq_ballot_daceb_of_mem_votersP1_2 hv12
    unfold P2Profile FullProfile restrictElectorate castProfile addCopiesProfile
    simp [hv, hballot]

lemma P4Profile_eq_addCopiesProfile_P3 :
    P4Profile =
      castProfile (h := votersP4_eq_union_votersP3_votersP1_10)
        (addCopiesProfile (V := votersP3) (W := votersP1_10) P3Profile
          ballot_bdeac.toLinearOrder) := by
  classical
  apply Profile.ext
  intro v
  by_cases hv : v.1 ∈ votersP3
  ·
    unfold P4Profile P3Profile FullProfile restrictElectorate castProfile addCopiesProfile
    simp [hv]
  · have hv4 : v.1 ∈ votersP4 := v.2
    have hv_union : v.1 ∈ votersP3 ∪ votersP1_10 := by
      have h :=
        congrArg (fun s => v.1 ∈ s) votersP4_eq_union_votersP3_votersP1_10
      exact (Eq.mp h.symm hv4)
    have hv10 : v.1 ∈ votersP1_10 := by
      rcases Finset.mem_union.mp hv_union with hv3 | hv10
      · exact (False.elim (hv hv3))
      · exact hv10
    have hballot : ballotsAll v.1 = ballot_bdeac :=
      ballotsAll_eq_ballot_bdeac_of_mem_votersP1_10 hv10
    unfold P4Profile FullProfile restrictElectorate castProfile addCopiesProfile
    simp [hv, hballot]

lemma P4Profile_eq_addCopiesProfile_P5 :
    P4Profile =
      castProfile (h := votersP4_eq_union_votersP5_votersP1_7)
        (addCopiesProfile (V := votersP5) (W := votersP1_7) P5Profile
          ballot_dbace.toLinearOrder) := by
  classical
  apply Profile.ext
  intro v
  by_cases hv : v.1 ∈ votersP5
  ·
    unfold P4Profile P5Profile FullProfile restrictElectorate castProfile addCopiesProfile
    simp [hv]
  · have hv4 : v.1 ∈ votersP4 := v.2
    have hv_union : v.1 ∈ votersP5 ∪ votersP1_7 := by
      have h :=
        congrArg (fun s => v.1 ∈ s) votersP4_eq_union_votersP5_votersP1_7
      exact (Eq.mp h.symm hv4)
    have hv17 : v.1 ∈ votersP1_7 := by
      rcases Finset.mem_union.mp hv_union with hv5 | hv17
      · exact (False.elim (hv hv5))
      · exact hv17
    have hballot : ballotsAll v.1 = ballot_dbace :=
      ballotsAll_eq_ballot_dbace_of_mem_votersP1_7 hv17
    unfold P4Profile FullProfile restrictElectorate castProfile addCopiesProfile
    simp [hv, hballot]

end Holliday

end SocialChoice
