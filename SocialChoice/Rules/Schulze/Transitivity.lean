import Mathlib.Data.List.Basic
import SocialChoice.Rules.Schulze.Defs
import SocialChoice.Rules.Schulze.Path

namespace SocialChoice

lemma schulze_transitivity_step
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b c : A) (l : List A) (u : List A)
    (hl : l ≠ []) (hu : u ≠ [])
    (hmem : l ++ b :: u ∈ pathsUpTo (A := A) (Fintype.card A) a c) :
    min (pathStrength P (l ++ [b])) (pathStrength P (b :: u)) ≤ strongestPath P a c := by
  exact pathStrength_concat_le_strongestPath (P := P) (a := a) (c := c)
    (l := l) (b := b) (u := u) hl hu hmem

lemma strongestPath_triangle_of_disjoint
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b c : A) (l u : List A)
    (hl : l ++ [b] ∈ pathsUpTo (A := A) (Fintype.card A) a b)
    (hu : b :: u ∈ pathsUpTo (A := A) (Fintype.card A) b c)
    (hdis : List.Disjoint l u)
    (hlmax : pathStrength P (l ++ [b]) = strongestPath P a b)
    (humax : pathStrength P (b :: u) = strongestPath P b c) :
    min (strongestPath P a b) (strongestPath P b c) ≤ strongestPath P a c := by
  have hmem : l ++ b :: u ∈ pathsUpTo (A := A) (Fintype.card A) a c := by
    exact mem_pathsUpTo_concat_of_disjoint (a := a) (b := b) (c := c) (l := l) (u := u) hl hu hdis
  have hlne : l ≠ [] := by
    intro hnil
    have hlen1 : (l ++ [b]).length = 1 := by simp [hnil]
    have hlen2 : 2 ≤ (l ++ [b]).length := by
      exact (path_props_of_mem_pathsUpTo (l := l ++ [b]) (a := a) (b := b) hl).2.2.2
    have : (2 : Nat) ≤ 1 := by
      have hlen2' := hlen2
      simp [hlen1] at hlen2'
    exact (by decide : ¬ ((2 : Nat) ≤ 1)) this
  have hune : u ≠ [] := by
    intro hnil
    have hlen1 : (b :: u).length = 1 := by simp [hnil]
    have hlen2 : 2 ≤ (b :: u).length := by
      exact (path_props_of_mem_pathsUpTo (l := b :: u) (a := b) (b := c) hu).2.2.2
    have : (2 : Nat) ≤ 1 := by
      have hlen2' := hlen2
      simp [hlen1] at hlen2'
    exact (by decide : ¬ ((2 : Nat) ≤ 1)) this
  have hstep := schulze_transitivity_step (P := P) (a := a) (b := b) (c := c)
    (l := l) (u := u) hlne hune hmem
  simpa [hlmax, humax] using hstep

lemma strongestPath_triangle_of_nodup
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b c : A) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    min (strongestPath P a b) (strongestPath P b c) ≤ strongestPath P a c := by
  classical
  have hne_ab : (pathsUpTo (A := A) (Fintype.card A) a b).Nonempty := by
    refine ⟨[a, b], ?_⟩
    refine mem_pathsUpTo_of_props (l := [a, b]) (a := a) (b := b) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp [List.nodup_cons, hab]
    · simp
  have hne_bc : (pathsUpTo (A := A) (Fintype.card A) b c).Nonempty := by
    refine ⟨[b, c], ?_⟩
    refine mem_pathsUpTo_of_props (l := [b, c]) (a := b) (b := c) ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp [List.nodup_cons, hbc]
    · simp
  rcases exists_max_path_props (P := P) (a := a) (b := b) hne_ab with
    ⟨l, _hl, hhead_l, hlast_l, _hnodup_l, hlen_l, hstrength_l⟩
  rcases exists_max_path_props (P := P) (a := b) (b := c) hne_bc with
    ⟨u, _hu, hhead_u, hlast_u, _hnodup_u, hlen_u, hstrength_u⟩
  let l1 := l.dropLast
  let u1 := u.tail
  have hl1ne : l1 ≠ [] := by
    cases l with
    | nil => simp at hlen_l
    | cons x xs =>
        cases xs with
        | nil => simp at hlen_l
        | cons y ys =>
            simp [l1]
  have hu1ne : u1 ≠ [] := by
    cases u with
    | nil => simp at hlen_u
    | cons x xs =>
        cases xs with
        | nil => simp at hlen_u
        | cons y ys =>
            simp [u1]
  have hdrop : l1 ++ [b] = l := by
    have hb : b ∈ l.getLast? := by
      simp [hlast_l]
    simpa [l1] using (List.dropLast_append_getLast? (l := l) (a := b) hb)
  have hcons : b :: u1 = u := by
    have hb : b ∈ u.head? := by
      simp [hhead_u]
    simpa [u1] using (List.cons_head?_tail (l := u) (a := b) hb)
  let lconcat := l1 ++ b :: u1
  have hconcat_strength :
      min (pathStrength P l) (pathStrength P u) ≤ pathStrength P lconcat := by
    have h := pathStrength_concat_of_append_cons
      (P := P) (l := l1) (b := b) (u := u1) hl1ne hu1ne
    simpa [lconcat, hdrop, hcons] using h
  have hhead_l1 : l1.head? = some a := by
    have hhead_eq : (l1 ++ [b]).head? = l1.head? :=
      List.head?_append_of_ne_nil (l₁ := l1) (l₂ := [b]) hl1ne
    calc
      l1.head? = (l1 ++ [b]).head? := by simpa using hhead_eq.symm
      _ = l.head? := by simp [hdrop]
      _ = some a := hhead_l
  have hhead_concat : lconcat.head? = some a := by
    have hhead_eq : lconcat.head? = l1.head? :=
      List.head?_append_of_ne_nil (l₁ := l1) (l₂ := b :: u1) hl1ne
    simpa [hhead_l1] using hhead_eq
  have hlast_concat : lconcat.getLast? = some c := by
    have hne : (b :: u1 : List A) ≠ [] := by simp
    have hlast_eq : lconcat.getLast? = (b :: u1).getLast? := by
      simpa [lconcat] using (List.getLast?_append_of_ne_nil l1 hne)
    calc
      lconcat.getLast? = (b :: u1).getLast? := hlast_eq
      _ = u.getLast? := by simp [hcons]
      _ = some c := hlast_u
  rcases exists_nodup_strength_ge (P := P) (a := a) (c := c) (l := lconcat)
      hhead_concat hlast_concat hac with
    ⟨l', hnodup', hhead', hlast', hstrength_le, _hlen_le⟩
  have hlen' : 2 ≤ l'.length := by
    cases l' with
    | nil =>
        simp at hhead'
    | cons x xs =>
        cases xs with
        | nil =>
            have ha : a = x := by
              apply Option.some.inj
              simpa using hhead'.symm
            have hc : c = x := by
              apply Option.some.inj
              simpa using hlast'.symm
            exact (hac (ha.trans hc.symm)).elim
        | cons y ys =>
            simp
  have hmem : l' ∈ pathsUpTo (A := A) (Fintype.card A) a c :=
    mem_pathsUpTo_of_props (l := l') (a := a) (b := c) hhead' hlast' hnodup' hlen'
  have hconcat_le : pathStrength P lconcat ≤ strongestPath P a c := by
    exact le_trans hstrength_le
      (pathStrength_of_mem_pathsUpTo_le_strongestPath (P := P) (a := a) (b := c) (l := l') hmem)
  have hmin_le : min (strongestPath P a b) (strongestPath P b c) ≤ pathStrength P lconcat := by
    simpa [hstrength_l, hstrength_u] using hconcat_strength
  exact le_trans hmin_le hconcat_le

lemma strongestPath_triangle
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b c : A) (hac : a ≠ c) :
    min (strongestPath P a b) (strongestPath P b c) ≤ strongestPath P a c := by
  by_cases hab : a = b
  · subst hab
    exact min_le_right _ _
  by_cases hbc : b = c
  · subst hbc
    exact min_le_left _ _
  exact strongestPath_triangle_of_nodup (P := P) (a := a) (b := b) (c := c)
    (hab := hab) (hbc := hbc) (hac := hac)

set_option maxHeartbeats 400000 in
lemma schulzeDefeats_trans_aux
    {sab sba sbc scb sac sca : Int}
    (h1 : min sab sbc ≤ sac)
    (h2 : min sbc sca ≤ sba)
    (h3 : min sca sab ≤ scb)
    (h_ab : sab > sba)
    (h_bc : sbc > scb) :
    sca < sac := by
  by_cases hcase : sab ≤ sbc
  · have h_sab_le_sac : sab ≤ sac := by
      simpa [min_eq_left hcase] using h1
    by_cases hsca_le_sbc : sca ≤ sbc
    · have h_sca_le_sba : sca ≤ sba := by
        simpa [min_eq_right hsca_le_sbc] using h2
      have h_sca_lt_sab : sca < sab := lt_of_le_of_lt h_sca_le_sba h_ab
      exact lt_of_lt_of_le h_sca_lt_sab h_sab_le_sac
    · have hsbc_le_sca : sbc ≤ sca := le_of_lt (lt_of_not_ge hsca_le_sbc)
      have h_sbc_le_sba : sbc ≤ sba := by
        simpa [min_eq_left hsbc_le_sca] using h2
      have h_sab_le_sba : sab ≤ sba := le_trans hcase h_sbc_le_sba
      exact (lt_irrefl _ (lt_of_le_of_lt h_sab_le_sba h_ab)).elim
  · have h_sbc_lt_sab : sbc < sab := lt_of_not_ge hcase
    have h_sbc_le_sac : sbc ≤ sac := by
      simpa [min_eq_right (le_of_lt h_sbc_lt_sab)] using h1
    by_cases hsca_le_sab : sca ≤ sab
    · have h_sca_le_scb : sca ≤ scb := by
        simpa [min_eq_left hsca_le_sab] using h3
      have h_scb_lt_sac : scb < sac := lt_of_lt_of_le h_bc h_sbc_le_sac
      exact lt_of_le_of_lt h_sca_le_scb h_scb_lt_sac
    · have hsab_le_sca : sab ≤ sca := le_of_lt (lt_of_not_ge hsca_le_sab)
      have h_sab_le_scb : sab ≤ scb := by
        simpa [min_eq_right hsab_le_sca] using h3
      have h_scb_lt_sab : scb < sab := lt_of_lt_of_le h_bc (le_of_lt h_sbc_lt_sab)
      exact (lt_irrefl _ (lt_of_le_of_lt h_sab_le_scb h_scb_lt_sab)).elim

lemma schulzeDefeats_trans
    {V A : Type} [Fintype V] [Fintype A]
    {P : Profile V A} {a b c : A}
    (hab : schulzeDefeats P a b) (hbc : schulzeDefeats P b c) :
    schulzeDefeats P a c := by
  have hab_ne : a ≠ b := schulzeDefeats_ne (P := P) hab
  have hbc_ne : b ≠ c := schulzeDefeats_ne (P := P) hbc
  have hac : a ≠ c := by
    intro hEq
    subst hEq
    exact (schulzeDefeats_asymm (P := P) hab) hbc
  have h1 :
      min (strongestPath P a b) (strongestPath P b c) ≤ strongestPath P a c :=
    strongestPath_triangle (P := P) (a := a) (b := b) (c := c) hac
  have h2 :
      min (strongestPath P b c) (strongestPath P c a) ≤ strongestPath P b a :=
    strongestPath_triangle (P := P) (a := b) (b := c) (c := a) hab_ne.symm
  have h3 :
      min (strongestPath P c a) (strongestPath P a b) ≤ strongestPath P c b :=
    strongestPath_triangle (P := P) (a := c) (b := a) (c := b) hbc_ne.symm
  exact schulzeDefeats_trans_aux
    (sab := strongestPath P a b)
    (sba := strongestPath P b a)
    (sbc := strongestPath P b c)
    (scb := strongestPath P c b)
    (sac := strongestPath P a c)
    (sca := strongestPath P c a)
    h1 h2 h3 hab hbc

lemma schulzeDefeats_transitive
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) : IsTrans A (schulzeDefeats P) := by
  refine ⟨?_⟩
  intro a b c hab hbc
  exact schulzeDefeats_trans (P := P) hab hbc

lemma exists_schulze_maximal
    {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (s : Finset A) (hs : s.Nonempty) :
    ∃ a ∈ s, ∀ b ∈ s, ¬ schulzeDefeats P b a := by
  classical
  refine Finset.induction_on s ?h0 ?hstep hs
  · intro hs'
    exact (Finset.not_nonempty_empty hs').elim
  · intro a s ha ih hs'
    by_cases hs_empty : s = ∅
    · subst hs_empty
      refine ⟨a, by simp, ?_⟩
      intro b hb
      simp at hb
      subst hb
      intro hba
      exact (schulzeDefeats_ne (P := P) hba) rfl
    · have hs_nonempty : s.Nonempty := by
        exact Finset.nonempty_iff_ne_empty.mpr hs_empty
      rcases ih hs_nonempty with ⟨m, hm, hmax⟩
      by_cases ham : schulzeDefeats P a m
      · refine ⟨a, by simp [ha], ?_⟩
        intro b hb
        have hb' : b = a ∨ b ∈ s := by
          simpa [Finset.mem_insert, ha] using hb
        cases hb' with
        | inl hba =>
            subst hba
            intro hba'
            exact (schulzeDefeats_ne (P := P) hba') rfl
        | inr hbs =>
            intro hba'
            have hbm : schulzeDefeats P b m :=
              schulzeDefeats_trans (P := P) hba' ham
            exact (hmax b hbs) hbm
      · refine ⟨m, by simp [hm], ?_⟩
        intro b hb
        have hb' : b = a ∨ b ∈ s := by
          simpa [Finset.mem_insert, ha] using hb
        cases hb' with
        | inl hba =>
            subst hba
            exact ham
        | inr hbs =>
            exact hmax b hbs

lemma schulze_nonempty
    {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (P : Profile V A) :
    (schulze (V := V) (A := A) P).Nonempty := by
  classical
  have hne : (Finset.univ : Finset A).Nonempty := Finset.univ_nonempty
  rcases exists_schulze_maximal (P := P) (s := (Finset.univ : Finset A)) hne with
    ⟨a, _ha_mem, hmax⟩
  have hmax' : ∀ b, ¬ schulzeDefeats P b a := by
    intro b
    exact hmax b (by simp)
  refine ⟨a, ?_⟩
  simp [schulze, hmax', Finset.mem_univ]

theorem schulze_isVotingRule : IsVotingRule schulze := by
  intro V A _ _ _ P
  classical
  simpa using (schulze_nonempty (P := P))

end SocialChoice
