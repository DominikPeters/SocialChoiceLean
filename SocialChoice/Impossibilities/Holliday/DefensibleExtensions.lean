import Mathlib.Tactic
import SocialChoice.Margin
import SocialChoice.Impossibilities.Holliday.DefensibleSlack
import SocialChoice.Impossibilities.Holliday.GapInstances

namespace SocialChoice

namespace Holliday

private lemma not_defensible_of_witness {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x y : A)
    (h : ∀ z, margin P z y < margin P y x) : x ∉ defensibleSetOf P := by
  classical
  intro hx
  have hx' := (mem_defensibleSet_iff (P := P) (x := x)).1 hx
  rcases hx' y with ⟨z, hz⟩
  exact (not_le_of_gt (h z)) hz

private lemma margin_add_newVoter_ge
    {U A : Type} [DecidableEq U] [Fintype A]
    {V : Finset U} {u : U} (hu : u ∉ V)
    (P : Profile (Electorate U V) A)
    (Q : Profile (Electorate U (insert u V)) A)
    (hagree : ∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v)
    (a b : A) :
    margin P a b - 1 ≤ margin Q a b := by
  have h : margin Q b a ≤ margin P b a + 1 :=
    margin_add_newVoter_le (hu := hu) P Q hagree b a
  have hskewP : margin P a b = - margin P b a := by
    simpa [skew_symmetric] using (margin_antisymmetric (P := P)) a b
  have hskewQ : margin Q a b = - margin Q b a := by
    simpa [skew_symmetric] using (margin_antisymmetric (P := Q)) a b
  linarith [h, hskewP, hskewQ]

private lemma not_defensible_add_newVoter_of_gap4
    {u : U450} {x y : A5} (hu : u ∉ votersP3)
    (Q : Profile (Electorate U450 (insert u votersP3)) A5)
    (hagree : ∀ v : Electorate U450 votersP3, Q.pref (liftVoter (u := u) v) = P3Profile.pref v)
    (hgap : ∀ z, margin P3Profile z y ≤ margin P3Profile y x - 4) :
    x ∉ defensibleSetOf Q := by
  refine not_defensible_of_witness (P := Q) (x := x) (y := y) ?_
  intro z
  have hupper : margin Q z y ≤ margin P3Profile z y + 1 :=
    margin_add_newVoter_le (hu := hu) P3Profile Q hagree z y
  have hlower : margin P3Profile y x - 1 ≤ margin Q y x :=
    margin_add_newVoter_ge (hu := hu) P3Profile Q hagree y x
  have hgapz : margin P3Profile z y ≤ margin P3Profile y x - 4 := hgap z
  linarith [hupper, hlower, hgapz]

private lemma margin_add_twoVoters_le
    {u2 u4 : U450} (hu2 : u2 ∉ votersP5) (hu4 : u4 ∉ insert u2 votersP5)
    (Q2 : Profile (Electorate U450 (insert u2 votersP5)) A5)
    (Q : Profile (Electorate U450 (insert u4 (insert u2 votersP5))) A5)
    (hagree2 :
      ∀ v : Electorate U450 votersP5, Q2.pref (liftVoter (u := u2) v) = P5Profile.pref v)
    (hagree4 :
      ∀ v : Electorate U450 (insert u2 votersP5),
        Q.pref (liftVoter (u := u4) v) = Q2.pref v)
    (a b : A5) :
    margin Q a b ≤ margin P5Profile a b + 2 := by
  have h1 : margin Q a b ≤ margin Q2 a b + 1 :=
    margin_add_newVoter_le (hu := hu4) Q2 Q hagree4 a b
  have h2 : margin Q2 a b ≤ margin P5Profile a b + 1 :=
    margin_add_newVoter_le (hu := hu2) P5Profile Q2 hagree2 a b
  linarith [h1, h2]

private lemma margin_add_twoVoters_ge
    {u2 u4 : U450} (hu2 : u2 ∉ votersP5) (hu4 : u4 ∉ insert u2 votersP5)
    (Q2 : Profile (Electorate U450 (insert u2 votersP5)) A5)
    (Q : Profile (Electorate U450 (insert u4 (insert u2 votersP5))) A5)
    (hagree2 :
      ∀ v : Electorate U450 votersP5, Q2.pref (liftVoter (u := u2) v) = P5Profile.pref v)
    (hagree4 :
      ∀ v : Electorate U450 (insert u2 votersP5),
        Q.pref (liftVoter (u := u4) v) = Q2.pref v)
    (a b : A5) :
    margin P5Profile a b - 2 ≤ margin Q a b := by
  have h1 : margin P5Profile a b - 1 ≤ margin Q2 a b :=
    margin_add_newVoter_ge (hu := hu2) P5Profile Q2 hagree2 a b
  have h2 : margin Q2 a b - 1 ≤ margin Q a b :=
    margin_add_newVoter_ge (hu := hu4) Q2 Q hagree4 a b
  linarith [h1, h2]

private lemma not_defensible_add_twoVoters_of_gap6
    {u2 u4 : U450} {x y : A5} (hu2 : u2 ∉ votersP5) (hu4 : u4 ∉ insert u2 votersP5)
    (Q2 : Profile (Electorate U450 (insert u2 votersP5)) A5)
    (Q : Profile (Electorate U450 (insert u4 (insert u2 votersP5))) A5)
    (hagree2 :
      ∀ v : Electorate U450 votersP5, Q2.pref (liftVoter (u := u2) v) = P5Profile.pref v)
    (hagree4 :
      ∀ v : Electorate U450 (insert u2 votersP5),
        Q.pref (liftVoter (u := u4) v) = Q2.pref v)
    (hgap : ∀ z, margin P5Profile z y ≤ margin P5Profile y x - 6) :
    x ∉ defensibleSetOf Q := by
  refine not_defensible_of_witness (P := Q) (x := x) (y := y) ?_
  intro z
  have hupper : margin Q z y ≤ margin P5Profile z y + 2 :=
    margin_add_twoVoters_le (hu2 := hu2) (hu4 := hu4) Q2 Q hagree2 hagree4 z y
  have hlower : margin P5Profile y x - 2 ≤ margin Q y x :=
    margin_add_twoVoters_ge (hu2 := hu2) (hu4 := hu4) Q2 Q hagree2 hagree4 y x
  have hgapz : margin P5Profile z y ≤ margin P5Profile y x - 6 := hgap z
  linarith [hupper, hlower, hgapz]

private lemma P3_gap_ba : ∀ z, margin P3Profile z b ≤ margin P3Profile b a - 4 := by
  intro z
  fin_cases z <;> simp [self_margin_zero]

private lemma P3_gap_ac : ∀ z, margin P3Profile z a ≤ margin P3Profile a c - 4 := by
  intro z
  fin_cases z <;> simp [self_margin_zero]

private lemma P3_gap_ae : ∀ z, margin P3Profile z a ≤ margin P3Profile a e - 4 := by
  intro z
  fin_cases z <;> simp [self_margin_zero]

lemma not_defensible_P3_add_newVoter_a {u : U450} (hu : u ∉ votersP3)
    (Q : Profile (Electorate U450 (insert u votersP3)) A5)
    (hagree : ∀ v : Electorate U450 votersP3, Q.pref (liftVoter (u := u) v) = P3Profile.pref v) :
    a ∉ defensibleSetOf Q :=
  not_defensible_add_newVoter_of_gap4 (hu := hu) (Q := Q) (hagree := hagree) (x := a) (y := b)
    P3_gap_ba

lemma not_defensible_P3_add_newVoter_c {u : U450} (hu : u ∉ votersP3)
    (Q : Profile (Electorate U450 (insert u votersP3)) A5)
    (hagree : ∀ v : Electorate U450 votersP3, Q.pref (liftVoter (u := u) v) = P3Profile.pref v) :
    c ∉ defensibleSetOf Q :=
  not_defensible_add_newVoter_of_gap4 (hu := hu) (Q := Q) (hagree := hagree) (x := c) (y := a)
    P3_gap_ac

lemma not_defensible_P3_add_newVoter_e {u : U450} (hu : u ∉ votersP3)
    (Q : Profile (Electorate U450 (insert u votersP3)) A5)
    (hagree : ∀ v : Electorate U450 votersP3, Q.pref (liftVoter (u := u) v) = P3Profile.pref v) :
    e ∉ defensibleSetOf Q :=
  not_defensible_add_newVoter_of_gap4 (hu := hu) (Q := Q) (hagree := hagree) (x := e) (y := a)
    P3_gap_ae

lemma defensibleSet_P3_add_newVoter_subset {u : U450} (hu : u ∉ votersP3)
    (Q : Profile (Electorate U450 (insert u votersP3)) A5)
    (hagree : ∀ v : Electorate U450 votersP3, Q.pref (liftVoter (u := u) v) = P3Profile.pref v) :
    defensibleSetOf Q ⊆ ({b, d} : Finset A5) := by
  intro x hx
  fin_cases x
  · exact (False.elim ((not_defensible_P3_add_newVoter_a (hu := hu) (Q := Q) hagree) hx))
  · simp
  · exact (False.elim ((not_defensible_P3_add_newVoter_c (hu := hu) (Q := Q) hagree) hx))
  · simp
  · exact (False.elim ((not_defensible_P3_add_newVoter_e (hu := hu) (Q := Q) hagree) hx))

private lemma P5_gap_ba : ∀ z, margin P5Profile z b ≤ margin P5Profile b a - 6 := by
  intro z
  fin_cases z <;> simp [self_margin_zero]

private lemma P5_gap_eb : ∀ z, margin P5Profile z e ≤ margin P5Profile e b - 6 := by
  intro z
  fin_cases z <;> simp [self_margin_zero]

private lemma P5_gap_ac : ∀ z, margin P5Profile z a ≤ margin P5Profile a c - 6 := by
  intro z
  fin_cases z <;> simp [self_margin_zero]

private lemma P5_gap_de : ∀ z, margin P5Profile z d ≤ margin P5Profile d e - 6 := by
  intro z
  fin_cases z <;> simp [self_margin_zero]

lemma not_defensible_P5_add_twoVoters_a {u2 u4 : U450} (hu2 : u2 ∉ votersP5)
    (hu4 : u4 ∉ insert u2 votersP5)
    (Q2 : Profile (Electorate U450 (insert u2 votersP5)) A5)
    (Q : Profile (Electorate U450 (insert u4 (insert u2 votersP5))) A5)
    (hagree2 :
      ∀ v : Electorate U450 votersP5, Q2.pref (liftVoter (u := u2) v) = P5Profile.pref v)
    (hagree4 :
      ∀ v : Electorate U450 (insert u2 votersP5),
        Q.pref (liftVoter (u := u4) v) = Q2.pref v) :
    a ∉ defensibleSetOf Q :=
  not_defensible_add_twoVoters_of_gap6 (hu2 := hu2) (hu4 := hu4) (Q2 := Q2) (Q := Q)
    (hagree2 := hagree2) (hagree4 := hagree4) (x := a) (y := b) P5_gap_ba

lemma not_defensible_P5_add_twoVoters_b {u2 u4 : U450} (hu2 : u2 ∉ votersP5)
    (hu4 : u4 ∉ insert u2 votersP5)
    (Q2 : Profile (Electorate U450 (insert u2 votersP5)) A5)
    (Q : Profile (Electorate U450 (insert u4 (insert u2 votersP5))) A5)
    (hagree2 :
      ∀ v : Electorate U450 votersP5, Q2.pref (liftVoter (u := u2) v) = P5Profile.pref v)
    (hagree4 :
      ∀ v : Electorate U450 (insert u2 votersP5),
        Q.pref (liftVoter (u := u4) v) = Q2.pref v) :
    b ∉ defensibleSetOf Q :=
  not_defensible_add_twoVoters_of_gap6 (hu2 := hu2) (hu4 := hu4) (Q2 := Q2) (Q := Q)
    (hagree2 := hagree2) (hagree4 := hagree4) (x := b) (y := e) P5_gap_eb

lemma not_defensible_P5_add_twoVoters_c {u2 u4 : U450} (hu2 : u2 ∉ votersP5)
    (hu4 : u4 ∉ insert u2 votersP5)
    (Q2 : Profile (Electorate U450 (insert u2 votersP5)) A5)
    (Q : Profile (Electorate U450 (insert u4 (insert u2 votersP5))) A5)
    (hagree2 :
      ∀ v : Electorate U450 votersP5, Q2.pref (liftVoter (u := u2) v) = P5Profile.pref v)
    (hagree4 :
      ∀ v : Electorate U450 (insert u2 votersP5),
        Q.pref (liftVoter (u := u4) v) = Q2.pref v) :
    c ∉ defensibleSetOf Q :=
  not_defensible_add_twoVoters_of_gap6 (hu2 := hu2) (hu4 := hu4) (Q2 := Q2) (Q := Q)
    (hagree2 := hagree2) (hagree4 := hagree4) (x := c) (y := a) P5_gap_ac

lemma not_defensible_P5_add_twoVoters_e {u2 u4 : U450} (hu2 : u2 ∉ votersP5)
    (hu4 : u4 ∉ insert u2 votersP5)
    (Q2 : Profile (Electorate U450 (insert u2 votersP5)) A5)
    (Q : Profile (Electorate U450 (insert u4 (insert u2 votersP5))) A5)
    (hagree2 :
      ∀ v : Electorate U450 votersP5, Q2.pref (liftVoter (u := u2) v) = P5Profile.pref v)
    (hagree4 :
      ∀ v : Electorate U450 (insert u2 votersP5),
        Q.pref (liftVoter (u := u4) v) = Q2.pref v) :
    e ∉ defensibleSetOf Q :=
  not_defensible_add_twoVoters_of_gap6 (hu2 := hu2) (hu4 := hu4) (Q2 := Q2) (Q := Q)
    (hagree2 := hagree2) (hagree4 := hagree4) (x := e) (y := d) P5_gap_de

lemma defensibleSet_P5_add_twoVoters_subset {u2 u4 : U450} (hu2 : u2 ∉ votersP5)
    (hu4 : u4 ∉ insert u2 votersP5)
    (Q2 : Profile (Electorate U450 (insert u2 votersP5)) A5)
    (Q : Profile (Electorate U450 (insert u4 (insert u2 votersP5))) A5)
    (hagree2 :
      ∀ v : Electorate U450 votersP5, Q2.pref (liftVoter (u := u2) v) = P5Profile.pref v)
    (hagree4 :
      ∀ v : Electorate U450 (insert u2 votersP5),
        Q.pref (liftVoter (u := u4) v) = Q2.pref v) :
    defensibleSetOf Q ⊆ ({d} : Finset A5) := by
  intro x hx
  fin_cases x
  · exact (False.elim ((not_defensible_P5_add_twoVoters_a (hu2 := hu2) (hu4 := hu4)
        (Q2 := Q2) (Q := Q) hagree2 hagree4) hx))
  · exact (False.elim ((not_defensible_P5_add_twoVoters_b (hu2 := hu2) (hu4 := hu4)
        (Q2 := Q2) (Q := Q) hagree2 hagree4) hx))
  · exact (False.elim ((not_defensible_P5_add_twoVoters_c (hu2 := hu2) (hu4 := hu4)
        (Q2 := Q2) (Q := Q) hagree2 hagree4) hx))
  · simp
  · exact (False.elim ((not_defensible_P5_add_twoVoters_e (hu2 := hu2) (hu4 := hu4)
        (Q2 := Q2) (Q := Q) hagree2 hagree4) hx))

end Holliday

end SocialChoice
