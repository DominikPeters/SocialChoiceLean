import Mathlib.Tactic
import SocialChoice.Axioms.Resolvability
import SocialChoice.Impossibilities.Holliday.CondorcetPositiveInvolvement
import SocialChoice.Impossibilities.Holliday.GapExtensions

namespace SocialChoice

namespace Holliday

lemma refines_defensible_P1 {f : VotingRule} (hpos : PositiveInvolvement f)
    (hcond : CondorcetConsistency f) :
    f P1Profile ⊆ defensibleSetOf P1Profile := by
  apply positiveInvolvement_condorcet_refines_defensible_of_gap (hpos := hpos) (hcond := hcond)
      (hcard := by decide) (P := P1Profile)
  intro x y _hx _hxy hy
  exact hgap_P1Profile (x := x) (y := y) hy

lemma refines_defensible_P3_add_newVoter {f : VotingRule} (hpos : PositiveInvolvement f)
    (hcond : CondorcetConsistency f)
    {u : U450} (hu : u ∉ votersP3)
    (Q : Profile (Electorate U450 (insert u votersP3)) A5)
    (hagree : ∀ v : Electorate U450 votersP3, Q.pref (liftVoter (u := u) v) = P3Profile.pref v) :
    f Q ⊆ defensibleSetOf Q := by
  apply positiveInvolvement_condorcet_refines_defensible_of_gap (hpos := hpos) (hcond := hcond)
      (hcard := by decide) (P := Q)
  intro x y _hx hxy hy
  exact hgap_P3Profile_add_newVoter (hu := hu) (Q := Q) (hagree := hagree) (x := x) (y := y) hy

lemma refines_defensible_P5_add_twoVoters {f : VotingRule} (hpos : PositiveInvolvement f)
    (hcond : CondorcetConsistency f)
    {u2 u4 : U450} (hu2 : u2 ∉ votersP5) (hu4 : u4 ∉ insert u2 votersP5)
    (Q2 : Profile (Electorate U450 (insert u2 votersP5)) A5)
    (Q : Profile (Electorate U450 (insert u4 (insert u2 votersP5))) A5)
    (hagree2 :
      ∀ v : Electorate U450 votersP5, Q2.pref (liftVoter (u := u2) v) = P5Profile.pref v)
    (hagree4 :
      ∀ v : Electorate U450 (insert u2 votersP5),
        Q.pref (liftVoter (u := u4) v) = Q2.pref v) :
    f Q ⊆ defensibleSetOf Q := by
  apply positiveInvolvement_condorcet_refines_defensible_of_gap (hpos := hpos) (hcond := hcond)
      (hcard := by decide) (P := Q)
  intro x y _hx hxy hy
  exact hgap_P5Profile_add_twoVoters (hu2 := hu2) (hu4 := hu4) (Q2 := Q2) (Q := Q)
    (hagree2 := hagree2) (hagree4 := hagree4) (x := x) (y := y) hy

lemma resolvability_P3_defensible {f : VotingRule} (hpos : PositiveInvolvement f)
    (hcond : CondorcetConsistency f) (hres : Resolvability f)
    {x : A5} (hx : x ∈ f P3Profile) {u : U450} (hu : u ∉ votersP3) :
    ∃ (r : LinearOrder A5)
      (Q : Profile (Electorate U450 (insert u votersP3)) A5),
      (∀ v : Electorate U450 votersP3, Q.pref (liftVoter (u := u) v) = P3Profile.pref v) ∧
      Q.pref (newVoter (u := u) (V := votersP3) hu) = r ∧
      f Q = {x} ∧ x ∈ defensibleSetOf Q := by
  obtain ⟨r, Q, hagree, hnew, hQ⟩ :=
    hres (V := votersP3) (u := u) (hu := hu) (P := P3Profile) (x := x) hx
  have href : f Q ⊆ defensibleSetOf Q :=
    refines_defensible_P3_add_newVoter (hpos := hpos) (hcond := hcond) (hu := hu) (Q := Q) hagree
  have hxQ : x ∈ f Q := by
    simp [hQ]
  exact ⟨r, Q, hagree, hnew, hQ, href hxQ⟩

lemma resolvability_P5_defensible {f : VotingRule} (hpos : PositiveInvolvement f)
    (hcond : CondorcetConsistency f) (hres : Resolvability f)
    {u2 u4 : U450} (hu2 : u2 ∉ votersP5) (hu4 : u4 ∉ insert u2 votersP5)
    (Q2 : Profile (Electorate U450 (insert u2 votersP5)) A5)
    (hagree2 :
      ∀ v : Electorate U450 votersP5, Q2.pref (liftVoter (u := u2) v) = P5Profile.pref v)
    {x : A5} (hx : x ∈ f Q2) :
    ∃ (r : LinearOrder A5)
      (Q : Profile (Electorate U450 (insert u4 (insert u2 votersP5))) A5),
      (∀ v : Electorate U450 (insert u2 votersP5),
          Q.pref (liftVoter (u := u4) v) = Q2.pref v) ∧
      Q.pref (newVoter (u := u4) (V := insert u2 votersP5) hu4) = r ∧
      f Q = {x} ∧ x ∈ defensibleSetOf Q := by
  obtain ⟨r, Q, hagree4, hnew, hQ⟩ :=
    hres (V := insert u2 votersP5) (u := u4) (hu := hu4) (P := Q2) (x := x) hx
  have href : f Q ⊆ defensibleSetOf Q :=
    refines_defensible_P5_add_twoVoters (hpos := hpos) (hcond := hcond)
      (hu2 := hu2) (hu4 := hu4) (Q2 := Q2) (Q := Q) (hagree2 := hagree2) (hagree4 := hagree4)
  have hxQ : x ∈ f Q := by
    simp [hQ]
  exact ⟨r, Q, hagree4, hnew, hQ, href hxQ⟩

end Holliday

end SocialChoice
