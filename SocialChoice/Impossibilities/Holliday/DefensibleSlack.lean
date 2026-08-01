import Mathlib.Tactic
import SocialChoice.Margin
import SocialChoice.Rules.DefensibleSet.Defs

namespace SocialChoice

open Finset
open scoped BigOperators

namespace Holliday

def DefensibleSlack {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x : A) (k : Int) : Prop :=
  ∀ y, ∃ z, margin P z y ≥ margin P y x + k

lemma mem_defensibleSet_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x : A) :
    x ∈ defensibleSetOf P ↔ ∀ y, ∃ z, margin P z y ≥ margin P y x := by
  classical
  simp [defensibleSetOf]

lemma defensibleSlack_add_newVoter
    {U A : Type} [DecidableEq U] [Fintype A]
    {V : Finset U} {u : U} (hu : u ∉ V)
    (P : Profile (Electorate U V) A)
    (Q : Profile (Electorate U (insert u V)) A)
    (hagree : ∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v)
    {x : A} {k : Int} (hslack : DefensibleSlack P x k) :
    DefensibleSlack Q x (k - 2) := by
  intro y
  rcases hslack y with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  have hlow : margin P z y - 1 ≤ margin Q z y := by
    have h := margin_le_add_newVoter (hu := hu) P Q hagree z y
    linarith
  have hhigh : margin Q y x ≤ margin P y x + 1 :=
    margin_add_newVoter_le (hu := hu) P Q hagree y x
  linarith

lemma defensible_add_newVoter_of_slack2
    {U A : Type} [DecidableEq U] [Fintype A]
    {V : Finset U} {u : U} (hu : u ∉ V)
    (P : Profile (Electorate U V) A)
    (Q : Profile (Electorate U (insert u V)) A)
    (hagree : ∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v)
    {x : A} (hslack : DefensibleSlack P x 2) :
    x ∈ defensibleSetOf Q := by
  classical
  have hslack' : DefensibleSlack Q x 0 :=
    defensibleSlack_add_newVoter (hu := hu) P Q hagree hslack
  refine (mem_defensibleSet_iff (P := Q) (x := x)).2 ?_
  intro y
  rcases hslack' y with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  simpa using hz

lemma defensible_add_newVoter_of_slack4
    {U A : Type} [DecidableEq U] [Fintype A]
    {V : Finset U} {u : U} (hu : u ∉ V)
    (P : Profile (Electorate U V) A)
    (Q : Profile (Electorate U (insert u V)) A)
    (hagree : ∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v)
    {x : A} (hslack : DefensibleSlack P x 4) :
    x ∈ defensibleSetOf Q := by
  classical
  have hslack' : DefensibleSlack Q x 2 :=
    defensibleSlack_add_newVoter (hu := hu) P Q hagree hslack
  refine (mem_defensibleSet_iff (P := Q) (x := x)).2 ?_
  intro y
  rcases hslack' y with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  linarith

end Holliday

end SocialChoice
