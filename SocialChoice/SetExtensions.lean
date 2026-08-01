import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Order
import Mathlib.Order.Basic
import SocialChoice.Axioms.Resolute
import SocialChoice.Profile

namespace SocialChoice

open Finset

structure SetExtension (A : Type) where
  weak : Finset A → Finset A → Prop

def SetExtension.strict {A : Type} (E : SetExtension A) (s t : Finset A) : Prop :=
  E.weak s t ∧ ¬ E.weak t s

def SetExtension.incomp {A : Type} (E : SetExtension A) (s t : Finset A) : Prop :=
  ¬ E.weak s t ∧ ¬ E.weak t s

def SetExtension.Complete {A : Type} (E : SetExtension A) : Prop :=
  ∀ s t : Finset A, s.Nonempty → t.Nonempty → E.weak s t ∨ E.weak t s

def TopInSet {A : Type} [DecidableEq A] (r : LinearOrder A) (s : Finset A) (a : A) : Prop :=
  a ∈ s ∧ ∀ b : A, b ∈ s → b ≠ a → r.lt a b

def BottomInSet {A : Type} [DecidableEq A] (r : LinearOrder A) (s : Finset A) (a : A) : Prop :=
  a ∈ s ∧ ∀ b : A, b ∈ s → b ≠ a → r.lt b a

lemma exists_topInSet {A : Type} [DecidableEq A] (r : LinearOrder A)
    {s : Finset A} (hs : s.Nonempty) : ∃ a, TopInSet r s a := by
  classical
  let _ := r
  refine ⟨s.min' hs, ?_⟩
  constructor
  · exact s.min'_mem hs
  · intro b hb hne
    have hle : s.min' hs ≤ b := s.min'_le b hb
    have hne' : s.min' hs ≠ b := by
      exact hne.symm
    have hlt : s.min' hs < b := lt_of_le_of_ne hle hne'
    simpa using hlt

lemma exists_bottomInSet {A : Type} [DecidableEq A] (r : LinearOrder A)
    {s : Finset A} (hs : s.Nonempty) : ∃ a, BottomInSet r s a := by
  classical
  let _ := r
  refine ⟨s.max' hs, ?_⟩
  constructor
  · exact s.max'_mem hs
  · intro b hb hne
    have hle : b ≤ s.max' hs := s.le_max' b hb
    have hlt : b < s.max' hs := lt_of_le_of_ne hle hne
    simpa using hlt

def OptimistWeak {A : Type} [DecidableEq A] (r : LinearOrder A)
    (s t : Finset A) : Prop :=
  ∃ a b : A, TopInSet r s a ∧ TopInSet r t b ∧ r.le a b

def PessimistWeak {A : Type} [DecidableEq A] (r : LinearOrder A)
    (s t : Finset A) : Prop :=
  ∃ a b : A, BottomInSet r s a ∧ BottomInSet r t b ∧ r.le a b

def OptimistExtension {A : Type} [DecidableEq A] (r : LinearOrder A) : SetExtension A :=
  { weak := OptimistWeak r }

def PessimistExtension {A : Type} [DecidableEq A] (r : LinearOrder A) : SetExtension A :=
  { weak := PessimistWeak r }

def KellyWeak {A : Type} (r : LinearOrder A) (s t : Finset A) : Prop :=
  ∀ x ∈ s, ∀ y ∈ t, r.le x y

def KellyExtension {A : Type} (r : LinearOrder A) : SetExtension A :=
  { weak := KellyWeak r }

def FishburnWeak {A : Type} [DecidableEq A] (r : LinearOrder A) (s t : Finset A) : Prop :=
  (∀ x ∈ s \ t, ∀ y ∈ s ∩ t, r.le x y) ∧
    (∀ y ∈ s ∩ t, ∀ z ∈ t \ s, r.le y z) ∧
    (∀ x ∈ s \ t, ∀ z ∈ t \ s, r.le x z)

def FishburnExtension {A : Type} [DecidableEq A] (r : LinearOrder A) : SetExtension A :=
  { weak := FishburnWeak r }

/-- Lemmas about the Optimist set extensions. -/

lemma optimist_complete {A : Type} [DecidableEq A] (r : LinearOrder A) :
    SetExtension.Complete (OptimistExtension r) := by
  intro s t hs ht
  obtain ⟨a, ha⟩ := exists_topInSet r hs
  obtain ⟨b, hb⟩ := exists_topInSet r ht
  have hcomp : r.le a b ∨ r.le b a := by
    let _ := r
    simpa using (le_total a b)
  cases hcomp with
  | inl hle => exact Or.inl ⟨a, b, ha, hb, hle⟩
  | inr hle => exact Or.inr ⟨b, a, hb, ha, hle⟩

lemma optimist_no_incomp {A : Type} [DecidableEq A] (r : LinearOrder A)
    {s t : Finset A} (hs : s.Nonempty) (ht : t.Nonempty) :
    ¬ (OptimistExtension r).incomp s t := by
  intro h
  have hcomp := optimist_complete r s t hs ht
  cases hcomp with
  | inl hw => exact h.1 hw
  | inr hw => exact h.2 hw

/-- Lemmas about the Pessimist set extensions. -/

lemma pessimist_complete {A : Type} [DecidableEq A] (r : LinearOrder A) :
    SetExtension.Complete (PessimistExtension r) := by
  intro s t hs ht
  obtain ⟨a, ha⟩ := exists_bottomInSet r hs
  obtain ⟨b, hb⟩ := exists_bottomInSet r ht
  have hcomp : r.le a b ∨ r.le b a := by
    let _ := r
    simpa using (le_total a b)
  cases hcomp with
  | inl hle => exact Or.inl ⟨a, b, ha, hb, hle⟩
  | inr hle => exact Or.inr ⟨b, a, hb, ha, hle⟩

lemma pessimist_no_incomp {A : Type} [DecidableEq A] (r : LinearOrder A)
    {s t : Finset A} (hs : s.Nonempty) (ht : t.Nonempty) :
    ¬ (PessimistExtension r).incomp s t := by
  intro h
  have hcomp := pessimist_complete r s t hs ht
  cases hcomp with
  | inl hw => exact h.1 hw
  | inr hw => exact h.2 hw

/-- Lemmas about the Fishburn set extensions. -/

lemma fishburn_min_tb_le {A : Type} [DecidableEq A] (tb r : LinearOrder A)
    {s t : Finset A} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : FishburnWeak r s t) :
    r.le (@Finset.min' A tb s hs) (@Finset.min' A tb t ht) := by
  classical
  let _ := tb
  set a := s.min' hs with ha
  set b := t.min' ht with hb
  have ha_mem : a ∈ s := by
    simpa [ha] using (s.min'_mem hs)
  have hb_mem : b ∈ t := by
    simpa [hb] using (t.min'_mem ht)
  obtain ⟨h1, h2, h3⟩ := hst
  have h : r.le a b := by
    by_cases ha_t : a ∈ t
    · have ha_st : a ∈ s ∩ t := by
        exact Finset.mem_inter.mpr ⟨ha_mem, ha_t⟩
      by_cases hb_s : b ∈ s
      · have hb_st : b ∈ s ∩ t := by
          exact Finset.mem_inter.mpr ⟨hb_s, hb_mem⟩
        have hle_ab : a ≤ b := by
          simpa [ha] using (s.min'_le b hb_s)
        have hle_ba : b ≤ a := by
          simpa [hb] using (t.min'_le a ha_t)
        have h_eq : a = b := le_antisymm hle_ab hle_ba
        let _ := r
        exact le_of_eq h_eq
      · have hb_ts : b ∈ t \ s := by
          exact Finset.mem_sdiff.mpr ⟨hb_mem, hb_s⟩
        exact h2 a ha_st b hb_ts
    · have ha_st : a ∈ s \ t := by
        exact Finset.mem_sdiff.mpr ⟨ha_mem, ha_t⟩
      by_cases hb_s : b ∈ s
      · have hb_st : b ∈ s ∩ t := by
          exact Finset.mem_inter.mpr ⟨hb_s, hb_mem⟩
        exact h1 a ha_st b hb_st
      · have hb_ts : b ∈ t \ s := by
          exact Finset.mem_sdiff.mpr ⟨hb_mem, hb_s⟩
        exact h3 a ha_st b hb_ts
  simpa [ha, hb] using h

lemma fishburnWeak_implies_optimistWeak {A : Type} [DecidableEq A] (r : LinearOrder A)
    {s t : Finset A} (hs : s.Nonempty) (ht : t.Nonempty) :
    FishburnWeak r s t → OptimistWeak r s t := by
  intro hfish
  refine ⟨s.min' hs, t.min' ht, ?_⟩
  have hs_top : TopInSet r s (s.min' hs) := by
    constructor
    · exact s.min'_mem hs
    · intro b hb hne
      have hle : s.min' hs ≤ b := s.min'_le b hb
      exact lt_of_le_of_ne hle hne.symm
  have ht_top : TopInSet r t (t.min' ht) := by
    constructor
    · exact t.min'_mem ht
    · intro b hb hne
      have hle : t.min' ht ≤ b := t.min'_le b hb
      exact lt_of_le_of_ne hle hne.symm
  refine ⟨hs_top, ht_top, ?_⟩
  exact fishburn_min_tb_le (tb := r) (r := r) (s := s) (t := t) hs ht hfish

lemma fishburnExtension_weak_implies_optimistExtension_weak
    {A : Type} [DecidableEq A] (r : LinearOrder A)
    {s t : Finset A} (hs : s.Nonempty) (ht : t.Nonempty) :
    (FishburnExtension (A := A) r).weak s t → (OptimistExtension (A := A) r).weak s t := by
  intro hfish
  simpa [FishburnExtension, OptimistExtension] using
    (fishburnWeak_implies_optimistWeak (r := r) hs ht hfish)

end SocialChoice
