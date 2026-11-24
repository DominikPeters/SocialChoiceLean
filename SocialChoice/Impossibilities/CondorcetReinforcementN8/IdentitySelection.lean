import SocialChoice.Impossibilities.CondorcetReinforcementN8.Kneser
import Mathlib.Combinatorics.SetFamily.KruskalKatona

set_option maxRecDepth 1000000

namespace SocialChoice
namespace CondorcetReinforcementN8
namespace IdentitySelection

open Nat

/-- Ordered triples of distinct voters from an eight-voter electorate. -/
abbrev OrderedTriple8 :=
  { t : Fin 8 × Fin 8 × Fin 8 // t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.2.2 ≠ t.1 }

namespace OrderedTriple8

def first (t : OrderedTriple8) : Fin 8 := t.val.1
def second (t : OrderedTriple8) : Fin 8 := t.val.2.1
def third (t : OrderedTriple8) : Fin 8 := t.val.2.2

theorem first_ne_second (t : OrderedTriple8) : t.first ≠ t.second := t.property.1
theorem second_ne_third (t : OrderedTriple8) : t.second ≠ t.third := t.property.2.1
theorem third_ne_first (t : OrderedTriple8) : t.third ≠ t.first := t.property.2.2
theorem first_ne_third (t : OrderedTriple8) : t.first ≠ t.third := by
  exact (t.third_ne_first).symm

/-- The unordered support of an ordered triple. -/
def support (t : OrderedTriple8) : Finset (Fin 8) := {t.first, t.second, t.third}

theorem support_card (t : OrderedTriple8) : t.support.card = 3 := by
  rw [support]
  simp [first_ne_second, first_ne_third, second_ne_third]

theorem first_mem_support (t : OrderedTriple8) : t.first ∈ t.support := by
  simp [support]

theorem second_mem_support (t : OrderedTriple8) : t.second ∈ t.support := by
  simp [support]

theorem third_mem_support (t : OrderedTriple8) : t.third ∈ t.support := by
  simp [support]

theorem eq_of_support_eq_of_first_second_eq {t u : OrderedTriple8}
    (hsupport : t.support = u.support)
    (hfirst : t.first = u.first) (hsecond : t.second = u.second) :
    t = u := by
  apply Subtype.ext
  rcases t with ⟨⟨a, b, c⟩, ht⟩
  rcases u with ⟨⟨a', b', c'⟩, hu⟩
  simp [first, second, third, support] at hfirst hsecond hsupport ⊢
  subst a'
  subst b'
  have hc_mem : c ∈ ({a, b, c'} : Finset (Fin 8)) := by
    have : c ∈ ({a, b, c} : Finset (Fin 8)) := by simp
    simpa [hsupport] using this
  simp at hc_mem
  rcases hc_mem with hc | hc | hc
  · exact False.elim (ht.2.2 hc)
  · exact False.elim (ht.2.1 hc.symm)
  · subst c'
    simp

theorem card : Fintype.card OrderedTriple8 = 336 := by
  decide

theorem exists_support_eq (T : Finset (Fin 8)) (hT : T.card = 3) :
    ∃ t : OrderedTriple8, t.support = T := by
  revert T
  decide

end OrderedTriple8

/-- The directed edge selected by a color from an ordered triple.

Color `0` selects the first-second edge, color `1` the second-third edge,
and color `2` the third-first edge. -/
def distinguishedEdge (x : Fin 3) (t : OrderedTriple8) : Fin 8 × Fin 8 :=
  match x with
  | 0 => (t.first, t.second)
  | 1 => (t.second, t.third)
  | 2 => (t.third, t.first)

def edgeCrosses (A : Finset (Fin 8)) (e : Fin 8 × Fin 8) : Prop :=
  (e.1 ∈ A ∧ e.2 ∉ A) ∨ (e.1 ∉ A ∧ e.2 ∈ A)

def insideEdge (S : Finset (Fin 8)) (e : Fin 8 × Fin 8) : Prop :=
  e.1 ∈ S ∧ e.2 ∈ S

def directedEdgesInside (S : Finset (Fin 8)) : Finset (Fin 8 × Fin 8) :=
  (S.product S).filter fun e => e.1 ≠ e.2

def internalEdges (T U : Finset (Fin 8)) : Finset (Fin 8 × Fin 8) :=
  directedEdgesInside T ∪ directedEdgesInside U

def freeVertices (T U : Finset (Fin 8)) : Finset (Fin 8) :=
  (Finset.univ : Finset (Fin 8)) \ (T ∪ U)

def remainingVertex (x : Fin 3) (t : OrderedTriple8) : Fin 8 :=
  match x with
  | 0 => t.third
  | 1 => t.first
  | 2 => t.second

def colorClass (κ : OrderedTriple8 → Fin 3) (x : Fin 3) : Finset OrderedTriple8 :=
  Finset.univ.filter fun t => κ t = x

def supportFamily (κ : OrderedTriple8 → Fin 3) (x : Fin 3) : Set (Finset (Fin 8)) :=
  {T | T.card = 3 ∧ ∃ t : OrderedTriple8, κ t = x ∧ t.support = T}

def supportFinset (κ : OrderedTriple8 → Fin 3) (x : Fin 3) : Finset (Finset (Fin 8)) :=
  Finset.univ.filter fun T => T.card = 3 ∧ ∃ t : OrderedTriple8, κ t = x ∧ t.support = T

theorem mem_supportFinset_iff (κ : OrderedTriple8 → Fin 3) (x : Fin 3) (T : Finset (Fin 8)) :
    T ∈ supportFinset κ x ↔ T ∈ supportFamily κ x := by
  simp [supportFinset, supportFamily]

theorem supportFamily_cover (κ : OrderedTriple8 → Fin 3) :
    ∀ T : Finset (Fin 8), T.card = 3 → ∃ x : Fin 3, T ∈ supportFamily κ x := by
  intro T hT
  rcases OrderedTriple8.exists_support_eq T hT with ⟨t, ht⟩
  refine ⟨κ t, hT, t, rfl, ht⟩

theorem not_all_supportFamilies_intersecting (κ : OrderedTriple8 → Fin 3) :
    ¬ ∀ x : Fin 3, (supportFamily κ x).Intersecting := by
  intro hInt
  exact Kneser.not_three_intersecting_cover_triples (supportFamily κ) hInt
    (supportFamily_cover κ)

theorem supportFinset_card_le_twenty_one_of_intersecting
    (κ : OrderedTriple8 → Fin 3) (x : Fin 3)
    (hInt : (supportFamily κ x).Intersecting) :
    (supportFinset κ x).card ≤ 21 := by
  have hIntFinset : ((supportFinset κ x : Finset (Finset (Fin 8))) :
      Set (Finset (Fin 8))).Intersecting :=
    Set.Intersecting.mono (fun T hT => (mem_supportFinset_iff κ x T).mp hT) hInt
  have hSized : ((supportFinset κ x : Finset (Finset (Fin 8))) :
      Set (Finset (Fin 8))).Sized 3 := by
    intro T hT
    exact ((mem_supportFinset_iff κ x T).mp hT).1
  have hEKR := Finset.erdos_ko_rado (𝒜 := supportFinset κ x) (n := 8) (r := 3)
    hIntFinset hSized (by norm_num)
  norm_num at hEKR
  exact hEKR

theorem colorClass_support_fiber_card_le_six
    (κ : OrderedTriple8 → Fin 3) (x : Fin 3) (T : Finset (Fin 8))
    (hT : T.card = 3) :
    ((colorClass κ x).filter fun t => t.support = T).card ≤ 6 := by
  let fiber : Finset OrderedTriple8 := (colorClass κ x).filter fun t => t.support = T
  have hmapsFirst : Set.MapsTo OrderedTriple8.first fiber T := by
    intro t ht
    simp [fiber, colorClass] at ht
    rw [← ht.2]
    exact OrderedTriple8.first_mem_support t
  have hfirstFibers :
      ∀ a ∈ T, ((fiber.filter fun t => t.first = a).card) ≤ 2 := by
    intro a ha
    let fiberA : Finset OrderedTriple8 := fiber.filter fun t => t.first = a
    have hmapsSecond : Set.MapsTo OrderedTriple8.second fiberA (T.erase a) := by
      intro t ht
      simp [fiberA, fiber, colorClass] at ht ⊢
      constructor
      · rw [← ht.1.2]
        exact OrderedTriple8.second_mem_support t
      · intro hsecond_eq_a
        exact OrderedTriple8.first_ne_second t (by
          rw [ht.2, hsecond_eq_a])
    have hinjSecond : ((fiberA : Finset OrderedTriple8) : Set OrderedTriple8).InjOn
        OrderedTriple8.second := by
      intro t ht u hu hsecond
      simp [fiberA, fiber, colorClass] at ht hu
      exact OrderedTriple8.eq_of_support_eq_of_first_second_eq
        (ht.1.2.trans hu.1.2.symm)
        (ht.2.trans hu.2.symm)
        hsecond
    have hcard := Finset.card_le_card_of_injOn OrderedTriple8.second hmapsSecond hinjSecond
    have herase : (T.erase a).card = 2 := by
      rw [Finset.card_erase_of_mem ha, hT]
    change fiberA.card ≤ 2
    omega
  have hcard := Finset.card_le_mul_card_image_of_maps_to
    (f := OrderedTriple8.first) (s := fiber) (t := T) hmapsFirst 2 hfirstFibers
  change fiber.card ≤ 6
  omega

theorem colorClass_card_le_six_mul_supportFinset_card
    (κ : OrderedTriple8 → Fin 3) (x : Fin 3) :
    (colorClass κ x).card ≤ 6 * (supportFinset κ x).card := by
  have hmapsSupport : Set.MapsTo OrderedTriple8.support (colorClass κ x) (supportFinset κ x) := by
    intro t ht
    simp [colorClass] at ht
    exact (mem_supportFinset_iff κ x t.support).mpr
      ⟨OrderedTriple8.support_card t, t, ht, rfl⟩
  have hfibers :
      ∀ T ∈ supportFinset κ x,
        ((colorClass κ x).filter fun t => t.support = T).card ≤ 6 := by
    intro T hT
    exact colorClass_support_fiber_card_le_six κ x T
      ((mem_supportFinset_iff κ x T).mp hT).1
  exact Finset.card_le_mul_card_image_of_maps_to
    (f := OrderedTriple8.support) (s := colorClass κ x) (t := supportFinset κ x)
    hmapsSupport 6 hfibers

theorem colorClass_card_le_one_twenty_six_of_intersecting
    (κ : OrderedTriple8 → Fin 3) (x : Fin 3)
    (hInt : (supportFamily κ x).Intersecting) :
    (colorClass κ x).card ≤ 126 := by
  have hsupport := supportFinset_card_le_twenty_one_of_intersecting κ x hInt
  have hcolor := colorClass_card_le_six_mul_supportFinset_card κ x
  omega

theorem distinguishedEdge_ne (x : Fin 3) (t : OrderedTriple8) :
    (distinguishedEdge x t).1 ≠ (distinguishedEdge x t).2 := by
  fin_cases x <;> simp [distinguishedEdge, OrderedTriple8.first_ne_second,
    OrderedTriple8.second_ne_third, OrderedTriple8.third_ne_first]

theorem remainingVertex_ne_distinguishedEdge (x : Fin 3) (t : OrderedTriple8) :
    remainingVertex x t ≠ (distinguishedEdge x t).1 ∧
      remainingVertex x t ≠ (distinguishedEdge x t).2 := by
  fin_cases x
  · exact ⟨OrderedTriple8.third_ne_first t, (OrderedTriple8.second_ne_third t).symm⟩
  · exact ⟨(OrderedTriple8.first_ne_second t), OrderedTriple8.first_ne_third t⟩
  · exact ⟨(OrderedTriple8.second_ne_third t), (OrderedTriple8.first_ne_second t).symm⟩

theorem distinguishedEdge_remaining_injective (x : Fin 3) :
    Function.Injective fun t : OrderedTriple8 => (distinguishedEdge x t, remainingVertex x t) := by
  fin_cases x
  · intro t u h
    apply Subtype.ext
    rcases t with ⟨⟨a, b, c⟩, ht⟩
    rcases u with ⟨⟨a', b', c'⟩, hu⟩
    simp [distinguishedEdge, remainingVertex, OrderedTriple8.first,
      OrderedTriple8.second, OrderedTriple8.third] at h ⊢
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro t u h
    apply Subtype.ext
    rcases t with ⟨⟨a, b, c⟩, ht⟩
    rcases u with ⟨⟨a', b', c'⟩, hu⟩
    simp [distinguishedEdge, remainingVertex, OrderedTriple8.first,
      OrderedTriple8.second, OrderedTriple8.third] at h ⊢
    rcases h with ⟨⟨hb, hc⟩, ha⟩
    exact ⟨ha, hb, hc⟩
  · intro t u h
    apply Subtype.ext
    rcases t with ⟨⟨a, b, c⟩, ht⟩
    rcases u with ⟨⟨a', b', c'⟩, hu⟩
    simp [distinguishedEdge, remainingVertex, OrderedTriple8.first,
      OrderedTriple8.second, OrderedTriple8.third] at h ⊢
    rcases h with ⟨⟨hc, ha⟩, hb⟩
    exact ⟨ha, hb, hc⟩

theorem remainingTarget_card (e : Fin 8 × Fin 8) (hne : e.1 ≠ e.2) :
    (Finset.univ.filter fun v : Fin 8 => v ≠ e.1 ∧ v ≠ e.2).card = 6 := by
  revert e
  decide

theorem directedEdgesInside_card_le_six (S : Finset (Fin 8)) (hS : S.card = 3) :
    (directedEdgesInside S).card ≤ 6 := by
  have hmapsFirst : Set.MapsTo (fun e : Fin 8 × Fin 8 => e.1) (directedEdgesInside S) S := by
    intro e he
    rw [directedEdgesInside] at he
    exact (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1
  have hfirstFibers :
      ∀ a ∈ S, (((directedEdgesInside S).filter fun e => e.1 = a).card) ≤ 2 := by
    intro a ha
    let fiberA : Finset (Fin 8 × Fin 8) :=
      (directedEdgesInside S).filter fun e => e.1 = a
    have hmapsSecond : Set.MapsTo (fun e : Fin 8 × Fin 8 => e.2) fiberA (S.erase a) := by
      intro e he
      rcases e with ⟨p, q⟩
      change (p, q) ∈ ((directedEdgesInside S).filter fun e => e.1 = a) at he
      have hedge : (p, q) ∈ directedEdgesInside S := (Finset.mem_filter.mp he).1
      have hp_eq : p = a := (Finset.mem_filter.mp he).2
      rw [directedEdgesInside] at hedge
      have hfilter := Finset.mem_filter.mp hedge
      have hprod := Finset.mem_product.mp hfilter.1
      have hpq_ne : p ≠ q := hfilter.2
      simp
      exact ⟨hprod.2, by
        intro hqa
        exact hpq_ne (hp_eq.trans hqa.symm)⟩
    have hinjSecond : ((fiberA : Finset (Fin 8 × Fin 8)) : Set (Fin 8 × Fin 8)).InjOn
        (fun e : Fin 8 × Fin 8 => e.2) := by
      intro e he f hf hsnd
      rcases e with ⟨p, q⟩
      rcases f with ⟨p', q'⟩
      change (p, q) ∈ ((directedEdgesInside S).filter fun e => e.1 = a) at he
      change (p', q') ∈ ((directedEdgesInside S).filter fun e => e.1 = a) at hf
      have hp_eq : p = a := (Finset.mem_filter.mp he).2
      have hp'_eq : p' = a := (Finset.mem_filter.mp hf).2
      simp at hsnd ⊢
      exact ⟨hp_eq.trans hp'_eq.symm, hsnd⟩
    have hcard := Finset.card_le_card_of_injOn (fun e : Fin 8 × Fin 8 => e.2)
      hmapsSecond hinjSecond
    have herase : (S.erase a).card = 2 := by
      rw [Finset.card_erase_of_mem ha, hS]
    change fiberA.card ≤ 2
    omega
  have hcard := Finset.card_le_mul_card_image_of_maps_to
    (f := fun e : Fin 8 × Fin 8 => e.1) (s := directedEdgesInside S) (t := S)
    hmapsFirst 2 hfirstFibers
  omega

theorem internalEdges_card_le_twelve
    (T U : Finset (Fin 8)) (hT : T.card = 3) (hU : U.card = 3) :
    (internalEdges T U).card ≤ 12 := by
  have hTedges := directedEdgesInside_card_le_six T hT
  have hUedges := directedEdgesInside_card_le_six U hU
  calc
    (internalEdges T U).card ≤ (directedEdgesInside T).card + (directedEdgesInside U).card := by
      simp [internalEdges, Finset.card_union_le]
    _ ≤ 12 := by omega

theorem mem_internalEdges_ne {T U : Finset (Fin 8)} {e : Fin 8 × Fin 8}
    (he : e ∈ internalEdges T U) :
    e.1 ≠ e.2 := by
  rw [internalEdges] at he
  rcases Finset.mem_union.mp he with heT | heU
  · rw [directedEdgesInside] at heT
    exact (Finset.mem_filter.mp heT).2
  · rw [directedEdgesInside] at heU
    exact (Finset.mem_filter.mp heU).2

theorem freeVertices_card
    (T U : Finset (Fin 8)) (hT : T.card = 3) (hU : U.card = 3) (hdisj : Disjoint T U) :
    (freeVertices T U).card = 2 := by
  have hUnion : (T ∪ U).card = 6 := by
    rw [Finset.card_union_of_disjoint hdisj, hT, hU]
  have hsubset : T ∪ U ⊆ (Finset.univ : Finset (Fin 8)) := by
    intro v hv
    simp
  rw [freeVertices, Finset.card_sdiff_of_subset hsubset, Finset.card_univ, Fintype.card_fin,
    hUnion]

theorem exists_freeVertex
    (T U : Finset (Fin 8)) (hT : T.card = 3) (hU : U.card = 3) (hdisj : Disjoint T U) :
    ∃ w, w ∈ freeVertices T U := by
  have hcard := freeVertices_card T U hT hU hdisj
  have hpos : 0 < (freeVertices T U).card := by omega
  exact Finset.card_pos.mp hpos

theorem exists_freeVertex_ne
    (T U : Finset (Fin 8)) (hT : T.card = 3) (hU : U.card = 3) (hdisj : Disjoint T U)
    (y : Fin 8) :
    ∃ w, w ∈ freeVertices T U ∧ w ≠ y := by
  have hcard := freeVertices_card T U hT hU hdisj
  have hlt : 1 < (freeVertices T U).card := by omega
  exact Finset.exists_mem_ne hlt y

theorem mem_freeVertices.mp {T U : Finset (Fin 8)} {w : Fin 8}
    (hw : w ∈ freeVertices T U) : w ∉ T ∧ w ∉ U := by
  rw [freeVertices] at hw
  simp at hw
  exact hw

theorem mem_freeVertices_of_not_mem {T U : Finset (Fin 8)} {w : Fin 8}
    (hwT : w ∉ T) (hwU : w ∉ U) : w ∈ freeVertices T U := by
  rw [freeVertices]
  simp [hwT, hwU]

theorem insert_free_properties
    (T U : Finset (Fin 8)) (hT : T.card = 3) (hdisj : Disjoint T U)
    {w : Fin 8} (hwT : w ∉ T) (hwU : w ∉ U) :
    (insert w T).card = 4 ∧
      T ⊆ insert w T ∧
      (∀ v ∈ U, v ∉ insert w T) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hwT, hT]
  · exact Finset.subset_insert w T
  · intro v hvU hvA
    rw [Finset.mem_insert] at hvA
    rcases hvA with rfl | hvT
    · exact hwU hvU
    · exact (Finset.disjoint_left.mp hdisj) hvT hvU

theorem exists_four_set_separating_edge
    (T U : Finset (Fin 8)) (hT : T.card = 3) (hU : U.card = 3)
    (hdisj : Disjoint T U) (e : Fin 8 × Fin 8) (hne : e.1 ≠ e.2)
    (hnotT : ¬ insideEdge T e) (hnotU : ¬ insideEdge U e) :
    ∃ A : Finset (Fin 8),
      A.card = 4 ∧ T ⊆ A ∧ (∀ v ∈ U, v ∉ A) ∧ edgeCrosses A e := by
  have finish :
      ∀ {w : Fin 8}, w ∈ freeVertices T U → edgeCrosses (insert w T) e →
        ∃ A : Finset (Fin 8),
          A.card = 4 ∧ T ⊆ A ∧ (∀ v ∈ U, v ∉ A) ∧ edgeCrosses A e := by
    intro w hw hcross
    have hwTU := mem_freeVertices.mp hw
    rcases insert_free_properties T U hT hdisj hwTU.1 hwTU.2 with ⟨hcard, hsub, havoid⟩
    exact ⟨insert w T, hcard, hsub, havoid, hcross⟩
  by_cases he1T : e.1 ∈ T
  · have he2notT : e.2 ∉ T := by
      intro he2T
      exact hnotT ⟨he1T, he2T⟩
    rcases exists_freeVertex_ne T U hT hU hdisj e.2 with ⟨w, hw, hw_ne⟩
    exact finish hw (by
      left
      refine ⟨Finset.mem_insert_of_mem he1T, ?_⟩
      intro he2A
      rw [Finset.mem_insert] at he2A
      rcases he2A with he2w | he2T
      · exact hw_ne he2w.symm
      · exact he2notT he2T)
  · by_cases he2T : e.2 ∈ T
    · rcases exists_freeVertex_ne T U hT hU hdisj e.1 with ⟨w, hw, hw_ne⟩
      exact finish hw (by
        right
        refine ⟨?_, Finset.mem_insert_of_mem he2T⟩
        intro he1A
        rw [Finset.mem_insert] at he1A
        rcases he1A with he1w | he1T'
        · exact hw_ne he1w.symm
        · exact he1T he1T')
    · by_cases he1U : e.1 ∈ U
      · have he2notU : e.2 ∉ U := by
          intro he2U
          exact hnotU ⟨he1U, he2U⟩
        have hw : e.2 ∈ freeVertices T U :=
          mem_freeVertices_of_not_mem he2T he2notU
        exact finish hw (by
          right
          refine ⟨?_, Finset.mem_insert_self _ _⟩
          intro he1A
          rw [Finset.mem_insert] at he1A
          rcases he1A with he1eq | he1T'
          · exact hne he1eq
          · exact he1T he1T')
      · by_cases he2U : e.2 ∈ U
        · have he1notU : e.1 ∉ U := by
            intro he1U'
            exact hnotU ⟨he1U', he2U⟩
          have hw : e.1 ∈ freeVertices T U :=
            mem_freeVertices_of_not_mem he1T he1notU
          exact finish hw (by
            left
            refine ⟨Finset.mem_insert_self _ _, ?_⟩
            intro he2A
            rw [Finset.mem_insert] at he2A
            rcases he2A with he2eq | he2T'
            · exact hne he2eq.symm
            · exact he2T he2T')
        · have hw : e.1 ∈ freeVertices T U :=
            mem_freeVertices_of_not_mem he1T he1U
          exact finish hw (by
            left
            refine ⟨Finset.mem_insert_self _ _, ?_⟩
            intro he2A
            rw [Finset.mem_insert] at he2A
            rcases he2A with he2eq | he2T'
            · exact hne he2eq.symm
            · exact he2T he2T')

def hasGoodWitness (κ : OrderedTriple8 → Fin 3) : Prop :=
  ∃ x : Fin 3, ∃ A : Finset (Fin 8), ∃ tA tB t : OrderedTriple8,
    A.card = 4 ∧
      tA.support ⊆ A ∧
      (∀ v ∈ tB.support, v ∉ A) ∧
      κ tA = x ∧ κ tB = x ∧ κ t = x ∧
      edgeCrosses A (distinguishedEdge x t)

theorem colorClass_card_le_seventy_two_of_nonintersecting_witness
    (κ : OrderedTriple8 → Fin 3) (x : Fin 3) (T U : Finset (Fin 8))
    (hTmem : T ∈ supportFamily κ x) (hUmem : U ∈ supportFamily κ x)
    (hdisj : Disjoint T U) (hbad : ¬ hasGoodWitness κ) :
    (colorClass κ x).card ≤ 72 := by
  rcases hTmem with ⟨hTcard, tT, htTcolor, htTsupp⟩
  rcases hUmem with ⟨hUcard, tU, htUcolor, htUsupp⟩
  have hmapsEdge : Set.MapsTo (distinguishedEdge x) (colorClass κ x) (internalEdges T U) := by
    intro t ht
    simp [colorClass] at ht
    let e := distinguishedEdge x t
    have hne : e.1 ≠ e.2 := distinguishedEdge_ne x t
    by_cases hTin : insideEdge T e
    · have heT : e ∈ directedEdgesInside T := by
        rw [directedEdgesInside]
        exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr hTin, hne⟩
      exact Finset.mem_union_left _ heT
    · by_cases hUin : insideEdge U e
      · have heU : e ∈ directedEdgesInside U := by
          rw [directedEdgesInside]
          exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr hUin, hne⟩
        exact Finset.mem_union_right _ heU
      · exfalso
        rcases exists_four_set_separating_edge T U hTcard hUcard hdisj e hne hTin hUin with
          ⟨A, hAcard, hTsub, hUavoid, hcross⟩
        exact hbad ⟨x, A, tT, tU, t, hAcard,
          by simpa [htTsupp] using hTsub,
          by
            intro v hv
            exact hUavoid v (by simpa [htUsupp] using hv),
          htTcolor, htUcolor, ht, hcross⟩
  have hfibers :
      ∀ e ∈ internalEdges T U,
        ((colorClass κ x).filter fun t => distinguishedEdge x t = e).card ≤ 6 := by
    intro e he
    let fiberE : Finset OrderedTriple8 :=
      (colorClass κ x).filter fun t => distinguishedEdge x t = e
    let target : Finset (Fin 8) :=
      Finset.univ.filter fun v : Fin 8 => v ≠ e.1 ∧ v ≠ e.2
    have hmapsRemaining : Set.MapsTo (remainingVertex x) fiberE target := by
      intro t ht
      simp [fiberE, target, colorClass] at ht ⊢
      simpa [ht.2] using remainingVertex_ne_distinguishedEdge x t
    have hinjRemaining : ((fiberE : Finset OrderedTriple8) : Set OrderedTriple8).InjOn
        (remainingVertex x) := by
      intro t ht u hu hrem
      simp [fiberE, colorClass] at ht hu
      exact distinguishedEdge_remaining_injective x
        (Prod.ext (ht.2.trans hu.2.symm) hrem)
    have hcard := Finset.card_le_card_of_injOn (remainingVertex x) hmapsRemaining hinjRemaining
    have htarget : target.card = 6 := by
      exact remainingTarget_card e (mem_internalEdges_ne he)
    change fiberE.card ≤ 6
    omega
  have hcard := Finset.card_le_mul_card_image_of_maps_to
    (f := distinguishedEdge x) (s := colorClass κ x) (t := internalEdges T U)
    hmapsEdge 6 hfibers
  have hedgeCard := internalEdges_card_le_twelve T U hTcard hUcard
  omega

theorem exists_disjoint_of_not_intersecting
    {H : Set (Finset (Fin 8))} (hnot : ¬ H.Intersecting) :
    ∃ T, T ∈ H ∧ ∃ U, U ∈ H ∧ Disjoint T U := by
  by_contra h
  apply hnot
  intro T hT U hU hdisj
  exact h ⟨T, hT, U, hU, hdisj⟩

theorem exists_nonintersecting_supportFamily (κ : OrderedTriple8 → Fin 3) :
    ∃ x : Fin 3, ∃ T U : Finset (Fin 8),
      T ∈ supportFamily κ x ∧ U ∈ supportFamily κ x ∧ Disjoint T U := by
  by_contra h
  apply not_all_supportFamilies_intersecting κ
  intro x T hT U hU hdisj
  exact h ⟨x, T, U, hT, hU, hdisj⟩

theorem colorClass_card_sum (κ : OrderedTriple8 → Fin 3) :
    (colorClass κ 0).card + (colorClass κ 1).card + (colorClass κ 2).card = 336 := by
  have hdisj01 : Disjoint (colorClass κ 0) (colorClass κ 1) := by
    rw [Finset.disjoint_left]
    intro t ht0 ht1
    simp [colorClass] at ht0 ht1
    omega
  have hdisj012 : Disjoint (colorClass κ 0 ∪ colorClass κ 1) (colorClass κ 2) := by
    rw [Finset.disjoint_left]
    intro t ht h2
    simp [colorClass] at ht h2
    rcases ht with h0 | h1 <;> omega
  have hcover : colorClass κ 0 ∪ colorClass κ 1 ∪ colorClass κ 2 =
      (Finset.univ : Finset OrderedTriple8) := by
    ext t
    simp [colorClass]
    exact (by decide : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2) (κ t)
  calc
    (colorClass κ 0).card + (colorClass κ 1).card + (colorClass κ 2).card
        = (colorClass κ 0 ∪ colorClass κ 1).card + (colorClass κ 2).card := by
          rw [Finset.card_union_of_disjoint hdisj01]
    _ = ((colorClass κ 0 ∪ colorClass κ 1) ∪ colorClass κ 2).card := by
          rw [Finset.card_union_of_disjoint hdisj012]
    _ = (Finset.univ : Finset OrderedTriple8).card := by
          rw [hcover]
    _ = 336 := by
          rw [Finset.card_univ, OrderedTriple8.card]

theorem identity_selection (κ : OrderedTriple8 → Fin 3) :
    hasGoodWitness κ := by
  by_contra hbad
  rcases exists_nonintersecting_supportFamily κ with ⟨x, T, U, hT, hU, hdisj⟩
  have hx72 := colorClass_card_le_seventy_two_of_nonintersecting_witness
    κ x T U hT hU hdisj hbad
  have hBound126 : ∀ y : Fin 3, (colorClass κ y).card ≤ 126 := by
    intro y
    by_cases hInt : (supportFamily κ y).Intersecting
    · exact colorClass_card_le_one_twenty_six_of_intersecting κ y hInt
    · rcases exists_disjoint_of_not_intersecting hInt with ⟨T', hT', U', hU', hdisj'⟩
      have h72 := colorClass_card_le_seventy_two_of_nonintersecting_witness
        κ y T' U' hT' hU' hdisj' hbad
      omega
  have h0 := hBound126 0
  have h1 := hBound126 1
  have h2 := hBound126 2
  have hsum := colorClass_card_sum κ
  fin_cases x
  · change (colorClass κ (0 : Fin 3)).card ≤ 72 at hx72
    omega
  · change (colorClass κ (1 : Fin 3)).card ≤ 72 at hx72
    omega
  · change (colorClass κ (2 : Fin 3)).card ≤ 72 at hx72
    omega

end IdentitySelection
end CondorcetReinforcementN8
end SocialChoice
