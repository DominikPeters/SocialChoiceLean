/-
Finite certificate for the Schrijver subgraph SG(8,3).

Vertices are the 16 stable 3-subsets of an 8-cycle, encoded by indices
0..15 in the order used in CondorcetReinforcementN8 feasibility notes. The proof below
checks a small bitmask certificate and derives the Kneser step needed for n=8:
three intersecting families of triples on an 8-set cannot cover all triples.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Combinatorics.SetFamily.Intersecting
import Batteries.Data.Nat.Lemmas
import Mathlib.Tactic

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unnecessarySimpa false

namespace SocialChoice
namespace CondorcetReinforcementN8
namespace Kneser

open Nat

/-- The 16 stable 3-subsets of an 8-cycle, in the vertex order used by the bitmask certificate. -/
def stableTriple : Fin 16 → Finset (Fin 8)
  | 0 => {0, 2, 4}
  | 1 => {0, 2, 5}
  | 2 => {0, 2, 6}
  | 3 => {0, 3, 5}
  | 4 => {0, 3, 6}
  | 5 => {0, 4, 6}
  | 6 => {1, 3, 5}
  | 7 => {1, 3, 6}
  | 8 => {1, 3, 7}
  | 9 => {1, 4, 6}
  | 10 => {1, 4, 7}
  | 11 => {1, 5, 7}
  | 12 => {2, 4, 6}
  | 13 => {2, 4, 7}
  | 14 => {2, 5, 7}
  | 15 => {3, 5, 7}
  | _ => ∅

/-- Boolean edge table for disjointness among the 16 stable triples. -/
def adjFast (i j : Fin 16) : Bool :=
  match i.val, j.val with
  | 0, 6 => true | 6, 0 => true
  | 0, 7 => true | 7, 0 => true
  | 0, 8 => true | 8, 0 => true
  | 0, 11 => true | 11, 0 => true
  | 0, 15 => true | 15, 0 => true
  | 1, 7 => true | 7, 1 => true
  | 1, 8 => true | 8, 1 => true
  | 1, 9 => true | 9, 1 => true
  | 1, 10 => true | 10, 1 => true
  | 2, 6 => true | 6, 2 => true
  | 2, 8 => true | 8, 2 => true
  | 2, 10 => true | 10, 2 => true
  | 2, 11 => true | 11, 2 => true
  | 2, 15 => true | 15, 2 => true
  | 3, 9 => true | 9, 3 => true
  | 3, 10 => true | 10, 3 => true
  | 3, 12 => true | 12, 3 => true
  | 3, 13 => true | 13, 3 => true
  | 4, 10 => true | 10, 4 => true
  | 4, 11 => true | 11, 4 => true
  | 4, 13 => true | 13, 4 => true
  | 4, 14 => true | 14, 4 => true
  | 5, 6 => true | 6, 5 => true
  | 5, 8 => true | 8, 5 => true
  | 5, 11 => true | 11, 5 => true
  | 5, 14 => true | 14, 5 => true
  | 5, 15 => true | 15, 5 => true
  | 6, 12 => true | 12, 6 => true
  | 6, 13 => true | 13, 6 => true
  | 7, 13 => true | 13, 7 => true
  | 7, 14 => true | 14, 7 => true
  | 8, 12 => true | 12, 8 => true
  | 9, 14 => true | 14, 9 => true
  | 9, 15 => true | 15, 9 => true
  | 11, 12 => true | 12, 11 => true
  | 12, 15 => true | 15, 12 => true
  | _, _ => false

theorem stableTriple_card (i : Fin 16) : (stableTriple i).card = 3 := by
  fin_cases i <;> decide

theorem adjFast_iff_disjoint (i j : Fin 16) :
    adjFast i j = true ↔ Disjoint (stableTriple i) (stableTriple j) := by
  fin_cases i <;> fin_cases j <;> decide

/-- Boolean test that the concrete edge `(i,j)` is absent inside a vertex set. -/
def noEdgeInSet (s : Finset (Fin 16)) (i j : Fin 16) : Bool :=
  !((i ∈ s) && (j ∈ s))

/-- Boolean independence test for vertex sets in the 16-vertex graph. -/
def independentSetFast (s : Finset (Fin 16)) : Bool :=
  noEdgeInSet s 0 6 &&
  noEdgeInSet s 0 7 &&
  noEdgeInSet s 0 8 &&
  noEdgeInSet s 0 11 &&
  noEdgeInSet s 0 15 &&
  noEdgeInSet s 1 7 &&
  noEdgeInSet s 1 8 &&
  noEdgeInSet s 1 9 &&
  noEdgeInSet s 1 10 &&
  noEdgeInSet s 2 6 &&
  noEdgeInSet s 2 8 &&
  noEdgeInSet s 2 10 &&
  noEdgeInSet s 2 11 &&
  noEdgeInSet s 2 15 &&
  noEdgeInSet s 3 9 &&
  noEdgeInSet s 3 10 &&
  noEdgeInSet s 3 12 &&
  noEdgeInSet s 3 13 &&
  noEdgeInSet s 4 10 &&
  noEdgeInSet s 4 11 &&
  noEdgeInSet s 4 13 &&
  noEdgeInSet s 4 14 &&
  noEdgeInSet s 5 6 &&
  noEdgeInSet s 5 8 &&
  noEdgeInSet s 5 11 &&
  noEdgeInSet s 5 14 &&
  noEdgeInSet s 5 15 &&
  noEdgeInSet s 6 12 &&
  noEdgeInSet s 6 13 &&
  noEdgeInSet s 7 13 &&
  noEdgeInSet s 7 14 &&
  noEdgeInSet s 8 12 &&
  noEdgeInSet s 9 14 &&
  noEdgeInSet s 9 15 &&
  noEdgeInSet s 11 12 &&
  noEdgeInSet s 12 15

/-- Boolean independence test for the 16-vertex stable Kneser subgraph. -/
def indepFast (m : Nat) : Bool :=
  (!((m.testBit 0) && (m.testBit 6))) &&
  (!((m.testBit 0) && (m.testBit 7))) &&
  (!((m.testBit 0) && (m.testBit 8))) &&
  (!((m.testBit 0) && (m.testBit 11))) &&
  (!((m.testBit 0) && (m.testBit 15))) &&
  (!((m.testBit 1) && (m.testBit 7))) &&
  (!((m.testBit 1) && (m.testBit 8))) &&
  (!((m.testBit 1) && (m.testBit 9))) &&
  (!((m.testBit 1) && (m.testBit 10))) &&
  (!((m.testBit 2) && (m.testBit 6))) &&
  (!((m.testBit 2) && (m.testBit 8))) &&
  (!((m.testBit 2) && (m.testBit 10))) &&
  (!((m.testBit 2) && (m.testBit 11))) &&
  (!((m.testBit 2) && (m.testBit 15))) &&
  (!((m.testBit 3) && (m.testBit 9))) &&
  (!((m.testBit 3) && (m.testBit 10))) &&
  (!((m.testBit 3) && (m.testBit 12))) &&
  (!((m.testBit 3) && (m.testBit 13))) &&
  (!((m.testBit 4) && (m.testBit 10))) &&
  (!((m.testBit 4) && (m.testBit 11))) &&
  (!((m.testBit 4) && (m.testBit 13))) &&
  (!((m.testBit 4) && (m.testBit 14))) &&
  (!((m.testBit 5) && (m.testBit 6))) &&
  (!((m.testBit 5) && (m.testBit 8))) &&
  (!((m.testBit 5) && (m.testBit 11))) &&
  (!((m.testBit 5) && (m.testBit 14))) &&
  (!((m.testBit 5) && (m.testBit 15))) &&
  (!((m.testBit 6) && (m.testBit 12))) &&
  (!((m.testBit 6) && (m.testBit 13))) &&
  (!((m.testBit 7) && (m.testBit 13))) &&
  (!((m.testBit 7) && (m.testBit 14))) &&
  (!((m.testBit 8) && (m.testBit 12))) &&
  (!((m.testBit 9) && (m.testBit 14))) &&
  (!((m.testBit 9) && (m.testBit 15))) &&
  (!((m.testBit 11) && (m.testBit 12))) &&
  (!((m.testBit 12) && (m.testBit 15)))

/-- The 16 maximum independent 6-sets, encoded as bitmasks. -/
def certFast (m : Nat) : Bool := m = 63 || m = 4151 || m = 12327 || m = 28679 || m = 4661 || m = 12837 || m = 13857 || m = 51274 || m = 4788 || m = 33240 || m = 35272 || m = 51528 || m = 4032 || m = 36288 || m = 52544 || m = 60672

/-- Cardinality of the first 16 bits of a bitmask. -/
def maskCard16 (m : Nat) : Nat :=
  (if m.testBit 0 then 1 else 0) +
  (if m.testBit 1 then 1 else 0) +
  (if m.testBit 2 then 1 else 0) +
  (if m.testBit 3 then 1 else 0) +
  (if m.testBit 4 then 1 else 0) +
  (if m.testBit 5 then 1 else 0) +
  (if m.testBit 6 then 1 else 0) +
  (if m.testBit 7 then 1 else 0) +
  (if m.testBit 8 then 1 else 0) +
  (if m.testBit 9 then 1 else 0) +
  (if m.testBit 10 then 1 else 0) +
  (if m.testBit 11 then 1 else 0) +
  (if m.testBit 12 then 1 else 0) +
  (if m.testBit 13 then 1 else 0) +
  (if m.testBit 14 then 1 else 0) +
  (if m.testBit 15 then 1 else 0)

theorem indepFast_large_chunk0 :
    ∀ k : Fin 2048,
      indepFast (0 + k.val) = true →
      (¬ 7 ≤ maskCard16 (0 + k.val)) ∧
        (maskCard16 (0 + k.val) = 6 →
          certFast (0 + k.val) = true) := by
  decide

theorem indepFast_large_chunk1 :
    ∀ k : Fin 2048,
      indepFast (2048 + k.val) = true →
      (¬ 7 ≤ maskCard16 (2048 + k.val)) ∧
        (maskCard16 (2048 + k.val) = 6 →
          certFast (2048 + k.val) = true) := by
  decide

theorem indepFast_large_chunk2 :
    ∀ k : Fin 2048,
      indepFast (4096 + k.val) = true →
      (¬ 7 ≤ maskCard16 (4096 + k.val)) ∧
        (maskCard16 (4096 + k.val) = 6 →
          certFast (4096 + k.val) = true) := by
  decide

theorem indepFast_large_chunk3 :
    ∀ k : Fin 2048,
      indepFast (6144 + k.val) = true →
      (¬ 7 ≤ maskCard16 (6144 + k.val)) ∧
        (maskCard16 (6144 + k.val) = 6 →
          certFast (6144 + k.val) = true) := by
  decide

theorem indepFast_large_chunk4 :
    ∀ k : Fin 2048,
      indepFast (8192 + k.val) = true →
      (¬ 7 ≤ maskCard16 (8192 + k.val)) ∧
        (maskCard16 (8192 + k.val) = 6 →
          certFast (8192 + k.val) = true) := by
  decide

theorem indepFast_large_chunk5 :
    ∀ k : Fin 2048,
      indepFast (10240 + k.val) = true →
      (¬ 7 ≤ maskCard16 (10240 + k.val)) ∧
        (maskCard16 (10240 + k.val) = 6 →
          certFast (10240 + k.val) = true) := by
  decide

theorem indepFast_large_chunk6 :
    ∀ k : Fin 2048,
      indepFast (12288 + k.val) = true →
      (¬ 7 ≤ maskCard16 (12288 + k.val)) ∧
        (maskCard16 (12288 + k.val) = 6 →
          certFast (12288 + k.val) = true) := by
  decide

theorem indepFast_large_chunk7 :
    ∀ k : Fin 2048,
      indepFast (14336 + k.val) = true →
      (¬ 7 ≤ maskCard16 (14336 + k.val)) ∧
        (maskCard16 (14336 + k.val) = 6 →
          certFast (14336 + k.val) = true) := by
  decide

theorem indepFast_large_chunk8 :
    ∀ k : Fin 2048,
      indepFast (16384 + k.val) = true →
      (¬ 7 ≤ maskCard16 (16384 + k.val)) ∧
        (maskCard16 (16384 + k.val) = 6 →
          certFast (16384 + k.val) = true) := by
  decide

theorem indepFast_large_chunk9 :
    ∀ k : Fin 2048,
      indepFast (18432 + k.val) = true →
      (¬ 7 ≤ maskCard16 (18432 + k.val)) ∧
        (maskCard16 (18432 + k.val) = 6 →
          certFast (18432 + k.val) = true) := by
  decide

theorem indepFast_large_chunk10 :
    ∀ k : Fin 2048,
      indepFast (20480 + k.val) = true →
      (¬ 7 ≤ maskCard16 (20480 + k.val)) ∧
        (maskCard16 (20480 + k.val) = 6 →
          certFast (20480 + k.val) = true) := by
  decide

theorem indepFast_large_chunk11 :
    ∀ k : Fin 2048,
      indepFast (22528 + k.val) = true →
      (¬ 7 ≤ maskCard16 (22528 + k.val)) ∧
        (maskCard16 (22528 + k.val) = 6 →
          certFast (22528 + k.val) = true) := by
  decide

theorem indepFast_large_chunk12 :
    ∀ k : Fin 2048,
      indepFast (24576 + k.val) = true →
      (¬ 7 ≤ maskCard16 (24576 + k.val)) ∧
        (maskCard16 (24576 + k.val) = 6 →
          certFast (24576 + k.val) = true) := by
  decide

theorem indepFast_large_chunk13 :
    ∀ k : Fin 2048,
      indepFast (26624 + k.val) = true →
      (¬ 7 ≤ maskCard16 (26624 + k.val)) ∧
        (maskCard16 (26624 + k.val) = 6 →
          certFast (26624 + k.val) = true) := by
  decide

theorem indepFast_large_chunk14 :
    ∀ k : Fin 2048,
      indepFast (28672 + k.val) = true →
      (¬ 7 ≤ maskCard16 (28672 + k.val)) ∧
        (maskCard16 (28672 + k.val) = 6 →
          certFast (28672 + k.val) = true) := by
  decide

theorem indepFast_large_chunk15 :
    ∀ k : Fin 2048,
      indepFast (30720 + k.val) = true →
      (¬ 7 ≤ maskCard16 (30720 + k.val)) ∧
        (maskCard16 (30720 + k.val) = 6 →
          certFast (30720 + k.val) = true) := by
  decide

theorem indepFast_large_chunk16 :
    ∀ k : Fin 2048,
      indepFast (32768 + k.val) = true →
      (¬ 7 ≤ maskCard16 (32768 + k.val)) ∧
        (maskCard16 (32768 + k.val) = 6 →
          certFast (32768 + k.val) = true) := by
  decide

theorem indepFast_large_chunk17 :
    ∀ k : Fin 2048,
      indepFast (34816 + k.val) = true →
      (¬ 7 ≤ maskCard16 (34816 + k.val)) ∧
        (maskCard16 (34816 + k.val) = 6 →
          certFast (34816 + k.val) = true) := by
  decide

theorem indepFast_large_chunk18 :
    ∀ k : Fin 2048,
      indepFast (36864 + k.val) = true →
      (¬ 7 ≤ maskCard16 (36864 + k.val)) ∧
        (maskCard16 (36864 + k.val) = 6 →
          certFast (36864 + k.val) = true) := by
  decide

theorem indepFast_large_chunk19 :
    ∀ k : Fin 2048,
      indepFast (38912 + k.val) = true →
      (¬ 7 ≤ maskCard16 (38912 + k.val)) ∧
        (maskCard16 (38912 + k.val) = 6 →
          certFast (38912 + k.val) = true) := by
  decide

theorem indepFast_large_chunk20 :
    ∀ k : Fin 2048,
      indepFast (40960 + k.val) = true →
      (¬ 7 ≤ maskCard16 (40960 + k.val)) ∧
        (maskCard16 (40960 + k.val) = 6 →
          certFast (40960 + k.val) = true) := by
  decide

theorem indepFast_large_chunk21 :
    ∀ k : Fin 2048,
      indepFast (43008 + k.val) = true →
      (¬ 7 ≤ maskCard16 (43008 + k.val)) ∧
        (maskCard16 (43008 + k.val) = 6 →
          certFast (43008 + k.val) = true) := by
  decide

theorem indepFast_large_chunk22 :
    ∀ k : Fin 2048,
      indepFast (45056 + k.val) = true →
      (¬ 7 ≤ maskCard16 (45056 + k.val)) ∧
        (maskCard16 (45056 + k.val) = 6 →
          certFast (45056 + k.val) = true) := by
  decide

theorem indepFast_large_chunk23 :
    ∀ k : Fin 2048,
      indepFast (47104 + k.val) = true →
      (¬ 7 ≤ maskCard16 (47104 + k.val)) ∧
        (maskCard16 (47104 + k.val) = 6 →
          certFast (47104 + k.val) = true) := by
  decide

theorem indepFast_large_chunk24 :
    ∀ k : Fin 2048,
      indepFast (49152 + k.val) = true →
      (¬ 7 ≤ maskCard16 (49152 + k.val)) ∧
        (maskCard16 (49152 + k.val) = 6 →
          certFast (49152 + k.val) = true) := by
  decide

theorem indepFast_large_chunk25 :
    ∀ k : Fin 2048,
      indepFast (51200 + k.val) = true →
      (¬ 7 ≤ maskCard16 (51200 + k.val)) ∧
        (maskCard16 (51200 + k.val) = 6 →
          certFast (51200 + k.val) = true) := by
  decide

theorem indepFast_large_chunk26 :
    ∀ k : Fin 2048,
      indepFast (53248 + k.val) = true →
      (¬ 7 ≤ maskCard16 (53248 + k.val)) ∧
        (maskCard16 (53248 + k.val) = 6 →
          certFast (53248 + k.val) = true) := by
  decide

theorem indepFast_large_chunk27 :
    ∀ k : Fin 2048,
      indepFast (55296 + k.val) = true →
      (¬ 7 ≤ maskCard16 (55296 + k.val)) ∧
        (maskCard16 (55296 + k.val) = 6 →
          certFast (55296 + k.val) = true) := by
  decide

theorem indepFast_large_chunk28 :
    ∀ k : Fin 2048,
      indepFast (57344 + k.val) = true →
      (¬ 7 ≤ maskCard16 (57344 + k.val)) ∧
        (maskCard16 (57344 + k.val) = 6 →
          certFast (57344 + k.val) = true) := by
  decide

theorem indepFast_large_chunk29 :
    ∀ k : Fin 2048,
      indepFast (59392 + k.val) = true →
      (¬ 7 ≤ maskCard16 (59392 + k.val)) ∧
        (maskCard16 (59392 + k.val) = 6 →
          certFast (59392 + k.val) = true) := by
  decide

theorem indepFast_large_chunk30 :
    ∀ k : Fin 2048,
      indepFast (61440 + k.val) = true →
      (¬ 7 ≤ maskCard16 (61440 + k.val)) ∧
        (maskCard16 (61440 + k.val) = 6 →
          certFast (61440 + k.val) = true) := by
  decide

theorem indepFast_large_chunk31 :
    ∀ k : Fin 2048,
      indepFast (63488 + k.val) = true →
      (¬ 7 ≤ maskCard16 (63488 + k.val)) ∧
        (maskCard16 (63488 + k.val) = 6 →
          certFast (63488 + k.val) = true) := by
  decide

theorem indepFast_large {m : Nat} (hm : m < 65536) (hind : indepFast m = true) :
    (¬ 7 ≤ maskCard16 m) ∧
      (maskCard16 m = 6 → certFast m = true) := by
  let q : Fin 32 := ⟨m / 2048, by omega⟩
  let r : Fin 2048 := ⟨m % 2048, Nat.mod_lt _ (by decide)⟩
  have hmqr : m = q.val * 2048 + r.val := by
    dsimp [q, r]
    omega
  have hq : q.val < 32 := q.isLt
  interval_cases q.val
  · have hm0 : m = 0 + r.val := by omega
    rw [hm0] at hind ⊢
    exact indepFast_large_chunk0 r hind
  · have hm1 : m = 2048 + r.val := by omega
    rw [hm1] at hind ⊢
    exact indepFast_large_chunk1 r hind
  · have hm2 : m = 4096 + r.val := by omega
    rw [hm2] at hind ⊢
    exact indepFast_large_chunk2 r hind
  · have hm3 : m = 6144 + r.val := by omega
    rw [hm3] at hind ⊢
    exact indepFast_large_chunk3 r hind
  · have hm4 : m = 8192 + r.val := by omega
    rw [hm4] at hind ⊢
    exact indepFast_large_chunk4 r hind
  · have hm5 : m = 10240 + r.val := by omega
    rw [hm5] at hind ⊢
    exact indepFast_large_chunk5 r hind
  · have hm6 : m = 12288 + r.val := by omega
    rw [hm6] at hind ⊢
    exact indepFast_large_chunk6 r hind
  · have hm7 : m = 14336 + r.val := by omega
    rw [hm7] at hind ⊢
    exact indepFast_large_chunk7 r hind
  · have hm8 : m = 16384 + r.val := by omega
    rw [hm8] at hind ⊢
    exact indepFast_large_chunk8 r hind
  · have hm9 : m = 18432 + r.val := by omega
    rw [hm9] at hind ⊢
    exact indepFast_large_chunk9 r hind
  · have hm10 : m = 20480 + r.val := by omega
    rw [hm10] at hind ⊢
    exact indepFast_large_chunk10 r hind
  · have hm11 : m = 22528 + r.val := by omega
    rw [hm11] at hind ⊢
    exact indepFast_large_chunk11 r hind
  · have hm12 : m = 24576 + r.val := by omega
    rw [hm12] at hind ⊢
    exact indepFast_large_chunk12 r hind
  · have hm13 : m = 26624 + r.val := by omega
    rw [hm13] at hind ⊢
    exact indepFast_large_chunk13 r hind
  · have hm14 : m = 28672 + r.val := by omega
    rw [hm14] at hind ⊢
    exact indepFast_large_chunk14 r hind
  · have hm15 : m = 30720 + r.val := by omega
    rw [hm15] at hind ⊢
    exact indepFast_large_chunk15 r hind
  · have hm16 : m = 32768 + r.val := by omega
    rw [hm16] at hind ⊢
    exact indepFast_large_chunk16 r hind
  · have hm17 : m = 34816 + r.val := by omega
    rw [hm17] at hind ⊢
    exact indepFast_large_chunk17 r hind
  · have hm18 : m = 36864 + r.val := by omega
    rw [hm18] at hind ⊢
    exact indepFast_large_chunk18 r hind
  · have hm19 : m = 38912 + r.val := by omega
    rw [hm19] at hind ⊢
    exact indepFast_large_chunk19 r hind
  · have hm20 : m = 40960 + r.val := by omega
    rw [hm20] at hind ⊢
    exact indepFast_large_chunk20 r hind
  · have hm21 : m = 43008 + r.val := by omega
    rw [hm21] at hind ⊢
    exact indepFast_large_chunk21 r hind
  · have hm22 : m = 45056 + r.val := by omega
    rw [hm22] at hind ⊢
    exact indepFast_large_chunk22 r hind
  · have hm23 : m = 47104 + r.val := by omega
    rw [hm23] at hind ⊢
    exact indepFast_large_chunk23 r hind
  · have hm24 : m = 49152 + r.val := by omega
    rw [hm24] at hind ⊢
    exact indepFast_large_chunk24 r hind
  · have hm25 : m = 51200 + r.val := by omega
    rw [hm25] at hind ⊢
    exact indepFast_large_chunk25 r hind
  · have hm26 : m = 53248 + r.val := by omega
    rw [hm26] at hind ⊢
    exact indepFast_large_chunk26 r hind
  · have hm27 : m = 55296 + r.val := by omega
    rw [hm27] at hind ⊢
    exact indepFast_large_chunk27 r hind
  · have hm28 : m = 57344 + r.val := by omega
    rw [hm28] at hind ⊢
    exact indepFast_large_chunk28 r hind
  · have hm29 : m = 59392 + r.val := by omega
    rw [hm29] at hind ⊢
    exact indepFast_large_chunk29 r hind
  · have hm30 : m = 61440 + r.val := by omega
    rw [hm30] at hind ⊢
    exact indepFast_large_chunk30 r hind
  · have hm31 : m = 63488 + r.val := by omega
    rw [hm31] at hind ⊢
    exact indepFast_large_chunk31 r hind

/-- The 16 maximum independent 6-sets as an indexed certificate list. -/
def certMask : Fin 16 → Nat
  | 0 => 63
  | 1 => 4151
  | 2 => 12327
  | 3 => 28679
  | 4 => 4661
  | 5 => 12837
  | 6 => 13857
  | 7 => 51274
  | 8 => 4788
  | 9 => 33240
  | 10 => 35272
  | 11 => 51528
  | 12 => 4032
  | 13 => 36288
  | 14 => 52544
  | 15 => 60672
  | _ => 0

theorem certFast_eq_certMask {m : Nat} (h : certFast m = true) :
    ∃ c : Fin 16, m = certMask c := by
  by_cases h0 : m = 63
  · exact ⟨0, by simpa [certMask] using h0⟩
  by_cases h1 : m = 4151
  · exact ⟨1, by simpa [certMask] using h1⟩
  by_cases h2 : m = 12327
  · exact ⟨2, by simpa [certMask] using h2⟩
  by_cases h3 : m = 28679
  · exact ⟨3, by simpa [certMask] using h3⟩
  by_cases h4 : m = 4661
  · exact ⟨4, by simpa [certMask] using h4⟩
  by_cases h5 : m = 12837
  · exact ⟨5, by simpa [certMask] using h5⟩
  by_cases h6 : m = 13857
  · exact ⟨6, by simpa [certMask] using h6⟩
  by_cases h7 : m = 51274
  · exact ⟨7, by simpa [certMask] using h7⟩
  by_cases h8 : m = 4788
  · exact ⟨8, by simpa [certMask] using h8⟩
  by_cases h9 : m = 33240
  · exact ⟨9, by simpa [certMask] using h9⟩
  by_cases h10 : m = 35272
  · exact ⟨10, by simpa [certMask] using h10⟩
  by_cases h11 : m = 51528
  · exact ⟨11, by simpa [certMask] using h11⟩
  by_cases h12 : m = 4032
  · exact ⟨12, by simpa [certMask] using h12⟩
  by_cases h13 : m = 36288
  · exact ⟨13, by simpa [certMask] using h13⟩
  by_cases h14 : m = 52544
  · exact ⟨14, by simpa [certMask] using h14⟩
  by_cases h15 : m = 60672
  · exact ⟨15, by simpa [certMask] using h15⟩
  simp [certFast, h0, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10, h11, h12, h13, h14, h15] at h

/-- Boolean test that vertex `i` has an edge to some vertex contained in bitmask `m`. -/
def hitsFast (m : Nat) (i : Fin 16) : Bool :=
  ((m.testBit 0) && adjFast i 0) ||
  ((m.testBit 1) && adjFast i 1) ||
  ((m.testBit 2) && adjFast i 2) ||
  ((m.testBit 3) && adjFast i 3) ||
  ((m.testBit 4) && adjFast i 4) ||
  ((m.testBit 5) && adjFast i 5) ||
  ((m.testBit 6) && adjFast i 6) ||
  ((m.testBit 7) && adjFast i 7) ||
  ((m.testBit 8) && adjFast i 8) ||
  ((m.testBit 9) && adjFast i 9) ||
  ((m.testBit 10) && adjFast i 10) ||
  ((m.testBit 11) && adjFast i 11) ||
  ((m.testBit 12) && adjFast i 12) ||
  ((m.testBit 13) && adjFast i 13) ||
  ((m.testBit 14) && adjFast i 14) ||
  ((m.testBit 15) && adjFast i 15)

theorem certMask_maximal (c i : Fin 16) :
    (certMask c).testBit i.val = false → hitsFast (certMask c) i = true := by
  fin_cases c <;> fin_cases i <;> decide


/-- An explicit odd cycle in the complement of each certified maximum independent set. -/
def oddCycleWitness : Fin 16 → List (Fin 16)
  | 0 => [6, 12, 15, 9, 14, 7, 13]
  | 1 => [3, 9, 14, 7, 13]
  | 2 => [3, 9, 14, 4, 10]
  | 3 => [3, 9, 15, 5, 11, 4, 10]
  | 4 => [1, 7, 13, 3, 10]
  | 5 => [1, 7, 14, 4, 10]
  | 6 => [1, 7, 14, 4, 11, 2, 8]
  | 7 => [0, 7, 13, 4, 10, 2, 8]
  | 8 => [0, 6, 13, 3, 10, 1, 8]
  | 9 => [1, 9, 14, 5, 11, 2, 10]
  | 10 => [1, 9, 14, 4, 10]
  | 11 => [1, 7, 13, 4, 10]
  | 12 => [3, 12, 15, 5, 14, 4, 13]
  | 13 => [3, 9, 14, 4, 13]
  | 14 => [1, 7, 13, 3, 9]
  | 15 => [0, 6, 12, 3, 9, 1, 7]
  | _ => []

private def witnessInComplement (c : Fin 16) : Bool :=
  (oddCycleWitness c).all (fun i => !((certMask c).testBit i.val))

private def witnessPathEdges : List (Fin 16) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => adjFast a b && witnessPathEdges (b :: rest)

private def witnessCloses (l : List (Fin 16)) : Bool :=
  match l with
  | [] => false
  | a :: rest =>
      match rest.getLast? with
      | none => false
      | some z => adjFast z a

private def witnessCycleEdges (c : Fin 16) : Bool :=
  witnessPathEdges (oddCycleWitness c) && witnessCloses (oddCycleWitness c)

theorem oddCycleWitness_odd (c : Fin 16) : (oddCycleWitness c).length % 2 = 1 := by
  fin_cases c <;> decide

theorem oddCycleWitness_inComplement (c : Fin 16) : witnessInComplement c = true := by
  fin_cases c <;> decide

theorem oddCycleWitness_edges (c : Fin 16) : witnessCycleEdges c = true := by
  fin_cases c <;> decide

theorem no_two_color_cycle5 (main x0 x1 x2 x3 x4 : Fin 3)
    (h0 : x0 ≠ main) (h1 : x1 ≠ main) (h2 : x2 ≠ main)
    (h3 : x3 ≠ main) (h4 : x4 ≠ main)
    (h01 : x0 ≠ x1) (h12 : x1 ≠ x2) (h23 : x2 ≠ x3)
    (h34 : x3 ≠ x4) (h40 : x4 ≠ x0) : False := by
  fin_cases main <;> fin_cases x0 <;> fin_cases x1 <;>
    fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;> simp at *

theorem no_two_color_cycle7 (main x0 x1 x2 x3 x4 x5 x6 : Fin 3)
    (h0 : x0 ≠ main) (h1 : x1 ≠ main) (h2 : x2 ≠ main)
    (h3 : x3 ≠ main) (h4 : x4 ≠ main) (h5 : x5 ≠ main)
    (h6 : x6 ≠ main)
    (h01 : x0 ≠ x1) (h12 : x1 ≠ x2) (h23 : x2 ≠ x3)
    (h34 : x3 ≠ x4) (h45 : x4 ≠ x5) (h56 : x5 ≠ x6)
    (h60 : x6 ≠ x0) : False := by
  fin_cases main <;> fin_cases x0 <;> fin_cases x1 <;>
    fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;>
    fin_cases x5 <;> fin_cases x6 <;> simp at *

/-- Bitmask of a color class in a coloring of the 16-vertex graph. -/
def colorMask (χ : Fin 16 → Fin 3) (c : Fin 3) : Nat :=
  Nat.ofBits (fun i : Fin 16 => decide (χ i = c))

def colorCount (χ : Fin 16 → Fin 3) (c : Fin 3) : Nat :=
  (if χ 0 = c then 1 else 0) +
  (if χ 1 = c then 1 else 0) +
  (if χ 2 = c then 1 else 0) +
  (if χ 3 = c then 1 else 0) +
  (if χ 4 = c then 1 else 0) +
  (if χ 5 = c then 1 else 0) +
  (if χ 6 = c then 1 else 0) +
  (if χ 7 = c then 1 else 0) +
  (if χ 8 = c then 1 else 0) +
  (if χ 9 = c then 1 else 0) +
  (if χ 10 = c then 1 else 0) +
  (if χ 11 = c then 1 else 0) +
  (if χ 12 = c then 1 else 0) +
  (if χ 13 = c then 1 else 0) +
  (if χ 14 = c then 1 else 0) +
  (if χ 15 = c then 1 else 0)

theorem colorMask_testBit (χ : Fin 16 → Fin 3) (c : Fin 3) (i : Fin 16) :
    (colorMask χ c).testBit i.val = decide (χ i = c) := by
  simp [colorMask]

theorem colorMask_lt (χ : Fin 16 → Fin 3) (c : Fin 3) : colorMask χ c < 65536 := by
  simpa [colorMask] using Nat.ofBits_lt_two_pow (fun i : Fin 16 => decide (χ i = c))

lemma colorIndicator_sum (x : Fin 3) :
    (if x = 0 then 1 else 0) +
    (if x = 1 then 1 else 0) +
    (if x = 2 then 1 else 0) = 1 := by
  fin_cases x <;> decide

theorem colorCount_sum (χ : Fin 16 → Fin 3) :
    colorCount χ 0 + colorCount χ 1 + colorCount χ 2 = 16 := by
  have h0 := colorIndicator_sum (χ 0)
  have h1 := colorIndicator_sum (χ 1)
  have h2 := colorIndicator_sum (χ 2)
  have h3 := colorIndicator_sum (χ 3)
  have h4 := colorIndicator_sum (χ 4)
  have h5 := colorIndicator_sum (χ 5)
  have h6 := colorIndicator_sum (χ 6)
  have h7 := colorIndicator_sum (χ 7)
  have h8 := colorIndicator_sum (χ 8)
  have h9 := colorIndicator_sum (χ 9)
  have h10 := colorIndicator_sum (χ 10)
  have h11 := colorIndicator_sum (χ 11)
  have h12 := colorIndicator_sum (χ 12)
  have h13 := colorIndicator_sum (χ 13)
  have h14 := colorIndicator_sum (χ 14)
  have h15 := colorIndicator_sum (χ 15)
  simp [colorCount] at *
  omega

theorem exists_colorCount_ge_six (χ : Fin 16 → Fin 3) :
    ∃ c : Fin 3, 6 ≤ colorCount χ c := by
  by_contra h
  simp only [not_exists, not_le] at h
  have h0 : colorCount χ 0 ≤ 5 := by
    have := h 0
    omega
  have h1 : colorCount χ 1 ≤ 5 := by
    have := h 1
    omega
  have h2 : colorCount χ 2 ≤ 5 := by
    have := h 2
    omega
  have hsum := colorCount_sum χ
  omega

theorem maskCard16_colorMask (χ : Fin 16 → Fin 3) (c : Fin 3) :
    maskCard16 (colorMask χ c) = colorCount χ c := by
  have h0 : (colorMask χ c).testBit (0 : Nat) = decide (χ 0 = c) := by
    simpa using colorMask_testBit χ c 0
  have h1 : (colorMask χ c).testBit (1 : Nat) = decide (χ 1 = c) := by
    simpa using colorMask_testBit χ c 1
  have h2 : (colorMask χ c).testBit (2 : Nat) = decide (χ 2 = c) := by
    simpa using colorMask_testBit χ c 2
  have h3 : (colorMask χ c).testBit (3 : Nat) = decide (χ 3 = c) := by
    simpa using colorMask_testBit χ c 3
  have h4 : (colorMask χ c).testBit (4 : Nat) = decide (χ 4 = c) := by
    simpa using colorMask_testBit χ c 4
  have h5 : (colorMask χ c).testBit (5 : Nat) = decide (χ 5 = c) := by
    simpa using colorMask_testBit χ c 5
  have h6 : (colorMask χ c).testBit (6 : Nat) = decide (χ 6 = c) := by
    simpa using colorMask_testBit χ c 6
  have h7 : (colorMask χ c).testBit (7 : Nat) = decide (χ 7 = c) := by
    simpa using colorMask_testBit χ c 7
  have h8 : (colorMask χ c).testBit (8 : Nat) = decide (χ 8 = c) := by
    simpa using colorMask_testBit χ c 8
  have h9 : (colorMask χ c).testBit (9 : Nat) = decide (χ 9 = c) := by
    simpa using colorMask_testBit χ c 9
  have h10 : (colorMask χ c).testBit (10 : Nat) = decide (χ 10 = c) := by
    simpa using colorMask_testBit χ c 10
  have h11 : (colorMask χ c).testBit (11 : Nat) = decide (χ 11 = c) := by
    simpa using colorMask_testBit χ c 11
  have h12 : (colorMask χ c).testBit (12 : Nat) = decide (χ 12 = c) := by
    simpa using colorMask_testBit χ c 12
  have h13 : (colorMask χ c).testBit (13 : Nat) = decide (χ 13 = c) := by
    simpa using colorMask_testBit χ c 13
  have h14 : (colorMask χ c).testBit (14 : Nat) = decide (χ 14 = c) := by
    simpa using colorMask_testBit χ c 14
  have h15 : (colorMask χ c).testBit (15 : Nat) = decide (χ 15 = c) := by
    simpa using colorMask_testBit χ c 15
  change
    (if (colorMask χ c).testBit (0 : Nat) then 1 else 0) +
    (if (colorMask χ c).testBit (1 : Nat) then 1 else 0) +
    (if (colorMask χ c).testBit (2 : Nat) then 1 else 0) +
    (if (colorMask χ c).testBit (3 : Nat) then 1 else 0) +
    (if (colorMask χ c).testBit (4 : Nat) then 1 else 0) +
    (if (colorMask χ c).testBit (5 : Nat) then 1 else 0) +
    (if (colorMask χ c).testBit (6 : Nat) then 1 else 0) +
    (if (colorMask χ c).testBit (7 : Nat) then 1 else 0) +
    (if (colorMask χ c).testBit (8 : Nat) then 1 else 0) +
    (if (colorMask χ c).testBit (9 : Nat) then 1 else 0) +
    (if (colorMask χ c).testBit (10 : Nat) then 1 else 0) +
    (if (colorMask χ c).testBit (11 : Nat) then 1 else 0) +
    (if (colorMask χ c).testBit (12 : Nat) then 1 else 0) +
    (if (colorMask χ c).testBit (13 : Nat) then 1 else 0) +
    (if (colorMask χ c).testBit (14 : Nat) then 1 else 0) +
    (if (colorMask χ c).testBit (15 : Nat) then 1 else 0) = colorCount χ c
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]
  simp [colorCount]

theorem colorMask_indep_of_proper (χ : Fin 16 → Fin 3)
    (hproper : ∀ i j : Fin 16, adjFast i j = true → χ i ≠ χ j)
    (c : Fin 3) :
    indepFast (colorMask χ c) = true := by
  have h0 : (colorMask χ c).testBit (0 : Nat) = decide (χ 0 = c) := by
    simpa using colorMask_testBit χ c 0
  have h1 : (colorMask χ c).testBit (1 : Nat) = decide (χ 1 = c) := by
    simpa using colorMask_testBit χ c 1
  have h2 : (colorMask χ c).testBit (2 : Nat) = decide (χ 2 = c) := by
    simpa using colorMask_testBit χ c 2
  have h3 : (colorMask χ c).testBit (3 : Nat) = decide (χ 3 = c) := by
    simpa using colorMask_testBit χ c 3
  have h4 : (colorMask χ c).testBit (4 : Nat) = decide (χ 4 = c) := by
    simpa using colorMask_testBit χ c 4
  have h5 : (colorMask χ c).testBit (5 : Nat) = decide (χ 5 = c) := by
    simpa using colorMask_testBit χ c 5
  have h6 : (colorMask χ c).testBit (6 : Nat) = decide (χ 6 = c) := by
    simpa using colorMask_testBit χ c 6
  have h7 : (colorMask χ c).testBit (7 : Nat) = decide (χ 7 = c) := by
    simpa using colorMask_testBit χ c 7
  have h8 : (colorMask χ c).testBit (8 : Nat) = decide (χ 8 = c) := by
    simpa using colorMask_testBit χ c 8
  have h9 : (colorMask χ c).testBit (9 : Nat) = decide (χ 9 = c) := by
    simpa using colorMask_testBit χ c 9
  have h10 : (colorMask χ c).testBit (10 : Nat) = decide (χ 10 = c) := by
    simpa using colorMask_testBit χ c 10
  have h11 : (colorMask χ c).testBit (11 : Nat) = decide (χ 11 = c) := by
    simpa using colorMask_testBit χ c 11
  have h12 : (colorMask χ c).testBit (12 : Nat) = decide (χ 12 = c) := by
    simpa using colorMask_testBit χ c 12
  have h13 : (colorMask χ c).testBit (13 : Nat) = decide (χ 13 = c) := by
    simpa using colorMask_testBit χ c 13
  have h14 : (colorMask χ c).testBit (14 : Nat) = decide (χ 14 = c) := by
    simpa using colorMask_testBit χ c 14
  have h15 : (colorMask χ c).testBit (15 : Nat) = decide (χ 15 = c) := by
    simpa using colorMask_testBit χ c 15
  simp [indepFast, h0, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10, h11, h12, h13, h14, h15]
  repeat' apply And.intro
  all_goals
    by_contra h
    push Not at h
    first
    | exact (hproper 0 6 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 0 7 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 0 8 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 0 11 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 0 15 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 1 7 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 1 8 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 1 9 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 1 10 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 2 6 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 2 8 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 2 10 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 2 11 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 2 15 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 3 9 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 3 10 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 3 12 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 3 13 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 4 10 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 4 11 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 4 13 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 4 14 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 5 6 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 5 8 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 5 11 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 5 14 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 5 15 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 6 12 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 6 13 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 7 13 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 7 14 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 8 12 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 9 14 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 9 15 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 11 12 (by decide)) (by simpa [h.1, h.2])
    | exact (hproper 12 15 (by decide)) (by simpa [h.1, h.2])

theorem no_coloring_with_certMask (χ : Fin 16 → Fin 3)
    (hproper : ∀ i j : Fin 16, adjFast i j = true → χ i ≠ χ j)
    (main : Fin 3) (cert : Fin 16)
    (hmask : colorMask χ main = certMask cert) : False := by
  have notMain (v : Fin 16) (hbit : (certMask cert).testBit v.val = false) :
      χ v ≠ main := by
    have hb : (colorMask χ main).testBit v.val = false := by
      rw [hmask]
      exact hbit
    have ht := colorMask_testBit χ main v
    have hdec : decide (χ v = main) = false := by
      rw [← ht]
      exact hb
    intro hv
    simp [hv] at hdec
  fin_cases cert <;> first
    | exact no_two_color_cycle7 main (χ 6) (χ 12) (χ 15) (χ 9) (χ 14) (χ 7) (χ 13) (notMain 6 (by decide)) (notMain 12 (by decide)) (notMain 15 (by decide)) (notMain 9 (by decide)) (notMain 14 (by decide)) (notMain 7 (by decide)) (notMain 13 (by decide)) (hproper 6 12 (by decide)) (hproper 12 15 (by decide)) (hproper 15 9 (by decide)) (hproper 9 14 (by decide)) (hproper 14 7 (by decide)) (hproper 7 13 (by decide)) (hproper 13 6 (by decide))
    | exact no_two_color_cycle5 main (χ 3) (χ 9) (χ 14) (χ 7) (χ 13) (notMain 3 (by decide)) (notMain 9 (by decide)) (notMain 14 (by decide)) (notMain 7 (by decide)) (notMain 13 (by decide)) (hproper 3 9 (by decide)) (hproper 9 14 (by decide)) (hproper 14 7 (by decide)) (hproper 7 13 (by decide)) (hproper 13 3 (by decide))
    | exact no_two_color_cycle5 main (χ 3) (χ 9) (χ 14) (χ 4) (χ 10) (notMain 3 (by decide)) (notMain 9 (by decide)) (notMain 14 (by decide)) (notMain 4 (by decide)) (notMain 10 (by decide)) (hproper 3 9 (by decide)) (hproper 9 14 (by decide)) (hproper 14 4 (by decide)) (hproper 4 10 (by decide)) (hproper 10 3 (by decide))
    | exact no_two_color_cycle7 main (χ 3) (χ 9) (χ 15) (χ 5) (χ 11) (χ 4) (χ 10) (notMain 3 (by decide)) (notMain 9 (by decide)) (notMain 15 (by decide)) (notMain 5 (by decide)) (notMain 11 (by decide)) (notMain 4 (by decide)) (notMain 10 (by decide)) (hproper 3 9 (by decide)) (hproper 9 15 (by decide)) (hproper 15 5 (by decide)) (hproper 5 11 (by decide)) (hproper 11 4 (by decide)) (hproper 4 10 (by decide)) (hproper 10 3 (by decide))
    | exact no_two_color_cycle5 main (χ 1) (χ 7) (χ 13) (χ 3) (χ 10) (notMain 1 (by decide)) (notMain 7 (by decide)) (notMain 13 (by decide)) (notMain 3 (by decide)) (notMain 10 (by decide)) (hproper 1 7 (by decide)) (hproper 7 13 (by decide)) (hproper 13 3 (by decide)) (hproper 3 10 (by decide)) (hproper 10 1 (by decide))
    | exact no_two_color_cycle5 main (χ 1) (χ 7) (χ 14) (χ 4) (χ 10) (notMain 1 (by decide)) (notMain 7 (by decide)) (notMain 14 (by decide)) (notMain 4 (by decide)) (notMain 10 (by decide)) (hproper 1 7 (by decide)) (hproper 7 14 (by decide)) (hproper 14 4 (by decide)) (hproper 4 10 (by decide)) (hproper 10 1 (by decide))
    | exact no_two_color_cycle7 main (χ 1) (χ 7) (χ 14) (χ 4) (χ 11) (χ 2) (χ 8) (notMain 1 (by decide)) (notMain 7 (by decide)) (notMain 14 (by decide)) (notMain 4 (by decide)) (notMain 11 (by decide)) (notMain 2 (by decide)) (notMain 8 (by decide)) (hproper 1 7 (by decide)) (hproper 7 14 (by decide)) (hproper 14 4 (by decide)) (hproper 4 11 (by decide)) (hproper 11 2 (by decide)) (hproper 2 8 (by decide)) (hproper 8 1 (by decide))
    | exact no_two_color_cycle7 main (χ 0) (χ 7) (χ 13) (χ 4) (χ 10) (χ 2) (χ 8) (notMain 0 (by decide)) (notMain 7 (by decide)) (notMain 13 (by decide)) (notMain 4 (by decide)) (notMain 10 (by decide)) (notMain 2 (by decide)) (notMain 8 (by decide)) (hproper 0 7 (by decide)) (hproper 7 13 (by decide)) (hproper 13 4 (by decide)) (hproper 4 10 (by decide)) (hproper 10 2 (by decide)) (hproper 2 8 (by decide)) (hproper 8 0 (by decide))
    | exact no_two_color_cycle7 main (χ 0) (χ 6) (χ 13) (χ 3) (χ 10) (χ 1) (χ 8) (notMain 0 (by decide)) (notMain 6 (by decide)) (notMain 13 (by decide)) (notMain 3 (by decide)) (notMain 10 (by decide)) (notMain 1 (by decide)) (notMain 8 (by decide)) (hproper 0 6 (by decide)) (hproper 6 13 (by decide)) (hproper 13 3 (by decide)) (hproper 3 10 (by decide)) (hproper 10 1 (by decide)) (hproper 1 8 (by decide)) (hproper 8 0 (by decide))
    | exact no_two_color_cycle7 main (χ 1) (χ 9) (χ 14) (χ 5) (χ 11) (χ 2) (χ 10) (notMain 1 (by decide)) (notMain 9 (by decide)) (notMain 14 (by decide)) (notMain 5 (by decide)) (notMain 11 (by decide)) (notMain 2 (by decide)) (notMain 10 (by decide)) (hproper 1 9 (by decide)) (hproper 9 14 (by decide)) (hproper 14 5 (by decide)) (hproper 5 11 (by decide)) (hproper 11 2 (by decide)) (hproper 2 10 (by decide)) (hproper 10 1 (by decide))
    | exact no_two_color_cycle5 main (χ 1) (χ 9) (χ 14) (χ 4) (χ 10) (notMain 1 (by decide)) (notMain 9 (by decide)) (notMain 14 (by decide)) (notMain 4 (by decide)) (notMain 10 (by decide)) (hproper 1 9 (by decide)) (hproper 9 14 (by decide)) (hproper 14 4 (by decide)) (hproper 4 10 (by decide)) (hproper 10 1 (by decide))
    | exact no_two_color_cycle5 main (χ 1) (χ 7) (χ 13) (χ 4) (χ 10) (notMain 1 (by decide)) (notMain 7 (by decide)) (notMain 13 (by decide)) (notMain 4 (by decide)) (notMain 10 (by decide)) (hproper 1 7 (by decide)) (hproper 7 13 (by decide)) (hproper 13 4 (by decide)) (hproper 4 10 (by decide)) (hproper 10 1 (by decide))
    | exact no_two_color_cycle7 main (χ 3) (χ 12) (χ 15) (χ 5) (χ 14) (χ 4) (χ 13) (notMain 3 (by decide)) (notMain 12 (by decide)) (notMain 15 (by decide)) (notMain 5 (by decide)) (notMain 14 (by decide)) (notMain 4 (by decide)) (notMain 13 (by decide)) (hproper 3 12 (by decide)) (hproper 12 15 (by decide)) (hproper 15 5 (by decide)) (hproper 5 14 (by decide)) (hproper 14 4 (by decide)) (hproper 4 13 (by decide)) (hproper 13 3 (by decide))
    | exact no_two_color_cycle5 main (χ 3) (χ 9) (χ 14) (χ 4) (χ 13) (notMain 3 (by decide)) (notMain 9 (by decide)) (notMain 14 (by decide)) (notMain 4 (by decide)) (notMain 13 (by decide)) (hproper 3 9 (by decide)) (hproper 9 14 (by decide)) (hproper 14 4 (by decide)) (hproper 4 13 (by decide)) (hproper 13 3 (by decide))
    | exact no_two_color_cycle5 main (χ 1) (χ 7) (χ 13) (χ 3) (χ 9) (notMain 1 (by decide)) (notMain 7 (by decide)) (notMain 13 (by decide)) (notMain 3 (by decide)) (notMain 9 (by decide)) (hproper 1 7 (by decide)) (hproper 7 13 (by decide)) (hproper 13 3 (by decide)) (hproper 3 9 (by decide)) (hproper 9 1 (by decide))
    | exact no_two_color_cycle7 main (χ 0) (χ 6) (χ 12) (χ 3) (χ 9) (χ 1) (χ 7) (notMain 0 (by decide)) (notMain 6 (by decide)) (notMain 12 (by decide)) (notMain 3 (by decide)) (notMain 9 (by decide)) (notMain 1 (by decide)) (notMain 7 (by decide)) (hproper 0 6 (by decide)) (hproper 6 12 (by decide)) (hproper 12 3 (by decide)) (hproper 3 9 (by decide)) (hproper 9 1 (by decide)) (hproper 1 7 (by decide)) (hproper 7 0 (by decide))

theorem not_three_colorable_adjFast (χ : Fin 16 → Fin 3) :
    (∀ i j : Fin 16, adjFast i j = true → χ i ≠ χ j) → False := by
  intro hproper
  rcases exists_colorCount_ge_six χ with ⟨main, hmain⟩
  have hind := colorMask_indep_of_proper χ hproper main
  have hlarge := indepFast_large (colorMask_lt χ main) hind
  have hnot7_count : ¬ 7 ≤ colorCount χ main := by
    intro h7
    exact hlarge.1 (by simpa [maskCard16_colorMask χ main] using h7)
  have hcount : colorCount χ main = 6 := by omega
  have hmaskCard : maskCard16 (colorMask χ main) = 6 := by
    simpa [maskCard16_colorMask χ main] using hcount
  have hcertFast := hlarge.2 hmaskCard
  rcases certFast_eq_certMask hcertFast with ⟨cert, hcert⟩
  exact no_coloring_with_certMask χ hproper main cert hcert

theorem not_three_intersecting_cover_stableTriples
    (H : Fin 3 → Set (Finset (Fin 8)))
    (hInt : ∀ c : Fin 3, (H c).Intersecting)
    (hCover : ∀ i : Fin 16, ∃ c : Fin 3, stableTriple i ∈ H c) :
    False := by
  classical
  let χ : Fin 16 → Fin 3 := fun i => Classical.choose (hCover i)
  have hχ_mem : ∀ i : Fin 16, stableTriple i ∈ H (χ i) := by
    intro i
    exact Classical.choose_spec (hCover i)
  exact not_three_colorable_adjFast χ (by
    intro i j hadj hsame
    have hdisj : Disjoint (stableTriple i) (stableTriple j) :=
      (adjFast_iff_disjoint i j).mp hadj
    have hi : stableTriple i ∈ H (χ i) := hχ_mem i
    have hj : stableTriple j ∈ H (χ i) := by
      simpa [hsame] using hχ_mem j
    rcases (hInt (χ i)).exists_mem_finset hi hj with ⟨x, hxi, hxj⟩
    exact (Finset.disjoint_left.mp hdisj) hxi hxj)

theorem not_three_intersecting_cover_triples
    (H : Fin 3 → Set (Finset (Fin 8)))
    (hInt : ∀ c : Fin 3, (H c).Intersecting)
    (hCover : ∀ T : Finset (Fin 8), T.card = 3 → ∃ c : Fin 3, T ∈ H c) :
    False :=
  not_three_intersecting_cover_stableTriples H hInt
    (fun i => hCover (stableTriple i) (stableTriple_card i))

end Kneser
end CondorcetReinforcementN8
end SocialChoice
