import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.Sort
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic
import SocialChoice.Profile
import SocialChoice.Margin
import SocialChoice.Rank
import SocialChoice.Axioms.Condorcet

namespace SocialChoice

open Finset

/-!
# List-Based Ballot Infrastructure

This file provides generic (type-agnostic) bridges between linear orders and list
representations of ballots. It is intended for proofs that reason about adjacent
swaps or list manipulations.
-/

/-! ## LinearOrder from a List -/

section LinearOrderFromList

variable {A : Type} [DecidableEq A]

/--
Construct a `LinearOrder` from a nodup list that covers all elements of a type.
The order is: `a < b` iff `a` appears before `b` in the list.
-/
@[reducible] noncomputable def linearOrderOfList (l : List A)
    (hnodup : l.Nodup) (hcomplete : ∀ a, a ∈ l) : LinearOrder A :=
  let e := List.Nodup.getEquivOfForallMemList l hnodup hcomplete
  LinearOrder.lift' e.symm e.symm.injective

lemma linearOrderOfList_lt (l : List A) (hnodup : l.Nodup) (hcomplete : ∀ a, a ∈ l) (a b : A) :
    (linearOrderOfList l hnodup hcomplete).lt a b ↔
      (List.Nodup.getEquivOfForallMemList l hnodup hcomplete).symm a <
      (List.Nodup.getEquivOfForallMemList l hnodup hcomplete).symm b := by
  rfl

lemma linearOrderOfList_lt_iff_idxOf (l : List A) (hnodup : l.Nodup) (hcomplete : ∀ a, a ∈ l)
    (a b : A) :
    (linearOrderOfList l hnodup hcomplete).lt a b ↔ l.idxOf a < l.idxOf b := by
  classical
  have ha :=
    List.Nodup.getEquivOfForallMemList_symm_apply_val (l := l) hnodup hcomplete a
  have hb :=
    List.Nodup.getEquivOfForallMemList_symm_apply_val (l := l) hnodup hcomplete b
  constructor
  · intro h
    have h' :
        ((List.Nodup.getEquivOfForallMemList l hnodup hcomplete).symm a).val <
          ((List.Nodup.getEquivOfForallMemList l hnodup hcomplete).symm b).val :=
      (Fin.val_fin_lt).2 h
    simpa [ha, hb] using h'
  · intro h
    have h' :
        ((List.Nodup.getEquivOfForallMemList l hnodup hcomplete).symm a).val <
          ((List.Nodup.getEquivOfForallMemList l hnodup hcomplete).symm b).val := by
      simpa [ha, hb] using h
    exact (Fin.val_fin_lt).1 h'

end LinearOrderFromList

/-! ## ListBallot Structure -/

section ListBallot

/--
A `ListBallot n` is a ranking of `Fin n` represented as a list,
where the first element is the most preferred candidate.
It must be a permutation of `finRange n`.
-/
structure ListBallot (n : ℕ) where
  ranking : List (Fin n)
  perm : ranking.Perm (List.finRange n)

namespace ListBallot

variable {n : ℕ}

/-- A ListBallot has no duplicates (follows from being a permutation). -/
lemma nodup (b : ListBallot n) : b.ranking.Nodup :=
  b.perm.nodup_iff.mpr (List.nodup_finRange n)

/-- Every element of Fin n appears in a ListBallot. -/
lemma complete (b : ListBallot n) (a : Fin n) : a ∈ b.ranking :=
  b.perm.mem_iff.mpr (List.mem_finRange a)

/-- Convert a ListBallot to a LinearOrder. -/
@[reducible] noncomputable def toLinearOrder (b : ListBallot n) : LinearOrder (Fin n) :=
  linearOrderOfList b.ranking b.nodup b.complete

/-- The lt relation of toLinearOrder corresponds to idxOf comparison. -/
lemma lt_iff_idxOf (b : ListBallot n) (a c : Fin n) :
    b.toLinearOrder.lt a c ↔ b.ranking.idxOf a < b.ranking.idxOf c := by
  rfl

/-- Create a ListBallot from a list with a decidable permutation proof. -/
def mk' (l : List (Fin n)) (h : l.Perm (List.finRange n) := by decide) : ListBallot n :=
  ⟨l, h⟩

/-- The identity ballot [0, 1, 2, ..., n-1]. -/
def identity (n : ℕ) : ListBallot n :=
  ⟨List.finRange n, List.Perm.refl _⟩

end ListBallot

end ListBallot

/-! ## Profile from ListBallots -/

section ProfileOfListBallots

variable {m n : ℕ}

/-- Construct a Profile from a function assigning ListBallots to voters. -/
noncomputable def profileOfListBallots (ballots : Fin m → ListBallot n) :
    Profile (Fin m) (Fin n) where
  pref := fun v => (ballots v).toLinearOrder

/-- Access the underlying ranking list for a voter in a list-based profile. -/
def profileBallotRanking (ballots : Fin m → ListBallot n) (v : Fin m) : List (Fin n) :=
  (ballots v).ranking

end ProfileOfListBallots

/-! ## List-Based Ballot Utilities -/

section ListBallotUtilities

variable {n : ℕ}

/-- Expand a ballot into a list with k identical copies. -/
def ballotCopies (k : Nat) (b : ListBallot n) : List (ListBallot n) :=
  List.replicate k b

/-- Expand a list of (count, ballot) pairs into a list of ballots. -/
def ballotList : List (Nat × ListBallot n) → List (ListBallot n)
  | [] => []
  | (k, b) :: t => ballotCopies k b ++ ballotList t

/-- Convert a list of ballots into a function on Fin length. -/
def ballotsOfList (l : List (ListBallot n)) : Fin l.length → ListBallot n :=
  fun v => l.get v

end ListBallotUtilities

/-! ## Profiles from ballot blocks -/

section ProfileOfBlocks

variable {n : ℕ}

/-- Build a profile from a block list by expanding the ballots. -/
noncomputable def profileOfBlocks (blocks : List (Nat × ListBallot n)) :
    Profile (Fin (ballotList blocks).length) (Fin n) :=
  profileOfListBallots (ballotsOfList (ballotList blocks))

end ProfileOfBlocks

/-! ## Computable Predicates -/

section ComputablePredicates

variable {α : Type} [DecidableEq α]

/-- Check if candidate `c` is at the top of ballot `l`. -/
def isTopOfList (l : List α) (c : α) : Bool :=
  l.head? = some c

/-- Check if `a` is preferred to `b` in ballot `l` (a appears before b). -/
def prefersInList (l : List α) (a b : α) : Bool :=
  l.idxOf a < l.idxOf b

/-- Get the position (0-indexed) of candidate `c` in ballot `l`. -/
def positionInList (l : List α) (c : α) : ℕ :=
  l.idxOf c

/-- Borda score: n - 1 - position (top candidate gets n-1 points). -/
def bordaScoreInList (l : List α) (c : α) : ℕ :=
  l.length - 1 - l.idxOf c

end ComputablePredicates

/-! ## Aggregate Computations -/

section AggregateComputations

variable {m n : ℕ}

/-- Count how many voters rank candidate `c` on top. -/
def countTop (ballots : Fin m → List (Fin n)) (c : Fin n) : ℕ :=
  (Finset.univ.filter fun v => isTopOfList (ballots v) c).card

/-- Count voters who prefer `a` to `b`. -/
def countPrefers (ballots : Fin m → List (Fin n)) (a b : Fin n) : ℕ :=
  (Finset.univ.filter fun v => prefersInList (ballots v) a b).card

/-- Margin of `a` over `b`: voters preferring a minus voters preferring b. -/
def marginList (ballots : Fin m → List (Fin n)) (a b : Fin n) : ℤ :=
  (countPrefers ballots a b : ℤ) - (countPrefers ballots b a : ℤ)

end AggregateComputations

/-! ## Margins from ballot blocks -/

section BallotBlockMargins

variable {n : ℕ}

/-- Margin contribution of a single ballot for a pair (a,b). -/
def marginOfBallot (b : ListBallot n) (a b' : Fin n) : Int :=
  if prefersInList b.ranking a b' then 1 else -1

/-- Margin computed from a list of (count, ballot) blocks. -/
def marginBlocks (blocks : List (Nat × ListBallot n)) (a b' : Fin n) : Int :=
  blocks.foldl (fun acc p => acc + (p.1 : Int) * marginOfBallot p.2 a b') 0

end BallotBlockMargins

/-! ## Margins from explicit ballot lists -/

section BallotListMargins

variable {n : ℕ}

/-- Margin computed from an explicit list of ballots. -/
def marginBallots (l : List (ListBallot n)) (a b : Fin n) : Int :=
  (l.map (fun ballot => marginOfBallot ballot a b)).sum

lemma idxOf_ne_of_ne (b : ListBallot n) {a c : Fin n} (hne : a ≠ c) :
    b.ranking.idxOf a ≠ b.ranking.idxOf c := by
  intro hidx
  have h :=
    (List.idxOf_inj (l := b.ranking) (x := a) (y := c) (b.complete a)).mp hidx
  exact hne h

lemma marginBallots_append (l₁ l₂ : List (ListBallot n)) (a b : Fin n) :
    marginBallots (l₁ ++ l₂) a b = marginBallots l₁ a b + marginBallots l₂ a b := by
  simp [marginBallots, List.map_append, List.sum_append]

lemma marginBallots_replicate (k : Nat) (b : ListBallot n) (a b' : Fin n) :
    marginBallots (List.replicate k b) a b' = (k : Int) * marginOfBallot b a b' := by
  simp [marginBallots, List.map_replicate, List.sum_replicate]

lemma marginBallots_ballotCopies (k : Nat) (b : ListBallot n) (a b' : Fin n) :
    marginBallots (ballotCopies k b) a b' = (k : Int) * marginOfBallot b a b' := by
  simp [ballotCopies, marginBallots_replicate]

lemma marginBlocks_foldl (blocks : List (Nat × ListBallot n)) (a b : Fin n) (acc : Int) :
    blocks.foldl (fun acc p => acc + (p.1 : Int) * marginOfBallot p.2 a b) acc =
      acc + marginBlocks blocks a b := by
  induction blocks generalizing acc with
  | nil =>
      simp [marginBlocks]
  | cons head tail ih =>
      cases head with
      | mk k ballot =>
          have ih1 :=
            ih (acc := acc + (k : Int) * marginOfBallot ballot a b)
          have ih2 :=
            ih (acc := (k : Int) * marginOfBallot ballot a b)
          calc
            List.foldl (fun acc p => acc + (p.1 : Int) * marginOfBallot p.2 a b)
                (acc + (k : Int) * marginOfBallot ballot a b) tail =
              (acc + (k : Int) * marginOfBallot ballot a b) + marginBlocks tail a b := ih1
            _ = acc + ((k : Int) * marginOfBallot ballot a b + marginBlocks tail a b) := by
              ac_rfl
            _ = acc + List.foldl (fun acc p => acc + (p.1 : Int) * marginOfBallot p.2 a b)
                ((k : Int) * marginOfBallot ballot a b) tail := by
              simpa [marginBlocks] using ih2.symm
            _ = acc + marginBlocks ((k, ballot) :: tail) a b := by
              simp [marginBlocks]

lemma marginBlocks_cons (k : Nat) (ballot : ListBallot n) (tail : List (Nat × ListBallot n))
    (a b : Fin n) :
    marginBlocks ((k, ballot) :: tail) a b =
      (k : Int) * marginOfBallot ballot a b + marginBlocks tail a b := by
  have h :=
    marginBlocks_foldl (blocks := tail) (a := a) (b := b)
      (acc := (k : Int) * marginOfBallot ballot a b)
  simpa [marginBlocks, add_assoc] using h

lemma marginBallots_ballotList (blocks : List (Nat × ListBallot n)) (a b : Fin n) :
    marginBallots (ballotList blocks) a b = marginBlocks blocks a b := by
  induction blocks with
  | nil =>
      simp [marginBallots, marginBlocks, ballotList]
  | cons head tail ih =>
      cases head with
      | mk k ballot =>
          simp [ballotList, marginBallots_append, marginBallots_ballotCopies, marginBlocks_cons, ih]

end BallotListMargins

/-! ## Margins from blocks to profiles -/

section MarginFromBlocks

variable {m n : ℕ}

lemma prefersInList_asymm (b : ListBallot n) {a c : Fin n}
    (h : prefersInList b.ranking a c = true) : prefersInList b.ranking c a = false := by
  have hlt : b.ranking.idxOf a < b.ranking.idxOf c := by
    simp [prefersInList, decide_eq_true_eq] at h
    exact h
  cases hca : prefersInList b.ranking c a with
  | true =>
      have hgt : b.ranking.idxOf c < b.ranking.idxOf a := by
        simp [prefersInList, decide_eq_true_eq] at hca
        exact hca
      exact (lt_asymm hlt hgt).elim
  | false =>
      rfl

lemma prefersInList_total (b : ListBallot n) {a c : Fin n} (hne : a ≠ c)
    (h : prefersInList b.ranking a c = false) : prefersInList b.ranking c a = true := by
  have hnot : ¬ b.ranking.idxOf a < b.ranking.idxOf c := by
    simpa [prefersInList, decide_eq_false_iff_not] using h
  have hne_idx : b.ranking.idxOf a ≠ b.ranking.idxOf c :=
    idxOf_ne_of_ne b hne
  cases hlt : lt_or_gt_of_ne hne_idx with
  | inl hlt' =>
      exact (hnot hlt').elim
  | inr hgt =>
      simpa [prefersInList, decide_eq_true_eq] using hgt

lemma marginOfBallot_eq_sub_indicators (b : ListBallot n) {a c : Fin n} (hne : a ≠ c) :
    marginOfBallot b a c =
      (if prefersInList b.ranking a c then 1 else 0) -
        (if prefersInList b.ranking c a then 1 else 0) := by
  cases h : prefersInList b.ranking a c with
  | true =>
      have h' : prefersInList b.ranking a c = true := by simp [h]
      have hca : prefersInList b.ranking c a = false :=
        prefersInList_asymm b h'
      simp [marginOfBallot, h, hca]
  | false =>
      have h' : prefersInList b.ranking a c = false := by simp [h]
      have hca : prefersInList b.ranking c a = true :=
        prefersInList_total b hne h'
      simp [marginOfBallot, h, hca]

lemma marginList_eq_sum_marginOfBallot (ballots : Fin m → ListBallot n) {a c : Fin n}
    (hne : a ≠ c) :
    marginList (fun v => (ballots v).ranking) a c =
      Finset.univ.sum (fun v => marginOfBallot (ballots v) a c) := by
  classical
  have hcount_ac :
      (countPrefers (fun v => (ballots v).ranking) a c : Int) =
        Finset.univ.sum (fun v => if prefersInList (ballots v).ranking a c then (1 : Int) else 0) := by
    unfold countPrefers
    simp
  have hcount_ca :
      (countPrefers (fun v => (ballots v).ranking) c a : Int) =
        Finset.univ.sum (fun v => if prefersInList (ballots v).ranking c a then (1 : Int) else 0) := by
    unfold countPrefers
    simp
  have hsum :
      (Finset.univ.sum
          (fun v => if prefersInList (ballots v).ranking a c then (1 : Int) else 0)) -
        (Finset.univ.sum
          (fun v => if prefersInList (ballots v).ranking c a then (1 : Int) else 0)) =
        Finset.univ.sum
          (fun v =>
            (if prefersInList (ballots v).ranking a c then (1 : Int) else 0) -
              (if prefersInList (ballots v).ranking c a then (1 : Int) else 0)) := by
    symm
    exact Finset.sum_sub_distrib _ _
  have hsum' :
      Finset.univ.sum
          (fun v =>
            (if prefersInList (ballots v).ranking a c then (1 : Int) else 0) -
              (if prefersInList (ballots v).ranking c a then (1 : Int) else 0)) =
        Finset.univ.sum (fun v => marginOfBallot (ballots v) a c) := by
    refine Finset.sum_congr rfl ?_
    intro v _hv
    simp [marginOfBallot_eq_sub_indicators (b := ballots v) (hne := hne)]
  calc
    marginList (fun v => (ballots v).ranking) a c =
        (countPrefers (fun v => (ballots v).ranking) a c : Int) -
          (countPrefers (fun v => (ballots v).ranking) c a : Int) := by
        simp [marginList]
    _ =
        (Finset.univ.sum
          (fun v => if prefersInList (ballots v).ranking a c then (1 : Int) else 0)) -
        (Finset.univ.sum
          (fun v => if prefersInList (ballots v).ranking c a then (1 : Int) else 0)) := by
        simp [hcount_ac, hcount_ca]
    _ =
        Finset.univ.sum
          (fun v =>
            (if prefersInList (ballots v).ranking a c then (1 : Int) else 0) -
              (if prefersInList (ballots v).ranking c a then (1 : Int) else 0)) := hsum
    _ = Finset.univ.sum (fun v => marginOfBallot (ballots v) a c) := hsum'

lemma ballotsOfList_sum_marginOfBallot (l : List (ListBallot n)) (a b : Fin n) :
    Finset.univ.sum (fun v => marginOfBallot (ballotsOfList l v) a b) =
      marginBallots l a b := by
  classical
  induction l with
  | nil =>
      simp [marginBallots]
  | cons head tail ih =>
      have hcons' :
          (fun v => marginOfBallot (ballotsOfList (head :: tail) v) a b) =
            Fin.cons (marginOfBallot head a b)
              (fun v => marginOfBallot (ballotsOfList tail v) a b) := by
        funext v
        refine Fin.cases ?h0 ?hs v
        · simp [ballotsOfList]
        · intro v
          simp [ballotsOfList]
      calc
        Finset.univ.sum (fun v => marginOfBallot (ballotsOfList (head :: tail) v) a b) =
            marginOfBallot head a b +
              Finset.univ.sum (fun v => marginOfBallot (ballotsOfList tail v) a b) := by
            rw [hcons']
            simp
        _ = marginOfBallot head a b + marginBallots tail a b := by simp [ih]
        _ = marginBallots (head :: tail) a b := by
            simp [marginBallots]

end MarginFromBlocks

/-! ## Bridge Lemmas -/

section BridgeLemmas

variable {m n : ℕ}

/-- Prefers in a list-based profile corresponds to prefersInList. -/
lemma prefers_iff_prefersInList (ballots : Fin m → ListBallot n) (v : Fin m) (a b : Fin n) :
    Prefers (profileOfListBallots ballots) v a b ↔ prefersInList (ballots v).ranking a b = true := by
  unfold Prefers profileOfListBallots prefersInList
  rw [(ballots v).lt_iff_idxOf]
  simp only [decide_eq_true_eq]

/-- Helper: the head of a nonempty list has idxOf 0. -/
lemma idxOf_head_eq_zero {α : Type} [DecidableEq α] {l : List α} (h : l ≠ []) :
    l.idxOf (l.head h) = 0 := by
  cases l with
  | nil => contradiction
  | cons x xs => simp [List.idxOf_cons_self]

/-- TopRank in a list-based profile corresponds to isTopOfList on the ranking. -/
lemma topRank_iff_isTopOfList (ballots : Fin m → ListBallot n) (v : Fin m) (c : Fin n) :
    TopRank (profileOfListBallots ballots) v c ↔ isTopOfList (ballots v).ranking c = true := by
  constructor
  · intro htop
    unfold isTopOfList
    simp only [decide_eq_true_eq]
    -- c is preferred to all others, so it must be first
    by_cases hn : n = 0
    · exact Fin.elim0 (hn ▸ c)
    · have hne : (ballots v).ranking ≠ [] := by
        intro h
        have := (ballots v).perm.length_eq
        simp [h, List.length_finRange] at this
        omega
      rw [List.head?_eq_some_head hne]
      congr 1
      by_contra hne'
      have hidx_head : (ballots v).ranking.idxOf ((ballots v).ranking.head hne) = 0 :=
        idxOf_head_eq_zero hne
      have hc_mem := (ballots v).complete c
      have hhead_ne_c : (ballots v).ranking.head hne ≠ c := hne'
      have := htop ((ballots v).ranking.head hne) hhead_ne_c
      unfold Prefers profileOfListBallots at this
      rw [(ballots v).lt_iff_idxOf] at this
      have hidx_c := List.idxOf_lt_length_of_mem hc_mem
      omega
  · intro htop
    unfold isTopOfList at htop
    simp only [decide_eq_true_eq] at htop
    intro d hd
    unfold Prefers profileOfListBallots
    rw [(ballots v).lt_iff_idxOf]
    have hne : (ballots v).ranking ≠ [] := by
      intro h
      simp [h] at htop
    rw [List.head?_eq_some_head hne] at htop
    injection htop with hc_head
    have hidx_c : (ballots v).ranking.idxOf c = 0 := by
      rw [← hc_head]
      exact idxOf_head_eq_zero hne
    have hd_mem := (ballots v).complete d
    have hidx_d := List.idxOf_lt_length_of_mem hd_mem
    have hd_ne : (ballots v).ranking.idxOf d ≠ 0 := by
      intro h
      have heq : (ballots v).ranking.idxOf c = (ballots v).ranking.idxOf d := by omega
      have h_eq := (List.idxOf_inj (l := (ballots v).ranking) (x := c) (y := d)
        ((ballots v).complete c)).mp heq
      exact hd h_eq.symm
    omega

/-- votersTop in a list-based profile equals the filter by isTopOfList. -/
lemma votersTop_eq_filter_isTopOfList (ballots : Fin m → ListBallot n) (c : Fin n) :
    votersTop (profileOfListBallots ballots) c =
    Finset.univ.filter (fun v => isTopOfList (ballots v).ranking c) := by
  ext v
  simp only [votersTop, mem_filter, mem_univ, true_and]
  exact topRank_iff_isTopOfList ballots v c

/-- The cardinality of votersTop equals countTop. -/
lemma votersTop_card_eq_countTop (ballots : Fin m → ListBallot n) (c : Fin n) :
    (votersTop (profileOfListBallots ballots) c).card =
    countTop (fun v => (ballots v).ranking) c := by
  unfold countTop
  rw [votersTop_eq_filter_isTopOfList]

/-- votersPreferring in a list-based profile equals the filter by prefersInList. -/
lemma votersPreferring_eq_filter_prefersInList (ballots : Fin m → ListBallot n) (a b : Fin n) :
    votersPreferring (profileOfListBallots ballots) a b =
    Finset.univ.filter (fun v => prefersInList (ballots v).ranking a b) := by
  ext v
  simp only [votersPreferring, mem_filter, mem_univ, true_and]
  exact prefers_iff_prefersInList ballots v a b

/-- The margin in a list-based profile equals marginList. -/
lemma margin_eq_marginList (ballots : Fin m → ListBallot n) (a b : Fin n) :
    margin (profileOfListBallots ballots) a b =
    marginList (fun v => (ballots v).ranking) a b := by
  unfold margin marginList countPrefers
  have h1 : ∀ v, Prefers (profileOfListBallots ballots) v a b ↔
      prefersInList (ballots v).ranking a b = true :=
    fun v => prefers_iff_prefersInList ballots v a b
  have h2 : ∀ v, Prefers (profileOfListBallots ballots) v b a ↔
      prefersInList (ballots v).ranking b a = true :=
    fun v => prefers_iff_prefersInList ballots v b a
  simp only [h1, h2, Int.ofNat_eq_natCast]

/-- Margins of a block-based profile reduce to `marginBlocks` for distinct candidates. -/
lemma margin_profileOfBlocks {n : ℕ} (blocks : List (Nat × ListBallot n)) {a b : Fin n}
    (hne : a ≠ b) :
    margin (profileOfBlocks blocks) a b = marginBlocks blocks a b := by
  classical
  unfold profileOfBlocks
  rw [margin_eq_marginList]
  have hsum :
      Finset.univ.sum
          (fun v => marginOfBallot (ballotsOfList (ballotList blocks) v) a b) =
        marginBallots (ballotList blocks) a b :=
    ballotsOfList_sum_marginOfBallot (l := ballotList blocks) (a := a) (b := b)
  have hmargin :
      marginList (fun v => (ballotsOfList (ballotList blocks) v).ranking) a b =
        Finset.univ.sum
          (fun v => marginOfBallot (ballotsOfList (ballotList blocks) v) a b) :=
    marginList_eq_sum_marginOfBallot (ballots := ballotsOfList (ballotList blocks)) (hne := hne)
  calc
    marginList (fun v => (ballotsOfList (ballotList blocks) v).ranking) a b =
        Finset.univ.sum
          (fun v => marginOfBallot (ballotsOfList (ballotList blocks) v) a b) := hmargin
    _ = marginBallots (ballotList blocks) a b := hsum
    _ = marginBlocks blocks a b := marginBallots_ballotList (blocks := blocks) (a := a) (b := b)

/-- margin_pos in a list-based profile corresponds to positive marginList. -/
lemma margin_pos_iff_marginList_pos (ballots : Fin m → ListBallot n) (a b : Fin n) :
    margin_pos (profileOfListBallots ballots) a b ↔
    marginList (fun v => (ballots v).ranking) a b > 0 := by
  unfold margin_pos
  rw [margin_eq_marginList]

/-- CondorcetWinner in a list-based profile. -/
lemma CondorcetWinner_iff_marginList (ballots : Fin m → ListBallot n) (c : Fin n) :
    CondorcetWinner (profileOfListBallots ballots) c ↔
    ∀ d : Fin n, c ≠ d → marginList (fun v => (ballots v).ranking) c d > 0 := by
  constructor
  · intro h d hne
    have hpos :=
      (CondorcetWinner_iff_margin_pos (profileOfListBallots ballots) c).mp h d
        (by simpa [eq_comm] using hne)
    simpa [margin_pos_iff_marginList_pos] using hpos
  · intro h
    have hpos :
        ∀ d : Fin n, c ≠ d → margin_pos (profileOfListBallots ballots) c d := by
      intro d hne
      have h' := h d hne
      simpa [margin_pos_iff_marginList_pos] using h'
    exact (CondorcetWinner_iff_margin_pos (profileOfListBallots ballots) c).mpr hpos

end BridgeLemmas

/-! ## List Representation of a LinearOrder -/

section ListOfLinearOrder

variable {A : Type} [Fintype A]

/-- A list representation of a linear order, obtained by sorting `Finset.univ`. -/
noncomputable def listOfLinearOrder (r : LinearOrder A) : List A := by
  classical
  let _ := r
  exact (Finset.univ.sort (fun a b => a ≤ b))

lemma listOfLinearOrder_nodup (r : LinearOrder A) : (listOfLinearOrder r).Nodup := by
  classical
  let _ := r
  unfold listOfLinearOrder
  exact
    (Finset.sort_nodup (s := (Finset.univ : Finset A)) (r := fun a b => a ≤ b))

lemma listOfLinearOrder_complete (r : LinearOrder A) (a : A) : a ∈ listOfLinearOrder r := by
  classical
  let _ := r
  have ha : a ∈ (Finset.univ : Finset A) := by simp
  unfold listOfLinearOrder
  exact
    (Finset.mem_sort (s := (Finset.univ : Finset A)) (r := fun a b => a ≤ b) (a := a)).2 ha

lemma listOfLinearOrder_sortedLT (r : LinearOrder A) :
    (listOfLinearOrder r).SortedLT := by
  classical
  let _ := r
  simpa [listOfLinearOrder] using
    (Finset.sortedLT_sort (s := (Finset.univ : Finset A)))

lemma listOfLinearOrder_lt_iff_idxOf (r : LinearOrder A) [DecidableEq A] (a b : A) :
    r.lt a b ↔ (listOfLinearOrder r).idxOf a < (listOfLinearOrder r).idxOf b := by
  classical
  let _ := r
  let l := listOfLinearOrder r
  have hsorted : l.SortedLT := listOfLinearOrder_sortedLT (r := r)
  have ha : a ∈ l := listOfLinearOrder_complete (r := r) a
  have hb : b ∈ l := listOfLinearOrder_complete (r := r) b
  let e := List.SortedLT.getIso l hsorted
  have hidxa : (e.symm ⟨a, ha⟩).val = l.idxOf a := by
    simp [e, List.SortedLT.coe_getIso_symm_apply]
  have hidxb : (e.symm ⟨b, hb⟩).val = l.idxOf b := by
    simp [e, List.SortedLT.coe_getIso_symm_apply]
  have hlt :
      r.lt a b ↔ (e.symm ⟨a, ha⟩ < e.symm ⟨b, hb⟩) := by
    have h :=
      (OrderIso.lt_iff_lt (e := e.symm) (x := ⟨a, ha⟩) (y := ⟨b, hb⟩))
    have h' : (⟨a, ha⟩ : {x // x ∈ l}) < ⟨b, hb⟩ ↔ a < b := by simp
    exact (h.trans h').symm
  calc
    r.lt a b ↔ (e.symm ⟨a, ha⟩ < e.symm ⟨b, hb⟩) := hlt
    _ ↔ (e.symm ⟨a, ha⟩).val < (e.symm ⟨b, hb⟩).val := (Fin.val_fin_lt).symm
    _ ↔ l.idxOf a < l.idxOf b := by simp [hidxa, hidxb]

lemma linearOrderOfList_listOfLinearOrder (r : LinearOrder A) [DecidableEq A] :
    linearOrderOfList (listOfLinearOrder r) (listOfLinearOrder_nodup r)
      (listOfLinearOrder_complete r) = r := by
  classical
  apply LinearOrder.ext_lt
  intro a b
  have h1 :=
    linearOrderOfList_lt_iff_idxOf (l := listOfLinearOrder r)
      (hnodup := listOfLinearOrder_nodup r) (hcomplete := listOfLinearOrder_complete r) a b
  have h2 := listOfLinearOrder_lt_iff_idxOf (r := r) a b
  exact h1.trans h2.symm

lemma listOfLinearOrder_linearOrderOfList_perm (l : List A) [DecidableEq A]
    (hnodup : l.Nodup) (hcomplete : ∀ a, a ∈ l) :
    List.Perm (listOfLinearOrder (linearOrderOfList l hnodup hcomplete)) l := by
  classical
  have hfinset : l.toFinset = (Finset.univ : Finset A) := by
    ext a
    constructor
    · intro _
      simp
    · intro _
      simpa using hcomplete a
  have hperm_l : (Finset.univ : Finset A).toList.Perm l := by
    simpa [hfinset] using (List.toFinset_toList (s := l) hnodup)
  have hperm_univ :
      List.Perm (listOfLinearOrder (linearOrderOfList l hnodup hcomplete))
        (Finset.univ : Finset A).toList := by
    let r := linearOrderOfList l hnodup hcomplete
    let _ := r
    unfold listOfLinearOrder
    simpa using
      (Finset.sort_perm_toList (s := (Finset.univ : Finset A)) (r := fun a b => a ≤ b))
  exact hperm_univ.trans hperm_l

end ListOfLinearOrder

/-! ## Adjacency and list positions -/

section AdjacentList

variable {A : Type} [Fintype A] [DecidableEq A]

/-- Adjacent in a list: `a` is immediately before `b`. -/
def AdjacentInList (l : List A) (a b : A) : Prop :=
  l.idxOf a + 1 = l.idxOf b

/-- Adjacent in a linear order: no alternative strictly between `a` and `b`. -/
def AdjacentInOrder (r : LinearOrder A) (a b : A) : Prop :=
  r.lt a b ∧ ∀ z : A, ¬(r.lt a z ∧ r.lt z b)

lemma adjacentInOrder_iff_adjacentInList (r : LinearOrder A) (a b : A) :
    AdjacentInOrder r a b ↔ AdjacentInList (listOfLinearOrder r) a b := by
  classical
  let _ := r
  let l := listOfLinearOrder r
  constructor
  · intro h
    rcases h with ⟨hab, hno⟩
    have hlt : l.idxOf a < l.idxOf b :=
      (listOfLinearOrder_lt_iff_idxOf (r := r) a b).1 hab
    by_contra hneq
    have hle : l.idxOf a + 1 ≤ l.idxOf b := Nat.succ_le_of_lt hlt
    have hlt' : l.idxOf a + 1 < l.idxOf b := lt_of_le_of_ne hle hneq
    have hb_len : l.idxOf b < l.length :=
      List.idxOf_lt_length_of_mem (listOfLinearOrder_complete (r := r) b)
    have ha1_len : l.idxOf a + 1 < l.length := lt_trans hlt' hb_len
    have hnodup : l.Nodup := listOfLinearOrder_nodup (r := r)
    set z := l[l.idxOf a + 1]'ha1_len with hzdef
    have hz_idx : l.idxOf z = l.idxOf a + 1 := by
      subst z
      simpa using (List.Nodup.idxOf_getElem hnodup (l.idxOf a + 1) ha1_len)
    have hidx_az : l.idxOf a < l.idxOf z := by
      simp [hz_idx]
    have hidx_zb : l.idxOf z < l.idxOf b := by
      simpa [hz_idx] using hlt'
    have haz : r.lt a z := (listOfLinearOrder_lt_iff_idxOf (r := r) a z).2 hidx_az
    have hzb : r.lt z b := (listOfLinearOrder_lt_iff_idxOf (r := r) z b).2 hidx_zb
    exact hno z ⟨haz, hzb⟩
  · intro h
    refine ⟨?_, ?_⟩
    · have hidx : l.idxOf a < l.idxOf b := by
        rw [← h]
        exact Nat.lt_succ_self (l.idxOf a)
      exact (listOfLinearOrder_lt_iff_idxOf (r := r) a b).2 hidx
    · intro z hz
      have hidx_az : l.idxOf a < l.idxOf z :=
        (listOfLinearOrder_lt_iff_idxOf (r := r) a z).1 hz.1
      have hidx_zb : l.idxOf z < l.idxOf b :=
        (listOfLinearOrder_lt_iff_idxOf (r := r) z b).1 hz.2
      have hle : l.idxOf a + 1 ≤ l.idxOf z := Nat.succ_le_of_lt hidx_az
      have hlt' : l.idxOf z < l.idxOf a + 1 := by
        have hlt'' := hidx_zb
        rw [← h] at hlt''
        exact hlt''
      exact (lt_irrefl _ (lt_of_lt_of_le hlt' hle))

omit [Fintype A] in
lemma adjacentInList_idxOf_succ (l : List A) (hnodup : l.Nodup) (x : A)
    (hx : l.idxOf x + 1 < l.length) :
    AdjacentInList l x (l[l.idxOf x + 1]'hx) := by
  have hidx : l.idxOf (l[l.idxOf x + 1]'hx) = l.idxOf x + 1 := by
    simp only [List.Nodup.idxOf_getElem hnodup (l.idxOf x + 1) hx]
  simp [AdjacentInList, hidx]

end AdjacentList

/-! ## Rank and list indices -/

section RankIdxOf

variable {A : Type} [Fintype A] [DecidableEq A]

lemma rank_eq_idxOf_listOfLinearOrder (r : LinearOrder A) (a : A) :
    rank r a = (listOfLinearOrder r).idxOf a := by
  classical
  let _ := r
  let l := listOfLinearOrder r
  have hsorted : l.SortedLT := listOfLinearOrder_sortedLT (r := r)
  have ha : a ∈ l := listOfLinearOrder_complete (r := r) a
  let e := List.SortedLT.getIso l hsorted
  let idx : Fin l.length := e.symm ⟨a, ha⟩
  have hrank : rank r a = Fintype.card {x : A // r.lt x a} := by
    simpa [rank] using (Fintype.card_subtype (p := fun x => r.lt x a)).symm
  have hcard :
      Fintype.card {x : A // r.lt x a} = Fintype.card {i : Fin l.length // i < idx} := by
    refine Fintype.card_congr ?_
    refine
      { toFun := fun x =>
          ⟨e.symm ⟨x.1, by
              simpa [l] using (listOfLinearOrder_complete (r := r) x.1)⟩, ?_⟩
        invFun := fun i =>
          ⟨(e i.1).1, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have hlt :
        e.symm ⟨x.1, by
            simpa [l] using (listOfLinearOrder_complete (r := r) x.1)⟩ < idx ↔
          (⟨x.1, by
              simpa [l] using (listOfLinearOrder_complete (r := r) x.1)⟩ : {y // y ∈ l}) <
            ⟨a, ha⟩ := by
        have h :=
          (OrderIso.lt_iff_lt (e := e)
            (x := e.symm ⟨x.1, by
              simpa [l] using (listOfLinearOrder_complete (r := r) x.1)⟩) (y := idx))
        simp [idx, h.symm]
      have hsub : (⟨x.1, by
            simpa [l] using (listOfLinearOrder_complete (r := r) x.1)⟩ : {y // y ∈ l}) <
          ⟨a, ha⟩ := by
        exact x.2
      exact hlt.mpr hsub
    · have hlt : e i.1 < ⟨a, ha⟩ := by
        have h' := (OrderIso.lt_iff_lt (e := e) (x := i.1) (y := idx)).2 i.2
        simp [idx] at h'
        exact h'
      exact hlt
    · intro x
      apply Subtype.ext
      have h := e.apply_symm_apply
        (⟨x.1, by
          simpa [l] using (listOfLinearOrder_complete (r := r) x.1)⟩ : {y // y ∈ l})
      simp
    · intro i
      apply Subtype.ext
      have h := e.symm_apply_apply i.1
      simp only [h]
  have hfin :
      Fintype.card {i : Fin l.length // i < idx} = idx.val := by
    have hcard' :
        Fintype.card {i : Fin l.length // i < idx} =
          Fintype.card (Fin idx.val) := by
      refine Fintype.card_congr ?_
      refine
        { toFun := fun i =>
            ⟨i.1.1, by
              exact (Fin.lt_def.mp i.2)⟩
          invFun := fun i =>
            ⟨⟨i.1, lt_trans i.2 idx.isLt⟩, by
              exact (Fin.lt_def.mpr i.2)⟩
          left_inv := ?_
          right_inv := ?_ }
      · intro i
        apply Subtype.ext
        apply Fin.ext
        rfl
      · intro i
        ext
        rfl
    simpa using (hcard'.trans (by simp))
  have hidx : idx.val = (listOfLinearOrder r).idxOf a := by
    simp [idx, e, l, List.SortedLT.coe_getIso_symm_apply]
  calc
    rank r a = Fintype.card {x : A // r.lt x a} := hrank
    _ = Fintype.card {i : Fin l.length // i < idx} := hcard
    _ = idx.val := hfin
    _ = (listOfLinearOrder r).idxOf a := by
      simp [hidx]

end RankIdxOf

/-! ## Preferences via list indices -/

section PrefersIdxOf

variable {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]

lemma prefers_iff_idxOf_listOfLinearOrder (P : Profile V A) (v : V) (a b : A) :
    Prefers P v a b ↔
      (listOfLinearOrder (P.pref v)).idxOf a < (listOfLinearOrder (P.pref v)).idxOf b := by
  classical
  exact listOfLinearOrder_lt_iff_idxOf (r := P.pref v) a b

end PrefersIdxOf

end SocialChoice
