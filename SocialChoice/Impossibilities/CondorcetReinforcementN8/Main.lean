import SocialChoice.Impossibilities.CondorcetReinforcementN8.IdentitySelection
import SocialChoice.Axioms.Condorcet
import SocialChoice.Axioms.Reinforcement
import SocialChoice.ListBallot

namespace SocialChoice
namespace CondorcetReinforcementN8

open Finset
open IdentitySelection

namespace Main

set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

/-- Successor in the candidate cycle `0 → 1 → 2 → 0`. -/
def nextCandidate : Fin 3 → Fin 3
  | 0 => 1
  | 1 => 2
  | 2 => 0

/-- Predecessor in the candidate cycle `0 → 2 → 1 → 0`. -/
def prevCandidate : Fin 3 → Fin 3
  | 0 => 2
  | 1 => 0
  | 2 => 1

theorem next_ne_self (x : Fin 3) : nextCandidate x ≠ x := by
  fin_cases x <;> decide

theorem prev_ne_self (x : Fin 3) : prevCandidate x ≠ x := by
  fin_cases x <;> decide

theorem next_ne_prev (x : Fin 3) : nextCandidate x ≠ prevCandidate x := by
  fin_cases x <;> decide

theorem fin3_eq_singleton_prev_of_nonempty_of_not_mem
    (x : Fin 3) (s : Finset (Fin 3)) (hne : s.Nonempty)
    (hx : x ∉ s) (hy : nextCandidate x ∉ s) :
    s = {prevCandidate x} := by
  classical
  fin_cases x
  · have h2 : (2 : Fin 3) ∈ s := by
      have h0not : (0 : Fin 3) ∉ s := by simpa using hx
      have h1not : (1 : Fin 3) ∉ s := by simpa [nextCandidate] using hy
      rcases hne with ⟨z, hz⟩
      fin_cases z <;> simp [nextCandidate, prevCandidate] at hx hy hz ⊢
      · exact False.elim (h0not hz)
      · exact False.elim (h1not hz)
      · exact hz
    have h0not : (0 : Fin 3) ∉ s := by simpa using hx
    have h1not : (1 : Fin 3) ∉ s := by simpa [nextCandidate] using hy
    ext y
    fin_cases y <;> simp [nextCandidate, prevCandidate, h0not, h1not, h2]
  · have h0 : (0 : Fin 3) ∈ s := by
      have h1not : (1 : Fin 3) ∉ s := by simpa using hx
      have h2not : (2 : Fin 3) ∉ s := by simpa [nextCandidate] using hy
      rcases hne with ⟨z, hz⟩
      fin_cases z <;> simp [nextCandidate, prevCandidate] at hx hy hz ⊢
      · exact hz
      · exact False.elim (h1not hz)
      · exact False.elim (h2not hz)
    have h1not : (1 : Fin 3) ∉ s := by simpa using hx
    have h2not : (2 : Fin 3) ∉ s := by simpa [nextCandidate] using hy
    ext y
    fin_cases y <;> simp [nextCandidate, prevCandidate, h0, h1not, h2not]
  · have h1 : (1 : Fin 3) ∈ s := by
      have h2not : (2 : Fin 3) ∉ s := by simpa using hx
      have h0not : (0 : Fin 3) ∉ s := by simpa [nextCandidate] using hy
      rcases hne with ⟨z, hz⟩
      fin_cases z <;> simp [nextCandidate, prevCandidate] at hx hy hz ⊢
      · exact False.elim (h0not hz)
      · exact hz
      · exact False.elim (h2not hz)
    have h2not : (2 : Fin 3) ∉ s := by simpa using hx
    have h0not : (0 : Fin 3) ∉ s := by simpa [nextCandidate] using hy
    ext y
    fin_cases y <;> simp [nextCandidate, prevCandidate, h0not, h1, h2not]

theorem perm_xyz (x : Fin 3) :
    [x, nextCandidate x, prevCandidate x].Perm (List.finRange 3) := by
  fin_cases x <;> decide

theorem perm_yzx (x : Fin 3) :
    [nextCandidate x, prevCandidate x, x].Perm (List.finRange 3) := by
  fin_cases x <;> decide

theorem perm_zxy (x : Fin 3) :
    [prevCandidate x, x, nextCandidate x].Perm (List.finRange 3) := by
  fin_cases x <;> decide

theorem perm_xzy (x : Fin 3) :
    [x, prevCandidate x, nextCandidate x].Perm (List.finRange 3) := by
  fin_cases x <;> decide

theorem perm_yxz (x : Fin 3) :
    [nextCandidate x, x, prevCandidate x].Perm (List.finRange 3) := by
  fin_cases x <;> decide

/-- The ballot `x ≻ y ≻ z`, where `y = nextCandidate x` and `z = prevCandidate x`. -/
def ballotXYZ (x : Fin 3) : ListBallot 3 :=
  ListBallot.mk' [x, nextCandidate x, prevCandidate x] (perm_xyz x)

/-- The ballot `y ≻ z ≻ x`, where `y = nextCandidate x` and `z = prevCandidate x`. -/
def ballotYZX (x : Fin 3) : ListBallot 3 :=
  ListBallot.mk' [nextCandidate x, prevCandidate x, x] (perm_yzx x)

/-- The ballot `z ≻ x ≻ y`, where `y = nextCandidate x` and `z = prevCandidate x`. -/
def ballotZXY (x : Fin 3) : ListBallot 3 :=
  ListBallot.mk' [prevCandidate x, x, nextCandidate x] (perm_zxy x)

/-- The ballot `x ≻ z ≻ y`, where `y = nextCandidate x` and `z = prevCandidate x`. -/
def ballotXZY (x : Fin 3) : ListBallot 3 :=
  ListBallot.mk' [x, prevCandidate x, nextCandidate x] (perm_xzy x)

/-- The ballot `y ≻ x ≻ z`, where `y = nextCandidate x` and `z = prevCandidate x`. -/
def ballotYXZ (x : Fin 3) : ListBallot 3 :=
  ListBallot.mk' [nextCandidate x, x, prevCandidate x] (perm_yxz x)

/-- The ballot `0 ≻ 1 ≻ 2`. -/
def ballot012 : ListBallot 3 :=
  ListBallot.mk' [0, 1, 2]

/-- The ballot `1 ≻ 2 ≻ 0`. -/
def ballot120 : ListBallot 3 :=
  ListBallot.mk' [1, 2, 0]

/-- The ballot `2 ≻ 0 ≻ 1`. -/
def ballot201 : ListBallot 3 :=
  ListBallot.mk' [2, 0, 1]

@[simp] theorem ballotXYZ_zero : ballotXYZ 0 = ballot012 := rfl
@[simp] theorem ballotYZX_zero : ballotYZX 0 = ballot120 := rfl
@[simp] theorem ballotZXY_zero : ballotZXY 0 = ballot201 := rfl
@[simp] theorem ballotXYZ_one : ballotXYZ 1 = ballot120 := rfl
@[simp] theorem ballotYZX_one : ballotYZX 1 = ballot201 := rfl
@[simp] theorem ballotZXY_one : ballotZXY 1 = ballot012 := rfl
@[simp] theorem ballotXYZ_two : ballotXYZ 2 = ballot201 := rfl
@[simp] theorem ballotYZX_two : ballotYZX 2 = ballot012 := rfl
@[simp] theorem ballotZXY_two : ballotZXY 2 = ballot120 := rfl

/-- The 5-voter profile `P⁵_xyz`.

Its first three voters have ballot `x ≻ z ≻ y`, and its last two voters have
ballot `z ≻ x ≻ y`. -/
def p5Ballot (x : Fin 3) : Fin 5 → ListBallot 3
  | ⟨0, _⟩ => ballotXZY x
  | ⟨1, _⟩ => ballotXZY x
  | ⟨2, _⟩ => ballotXZY x
  | ⟨3, _⟩ => ballotZXY x
  | ⟨4, _⟩ => ballotZXY x
  | _ => ballotXYZ x

noncomputable def p5Profile (x : Fin 3) : Profile (Fin 5) (Fin 3) :=
  profileOfListBallots (p5Ballot x)

theorem p5_condorcetWinner (x : Fin 3) :
    CondorcetWinner (p5Profile x) x := by
  classical
  intro d hd
  unfold StrictMajority p5Profile
  rw [votersPreferring_eq_filter_prefersInList]
  fin_cases x <;> fin_cases d <;>
    simp_all [p5Ballot, ballotXZY, ballotZXY, ballotXYZ, nextCandidate,
      prevCandidate, prefersInList] <;> decide +revert

/-- The 4-voter profile `P²_xyz`. -/
def p2Ballot (x : Fin 3) : Fin 4 → ListBallot 3
  | ⟨0, _⟩ => ballotXYZ x
  | ⟨1, _⟩ => ballotXZY x
  | ⟨2, _⟩ => ballotZXY x
  | ⟨3, _⟩ => ballotZXY x
  | _ => ballotXYZ x

noncomputable def p2Profile (x : Fin 3) : Profile (Fin 4) (Fin 3) :=
  profileOfListBallots (p2Ballot x)

/-- The 4-voter profile `P³_xyz`. -/
def p3Ballot (x : Fin 3) : Fin 4 → ListBallot 3
  | ⟨0, _⟩ => ballotXZY x
  | ⟨1, _⟩ => ballotXZY x
  | ⟨2, _⟩ => ballotYZX x
  | ⟨3, _⟩ => ballotZXY x
  | _ => ballotXYZ x

noncomputable def p3Profile (x : Fin 3) : Profile (Fin 4) (Fin 3) :=
  profileOfListBallots (p3Ballot x)

/-- The 3-voter cycle `C_xyz`. -/
def cycleBallot (x : Fin 3) : Fin 3 → ListBallot 3
  | ⟨0, _⟩ => ballotXYZ x
  | ⟨1, _⟩ => ballotYZX x
  | ⟨2, _⟩ => ballotZXY x
  | _ => ballotXYZ x

noncomputable def cycleProfile (x : Fin 3) : Profile (Fin 3) (Fin 3) :=
  profileOfListBallots (cycleBallot x)

/-- The anonymous profile `C_xyz + P²_xyz`. -/
def cyclePlusP2Ballot (x : Fin 3) : Fin 7 → ListBallot 3
  | ⟨0, _⟩ => ballotXYZ x
  | ⟨1, _⟩ => ballotYZX x
  | ⟨2, _⟩ => ballotZXY x
  | ⟨3, _⟩ => ballotXYZ x
  | ⟨4, _⟩ => ballotXZY x
  | ⟨5, _⟩ => ballotZXY x
  | ⟨6, _⟩ => ballotZXY x
  | _ => ballotXYZ x

noncomputable def cyclePlusP2Profile (x : Fin 3) : Profile (Fin 7) (Fin 3) :=
  profileOfListBallots (cyclePlusP2Ballot x)

theorem cyclePlusP2_condorcetWinner_prev (x : Fin 3) :
    CondorcetWinner (cyclePlusP2Profile x) (prevCandidate x) := by
  classical
  intro d hd
  unfold StrictMajority cyclePlusP2Profile
  rw [votersPreferring_eq_filter_prefersInList]
  fin_cases x <;> fin_cases d <;>
    simp_all [cyclePlusP2Ballot, ballotXYZ, ballotYZX, ballotZXY, ballotXZY,
      nextCandidate, prevCandidate, prefersInList] <;> decide +revert

/-- The anonymous profile `C_xyz + P³_xyz`. -/
def cyclePlusP3Ballot (x : Fin 3) : Fin 7 → ListBallot 3
  | ⟨0, _⟩ => ballotXYZ x
  | ⟨1, _⟩ => ballotYZX x
  | ⟨2, _⟩ => ballotZXY x
  | ⟨3, _⟩ => ballotXZY x
  | ⟨4, _⟩ => ballotXZY x
  | ⟨5, _⟩ => ballotYZX x
  | ⟨6, _⟩ => ballotZXY x
  | _ => ballotXYZ x

noncomputable def cyclePlusP3Profile (x : Fin 3) : Profile (Fin 7) (Fin 3) :=
  profileOfListBallots (cyclePlusP3Ballot x)

theorem cyclePlusP3_condorcetWinner_prev (x : Fin 3) :
    CondorcetWinner (cyclePlusP3Profile x) (prevCandidate x) := by
  classical
  intro d hd
  unfold StrictMajority cyclePlusP3Profile
  rw [votersPreferring_eq_filter_prefersInList]
  fin_cases x <;> fin_cases d <;>
    simp_all [cyclePlusP3Ballot, ballotXYZ, ballotYZX, ballotZXY, ballotXZY,
      nextCandidate, prevCandidate, prefersInList] <;> decide +revert

/-- The anonymous profile `P²_xyz` plus one voter with ballot `y ≻ x ≻ z`. -/
def p2PlusYXZBallot (x : Fin 3) : Fin 5 → ListBallot 3
  | ⟨0, _⟩ => ballotXYZ x
  | ⟨1, _⟩ => ballotXZY x
  | ⟨2, _⟩ => ballotZXY x
  | ⟨3, _⟩ => ballotZXY x
  | ⟨4, _⟩ => ballotYXZ x
  | _ => ballotXYZ x

noncomputable def p2PlusYXZProfile (x : Fin 3) : Profile (Fin 5) (Fin 3) :=
  profileOfListBallots (p2PlusYXZBallot x)

theorem p2PlusYXZ_condorcetWinner (x : Fin 3) :
    CondorcetWinner (p2PlusYXZProfile x) x := by
  classical
  intro d hd
  unfold StrictMajority p2PlusYXZProfile
  rw [votersPreferring_eq_filter_prefersInList]
  fin_cases x <;> fin_cases d <;>
    simp_all [p2PlusYXZBallot, ballotXYZ, ballotZXY, ballotXZY, ballotYXZ,
      nextCandidate, prevCandidate, prefersInList] <;> decide +revert

/-- The anonymous profile `P³_xyz` plus one voter with ballot `y ≻ x ≻ z`. -/
def p3PlusYXZBallot (x : Fin 3) : Fin 5 → ListBallot 3
  | ⟨0, _⟩ => ballotXZY x
  | ⟨1, _⟩ => ballotXZY x
  | ⟨2, _⟩ => ballotYZX x
  | ⟨3, _⟩ => ballotZXY x
  | ⟨4, _⟩ => ballotYXZ x
  | _ => ballotXYZ x

noncomputable def p3PlusYXZProfile (x : Fin 3) : Profile (Fin 5) (Fin 3) :=
  profileOfListBallots (p3PlusYXZBallot x)

theorem p3PlusYXZ_condorcetWinner (x : Fin 3) :
    CondorcetWinner (p3PlusYXZProfile x) x := by
  classical
  intro d hd
  unfold StrictMajority p3PlusYXZProfile
  rw [votersPreferring_eq_filter_prefersInList]
  fin_cases x <;> fin_cases d <;>
    simp_all [p3PlusYXZBallot, ballotYZX, ballotZXY, ballotXZY, ballotYXZ,
      nextCandidate, prevCandidate, prefersInList] <;> decide +revert

section NamedProfiles

variable {U A : Type} [DecidableEq U] [Fintype A]

/-- Reindex a profile along an equivalence of voter types. -/
noncomputable def reindexVoters {V W : Type} [Fintype V] [Fintype W]
    (P : Profile V A) (e : W ≃ V) : Profile W A :=
  { pref := fun w => P.pref (e w) }

theorem votersPreferring_reindexVoters_card {V W : Type} [Fintype V] [Fintype W]
    (P : Profile V A) (e : W ≃ V) (a b : A) :
    (votersPreferring (reindexVoters P e) a b).card =
      (votersPreferring P a b).card := by
  classical
  refine Finset.card_bij
    (s := votersPreferring (reindexVoters P e) a b)
    (t := votersPreferring P a b)
    (i := fun w _ => e w) ?_ ?_ ?_
  · intro w hw
    have hpref : Prefers (reindexVoters P e) w a b := (Finset.mem_filter.mp hw).2
    change @LT.lt A (P.pref (e w)).toLT a b at hpref
    exact Finset.mem_filter.mpr ⟨by simp, hpref⟩
  · intro w₁ _ w₂ _ h
    exact e.injective h
  · intro v hv
    refine ⟨e.symm v, ?_, by simp⟩
    have hpref : Prefers P v a b := (Finset.mem_filter.mp hv).2
    refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
    change @LT.lt A ((reindexVoters P e).pref (e.symm v)).toLT a b
    rw [show (reindexVoters P e).pref (e.symm v) = P.pref v by
      simp [reindexVoters]]
    exact hpref

theorem condorcetWinner_reindexVoters_iff {V W : Type} [Fintype V] [Fintype W]
    (P : Profile V A) (e : W ≃ V) (c : A) :
    CondorcetWinner (reindexVoters P e) c ↔ CondorcetWinner P c := by
  classical
  constructor
  · intro h d hd
    have hmaj := h d hd
    unfold StrictMajority at hmaj ⊢
    rw [votersPreferring_reindexVoters_card] at hmaj
    simpa [Fintype.card_congr e] using hmaj
  · intro h d hd
    have hmaj := h d hd
    unfold StrictMajority at hmaj ⊢
    rw [votersPreferring_reindexVoters_card, Fintype.card_congr e]
    exact hmaj

theorem condorcetWinner_castProfile_iff {S T : Finset U}
    (h : S = T) (P : Profile (Electorate U S) A) (c : A) :
    CondorcetWinner (castProfile h P) c ↔ CondorcetWinner P c := by
  cases h
  simp

theorem reindex_cyclePlusP2_condorcetWinner_prev {W : Type} [Fintype W]
    (x : Fin 3) (e : W ≃ Fin 7) :
    CondorcetWinner (reindexVoters (cyclePlusP2Profile x) e) (prevCandidate x) :=
  (condorcetWinner_reindexVoters_iff (A := Fin 3) (cyclePlusP2Profile x) e
    (prevCandidate x)).mpr (cyclePlusP2_condorcetWinner_prev x)

theorem reindex_cyclePlusP3_condorcetWinner_prev {W : Type} [Fintype W]
    (x : Fin 3) (e : W ≃ Fin 7) :
    CondorcetWinner (reindexVoters (cyclePlusP3Profile x) e) (prevCandidate x) :=
  (condorcetWinner_reindexVoters_iff (A := Fin 3) (cyclePlusP3Profile x) e
    (prevCandidate x)).mpr (cyclePlusP3_condorcetWinner_prev x)

theorem reindex_p2PlusYXZ_condorcetWinner {W : Type} [Fintype W]
    (x : Fin 3) (e : W ≃ Fin 5) :
    CondorcetWinner (reindexVoters (p2PlusYXZProfile x) e) x :=
  (condorcetWinner_reindexVoters_iff (A := Fin 3) (p2PlusYXZProfile x) e x).mpr
    (p2PlusYXZ_condorcetWinner x)

theorem reindex_p3PlusYXZ_condorcetWinner {W : Type} [Fintype W]
    (x : Fin 3) (e : W ≃ Fin 5) :
    CondorcetWinner (reindexVoters (p3PlusYXZProfile x) e) x :=
  (condorcetWinner_reindexVoters_iff (A := Fin 3) (p3PlusYXZProfile x) e x).mpr
    (p3PlusYXZ_condorcetWinner x)

theorem reindex_p5_condorcetWinner {W : Type} [Fintype W]
    (x : Fin 3) (e : W ≃ Fin 5) :
    CondorcetWinner (reindexVoters (p5Profile x) e) x :=
  (condorcetWinner_reindexVoters_iff (A := Fin 3) (p5Profile x) e x).mpr
    (p5_condorcetWinner x)

/-- Seven named voters ordered as the 3-cycle block followed by a 4-voter gadget block. -/
def sevenVoters (a b c p u v w : Fin 8) : Finset (Fin 8) :=
  {a, b, c, p, u, v, w}

theorem cycle_union_four_eq_sevenVoters (a b c p u v w : Fin 8) :
    ({a, b, c} : Finset (Fin 8)) ∪ ({p, u, v, w} : Finset (Fin 8)) =
      sevenVoters a b c p u v w := by
  ext r
  simp [sevenVoters, or_assoc, or_left_comm, or_comm]

def sevenVoterIndex (a b c p u v w : Fin 8)
    (r : Electorate (Fin 8) (sevenVoters a b c p u v w)) : Fin 7 :=
  if r.1 = a then
    0
  else if r.1 = b then
    1
  else if r.1 = c then
    2
  else if r.1 = p then
    3
  else if r.1 = u then
    4
  else if r.1 = v then
    5
  else
    6

theorem sevenVoterIndex_surjective
    {a b c p u v w : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (hap : a ≠ p) (hau : a ≠ u) (hav : a ≠ v) (haw : a ≠ w)
    (hbc : b ≠ c) (hbp : b ≠ p) (hbu : b ≠ u) (hbv : b ≠ v) (hbw : b ≠ w)
    (hcp : c ≠ p) (hcu : c ≠ u) (hcv : c ≠ v) (hcw : c ≠ w)
    (hpu : p ≠ u) (hpv : p ≠ v) (hpw : p ≠ w)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    Function.Surjective (sevenVoterIndex a b c p u v w) := by
  intro k
  fin_cases k
  · refine ⟨⟨a, ?_⟩, ?_⟩
    · simp [sevenVoters]
    · simp [sevenVoterIndex]
  · refine ⟨⟨b, ?_⟩, ?_⟩
    · simp [sevenVoters]
    · simp [sevenVoterIndex, hab.symm]
  · refine ⟨⟨c, ?_⟩, ?_⟩
    · simp [sevenVoters]
    · simp [sevenVoterIndex, hac.symm, hbc.symm]
  · refine ⟨⟨p, ?_⟩, ?_⟩
    · simp [sevenVoters]
    · simp [sevenVoterIndex, hap.symm, hbp.symm, hcp.symm]
  · refine ⟨⟨u, ?_⟩, ?_⟩
    · simp [sevenVoters]
    · simp [sevenVoterIndex, hau.symm, hbu.symm, hcu.symm, hpu.symm]
  · refine ⟨⟨v, ?_⟩, ?_⟩
    · simp [sevenVoters]
    · simp [sevenVoterIndex, hav.symm, hbv.symm, hcv.symm, hpv.symm, huv.symm]
  · refine ⟨⟨w, ?_⟩, ?_⟩
    · simp [sevenVoters]
    · simp [sevenVoterIndex, haw.symm, hbw.symm, hcw.symm, hpw.symm, huw.symm, hvw.symm]

theorem sevenVoterIndex_injective
    {a b c p u v w : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (hap : a ≠ p) (hau : a ≠ u) (hav : a ≠ v) (haw : a ≠ w)
    (hbc : b ≠ c) (hbp : b ≠ p) (hbu : b ≠ u) (hbv : b ≠ v) (hbw : b ≠ w)
    (hcp : c ≠ p) (hcu : c ≠ u) (hcv : c ≠ v) (hcw : c ≠ w)
    (hpu : p ≠ u) (hpv : p ≠ v) (hpw : p ≠ w)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    Function.Injective (sevenVoterIndex a b c p u v w) := by
  intro r s hidx
  have hr : r.1 = a ∨ r.1 = b ∨ r.1 = c ∨ r.1 = p ∨ r.1 = u ∨ r.1 = v ∨ r.1 = w := by
    have hr' := r.2
    change r.1 ∈ ({a, b, c, p, u, v, w} : Finset (Fin 8)) at hr'
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hr'
    exact hr'
  have hs : s.1 = a ∨ s.1 = b ∨ s.1 = c ∨ s.1 = p ∨ s.1 = u ∨ s.1 = v ∨ s.1 = w := by
    have hs' := s.2
    change s.1 ∈ ({a, b, c, p, u, v, w} : Finset (Fin 8)) at hs'
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hs'
    exact hs'
  rcases hr with hr | hr | hr | hr | hr | hr | hr <;>
    rcases hs with hs | hs | hs | hs | hs | hs | hs
  all_goals
    first
    | apply Subtype.ext
      exact hr.trans hs.symm
    | simp [sevenVoterIndex, hr, hs, hab, hac, hap, hau, hav, haw, hbc, hbp, hbu, hbv, hbw,
        hcp, hcu, hcv, hcw, hpu, hpv, hpw, huv, huw, hvw,
        hab.symm, hac.symm, hap.symm, hau.symm, hav.symm, haw.symm, hbc.symm, hbp.symm,
        hbu.symm, hbv.symm, hbw.symm, hcp.symm, hcu.symm, hcv.symm, hcw.symm,
        hpu.symm, hpv.symm, hpw.symm, huv.symm, huw.symm, hvw.symm] at hidx

noncomputable def sevenVoterEquiv
    {a b c p u v w : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (hap : a ≠ p) (hau : a ≠ u) (hav : a ≠ v) (haw : a ≠ w)
    (hbc : b ≠ c) (hbp : b ≠ p) (hbu : b ≠ u) (hbv : b ≠ v) (hbw : b ≠ w)
    (hcp : c ≠ p) (hcu : c ≠ u) (hcv : c ≠ v) (hcw : c ≠ w)
    (hpu : p ≠ u) (hpv : p ≠ v) (hpw : p ≠ w)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    Electorate (Fin 8) (sevenVoters a b c p u v w) ≃ Fin 7 :=
  Equiv.ofBijective (sevenVoterIndex a b c p u v w)
    ⟨sevenVoterIndex_injective hab hac hap hau hav haw hbc hbp hbu hbv hbw
        hcp hcu hcv hcw hpu hpv hpw huv huw hvw,
      sevenVoterIndex_surjective hab hac hap hau hav haw hbc hbp hbu hbv hbw
        hcp hcu hcv hcw hpu hpv hpw huv huw hvw⟩

@[simp] theorem sevenVoterEquiv_apply
    {a b c p u v w : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (hap : a ≠ p) (hau : a ≠ u) (hav : a ≠ v) (haw : a ≠ w)
    (hbc : b ≠ c) (hbp : b ≠ p) (hbu : b ≠ u) (hbv : b ≠ v) (hbw : b ≠ w)
    (hcp : c ≠ p) (hcu : c ≠ u) (hcv : c ≠ v) (hcw : c ≠ w)
    (hpu : p ≠ u) (hpv : p ≠ v) (hpw : p ≠ w)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (r : Electorate (Fin 8) (sevenVoters a b c p u v w)) :
    sevenVoterEquiv hab hac hap hau hav haw hbc hbp hbu hbv hbw hcp hcu hcv hcw
      hpu hpv hpw huv huw hvw r =
      sevenVoterIndex a b c p u v w r := rfl

theorem seven_reindex_cyclePlusP2_condorcetWinner_prev
    (x : Fin 3) {a b c p u v w : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (hap : a ≠ p) (hau : a ≠ u) (hav : a ≠ v) (haw : a ≠ w)
    (hbc : b ≠ c) (hbp : b ≠ p) (hbu : b ≠ u) (hbv : b ≠ v) (hbw : b ≠ w)
    (hcp : c ≠ p) (hcu : c ≠ u) (hcv : c ≠ v) (hcw : c ≠ w)
    (hpu : p ≠ u) (hpv : p ≠ v) (hpw : p ≠ w)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    CondorcetWinner
      (reindexVoters (cyclePlusP2Profile x)
        (sevenVoterEquiv hab hac hap hau hav haw hbc hbp hbu hbv hbw hcp hcu hcv hcw
          hpu hpv hpw huv huw hvw))
      (prevCandidate x) :=
  reindex_cyclePlusP2_condorcetWinner_prev x
    (sevenVoterEquiv hab hac hap hau hav haw hbc hbp hbu hbv hbw hcp hcu hcv hcw
      hpu hpv hpw huv huw hvw)

theorem seven_reindex_cyclePlusP3_condorcetWinner_prev
    (x : Fin 3) {a b c p u v w : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (hap : a ≠ p) (hau : a ≠ u) (hav : a ≠ v) (haw : a ≠ w)
    (hbc : b ≠ c) (hbp : b ≠ p) (hbu : b ≠ u) (hbv : b ≠ v) (hbw : b ≠ w)
    (hcp : c ≠ p) (hcu : c ≠ u) (hcv : c ≠ v) (hcw : c ≠ w)
    (hpu : p ≠ u) (hpv : p ≠ v) (hpw : p ≠ w)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    CondorcetWinner
      (reindexVoters (cyclePlusP3Profile x)
        (sevenVoterEquiv hab hac hap hau hav haw hbc hbp hbu hbv hbw hcp hcu hcv hcw
          hpu hpv hpw huv huw hvw))
      (prevCandidate x) :=
  reindex_cyclePlusP3_condorcetWinner_prev x
    (sevenVoterEquiv hab hac hap hau hav haw hbc hbp hbu hbv hbw hcp hcu hcv hcw
      hpu hpv hpw huv huw hvw)

/-- Five named voters ordered for a 5-voter gadget profile. -/
def fiveVoters (a b c d e : Fin 8) : Finset (Fin 8) :=
  {a, b, c, d, e}

/-- Eight named voters ordered for final-profile comparisons. -/
def eightVoters (p q r u a b d e : Fin 8) : Finset (Fin 8) :=
  {p, q, r, u, a, b, d, e}

theorem four_union_four_middle_left_eq_eightVoters (p q r u a b d e : Fin 8) :
    ({p, u, r, d} : Finset (Fin 8)) ∪ ({q, a, b, e} : Finset (Fin 8)) =
      eightVoters p q r u a b d e := by
  ext s
  simp [eightVoters, or_assoc, or_left_comm, or_comm]

theorem four_union_four_middle_right_eq_eightVoters (p q r u a b d e : Fin 8) :
    ({p, u, d, e} : Finset (Fin 8)) ∪ ({q, r, a, b} : Finset (Fin 8)) =
      eightVoters p q r u a b d e := by
  ext s
  simp [eightVoters, or_assoc, or_left_comm, or_comm]

theorem three_union_five_middle_left_eq_eightVoters (p q r u a b d e : Fin 8) :
    ({p, q, r} : Finset (Fin 8)) ∪ ({u, a, b, d, e} : Finset (Fin 8)) =
      eightVoters p q r u a b d e := by
  ext s
  simp [eightVoters, or_assoc, or_left_comm, or_comm]

theorem four_union_singleton_eq_fiveVoters (a b c d e : Fin 8) :
    ({a, b, c, d} : Finset (Fin 8)) ∪ ({e} : Finset (Fin 8)) =
      fiveVoters a b c d e := by
  ext r
  simp [fiveVoters, or_assoc, or_left_comm, or_comm]

theorem three_union_two_eq_fiveVoters (a b c d e : Fin 8) :
    ({a, b, c} : Finset (Fin 8)) ∪ ({d, e} : Finset (Fin 8)) =
      fiveVoters a b c d e := by
  ext r
  simp [fiveVoters, or_assoc, or_left_comm, or_comm]

def fiveVoterIndex (a b c d e : Fin 8)
    (r : Electorate (Fin 8) (fiveVoters a b c d e)) : Fin 5 :=
  if r.1 = a then
    0
  else if r.1 = b then
    1
  else if r.1 = c then
    2
  else if r.1 = d then
    3
  else
    4

theorem fiveVoterIndex_surjective
    {a b c d e : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    Function.Surjective (fiveVoterIndex a b c d e) := by
  intro k
  fin_cases k
  · refine ⟨⟨a, ?_⟩, ?_⟩
    · simp [fiveVoters]
    · simp [fiveVoterIndex]
  · refine ⟨⟨b, ?_⟩, ?_⟩
    · simp [fiveVoters]
    · simp [fiveVoterIndex, hab.symm]
  · refine ⟨⟨c, ?_⟩, ?_⟩
    · simp [fiveVoters]
    · simp [fiveVoterIndex, hac.symm, hbc.symm]
  · refine ⟨⟨d, ?_⟩, ?_⟩
    · simp [fiveVoters]
    · simp [fiveVoterIndex, had.symm, hbd.symm, hcd.symm]
  · refine ⟨⟨e, ?_⟩, ?_⟩
    · simp [fiveVoters]
    · simp [fiveVoterIndex, hae.symm, hbe.symm, hce.symm, hde.symm]

theorem fiveVoterIndex_injective
    {a b c d e : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    Function.Injective (fiveVoterIndex a b c d e) := by
  intro r s hidx
  have hr : r.1 = a ∨ r.1 = b ∨ r.1 = c ∨ r.1 = d ∨ r.1 = e := by
    have hr' := r.2
    change r.1 ∈ ({a, b, c, d, e} : Finset (Fin 8)) at hr'
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hr'
    exact hr'
  have hs : s.1 = a ∨ s.1 = b ∨ s.1 = c ∨ s.1 = d ∨ s.1 = e := by
    have hs' := s.2
    change s.1 ∈ ({a, b, c, d, e} : Finset (Fin 8)) at hs'
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hs'
    exact hs'
  rcases hr with hr | hr | hr | hr | hr <;>
    rcases hs with hs | hs | hs | hs | hs
  all_goals
    first
    | apply Subtype.ext
      exact hr.trans hs.symm
    | simp [fiveVoterIndex, hr, hs, hab, hac, had, hae, hbc, hbd, hbe, hcd, hce, hde,
        hab.symm, hac.symm, had.symm, hae.symm, hbc.symm, hbd.symm, hbe.symm,
        hcd.symm, hce.symm, hde.symm] at hidx

noncomputable def fiveVoterEquiv
    {a b c d e : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    Electorate (Fin 8) (fiveVoters a b c d e) ≃ Fin 5 :=
  Equiv.ofBijective (fiveVoterIndex a b c d e)
    ⟨fiveVoterIndex_injective hab hac had hae hbc hbd hbe hcd hce hde,
      fiveVoterIndex_surjective hab hac had hae hbc hbd hbe hcd hce hde⟩

@[simp] theorem fiveVoterEquiv_apply
    {a b c d e : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (r : Electorate (Fin 8) (fiveVoters a b c d e)) :
    fiveVoterEquiv hab hac had hae hbc hbd hbe hcd hce hde r =
      fiveVoterIndex a b c d e r := rfl

theorem five_reindex_p2PlusYXZ_condorcetWinner
    (x : Fin 3) {a b c d e : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    CondorcetWinner
      (reindexVoters (p2PlusYXZProfile x)
        (fiveVoterEquiv hab hac had hae hbc hbd hbe hcd hce hde)) x :=
  reindex_p2PlusYXZ_condorcetWinner x
    (fiveVoterEquiv hab hac had hae hbc hbd hbe hcd hce hde)

theorem five_reindex_p3PlusYXZ_condorcetWinner
    (x : Fin 3) {a b c d e : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    CondorcetWinner
      (reindexVoters (p3PlusYXZProfile x)
        (fiveVoterEquiv hab hac had hae hbc hbd hbe hcd hce hde)) x :=
  reindex_p3PlusYXZ_condorcetWinner x
    (fiveVoterEquiv hab hac had hae hbc hbd hbe hcd hce hde)

theorem five_reindex_p5_condorcetWinner
    (x : Fin 3) {a b c d e : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    CondorcetWinner
      (reindexVoters (p5Profile x)
        (fiveVoterEquiv hab hac had hae hbc hbd hbe hcd hce hde)) x :=
  reindex_p5_condorcetWinner x
    (fiveVoterEquiv hab hac had hae hbc hbd hbe hcd hce hde)

/-- Glue two profiles on named electorates into a profile on the union electorate. -/
noncomputable def unionNamedProfiles (V W : Finset U)
    (P : Profile (Electorate U V) A) (Q : Profile (Electorate U W) A) :
    Profile (Electorate U (V ∪ W)) A :=
  { pref := fun v =>
      if hV : v.1 ∈ V then
        P.pref ⟨v.1, hV⟩
      else
        Q.pref ⟨v.1, by
          rcases Finset.mem_union.mp v.2 with h | h
          · exact False.elim (hV h)
          · exact h⟩ }

theorem restrict_unionNamedProfiles_left (V W : Finset U)
    (P : Profile (Electorate U V) A) (Q : Profile (Electorate U W) A) :
    restrictElectorate (unionNamedProfiles V W P Q) V
        (by intro x hx; exact Finset.mem_union.mpr (Or.inl hx)) =
      P := by
  apply Profile.ext
  intro v
  simp [unionNamedProfiles, restrictElectorate]

theorem restrict_unionNamedProfiles_right (V W : Finset U) (hdisj : Disjoint V W)
    (P : Profile (Electorate U V) A) (Q : Profile (Electorate U W) A) :
    restrictElectorate (unionNamedProfiles V W P Q) W
        (by intro x hx; exact Finset.mem_union.mpr (Or.inr hx)) =
      Q := by
  apply Profile.ext
  intro v
  have hvnot : v.1 ∉ V := by
    intro hv
    exact (Finset.disjoint_left.mp hdisj) hv v.2
  simp [unionNamedProfiles, restrictElectorate, hvnot]

theorem reinforcement_union_singleton
    {U A : Type} [DecidableEq U] [Fintype A] [DecidableEq A]
    (f : VotingRule) (hrein : Reinforcement f) (V W : Finset U) (hdisj : Disjoint V W)
    (P : Profile (Electorate U V) A) (Q : Profile (Electorate U W) A) (a : A)
    (hP : f P = {a}) (hQ : f Q = {a}) :
    f (unionNamedProfiles V W P Q) = {a} := by
  classical
  let R : Profile (Electorate U (V ∪ W)) A := unionNamedProfiles V W P Q
  have hnonempty : (f P ∩ f Q).Nonempty := by
    rw [hP, hQ]
    exact ⟨a, by simp⟩
  have hR := hrein V W hdisj P Q R
    (by simp [R, restrict_unionNamedProfiles_left])
    (by simp [R, restrict_unionNamedProfiles_right, hdisj])
    hnonempty
  simpa [R, hP, hQ] using hR

theorem reinforcement_union_mem_of_mem
    {U A : Type} [DecidableEq U] [Fintype A] [DecidableEq A]
    (f : VotingRule) (hrein : Reinforcement f) (V W : Finset U) (hdisj : Disjoint V W)
    (P : Profile (Electorate U V) A) (Q : Profile (Electorate U W) A) {a : A}
    (hP : a ∈ f P) (hQ : a ∈ f Q) :
    a ∈ f (unionNamedProfiles V W P Q) := by
  classical
  let R : Profile (Electorate U (V ∪ W)) A := unionNamedProfiles V W P Q
  have hsub := reinforcement_subset hrein V W hdisj P Q R
    (by simp [R, restrict_unionNamedProfiles_left])
    (by simp [R, restrict_unionNamedProfiles_right, hdisj])
  exact hsub (Finset.mem_inter.mpr ⟨hP, hQ⟩)

end NamedProfiles

/-- A named copy of the 4-voter profile `P²_xyz`.

The voter `p` receives `x ≻ y ≻ z`, the voter `u` receives `x ≻ z ≻ y`,
and the other two voters receive `z ≻ x ≻ y`. -/
def p2NamedBallot (x : Fin 3) (p u : Fin 8) {S : Finset (Fin 8)}
    (v : Electorate (Fin 8) S) : ListBallot 3 :=
  if v.1 = p then
    ballotXYZ x
  else if v.1 = u then
    ballotXZY x
  else
    ballotZXY x

noncomputable def p2NamedProfile (x : Fin 3) (S : Finset (Fin 8)) (p u : Fin 8) :
    Profile (Electorate (Fin 8) S) (Fin 3) :=
  { pref := fun v => (p2NamedBallot x p u v).toLinearOrder }

/-- A named copy of the 4-voter profile `P³_xyz`.

The voter `q` receives `y ≻ z ≻ x`, the voter `w` receives `z ≻ x ≻ y`,
and the other two voters receive `x ≻ z ≻ y`. -/
def p3NamedBallot (x : Fin 3) (q w : Fin 8) {S : Finset (Fin 8)}
    (v : Electorate (Fin 8) S) : ListBallot 3 :=
  if v.1 = q then
    ballotYZX x
  else if v.1 = w then
    ballotZXY x
  else
    ballotXZY x

noncomputable def p3NamedProfile (x : Fin 3) (S : Finset (Fin 8)) (q w : Fin 8) :
    Profile (Electorate (Fin 8) S) (Fin 3) :=
  { pref := fun v => (p3NamedBallot x q w v).toLinearOrder }

/-- A named copy of the 5-voter profile `P⁵_xyz`. -/
def p5NamedBallot (x : Fin 3) (a b c : Fin 8) {S : Finset (Fin 8)}
    (v : Electorate (Fin 8) S) : ListBallot 3 :=
  if v.1 = a then
    ballotXZY x
  else if v.1 = b then
    ballotXZY x
  else if v.1 = c then
    ballotXZY x
  else
    ballotZXY x

noncomputable def p5NamedProfile (x : Fin 3) (S : Finset (Fin 8)) (a b c : Fin 8) :
    Profile (Electorate (Fin 8) S) (Fin 3) :=
  { pref := fun v => (p5NamedBallot x a b c v).toLinearOrder }

theorem p5Named_eq_reindex_p5
    (x : Fin 3) {a b c d e : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    p5NamedProfile x (fiveVoters a b c d e) a b c =
      reindexVoters (p5Profile x) (fiveVoterEquiv hab hac had hae hbc hbd hbe hcd hce hde) := by
  apply Profile.ext
  intro r
  rcases r with ⟨r, hrmem⟩
  have hr : r = a ∨ r = b ∨ r = c ∨ r = d ∨ r = e := by
    have hr' := hrmem
    change r ∈ ({a, b, c, d, e} : Finset (Fin 8)) at hr'
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hr'
    exact hr'
  rcases hr with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [p5NamedProfile, p5NamedBallot, reindexVoters, p5Profile, p5Ballot,
      profileOfListBallots, fiveVoterEquiv, fiveVoterIndex, hab, hac, had, hae, hbc,
      hbd, hbe, hcd, hce, hde, hab.symm, hac.symm, had.symm, hae.symm, hbc.symm,
      hbd.symm, hbe.symm, hcd.symm, hce.symm, hde.symm] <;> rfl

theorem p5Named_condorcetWinner
    (x : Fin 3) {a b c d e : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    CondorcetWinner (p5NamedProfile x (fiveVoters a b c d e) a b c) x := by
  rw [p5Named_eq_reindex_p5 x hab hac had hae hbc hbd hbe hcd hce hde]
  exact five_reindex_p5_condorcetWinner x hab hac had hae hbc hbd hbe hcd hce hde

/-- A named copy of the 3-voter cycle `C_xyz`. -/
def cycleNamedBallot (x : Fin 3) (p q : Fin 8) {S : Finset (Fin 8)}
    (v : Electorate (Fin 8) S) : ListBallot 3 :=
  if v.1 = p then
    ballotXYZ x
  else if v.1 = q then
    ballotYZX x
  else
    ballotZXY x

noncomputable def cycleNamedProfile (x : Fin 3) (S : Finset (Fin 8)) (p q : Fin 8) :
    Profile (Electorate (Fin 8) S) (Fin 3) :=
  { pref := fun v => (cycleNamedBallot x p q v).toLinearOrder }

theorem finalProfile_middle_left_eq_cycle_p5
    (x : Fin 3) {p q r u a b d e : Fin 8}
    (hpq : p ≠ q) (hpr : p ≠ r) (hpu : p ≠ u) (hpa : p ≠ a)
    (hpb : p ≠ b) (hpd : p ≠ d) (hpe : p ≠ e)
    (hqr : q ≠ r) (hqu : q ≠ u) (hqa : q ≠ a) (hqb : q ≠ b)
    (hqd : q ≠ d) (hqe : q ≠ e)
    (hru : r ≠ u) (hra : r ≠ a) (hrb : r ≠ b) (hrd : r ≠ d) (hre : r ≠ e)
    (hua : u ≠ a) (hub : u ≠ b) (hud : u ≠ d) (hue : u ≠ e)
    (hab : a ≠ b) (had : a ≠ d) (hae : a ≠ e)
    (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e) :
    castProfile (four_union_four_middle_left_eq_eightVoters p q r u a b d e)
      (unionNamedProfiles ({p, u, r, d} : Finset (Fin 8)) ({q, a, b, e} : Finset (Fin 8))
        (p2NamedProfile x ({p, u, r, d} : Finset (Fin 8)) p u)
        (p3NamedProfile x ({q, a, b, e} : Finset (Fin 8)) q e)) =
      castProfile (three_union_five_middle_left_eq_eightVoters p q r u a b d e)
        (unionNamedProfiles ({p, q, r} : Finset (Fin 8)) ({u, a, b, d, e} : Finset (Fin 8))
          (cycleNamedProfile x ({p, q, r} : Finset (Fin 8)) p q)
          (p5NamedProfile x ({u, a, b, d, e} : Finset (Fin 8)) u a b)) := by
  apply Profile.ext
  intro v
  have hv :
      v.1 = p ∨ v.1 = q ∨ v.1 = r ∨ v.1 = u ∨
        v.1 = a ∨ v.1 = b ∨ v.1 = d ∨ v.1 = e := by
    have hv' := v.2
    change v.1 ∈ ({p, q, r, u, a, b, d, e} : Finset (Fin 8)) at hv'
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hv'
    exact hv'
  rcases hv with hv | hv | hv | hv | hv | hv | hv | hv
  all_goals
    simp [castProfile, unionNamedProfiles, p2NamedProfile, p2NamedBallot, p3NamedProfile,
      p3NamedBallot, cycleNamedProfile, cycleNamedBallot, p5NamedProfile, p5NamedBallot,
      hv, hpq, hpr, hpu, hpa, hpb, hpd, hpe, hqr, hqu, hqa, hqb, hqd, hqe,
      hru, hra, hrb, hrd, hre, hua, hub, hud, hue, hab, had, hae, hbd, hbe, hde,
      hpq.symm, hpr.symm, hpu.symm, hpa.symm, hpb.symm, hpd.symm, hpe.symm,
      hqr.symm, hqu.symm, hqa.symm, hqb.symm, hqd.symm, hqe.symm, hru.symm,
      hra.symm, hrb.symm, hrd.symm, hre.symm, hua.symm, hub.symm, hud.symm,
      hue.symm, hab.symm, had.symm, hae.symm, hbd.symm, hbe.symm, hde.symm]

theorem finalProfile_middle_right_eq_cycle_p5
    (x : Fin 3) {p q r u a b d e : Fin 8}
    (hpq : p ≠ q) (hpr : p ≠ r) (hpu : p ≠ u) (hpa : p ≠ a)
    (hpb : p ≠ b) (hpd : p ≠ d) (hpe : p ≠ e)
    (hqr : q ≠ r) (hqu : q ≠ u) (hqa : q ≠ a) (hqb : q ≠ b)
    (hqd : q ≠ d) (hqe : q ≠ e)
    (hru : r ≠ u) (hra : r ≠ a) (hrb : r ≠ b) (hrd : r ≠ d) (hre : r ≠ e)
    (hua : u ≠ a) (hub : u ≠ b) (hud : u ≠ d) (hue : u ≠ e)
    (hab : a ≠ b) (had : a ≠ d) (hae : a ≠ e)
    (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e) :
    castProfile (four_union_four_middle_right_eq_eightVoters p q r u a b d e)
      (unionNamedProfiles ({p, u, d, e} : Finset (Fin 8)) ({q, r, a, b} : Finset (Fin 8))
        (p2NamedProfile x ({p, u, d, e} : Finset (Fin 8)) p u)
        (p3NamedProfile x ({q, r, a, b} : Finset (Fin 8)) q r)) =
      castProfile (three_union_five_middle_left_eq_eightVoters p q r u a b d e)
        (unionNamedProfiles ({p, q, r} : Finset (Fin 8)) ({u, a, b, d, e} : Finset (Fin 8))
          (cycleNamedProfile x ({p, q, r} : Finset (Fin 8)) p q)
          (p5NamedProfile x ({u, a, b, d, e} : Finset (Fin 8)) u a b)) := by
  apply Profile.ext
  intro v
  have hv :
      v.1 = p ∨ v.1 = q ∨ v.1 = r ∨ v.1 = u ∨
        v.1 = a ∨ v.1 = b ∨ v.1 = d ∨ v.1 = e := by
    have hv' := v.2
    change v.1 ∈ ({p, q, r, u, a, b, d, e} : Finset (Fin 8)) at hv'
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hv'
    exact hv'
  rcases hv with hv | hv | hv | hv | hv | hv | hv | hv
  all_goals
    simp [castProfile, unionNamedProfiles, p2NamedProfile, p2NamedBallot, p3NamedProfile,
      p3NamedBallot, cycleNamedProfile, cycleNamedBallot, p5NamedProfile, p5NamedBallot,
      hv, hpq, hpr, hpu, hpa, hpb, hpd, hpe, hqr, hqu, hqa, hqb, hqd, hqe,
      hru, hra, hrb, hrd, hre, hua, hub, hud, hue, hab, had, hae, hbd, hbe, hde,
      hpq.symm, hpr.symm, hpu.symm, hpa.symm, hpb.symm, hpd.symm, hpe.symm,
      hqr.symm, hqu.symm, hqa.symm, hqb.symm, hqd.symm, hqe.symm, hru.symm,
      hra.symm, hrb.symm, hrd.symm, hre.symm, hua.symm, hub.symm, hud.symm,
      hue.symm, hab.symm, had.symm, hae.symm, hbd.symm, hbe.symm, hde.symm]

theorem p2_p3_middle_left_union_eq_singleton_prev
    (f : VotingRule) (hrein : Reinforcement f) (x : Fin 3) {p q r u a b d e : Fin 8}
    (hpq : p ≠ q) (hpu : p ≠ u) (hpa : p ≠ a) (hpb : p ≠ b) (hpe : p ≠ e)
    (hqu : q ≠ u) (hqr : q ≠ r) (hqd : q ≠ d)
    (hru : r ≠ u) (hra : r ≠ a) (hrb : r ≠ b) (hre : r ≠ e)
    (hua : u ≠ a) (hub : u ≠ b) (hue : u ≠ e)
    (hdu : d ≠ u) (hda : d ≠ a) (hdb : d ≠ b) (hde : d ≠ e)
    (hP2 : f (p2NamedProfile x ({p, u, r, d} : Finset (Fin 8)) p u) =
      {prevCandidate x})
    (hP3 : f (p3NamedProfile x ({q, a, b, e} : Finset (Fin 8)) q e) =
      {prevCandidate x}) :
    f (unionNamedProfiles ({p, u, r, d} : Finset (Fin 8)) ({q, a, b, e} : Finset (Fin 8))
        (p2NamedProfile x ({p, u, r, d} : Finset (Fin 8)) p u)
        (p3NamedProfile x ({q, a, b, e} : Finset (Fin 8)) q e)) =
      {prevCandidate x} := by
  classical
  have hdisj : Disjoint ({p, u, r, d} : Finset (Fin 8)) ({q, a, b, e} : Finset (Fin 8)) := by
    rw [Finset.disjoint_left]
    intro s hsL hsR
    simp at hsL hsR
    rcases hsL with rfl | rfl | rfl | rfl <;> rcases hsR with rfl | rfl | rfl | rfl
    all_goals simp_all
  exact reinforcement_union_singleton f hrein
    ({p, u, r, d} : Finset (Fin 8)) ({q, a, b, e} : Finset (Fin 8)) hdisj
    (p2NamedProfile x ({p, u, r, d} : Finset (Fin 8)) p u)
    (p3NamedProfile x ({q, a, b, e} : Finset (Fin 8)) q e)
    (prevCandidate x) hP2 hP3

theorem p2_p3_middle_right_union_eq_singleton_prev
    (f : VotingRule) (hrein : Reinforcement f) (x : Fin 3) {p q r u a b d e : Fin 8}
    (hpq : p ≠ q) (hpr : p ≠ r) (hpa : p ≠ a) (hpb : p ≠ b)
    (hqu : q ≠ u) (hqd : q ≠ d) (hqe : q ≠ e)
    (hru : r ≠ u) (hrd : r ≠ d) (hre : r ≠ e)
    (hua : u ≠ a) (hub : u ≠ b)
    (hda : d ≠ a) (hdb : d ≠ b)
    (hea : e ≠ a) (heb : e ≠ b)
    (hP2 : f (p2NamedProfile x ({p, u, d, e} : Finset (Fin 8)) p u) =
      {prevCandidate x})
    (hP3 : f (p3NamedProfile x ({q, r, a, b} : Finset (Fin 8)) q r) =
      {prevCandidate x}) :
    f (unionNamedProfiles ({p, u, d, e} : Finset (Fin 8)) ({q, r, a, b} : Finset (Fin 8))
        (p2NamedProfile x ({p, u, d, e} : Finset (Fin 8)) p u)
        (p3NamedProfile x ({q, r, a, b} : Finset (Fin 8)) q r)) =
      {prevCandidate x} := by
  classical
  have hdisj : Disjoint ({p, u, d, e} : Finset (Fin 8)) ({q, r, a, b} : Finset (Fin 8)) := by
    rw [Finset.disjoint_left]
    intro s hsL hsR
    simp at hsL hsR
    rcases hsL with rfl | rfl | rfl | rfl <;> rcases hsR with rfl | rfl | rfl | rfl
    all_goals simp_all
  exact reinforcement_union_singleton f hrein
    ({p, u, d, e} : Finset (Fin 8)) ({q, r, a, b} : Finset (Fin 8)) hdisj
    (p2NamedProfile x ({p, u, d, e} : Finset (Fin 8)) p u)
    (p3NamedProfile x ({q, r, a, b} : Finset (Fin 8)) q r)
    (prevCandidate x) hP2 hP3

theorem cycle_p5_union_mem
    (f : VotingRule) (hcond : CondorcetConsistency f) (hrein : Reinforcement f)
    (x : Fin 3) {p q r u a b d e : Fin 8}
    (hpu : p ≠ u) (hpa : p ≠ a) (hpb : p ≠ b) (hpd : p ≠ d) (hpe : p ≠ e)
    (hqu : q ≠ u) (hqa : q ≠ a) (hqb : q ≠ b) (hqd : q ≠ d) (hqe : q ≠ e)
    (hru : r ≠ u) (hra : r ≠ a) (hrb : r ≠ b) (hrd : r ≠ d) (hre : r ≠ e)
    (hua : u ≠ a) (hub : u ≠ b) (hud : u ≠ d) (hue : u ≠ e)
    (hab : a ≠ b) (had : a ≠ d) (hae : a ≠ e)
    (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e)
    (hxCycle : x ∈ f (cycleNamedProfile x ({p, q, r} : Finset (Fin 8)) p q)) :
    x ∈ f (unionNamedProfiles ({p, q, r} : Finset (Fin 8)) ({u, a, b, d, e} : Finset (Fin 8))
        (cycleNamedProfile x ({p, q, r} : Finset (Fin 8)) p q)
        (p5NamedProfile x ({u, a, b, d, e} : Finset (Fin 8)) u a b)) := by
  classical
  have hdisj : Disjoint ({p, q, r} : Finset (Fin 8)) ({u, a, b, d, e} : Finset (Fin 8)) := by
    rw [Finset.disjoint_left]
    intro s hsC hsP5
    simp at hsC hsP5
    rcases hsC with rfl | rfl | rfl <;> rcases hsP5 with rfl | rfl | rfl | rfl | rfl
    all_goals simp_all
  have hP5 :
      f (p5NamedProfile x (fiveVoters u a b d e) u a b) = {x} := by
    exact hcond (p5NamedProfile x (fiveVoters u a b d e) u a b) x
      (p5Named_condorcetWinner x hua hub hud hue hab had hae hbd hbe hde)
  have hxP5 : x ∈ f (p5NamedProfile x ({u, a, b, d, e} : Finset (Fin 8)) u a b) := by
    change x ∈ f (p5NamedProfile x (fiveVoters u a b d e) u a b)
    simp [hP5]
  exact reinforcement_union_mem_of_mem f hrein
    ({p, q, r} : Finset (Fin 8)) ({u, a, b, d, e} : Finset (Fin 8)) hdisj
    (cycleNamedProfile x ({p, q, r} : Finset (Fin 8)) p q)
    (p5NamedProfile x ({u, a, b, d, e} : Finset (Fin 8)) u a b)
    hxCycle hxP5

theorem finalProfile_middle_left_contradiction
    (f : VotingRule) (hcond : CondorcetConsistency f) (hrein : Reinforcement f)
    (x : Fin 3) {p q r u a b d e : Fin 8}
    (hpq : p ≠ q) (hpr : p ≠ r) (hpu : p ≠ u) (hpa : p ≠ a)
    (hpb : p ≠ b) (hpd : p ≠ d) (hpe : p ≠ e)
    (hqr : q ≠ r) (hqu : q ≠ u) (hqa : q ≠ a) (hqb : q ≠ b)
    (hqd : q ≠ d) (hqe : q ≠ e)
    (hru : r ≠ u) (hra : r ≠ a) (hrb : r ≠ b) (hrd : r ≠ d) (hre : r ≠ e)
    (hua : u ≠ a) (hub : u ≠ b) (hud : u ≠ d) (hue : u ≠ e)
    (hab : a ≠ b) (had : a ≠ d) (hae : a ≠ e)
    (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e)
    (hP2 : f (p2NamedProfile x ({p, u, r, d} : Finset (Fin 8)) p u) =
      {prevCandidate x})
    (hP3 : f (p3NamedProfile x ({q, a, b, e} : Finset (Fin 8)) q e) =
      {prevCandidate x})
    (hxCycle : x ∈ f (cycleNamedProfile x ({p, q, r} : Finset (Fin 8)) p q)) :
    False := by
  classical
  let L : Profile
      (Electorate (Fin 8) (({p, u, r, d} : Finset (Fin 8)) ∪ ({q, a, b, e} : Finset (Fin 8))))
      (Fin 3) :=
    unionNamedProfiles ({p, u, r, d} : Finset (Fin 8)) ({q, a, b, e} : Finset (Fin 8))
      (p2NamedProfile x ({p, u, r, d} : Finset (Fin 8)) p u)
      (p3NamedProfile x ({q, a, b, e} : Finset (Fin 8)) q e)
  let R : Profile
      (Electorate (Fin 8) (({p, q, r} : Finset (Fin 8)) ∪ ({u, a, b, d, e} : Finset (Fin 8))))
      (Fin 3) :=
    unionNamedProfiles ({p, q, r} : Finset (Fin 8)) ({u, a, b, d, e} : Finset (Fin 8))
      (cycleNamedProfile x ({p, q, r} : Finset (Fin 8)) p q)
      (p5NamedProfile x ({u, a, b, d, e} : Finset (Fin 8)) u a b)
  have hL :
      f L = {prevCandidate x} := by
    simpa [L] using p2_p3_middle_left_union_eq_singleton_prev f hrein x hpq hpu hpa hpb
      hpe hqu hqr hqd hru hra hrb hre hua hub hue hud.symm had.symm hbd.symm hde
      hP2 hP3
  have hLcast :
      f (castProfile (four_union_four_middle_left_eq_eightVoters p q r u a b d e) L) =
        {prevCandidate x} := by
    have hcast := votingRule_castProfile (f := f)
      (four_union_four_middle_left_eq_eightVoters p q r u a b d e) L
    rw [hcast, hL]
  have hxR : x ∈ f R := by
    simpa [R] using cycle_p5_union_mem f hcond hrein x hpu hpa hpb hpd hpe hqu hqa
      hqb hqd hqe hru hra hrb hrd hre hua hub hud hue hab had hae hbd hbe hde hxCycle
  have hxRcast :
      x ∈ f (castProfile (three_union_five_middle_left_eq_eightVoters p q r u a b d e) R) := by
    have hcast := votingRule_castProfile (f := f)
      (three_union_five_middle_left_eq_eightVoters p q r u a b d e) R
    simpa [hcast] using hxR
  have hprofiles :
      castProfile (four_union_four_middle_left_eq_eightVoters p q r u a b d e) L =
        castProfile (three_union_five_middle_left_eq_eightVoters p q r u a b d e) R := by
    simpa [L, R] using finalProfile_middle_left_eq_cycle_p5 x hpq hpr hpu hpa hpb hpd
      hpe hqr hqu hqa hqb hqd hqe hru hra hrb hrd hre hua hub hud hue hab had hae
      hbd hbe hde
  have hxLcast :
      x ∈ f (castProfile (four_union_four_middle_left_eq_eightVoters p q r u a b d e) L) := by
    simpa [hprofiles] using hxRcast
  have hxEq : x = prevCandidate x := by
    have hxSingleton : x ∈ ({prevCandidate x} : Finset (Fin 3)) := by
      simpa [hLcast] using hxLcast
    simpa using hxSingleton
  exact (prev_ne_self x) hxEq.symm

theorem finalProfile_middle_right_contradiction
    (f : VotingRule) (hcond : CondorcetConsistency f) (hrein : Reinforcement f)
    (x : Fin 3) {p q r u a b d e : Fin 8}
    (hpq : p ≠ q) (hpr : p ≠ r) (hpu : p ≠ u) (hpa : p ≠ a)
    (hpb : p ≠ b) (hpd : p ≠ d) (hpe : p ≠ e)
    (hqr : q ≠ r) (hqu : q ≠ u) (hqa : q ≠ a) (hqb : q ≠ b)
    (hqd : q ≠ d) (hqe : q ≠ e)
    (hru : r ≠ u) (hra : r ≠ a) (hrb : r ≠ b) (hrd : r ≠ d) (hre : r ≠ e)
    (hua : u ≠ a) (hub : u ≠ b) (hud : u ≠ d) (hue : u ≠ e)
    (hab : a ≠ b) (had : a ≠ d) (hae : a ≠ e)
    (hbd : b ≠ d) (hbe : b ≠ e) (hde : d ≠ e)
    (hP2 : f (p2NamedProfile x ({p, u, d, e} : Finset (Fin 8)) p u) =
      {prevCandidate x})
    (hP3 : f (p3NamedProfile x ({q, r, a, b} : Finset (Fin 8)) q r) =
      {prevCandidate x})
    (hxCycle : x ∈ f (cycleNamedProfile x ({p, q, r} : Finset (Fin 8)) p q)) :
    False := by
  classical
  let L : Profile
      (Electorate (Fin 8) (({p, u, d, e} : Finset (Fin 8)) ∪ ({q, r, a, b} : Finset (Fin 8))))
      (Fin 3) :=
    unionNamedProfiles ({p, u, d, e} : Finset (Fin 8)) ({q, r, a, b} : Finset (Fin 8))
      (p2NamedProfile x ({p, u, d, e} : Finset (Fin 8)) p u)
      (p3NamedProfile x ({q, r, a, b} : Finset (Fin 8)) q r)
  let R : Profile
      (Electorate (Fin 8) (({p, q, r} : Finset (Fin 8)) ∪ ({u, a, b, d, e} : Finset (Fin 8))))
      (Fin 3) :=
    unionNamedProfiles ({p, q, r} : Finset (Fin 8)) ({u, a, b, d, e} : Finset (Fin 8))
      (cycleNamedProfile x ({p, q, r} : Finset (Fin 8)) p q)
      (p5NamedProfile x ({u, a, b, d, e} : Finset (Fin 8)) u a b)
  have hL :
      f L = {prevCandidate x} := by
    simpa [L] using p2_p3_middle_right_union_eq_singleton_prev f hrein x hpq hpr hpa hpb
      hqu hqd hqe hru hrd hre hua hub had.symm hbd.symm hae.symm hbe.symm hP2 hP3
  have hLcast :
      f (castProfile (four_union_four_middle_right_eq_eightVoters p q r u a b d e) L) =
        {prevCandidate x} := by
    have hcast := votingRule_castProfile (f := f)
      (four_union_four_middle_right_eq_eightVoters p q r u a b d e) L
    rw [hcast, hL]
  have hxR : x ∈ f R := by
    simpa [R] using cycle_p5_union_mem f hcond hrein x hpu hpa hpb hpd hpe hqu hqa
      hqb hqd hqe hru hra hrb hrd hre hua hub hud hue hab had hae hbd hbe hde hxCycle
  have hxRcast :
      x ∈ f (castProfile (three_union_five_middle_left_eq_eightVoters p q r u a b d e) R) := by
    have hcast := votingRule_castProfile (f := f)
      (three_union_five_middle_left_eq_eightVoters p q r u a b d e) R
    simpa [hcast] using hxR
  have hprofiles :
      castProfile (four_union_four_middle_right_eq_eightVoters p q r u a b d e) L =
        castProfile (three_union_five_middle_left_eq_eightVoters p q r u a b d e) R := by
    simpa [L, R] using finalProfile_middle_right_eq_cycle_p5 x hpq hpr hpu hpa hpb hpd
      hpe hqr hqu hqa hqb hqd hqe hru hra hrb hrd hre hua hub hud hue hab had hae
      hbd hbe hde
  have hxLcast :
      x ∈ f (castProfile (four_union_four_middle_right_eq_eightVoters p q r u a b d e) L) := by
    simpa [hprofiles] using hxRcast
  have hxEq : x = prevCandidate x := by
    have hxSingleton : x ∈ ({prevCandidate x} : Finset (Fin 3)) := by
      simpa [hLcast] using hxLcast
    simpa using hxSingleton
  exact (prev_ne_self x) hxEq.symm

theorem cast_union_cycle_p2_eq_reindex_cyclePlusP2
    (x : Fin 3) {a b c p u v w : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (hap : a ≠ p) (hau : a ≠ u) (hav : a ≠ v) (haw : a ≠ w)
    (hbc : b ≠ c) (hbp : b ≠ p) (hbu : b ≠ u) (hbv : b ≠ v) (hbw : b ≠ w)
    (hcp : c ≠ p) (hcu : c ≠ u) (hcv : c ≠ v) (hcw : c ≠ w)
    (hpu : p ≠ u) (hpv : p ≠ v) (hpw : p ≠ w)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    castProfile (cycle_union_four_eq_sevenVoters a b c p u v w)
      (unionNamedProfiles ({a, b, c} : Finset (Fin 8)) ({p, u, v, w} : Finset (Fin 8))
        (cycleNamedProfile x ({a, b, c} : Finset (Fin 8)) a b)
        (p2NamedProfile x ({p, u, v, w} : Finset (Fin 8)) p u)) =
      reindexVoters (cyclePlusP2Profile x)
        (sevenVoterEquiv hab hac hap hau hav haw hbc hbp hbu hbv hbw hcp hcu hcv hcw
          hpu hpv hpw huv huw hvw) := by
  apply Profile.ext
  intro r
  rcases r with ⟨r, hrmem⟩
  have hr : r = a ∨ r = b ∨ r = c ∨ r = p ∨ r = u ∨ r = v ∨ r = w := by
    have hr' := hrmem
    change r ∈ ({a, b, c, p, u, v, w} : Finset (Fin 8)) at hr'
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hr'
    exact hr'
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [castProfile, unionNamedProfiles, reindexVoters, cycleNamedProfile, cycleNamedBallot,
      p2NamedProfile, p2NamedBallot, cyclePlusP2Profile, cyclePlusP2Ballot, profileOfListBallots,
      sevenVoterEquiv, sevenVoterIndex, hab, hac, hap, hau, hav, haw, hbc, hbp, hbu,
      hbv, hbw, hcp, hcu, hcv, hcw, hpu, hpv, hpw, huv, huw, hvw,
      hab.symm, hac.symm, hap.symm, hau.symm, hav.symm, haw.symm, hbc.symm, hbp.symm,
      hbu.symm, hbv.symm, hbw.symm, hcp.symm, hcu.symm, hcv.symm, hcw.symm,
      hpu.symm, hpv.symm, hpw.symm, huv.symm, huw.symm, hvw.symm] <;> rfl

theorem cast_union_cycle_p3_eq_reindex_cyclePlusP3
    (x : Fin 3) {a b c p u q w : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (hap : a ≠ p) (hau : a ≠ u) (haq : a ≠ q) (haw : a ≠ w)
    (hbc : b ≠ c) (hbp : b ≠ p) (hbu : b ≠ u) (hbq : b ≠ q) (hbw : b ≠ w)
    (hcp : c ≠ p) (hcu : c ≠ u) (hcq : c ≠ q) (hcw : c ≠ w)
    (hpu : p ≠ u) (hpq : p ≠ q) (hpw : p ≠ w)
    (huq : u ≠ q) (huw : u ≠ w) (hqw : q ≠ w) :
    castProfile (cycle_union_four_eq_sevenVoters a b c p u q w)
      (unionNamedProfiles ({a, b, c} : Finset (Fin 8)) ({p, u, q, w} : Finset (Fin 8))
        (cycleNamedProfile x ({a, b, c} : Finset (Fin 8)) a b)
        (p3NamedProfile x ({p, u, q, w} : Finset (Fin 8)) q w)) =
      reindexVoters (cyclePlusP3Profile x)
        (sevenVoterEquiv hab hac hap hau haq haw hbc hbp hbu hbq hbw hcp hcu hcq hcw
          hpu hpq hpw huq huw hqw) := by
  apply Profile.ext
  intro r
  rcases r with ⟨r, hrmem⟩
  have hr : r = a ∨ r = b ∨ r = c ∨ r = p ∨ r = u ∨ r = q ∨ r = w := by
    have hr' := hrmem
    change r ∈ ({a, b, c, p, u, q, w} : Finset (Fin 8)) at hr'
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hr'
    exact hr'
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [castProfile, unionNamedProfiles, reindexVoters, cycleNamedProfile, cycleNamedBallot,
      p3NamedProfile, p3NamedBallot, cyclePlusP3Profile, cyclePlusP3Ballot, profileOfListBallots,
      sevenVoterEquiv, sevenVoterIndex, hab, hac, hap, hau, haq, haw, hbc, hbp, hbu,
      hbq, hbw, hcp, hcu, hcq, hcw, hpu, hpq, hpw, huq, huw, hqw,
      hab.symm, hac.symm, hap.symm, hau.symm, haq.symm, haw.symm, hbc.symm, hbp.symm,
      hbu.symm, hbq.symm, hbw.symm, hcp.symm, hcu.symm, hcq.symm, hcw.symm,
      hpu.symm, hpq.symm, hpw.symm, huq.symm, huw.symm, hqw.symm] <;> rfl

theorem cast_union_cycle_p2_condorcetWinner_prev
    (x : Fin 3) {a b c p u v w : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (hap : a ≠ p) (hau : a ≠ u) (hav : a ≠ v) (haw : a ≠ w)
    (hbc : b ≠ c) (hbp : b ≠ p) (hbu : b ≠ u) (hbv : b ≠ v) (hbw : b ≠ w)
    (hcp : c ≠ p) (hcu : c ≠ u) (hcv : c ≠ v) (hcw : c ≠ w)
    (hpu : p ≠ u) (hpv : p ≠ v) (hpw : p ≠ w)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    CondorcetWinner
      (castProfile (cycle_union_four_eq_sevenVoters a b c p u v w)
        (unionNamedProfiles ({a, b, c} : Finset (Fin 8)) ({p, u, v, w} : Finset (Fin 8))
          (cycleNamedProfile x ({a, b, c} : Finset (Fin 8)) a b)
          (p2NamedProfile x ({p, u, v, w} : Finset (Fin 8)) p u)))
      (prevCandidate x) := by
  rw [cast_union_cycle_p2_eq_reindex_cyclePlusP2 x hab hac hap hau hav haw hbc hbp hbu
    hbv hbw hcp hcu hcv hcw hpu hpv hpw huv huw hvw]
  exact seven_reindex_cyclePlusP2_condorcetWinner_prev x hab hac hap hau hav haw hbc hbp hbu
    hbv hbw hcp hcu hcv hcw hpu hpv hpw huv huw hvw

theorem p2Named_not_mem_of_cycle_winner
    (f : VotingRule) (hcond : CondorcetConsistency f) (hrein : Reinforcement f)
    (x : Fin 3) {a b c p u v w : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (hap : a ≠ p) (hau : a ≠ u) (hav : a ≠ v) (haw : a ≠ w)
    (hbc : b ≠ c) (hbp : b ≠ p) (hbu : b ≠ u) (hbv : b ≠ v) (hbw : b ≠ w)
    (hcp : c ≠ p) (hcu : c ≠ u) (hcv : c ≠ v) (hcw : c ≠ w)
    (hpu : p ≠ u) (hpv : p ≠ v) (hpw : p ≠ w)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hxCycle : x ∈ f (cycleNamedProfile x ({a, b, c} : Finset (Fin 8)) a b)) :
    x ∉ f (p2NamedProfile x ({p, u, v, w} : Finset (Fin 8)) p u) := by
  classical
  intro hxP2
  let C : Profile (Electorate (Fin 8) ({a, b, c} : Finset (Fin 8))) (Fin 3) :=
    cycleNamedProfile x ({a, b, c} : Finset (Fin 8)) a b
  let P : Profile (Electorate (Fin 8) ({p, u, v, w} : Finset (Fin 8))) (Fin 3) :=
    p2NamedProfile x ({p, u, v, w} : Finset (Fin 8)) p u
  let R : Profile
      (Electorate (Fin 8) (({a, b, c} : Finset (Fin 8)) ∪ ({p, u, v, w} : Finset (Fin 8))))
      (Fin 3) :=
    unionNamedProfiles ({a, b, c} : Finset (Fin 8)) ({p, u, v, w} : Finset (Fin 8)) C P
  have hdisj : Disjoint ({a, b, c} : Finset (Fin 8)) ({p, u, v, w} : Finset (Fin 8)) := by
    rw [Finset.disjoint_left]
    intro r hrC hrP
    simp at hrC hrP
    rcases hrC with rfl | rfl | rfl <;> rcases hrP with rfl | rfl | rfl | rfl
    all_goals simp_all
  have hxR : x ∈ f R := by
    have hsub := reinforcement_subset hrein
      (V := ({a, b, c} : Finset (Fin 8))) (W := ({p, u, v, w} : Finset (Fin 8)))
      hdisj (P := C) (Q := P) (R := R)
      (by simp [R, C, P, restrict_unionNamedProfiles_left])
      (by simp [R, C, P, restrict_unionNamedProfiles_right, hdisj])
    have hxInter : x ∈ f C ∩ f P := by
      exact Finset.mem_inter.mpr ⟨by simpa [C] using hxCycle, by simpa [P] using hxP2⟩
    exact hsub hxInter
  have hcast :
      f (castProfile (cycle_union_four_eq_sevenVoters a b c p u v w) R) =
        f R :=
    votingRule_castProfile (f := f) (cycle_union_four_eq_sevenVoters a b c p u v w) R
  have hxCast : x ∈ f (castProfile (cycle_union_four_eq_sevenVoters a b c p u v w) R) := by
    simpa [hcast] using hxR
  have hcw :
      CondorcetWinner
        (castProfile (cycle_union_four_eq_sevenVoters a b c p u v w) R)
        (prevCandidate x) := by
    simpa [R, C, P] using
      cast_union_cycle_p2_condorcetWinner_prev x hab hac hap hau hav haw hbc hbp hbu
        hbv hbw hcp hcu hcv hcw hpu hpv hpw huv huw hvw
  have hwin :
      f (castProfile (cycle_union_four_eq_sevenVoters a b c p u v w) R) =
        {prevCandidate x} :=
    hcond (castProfile (cycle_union_four_eq_sevenVoters a b c p u v w) R) (prevCandidate x) hcw
  have hxEq : x = prevCandidate x := by
    have hxSingleton : x ∈ ({prevCandidate x} : Finset (Fin 3)) := by
      simpa [hwin] using hxCast
    simpa using hxSingleton
  exact (prev_ne_self x) hxEq.symm

theorem cast_union_cycle_p3_condorcetWinner_prev
    (x : Fin 3) {a b c p u q w : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (hap : a ≠ p) (hau : a ≠ u) (haq : a ≠ q) (haw : a ≠ w)
    (hbc : b ≠ c) (hbp : b ≠ p) (hbu : b ≠ u) (hbq : b ≠ q) (hbw : b ≠ w)
    (hcp : c ≠ p) (hcu : c ≠ u) (hcq : c ≠ q) (hcw : c ≠ w)
    (hpu : p ≠ u) (hpq : p ≠ q) (hpw : p ≠ w)
    (huq : u ≠ q) (huw : u ≠ w) (hqw : q ≠ w) :
    CondorcetWinner
      (castProfile (cycle_union_four_eq_sevenVoters a b c p u q w)
        (unionNamedProfiles ({a, b, c} : Finset (Fin 8)) ({p, u, q, w} : Finset (Fin 8))
          (cycleNamedProfile x ({a, b, c} : Finset (Fin 8)) a b)
          (p3NamedProfile x ({p, u, q, w} : Finset (Fin 8)) q w)))
      (prevCandidate x) := by
  rw [cast_union_cycle_p3_eq_reindex_cyclePlusP3 x hab hac hap hau haq haw hbc hbp hbu
    hbq hbw hcp hcu hcq hcw hpu hpq hpw huq huw hqw]
  exact seven_reindex_cyclePlusP3_condorcetWinner_prev x hab hac hap hau haq haw hbc hbp hbu
    hbq hbw hcp hcu hcq hcw hpu hpq hpw huq huw hqw

theorem p3Named_not_mem_of_cycle_winner
    (f : VotingRule) (hcond : CondorcetConsistency f) (hrein : Reinforcement f)
    (x : Fin 3) {a b c p u q w : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (hap : a ≠ p) (hau : a ≠ u) (haq : a ≠ q) (haw : a ≠ w)
    (hbc : b ≠ c) (hbp : b ≠ p) (hbu : b ≠ u) (hbq : b ≠ q) (hbw : b ≠ w)
    (hcp : c ≠ p) (hcu : c ≠ u) (hcq : c ≠ q) (hcw : c ≠ w)
    (hpu : p ≠ u) (hpq : p ≠ q) (hpw : p ≠ w)
    (huq : u ≠ q) (huw : u ≠ w) (hqw : q ≠ w)
    (hxCycle : x ∈ f (cycleNamedProfile x ({a, b, c} : Finset (Fin 8)) a b)) :
    x ∉ f (p3NamedProfile x ({p, u, q, w} : Finset (Fin 8)) q w) := by
  classical
  intro hxP3
  let C : Profile (Electorate (Fin 8) ({a, b, c} : Finset (Fin 8))) (Fin 3) :=
    cycleNamedProfile x ({a, b, c} : Finset (Fin 8)) a b
  let P : Profile (Electorate (Fin 8) ({p, u, q, w} : Finset (Fin 8))) (Fin 3) :=
    p3NamedProfile x ({p, u, q, w} : Finset (Fin 8)) q w
  let R : Profile
      (Electorate (Fin 8) (({a, b, c} : Finset (Fin 8)) ∪ ({p, u, q, w} : Finset (Fin 8))))
      (Fin 3) :=
    unionNamedProfiles ({a, b, c} : Finset (Fin 8)) ({p, u, q, w} : Finset (Fin 8)) C P
  have hdisj : Disjoint ({a, b, c} : Finset (Fin 8)) ({p, u, q, w} : Finset (Fin 8)) := by
    rw [Finset.disjoint_left]
    intro r hrC hrP
    simp at hrC hrP
    rcases hrC with rfl | rfl | rfl <;> rcases hrP with rfl | rfl | rfl | rfl
    all_goals simp_all
  have hxR : x ∈ f R := by
    have hsub := reinforcement_subset hrein
      (V := ({a, b, c} : Finset (Fin 8))) (W := ({p, u, q, w} : Finset (Fin 8)))
      hdisj (P := C) (Q := P) (R := R)
      (by simp [R, C, P, restrict_unionNamedProfiles_left])
      (by simp [R, C, P, restrict_unionNamedProfiles_right, hdisj])
    have hxInter : x ∈ f C ∩ f P := by
      exact Finset.mem_inter.mpr ⟨by simpa [C] using hxCycle, by simpa [P] using hxP3⟩
    exact hsub hxInter
  have hcast :
      f (castProfile (cycle_union_four_eq_sevenVoters a b c p u q w) R) =
        f R :=
    votingRule_castProfile (f := f) (cycle_union_four_eq_sevenVoters a b c p u q w) R
  have hxCast : x ∈ f (castProfile (cycle_union_four_eq_sevenVoters a b c p u q w) R) := by
    simpa [hcast] using hxR
  have hcw :
      CondorcetWinner
        (castProfile (cycle_union_four_eq_sevenVoters a b c p u q w) R)
        (prevCandidate x) := by
    simpa [R, C, P] using
      cast_union_cycle_p3_condorcetWinner_prev x hab hac hap hau haq haw hbc hbp hbu
        hbq hbw hcp hcu hcq hcw hpu hpq hpw huq huw hqw
  have hwin :
      f (castProfile (cycle_union_four_eq_sevenVoters a b c p u q w) R) =
        {prevCandidate x} :=
    hcond (castProfile (cycle_union_four_eq_sevenVoters a b c p u q w) R) (prevCandidate x) hcw
  have hxEq : x = prevCandidate x := by
    have hxSingleton : x ∈ ({prevCandidate x} : Finset (Fin 3)) := by
      simpa [hwin] using hxCast
    simpa using hxSingleton
  exact (prev_ne_self x) hxEq.symm

/-- A one-voter named profile with ballot `y ≻ x ≻ z`. -/
def singletonYXZBallot (x : Fin 3) {u : Fin 8}
    (_v : Electorate (Fin 8) ({u} : Finset (Fin 8))) : ListBallot 3 :=
  ballotYXZ x

noncomputable def singletonYXZProfile (x : Fin 3) (u : Fin 8) :
    Profile (Electorate (Fin 8) ({u} : Finset (Fin 8))) (Fin 3) :=
  { pref := fun v => (singletonYXZBallot x v).toLinearOrder }

theorem singletonYXZ_condorcetWinner_next (x : Fin 3) (u : Fin 8) :
    CondorcetWinner (singletonYXZProfile x u) (nextCandidate x) := by
  classical
  intro d hd
  have hvoters (a b : Fin 3) :
      votersPreferring (singletonYXZProfile x u) a b =
        Finset.univ.filter
          (fun v => prefersInList (singletonYXZBallot x v).ranking a b) := by
    ext v
    simp only [votersPreferring, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold Prefers singletonYXZProfile prefersInList
    rw [ListBallot.lt_iff_idxOf]
    simp [decide_eq_true_eq]
  unfold StrictMajority
  rw [hvoters]
  fin_cases x <;> fin_cases d <;>
    simp_all [singletonYXZBallot, ballotYXZ, nextCandidate, prevCandidate,
      prefersInList, ListBallot.mk'] <;> norm_num

theorem cast_union_p2_singletonYXZ_eq_reindex_p2PlusYXZ
    (x : Fin 3) {p u v w yv : Fin 8}
    (hpu : p ≠ u) (hpv : p ≠ v) (hpw : p ≠ w) (hpy : p ≠ yv)
    (huv : u ≠ v) (huw : u ≠ w) (huy : u ≠ yv)
    (hvw : v ≠ w) (hvy : v ≠ yv) (hwy : w ≠ yv) :
    castProfile (four_union_singleton_eq_fiveVoters p u v w yv)
      (unionNamedProfiles ({p, u, v, w} : Finset (Fin 8)) ({yv} : Finset (Fin 8))
        (p2NamedProfile x ({p, u, v, w} : Finset (Fin 8)) p u)
        (singletonYXZProfile x yv)) =
      reindexVoters (p2PlusYXZProfile x)
        (fiveVoterEquiv hpu hpv hpw hpy huv huw huy hvw hvy hwy) := by
  apply Profile.ext
  intro r
  rcases r with ⟨r, hrmem⟩
  have hr : r = p ∨ r = u ∨ r = v ∨ r = w ∨ r = yv := by
    have hr' := hrmem
    change r ∈ ({p, u, v, w, yv} : Finset (Fin 8)) at hr'
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hr'
    exact hr'
  rcases hr with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [castProfile, unionNamedProfiles, reindexVoters, p2NamedProfile, p2NamedBallot,
      singletonYXZProfile, singletonYXZBallot, p2PlusYXZProfile, p2PlusYXZBallot,
      profileOfListBallots, fiveVoterEquiv, fiveVoterIndex, hpu, hpv, hpw, hpy,
      huv, huw, huy, hvw, hvy, hwy, hpu.symm, hpv.symm, hpw.symm, hpy.symm,
      huv.symm, huw.symm, huy.symm, hvw.symm, hvy.symm, hwy.symm] <;> rfl

theorem cast_union_p3_singletonYXZ_eq_reindex_p3PlusYXZ
    (x : Fin 3) {p u q w yv : Fin 8}
    (hpu : p ≠ u) (hpq : p ≠ q) (hpw : p ≠ w) (hpy : p ≠ yv)
    (huq : u ≠ q) (huw : u ≠ w) (huy : u ≠ yv)
    (hqw : q ≠ w) (hqy : q ≠ yv) (hwy : w ≠ yv) :
    castProfile (four_union_singleton_eq_fiveVoters p u q w yv)
      (unionNamedProfiles ({p, u, q, w} : Finset (Fin 8)) ({yv} : Finset (Fin 8))
        (p3NamedProfile x ({p, u, q, w} : Finset (Fin 8)) q w)
        (singletonYXZProfile x yv)) =
      reindexVoters (p3PlusYXZProfile x)
        (fiveVoterEquiv hpu hpq hpw hpy huq huw huy hqw hqy hwy) := by
  apply Profile.ext
  intro r
  rcases r with ⟨r, hrmem⟩
  have hr : r = p ∨ r = u ∨ r = q ∨ r = w ∨ r = yv := by
    have hr' := hrmem
    change r ∈ ({p, u, q, w, yv} : Finset (Fin 8)) at hr'
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hr'
    exact hr'
  rcases hr with rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [castProfile, unionNamedProfiles, reindexVoters, p3NamedProfile, p3NamedBallot,
      singletonYXZProfile, singletonYXZBallot, p3PlusYXZProfile, p3PlusYXZBallot,
      profileOfListBallots, fiveVoterEquiv, fiveVoterIndex, hpu, hpq, hpw, hpy,
      huq, huw, huy, hqw, hqy, hwy, hpu.symm, hpq.symm, hpw.symm, hpy.symm,
      huq.symm, huw.symm, huy.symm, hqw.symm, hqy.symm, hwy.symm] <;> rfl

theorem cast_union_p2_singletonYXZ_condorcetWinner
    (x : Fin 3) {p u v w yv : Fin 8}
    (hpu : p ≠ u) (hpv : p ≠ v) (hpw : p ≠ w) (hpy : p ≠ yv)
    (huv : u ≠ v) (huw : u ≠ w) (huy : u ≠ yv)
    (hvw : v ≠ w) (hvy : v ≠ yv) (hwy : w ≠ yv) :
    CondorcetWinner
      (castProfile (four_union_singleton_eq_fiveVoters p u v w yv)
        (unionNamedProfiles ({p, u, v, w} : Finset (Fin 8)) ({yv} : Finset (Fin 8))
          (p2NamedProfile x ({p, u, v, w} : Finset (Fin 8)) p u)
          (singletonYXZProfile x yv))) x := by
  rw [cast_union_p2_singletonYXZ_eq_reindex_p2PlusYXZ x hpu hpv hpw hpy huv huw huy
    hvw hvy hwy]
  exact five_reindex_p2PlusYXZ_condorcetWinner x hpu hpv hpw hpy huv huw huy hvw hvy hwy

theorem p2Named_not_next_of_singleton
    (f : VotingRule) (hcond : CondorcetConsistency f) (hrein : Reinforcement f)
    (x : Fin 3) {p u v w yv : Fin 8}
    (hpu : p ≠ u) (hpv : p ≠ v) (hpw : p ≠ w) (hpy : p ≠ yv)
    (huv : u ≠ v) (huw : u ≠ w) (huy : u ≠ yv)
    (hvw : v ≠ w) (hvy : v ≠ yv) (hwy : w ≠ yv) :
    nextCandidate x ∉ f (p2NamedProfile x ({p, u, v, w} : Finset (Fin 8)) p u) := by
  classical
  intro hyP2
  let P : Profile (Electorate (Fin 8) ({p, u, v, w} : Finset (Fin 8))) (Fin 3) :=
    p2NamedProfile x ({p, u, v, w} : Finset (Fin 8)) p u
  let Y : Profile (Electorate (Fin 8) ({yv} : Finset (Fin 8))) (Fin 3) :=
    singletonYXZProfile x yv
  let R : Profile
      (Electorate (Fin 8) (({p, u, v, w} : Finset (Fin 8)) ∪ ({yv} : Finset (Fin 8))))
      (Fin 3) :=
    unionNamedProfiles ({p, u, v, w} : Finset (Fin 8)) ({yv} : Finset (Fin 8)) P Y
  have hdisj : Disjoint ({p, u, v, w} : Finset (Fin 8)) ({yv} : Finset (Fin 8)) := by
    rw [Finset.disjoint_left]
    intro r hrP hrY
    simp at hrP hrY
    subst hrY
    rcases hrP with rfl | rfl | rfl | rfl <;> simp_all
  have hYwin : f Y = {nextCandidate x} := by
    simpa [Y] using hcond (singletonYXZProfile x yv) (nextCandidate x)
      (singletonYXZ_condorcetWinner_next x yv)
  have hyR : nextCandidate x ∈ f R := by
    have hsub := reinforcement_subset hrein
      (V := ({p, u, v, w} : Finset (Fin 8))) (W := ({yv} : Finset (Fin 8)))
      hdisj (P := P) (Q := Y) (R := R)
      (by simp [R, P, Y, restrict_unionNamedProfiles_left])
      (by simp [R, P, Y, restrict_unionNamedProfiles_right, hdisj])
    have hyInter : nextCandidate x ∈ f P ∩ f Y := by
      exact Finset.mem_inter.mpr ⟨by simpa [P] using hyP2, by simp [hYwin]⟩
    exact hsub hyInter
  have hcast :
      f (castProfile (four_union_singleton_eq_fiveVoters p u v w yv) R) = f R :=
    votingRule_castProfile (f := f) (four_union_singleton_eq_fiveVoters p u v w yv) R
  have hyCast :
      nextCandidate x ∈ f (castProfile (four_union_singleton_eq_fiveVoters p u v w yv) R) := by
    simpa [hcast] using hyR
  have hcw :
      CondorcetWinner
        (castProfile (four_union_singleton_eq_fiveVoters p u v w yv) R) x := by
    simpa [R, P, Y] using
      cast_union_p2_singletonYXZ_condorcetWinner x hpu hpv hpw hpy huv huw huy hvw hvy hwy
  have hwin :
      f (castProfile (four_union_singleton_eq_fiveVoters p u v w yv) R) = {x} :=
    hcond (castProfile (four_union_singleton_eq_fiveVoters p u v w yv) R) x hcw
  have hyEq : nextCandidate x = x := by
    have hySingleton : nextCandidate x ∈ ({x} : Finset (Fin 3)) := by
      simpa [hwin] using hyCast
    simpa using hySingleton
  exact (next_ne_self x) hyEq

theorem cast_union_p3_singletonYXZ_condorcetWinner
    (x : Fin 3) {p u q w yv : Fin 8}
    (hpu : p ≠ u) (hpq : p ≠ q) (hpw : p ≠ w) (hpy : p ≠ yv)
    (huq : u ≠ q) (huw : u ≠ w) (huy : u ≠ yv)
    (hqw : q ≠ w) (hqy : q ≠ yv) (hwy : w ≠ yv) :
    CondorcetWinner
      (castProfile (four_union_singleton_eq_fiveVoters p u q w yv)
        (unionNamedProfiles ({p, u, q, w} : Finset (Fin 8)) ({yv} : Finset (Fin 8))
          (p3NamedProfile x ({p, u, q, w} : Finset (Fin 8)) q w)
          (singletonYXZProfile x yv))) x := by
  rw [cast_union_p3_singletonYXZ_eq_reindex_p3PlusYXZ x hpu hpq hpw hpy huq huw huy
    hqw hqy hwy]
  exact five_reindex_p3PlusYXZ_condorcetWinner x hpu hpq hpw hpy huq huw huy hqw hqy hwy

theorem p3Named_not_next_of_singleton
    (f : VotingRule) (hcond : CondorcetConsistency f) (hrein : Reinforcement f)
    (x : Fin 3) {p u q w yv : Fin 8}
    (hpu : p ≠ u) (hpq : p ≠ q) (hpw : p ≠ w) (hpy : p ≠ yv)
    (huq : u ≠ q) (huw : u ≠ w) (huy : u ≠ yv)
    (hqw : q ≠ w) (hqy : q ≠ yv) (hwy : w ≠ yv) :
    nextCandidate x ∉ f (p3NamedProfile x ({p, u, q, w} : Finset (Fin 8)) q w) := by
  classical
  intro hyP3
  let P : Profile (Electorate (Fin 8) ({p, u, q, w} : Finset (Fin 8))) (Fin 3) :=
    p3NamedProfile x ({p, u, q, w} : Finset (Fin 8)) q w
  let Y : Profile (Electorate (Fin 8) ({yv} : Finset (Fin 8))) (Fin 3) :=
    singletonYXZProfile x yv
  let R : Profile
      (Electorate (Fin 8) (({p, u, q, w} : Finset (Fin 8)) ∪ ({yv} : Finset (Fin 8))))
      (Fin 3) :=
    unionNamedProfiles ({p, u, q, w} : Finset (Fin 8)) ({yv} : Finset (Fin 8)) P Y
  have hdisj : Disjoint ({p, u, q, w} : Finset (Fin 8)) ({yv} : Finset (Fin 8)) := by
    rw [Finset.disjoint_left]
    intro r hrP hrY
    simp at hrP hrY
    subst hrY
    rcases hrP with rfl | rfl | rfl | rfl <;> simp_all
  have hYwin : f Y = {nextCandidate x} := by
    simpa [Y] using hcond (singletonYXZProfile x yv) (nextCandidate x)
      (singletonYXZ_condorcetWinner_next x yv)
  have hyR : nextCandidate x ∈ f R := by
    have hsub := reinforcement_subset hrein
      (V := ({p, u, q, w} : Finset (Fin 8))) (W := ({yv} : Finset (Fin 8)))
      hdisj (P := P) (Q := Y) (R := R)
      (by simp [R, P, Y, restrict_unionNamedProfiles_left])
      (by simp [R, P, Y, restrict_unionNamedProfiles_right, hdisj])
    have hyInter : nextCandidate x ∈ f P ∩ f Y := by
      exact Finset.mem_inter.mpr ⟨by simpa [P] using hyP3, by simp [hYwin]⟩
    exact hsub hyInter
  have hcast :
      f (castProfile (four_union_singleton_eq_fiveVoters p u q w yv) R) = f R :=
    votingRule_castProfile (f := f) (four_union_singleton_eq_fiveVoters p u q w yv) R
  have hyCast :
      nextCandidate x ∈ f (castProfile (four_union_singleton_eq_fiveVoters p u q w yv) R) := by
    simpa [hcast] using hyR
  have hcw :
      CondorcetWinner
        (castProfile (four_union_singleton_eq_fiveVoters p u q w yv) R) x := by
    simpa [R, P, Y] using
      cast_union_p3_singletonYXZ_condorcetWinner x hpu hpq hpw hpy huq huw huy hqw hqy hwy
  have hwin :
      f (castProfile (four_union_singleton_eq_fiveVoters p u q w yv) R) = {x} :=
    hcond (castProfile (four_union_singleton_eq_fiveVoters p u q w yv) R) x hcw
  have hyEq : nextCandidate x = x := by
    have hySingleton : nextCandidate x ∈ ({x} : Finset (Fin 3)) := by
      simpa [hwin] using hyCast
    simpa using hySingleton
  exact (next_ne_self x) hyEq

theorem p2Named_eq_singleton_prev_of_cycle_winner
    (f : VotingRule) (hf : IsVotingRule f) (hcond : CondorcetConsistency f)
    (hrein : Reinforcement f) (x : Fin 3) {a b c p u v w yv : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (hap : a ≠ p) (hau : a ≠ u) (hav : a ≠ v) (haw : a ≠ w)
    (hbc : b ≠ c) (hbp : b ≠ p) (hbu : b ≠ u) (hbv : b ≠ v) (hbw : b ≠ w)
    (hcp : c ≠ p) (hcu : c ≠ u) (hcv : c ≠ v) (hcw : c ≠ w)
    (hpu : p ≠ u) (hpv : p ≠ v) (hpw : p ≠ w) (hpy : p ≠ yv)
    (huv : u ≠ v) (huw : u ≠ w) (huy : u ≠ yv)
    (hvw : v ≠ w) (hvy : v ≠ yv) (hwy : w ≠ yv)
    (hxCycle : x ∈ f (cycleNamedProfile x ({a, b, c} : Finset (Fin 8)) a b)) :
    f (p2NamedProfile x ({p, u, v, w} : Finset (Fin 8)) p u) = {prevCandidate x} := by
  classical
  apply fin3_eq_singleton_prev_of_nonempty_of_not_mem x
  · exact hf (p2NamedProfile x ({p, u, v, w} : Finset (Fin 8)) p u)
  · exact p2Named_not_mem_of_cycle_winner f hcond hrein x hab hac hap hau hav haw hbc hbp
      hbu hbv hbw hcp hcu hcv hcw hpu hpv hpw huv huw hvw hxCycle
  · exact p2Named_not_next_of_singleton f hcond hrein x hpu hpv hpw hpy huv huw huy hvw
      hvy hwy

theorem p3Named_eq_singleton_prev_of_cycle_winner
    (f : VotingRule) (hf : IsVotingRule f) (hcond : CondorcetConsistency f)
    (hrein : Reinforcement f) (x : Fin 3) {a b c p u q w yv : Fin 8}
    (hab : a ≠ b) (hac : a ≠ c) (hap : a ≠ p) (hau : a ≠ u) (haq : a ≠ q) (haw : a ≠ w)
    (hbc : b ≠ c) (hbp : b ≠ p) (hbu : b ≠ u) (hbq : b ≠ q) (hbw : b ≠ w)
    (hcp : c ≠ p) (hcu : c ≠ u) (hcq : c ≠ q) (hcw : c ≠ w)
    (hpu : p ≠ u) (hpq : p ≠ q) (hpw : p ≠ w) (hpy : p ≠ yv)
    (huq : u ≠ q) (huw : u ≠ w) (huy : u ≠ yv)
    (hqw : q ≠ w) (hqy : q ≠ yv) (hwy : w ≠ yv)
    (hxCycle : x ∈ f (cycleNamedProfile x ({a, b, c} : Finset (Fin 8)) a b)) :
    f (p3NamedProfile x ({p, u, q, w} : Finset (Fin 8)) q w) = {prevCandidate x} := by
  classical
  apply fin3_eq_singleton_prev_of_nonempty_of_not_mem x
  · exact hf (p3NamedProfile x ({p, u, q, w} : Finset (Fin 8)) q w)
  · exact p3Named_not_mem_of_cycle_winner f hcond hrein x hab hac hap hau haq haw hbc hbp
      hbu hbq hbw hcp hcu hcq hcw hpu hpq hpw huq huw hqw hxCycle
  · exact p3Named_not_next_of_singleton f hcond hrein x hpu hpq hpw hpy huq huw huy hqw
      hqy hwy

/-- Canonical cycle ballot assigned to a named voter in an ordered triple. -/
def canonicalCycleBallot (t : OrderedTriple8) (v : Electorate (Fin 8) t.support) :
    ListBallot 3 :=
  if v.1 = t.first then
    ballot012
  else if v.1 = t.second then
    ballot120
  else
    ballot201

/-- The canonical 3-voter cycle profile on the support of an ordered triple. -/
noncomputable def canonicalCycleProfile (t : OrderedTriple8) :
    Profile (Electorate (Fin 8) t.support) (Fin 3) :=
  { pref := fun v => (canonicalCycleBallot t v).toLinearOrder }

/-- The first named voter of an ordered triple as an electorate element. -/
def firstVoter (t : OrderedTriple8) : Electorate (Fin 8) t.support :=
  ⟨t.first, OrderedTriple8.first_mem_support t⟩

/-- The second named voter of an ordered triple as an electorate element. -/
def secondVoter (t : OrderedTriple8) : Electorate (Fin 8) t.support :=
  ⟨t.second, OrderedTriple8.second_mem_support t⟩

/-- The third named voter of an ordered triple as an electorate element. -/
def thirdVoter (t : OrderedTriple8) : Electorate (Fin 8) t.support :=
  ⟨t.third, OrderedTriple8.third_mem_support t⟩

/-- In the canonical cycle, the voter who ranks color `x` first. -/
def topVoter (x : Fin 3) (t : OrderedTriple8) : Fin 8 :=
  match x with
  | 0 => t.first
  | 1 => t.second
  | 2 => t.third

/-- In the canonical cycle, the voter who ranks color `x` last. -/
def bottomVoter (x : Fin 3) (t : OrderedTriple8) : Fin 8 :=
  match x with
  | 0 => t.second
  | 1 => t.third
  | 2 => t.first

/-- In the canonical cycle, the remaining voter for color `x`. -/
def middleVoter (x : Fin 3) (t : OrderedTriple8) : Fin 8 :=
  match x with
  | 0 => t.third
  | 1 => t.first
  | 2 => t.second

theorem distinguishedEdge_eq_top_bottom (x : Fin 3) (t : OrderedTriple8) :
    distinguishedEdge x t = (topVoter x t, bottomVoter x t) := by
  fin_cases x <;> rfl

theorem topVoter_mem_support (x : Fin 3) (t : OrderedTriple8) :
    topVoter x t ∈ t.support := by
  fin_cases x <;> simp [topVoter, OrderedTriple8.first_mem_support,
    OrderedTriple8.second_mem_support, OrderedTriple8.third_mem_support]

theorem bottomVoter_mem_support (x : Fin 3) (t : OrderedTriple8) :
    bottomVoter x t ∈ t.support := by
  fin_cases x <;> simp [bottomVoter, OrderedTriple8.first_mem_support,
    OrderedTriple8.second_mem_support, OrderedTriple8.third_mem_support]

theorem middleVoter_mem_support (x : Fin 3) (t : OrderedTriple8) :
    middleVoter x t ∈ t.support := by
  fin_cases x <;> simp [middleVoter, OrderedTriple8.first_mem_support,
    OrderedTriple8.second_mem_support, OrderedTriple8.third_mem_support]

theorem topVoter_ne_bottomVoter (x : Fin 3) (t : OrderedTriple8) :
    topVoter x t ≠ bottomVoter x t := by
  fin_cases x <;> simp [topVoter, bottomVoter, OrderedTriple8.first_ne_second,
    OrderedTriple8.second_ne_third, OrderedTriple8.third_ne_first]

theorem topVoter_ne_middleVoter (x : Fin 3) (t : OrderedTriple8) :
    topVoter x t ≠ middleVoter x t := by
  fin_cases x <;> simp [topVoter, middleVoter, OrderedTriple8.first_ne_third,
    OrderedTriple8.first_ne_second, OrderedTriple8.second_ne_third,
    (OrderedTriple8.first_ne_second t).symm, (OrderedTriple8.second_ne_third t).symm]

theorem bottomVoter_ne_middleVoter (x : Fin 3) (t : OrderedTriple8) :
    bottomVoter x t ≠ middleVoter x t := by
  fin_cases x <;> simp [bottomVoter, middleVoter, OrderedTriple8.second_ne_third,
    OrderedTriple8.first_ne_second, OrderedTriple8.third_ne_first,
    (OrderedTriple8.first_ne_third t).symm]

theorem support_eq_top_bottom_middle (x : Fin 3) (t : OrderedTriple8) :
    t.support = ({topVoter x t, bottomVoter x t, middleVoter x t} : Finset (Fin 8)) := by
  fin_cases x <;> ext v <;>
    simp [OrderedTriple8.support, topVoter, bottomVoter, middleVoter, or_assoc,
      or_left_comm, or_comm]

theorem edgeCrosses_iff_top_bottom (A : Finset (Fin 8)) (x : Fin 3) (t : OrderedTriple8) :
    edgeCrosses A (distinguishedEdge x t) ↔
      (topVoter x t ∈ A ∧ bottomVoter x t ∉ A) ∨
        (topVoter x t ∉ A ∧ bottomVoter x t ∈ A) := by
  rw [distinguishedEdge_eq_top_bottom]
  rfl

/-- The complementary 4-voter side of a witness partition. -/
def otherSide (A : Finset (Fin 8)) : Finset (Fin 8) :=
  (Finset.univ : Finset (Fin 8)) \ A

theorem mem_otherSide_iff (A : Finset (Fin 8)) (v : Fin 8) :
    v ∈ otherSide A ↔ v ∉ A := by
  simp [otherSide]

theorem otherSide_card {A : Finset (Fin 8)} (hA : A.card = 4) :
    (otherSide A).card = 4 := by
  rw [otherSide, Finset.card_sdiff, Finset.card_univ, Fintype.card_fin]
  simp [hA]

theorem support_subset_otherSide_of_forall_not_mem
    {A : Finset (Fin 8)} {t : OrderedTriple8}
    (ht : ∀ v ∈ t.support, v ∉ A) :
    t.support ⊆ otherSide A := by
  intro v hv
  exact (mem_otherSide_iff A v).mpr (ht v hv)

theorem exists_mem_notMem_support_of_card_four
    (S : Finset (Fin 8)) (hS : S.card = 4) (t : OrderedTriple8) :
    ∃ v, v ∈ S ∧ v ∉ t.support := by
  have hnot : ¬ S ⊆ t.support := by
    intro hsubset
    have hcard := Finset.card_le_card hsubset
    rw [hS, OrderedTriple8.support_card t] at hcard
    omega
  exact Finset.not_subset.mp hnot

theorem exists_four_eq_of_card_four_of_two_mem
    (S : Finset (Fin 8)) (hS : S.card = 4) (p r : Fin 8)
    (hp : p ∈ S) (hr : r ∈ S) (hpr : p ≠ r) :
    ∃ u d : Fin 8,
      S = ({p, u, r, d} : Finset (Fin 8)) ∧
      p ≠ u ∧ p ≠ d ∧ u ≠ r ∧ u ≠ d ∧ r ≠ d := by
  have hcardSp : (S.erase p).card = 3 := by
    rw [Finset.card_erase_of_mem hp, hS]
  have hrSp : r ∈ S.erase p := by
    exact Finset.mem_erase.mpr ⟨hpr.symm, hr⟩
  have hcardT : ((S.erase p).erase r).card = 2 := by
    rw [Finset.card_erase_of_mem hrSp, hcardSp]
  rcases Finset.card_eq_two.mp hcardT with ⟨u, d, hud, hT⟩
  have huT : u ∈ (S.erase p).erase r := by
    rw [hT]
    simp [hud]
  have hdT : d ∈ (S.erase p).erase r := by
    rw [hT]
    simp [hud]
  have huner : u ≠ r := (Finset.mem_erase.mp huT).1
  have hdner : d ≠ r := (Finset.mem_erase.mp hdT).1
  have huSp : u ∈ S.erase p := (Finset.mem_erase.mp huT).2
  have hdSp : d ∈ S.erase p := (Finset.mem_erase.mp hdT).2
  have hunep : u ≠ p := (Finset.mem_erase.mp huSp).1
  have hdnep : d ≠ p := (Finset.mem_erase.mp hdSp).1
  refine ⟨u, d, ?_, hunep.symm, hdnep.symm, huner, hud, hdner.symm⟩
  calc
    S = insert p (S.erase p) := (Finset.insert_erase hp).symm
    _ = insert p (insert r ((S.erase p).erase r)) := by rw [Finset.insert_erase hrSp]
    _ = ({p, u, r, d} : Finset (Fin 8)) := by
      rw [hT]
      ext s
      simp [or_assoc, or_left_comm, or_comm]

theorem exists_four_eq_of_card_four_of_one_mem
    (S : Finset (Fin 8)) (hS : S.card = 4) (q : Fin 8) (hq : q ∈ S) :
    ∃ a b e : Fin 8,
      S = ({q, a, b, e} : Finset (Fin 8)) ∧
      q ≠ a ∧ q ≠ b ∧ q ≠ e ∧ a ≠ b ∧ a ≠ e ∧ b ≠ e := by
  have hcardT : (S.erase q).card = 3 := by
    rw [Finset.card_erase_of_mem hq, hS]
  rcases Finset.card_eq_three.mp hcardT with ⟨a, b, e, hab, hae, hbe, hT⟩
  have haT : a ∈ S.erase q := by
    rw [hT]
    simp [hab, hae]
  have hbT : b ∈ S.erase q := by
    rw [hT]
    simp [hab, hbe]
  have heT : e ∈ S.erase q := by
    rw [hT]
    simp [hae, hbe]
  have hqa : q ≠ a := (Finset.mem_erase.mp haT).1.symm
  have hqb : q ≠ b := (Finset.mem_erase.mp hbT).1.symm
  have hqe : q ≠ e := (Finset.mem_erase.mp heT).1.symm
  refine ⟨a, b, e, ?_, hqa, hqb, hqe, hab, hae, hbe⟩
  calc
    S = insert q (S.erase q) := (Finset.insert_erase hq).symm
    _ = ({q, a, b, e} : Finset (Fin 8)) := by
      rw [hT]

theorem p2Named_eq_singleton_prev_of_disjoint_cycle
    (f : VotingRule) (hf : IsVotingRule f) (hcond : CondorcetConsistency f)
    (hrein : Reinforcement f) (x : Fin 3) {tC : OrderedTriple8}
    {p u v w yv : Fin 8}
    (hpu : p ≠ u) (hpv : p ≠ v) (hpw : p ≠ w) (hpy : p ≠ yv)
    (huv : u ≠ v) (huw : u ≠ w) (huy : u ≠ yv)
    (hvw : v ≠ w) (hvy : v ≠ yv) (hwy : w ≠ yv)
    (hdisj : ∀ z ∈ tC.support, z ∉ ({p, u, v, w} : Finset (Fin 8)))
    (hxCycle : x ∈ f (cycleNamedProfile x tC.support (topVoter x tC) (bottomVoter x tC))) :
    f (p2NamedProfile x ({p, u, v, w} : Finset (Fin 8)) p u) = {prevCandidate x} := by
  classical
  let a := topVoter x tC
  let b := bottomVoter x tC
  let c := middleVoter x tC
  have ha : a ∈ tC.support := by simp [a, topVoter_mem_support]
  have hb : b ∈ tC.support := by simp [b, bottomVoter_mem_support]
  have hc : c ∈ tC.support := by simp [c, middleVoter_mem_support]
  have hne_block : ∀ {z y : Fin 8}, z ∈ tC.support → y ∈ ({p, u, v, w} : Finset (Fin 8)) →
      z ≠ y := by
    intro z y hz hy hzy
    exact hdisj z hz (by simpa [hzy] using hy)
  have hxCycle' :
      x ∈ f (cycleNamedProfile x ({a, b, c} : Finset (Fin 8)) a b) := by
    change x ∈ f (cycleNamedProfile x
      ({topVoter x tC, bottomVoter x tC, middleVoter x tC} : Finset (Fin 8))
      (topVoter x tC) (bottomVoter x tC))
    rw [← support_eq_top_bottom_middle x tC]
    exact hxCycle
  exact p2Named_eq_singleton_prev_of_cycle_winner f hf hcond hrein x
    (by simp [a, b, topVoter_ne_bottomVoter])
    (by simp [a, c, topVoter_ne_middleVoter])
    (hne_block ha (by simp))
    (hne_block ha (by simp))
    (hne_block ha (by simp))
    (hne_block ha (by simp))
    (by simp [b, c, bottomVoter_ne_middleVoter])
    (hne_block hb (by simp))
    (hne_block hb (by simp))
    (hne_block hb (by simp))
    (hne_block hb (by simp))
    (hne_block hc (by simp))
    (hne_block hc (by simp))
    (hne_block hc (by simp))
    (hne_block hc (by simp))
    hpu hpv hpw hpy huv huw huy hvw hvy hwy hxCycle'

theorem p3Named_eq_singleton_prev_of_disjoint_cycle
    (f : VotingRule) (hf : IsVotingRule f) (hcond : CondorcetConsistency f)
    (hrein : Reinforcement f) (x : Fin 3) {tC : OrderedTriple8}
    {p u q w yv : Fin 8}
    (hpu : p ≠ u) (hpq : p ≠ q) (hpw : p ≠ w) (hpy : p ≠ yv)
    (huq : u ≠ q) (huw : u ≠ w) (huy : u ≠ yv)
    (hqw : q ≠ w) (hqy : q ≠ yv) (hwy : w ≠ yv)
    (hdisj : ∀ z ∈ tC.support, z ∉ ({p, u, q, w} : Finset (Fin 8)))
    (hxCycle : x ∈ f (cycleNamedProfile x tC.support (topVoter x tC) (bottomVoter x tC))) :
    f (p3NamedProfile x ({p, u, q, w} : Finset (Fin 8)) q w) = {prevCandidate x} := by
  classical
  let a := topVoter x tC
  let b := bottomVoter x tC
  let c := middleVoter x tC
  have ha : a ∈ tC.support := by simp [a, topVoter_mem_support]
  have hb : b ∈ tC.support := by simp [b, bottomVoter_mem_support]
  have hc : c ∈ tC.support := by simp [c, middleVoter_mem_support]
  have hne_block : ∀ {z y : Fin 8}, z ∈ tC.support → y ∈ ({p, u, q, w} : Finset (Fin 8)) →
      z ≠ y := by
    intro z y hz hy hzy
    exact hdisj z hz (by simpa [hzy] using hy)
  have hxCycle' :
      x ∈ f (cycleNamedProfile x ({a, b, c} : Finset (Fin 8)) a b) := by
    change x ∈ f (cycleNamedProfile x
      ({topVoter x tC, bottomVoter x tC, middleVoter x tC} : Finset (Fin 8))
      (topVoter x tC) (bottomVoter x tC))
    rw [← support_eq_top_bottom_middle x tC]
    exact hxCycle
  exact p3Named_eq_singleton_prev_of_cycle_winner f hf hcond hrein x
    (by simp [a, b, topVoter_ne_bottomVoter])
    (by simp [a, c, topVoter_ne_middleVoter])
    (hne_block ha (by simp))
    (hne_block ha (by simp))
    (hne_block ha (by simp))
    (hne_block ha (by simp))
    (by simp [b, c, bottomVoter_ne_middleVoter])
    (hne_block hb (by simp))
    (hne_block hb (by simp))
    (hne_block hb (by simp))
    (hne_block hb (by simp))
    (hne_block hc (by simp))
    (hne_block hc (by simp))
    (hne_block hc (by simp))
    (hne_block hc (by simp))
    hpu hpq hpw hpy huq huw huy hqw hqy hwy hxCycle'

@[simp] theorem canonicalCycleBallot_first (t : OrderedTriple8) :
    canonicalCycleBallot t (firstVoter t) = ballot012 := by
  simp [canonicalCycleBallot, firstVoter]

@[simp] theorem canonicalCycleBallot_second (t : OrderedTriple8) :
    canonicalCycleBallot t (secondVoter t) = ballot120 := by
  simp [canonicalCycleBallot, secondVoter, (OrderedTriple8.first_ne_second t).symm]

@[simp] theorem canonicalCycleBallot_third (t : OrderedTriple8) :
    canonicalCycleBallot t (thirdVoter t) = ballot201 := by
  simp [canonicalCycleBallot, thirdVoter, OrderedTriple8.third_ne_first t,
    (OrderedTriple8.second_ne_third t).symm]

@[simp] theorem canonicalCycleProfile_first_pref (t : OrderedTriple8) :
    (canonicalCycleProfile t).pref (firstVoter t) = ballot012.toLinearOrder := by
  simp [canonicalCycleProfile]

@[simp] theorem canonicalCycleProfile_second_pref (t : OrderedTriple8) :
    (canonicalCycleProfile t).pref (secondVoter t) = ballot120.toLinearOrder := by
  simp [canonicalCycleProfile]

@[simp] theorem canonicalCycleProfile_third_pref (t : OrderedTriple8) :
    (canonicalCycleProfile t).pref (thirdVoter t) = ballot201.toLinearOrder := by
  simp [canonicalCycleProfile]

theorem cycleNamedProfile_eq_canonical (x : Fin 3) (t : OrderedTriple8) :
    cycleNamedProfile x t.support (topVoter x t) (bottomVoter x t) =
      canonicalCycleProfile t := by
  apply Profile.ext
  intro v
  fin_cases x
  · have hballot :
        cycleNamedBallot 0 (topVoter 0 t) (bottomVoter 0 t) v =
          canonicalCycleBallot t v := by
      simp [cycleNamedBallot, canonicalCycleBallot, topVoter, bottomVoter]
    simpa [cycleNamedProfile, canonicalCycleProfile] using congrArg ListBallot.toLinearOrder hballot
  · have hballot :
        cycleNamedBallot 1 (topVoter 1 t) (bottomVoter 1 t) v =
      canonicalCycleBallot t v := by
      have hv : v.1 = t.first ∨ v.1 = t.second ∨ v.1 = t.third := by
        have hv' := v.2
        change v.1 ∈ ({t.first, t.second, t.third} : Finset (Fin 8)) at hv'
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hv'
        exact hv'
      rcases hv with hv | hv | hv
      · simp [cycleNamedBallot, canonicalCycleBallot, topVoter, bottomVoter, hv,
          OrderedTriple8.first_ne_second, OrderedTriple8.first_ne_third]
      · simp [cycleNamedBallot, canonicalCycleBallot, topVoter, hv,
          (OrderedTriple8.first_ne_second t).symm]
      · simp [cycleNamedBallot, canonicalCycleBallot, topVoter, bottomVoter, hv,
          OrderedTriple8.third_ne_first, (OrderedTriple8.second_ne_third t).symm]
    simpa [cycleNamedProfile, canonicalCycleProfile] using congrArg ListBallot.toLinearOrder hballot
  · have hballot :
        cycleNamedBallot 2 (topVoter 2 t) (bottomVoter 2 t) v =
      canonicalCycleBallot t v := by
      have hv : v.1 = t.first ∨ v.1 = t.second ∨ v.1 = t.third := by
        have hv' := v.2
        change v.1 ∈ ({t.first, t.second, t.third} : Finset (Fin 8)) at hv'
        rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hv'
        exact hv'
      rcases hv with hv | hv | hv
      · simp [cycleNamedBallot, canonicalCycleBallot, topVoter, bottomVoter, hv,
          OrderedTriple8.first_ne_third]
      · simp [cycleNamedBallot, canonicalCycleBallot, topVoter, bottomVoter, hv,
          (OrderedTriple8.first_ne_second t).symm, OrderedTriple8.second_ne_third]
      · simp [cycleNamedBallot, canonicalCycleBallot, topVoter, hv,
          (OrderedTriple8.first_ne_third t).symm, (OrderedTriple8.second_ne_third t).symm]
    simpa [cycleNamedProfile, canonicalCycleProfile] using congrArg ListBallot.toLinearOrder hballot

/-- The winner chosen from the canonical cycle profile for a total voting rule. -/
noncomputable def cycleColor (f : VotingRule) (hf : IsVotingRule f) :
    OrderedTriple8 → Fin 3 :=
  fun t => Classical.choose (hf (canonicalCycleProfile t))

theorem cycleColor_mem (f : VotingRule) (hf : IsVotingRule f) (t : OrderedTriple8) :
    cycleColor f hf t ∈ f (canonicalCycleProfile t) :=
  Classical.choose_spec (hf (canonicalCycleProfile t))

theorem cycleColor_mem_cycleNamed (f : VotingRule) (hf : IsVotingRule f) (t : OrderedTriple8) :
    cycleColor f hf t ∈
      f (cycleNamedProfile (cycleColor f hf t) t.support
        (topVoter (cycleColor f hf t) t) (bottomVoter (cycleColor f hf t) t)) := by
  rw [cycleNamedProfile_eq_canonical]
  exact cycleColor_mem f hf t

theorem cycleColor_eq_mem_cycleNamed
    (f : VotingRule) (hf : IsVotingRule f) {x : Fin 3} {t : OrderedTriple8}
    (hcolor : cycleColor f hf t = x) :
    x ∈ f (cycleNamedProfile x t.support (topVoter x t) (bottomVoter x t)) := by
  simpa [hcolor] using cycleColor_mem_cycleNamed f hf t

/-- Applying the finite identity-selection lemma to the coloring induced by a rule. -/
theorem exists_rule_identity_witness (f : VotingRule) (hf : IsVotingRule f) :
    hasGoodWitness (cycleColor f hf) :=
  identity_selection (cycleColor f hf)

theorem exists_rule_identity_witness_with_membership (f : VotingRule) (hf : IsVotingRule f) :
    ∃ x : Fin 3, ∃ A : Finset (Fin 8), ∃ tA tB t : OrderedTriple8,
      A.card = 4 ∧
        tA.support ⊆ A ∧
        (∀ v ∈ tB.support, v ∉ A) ∧
        x ∈ f (cycleNamedProfile x tA.support (topVoter x tA) (bottomVoter x tA)) ∧
        x ∈ f (cycleNamedProfile x tB.support (topVoter x tB) (bottomVoter x tB)) ∧
        x ∈ f (cycleNamedProfile x t.support (topVoter x t) (bottomVoter x t)) ∧
        edgeCrosses A (distinguishedEdge x t) := by
  rcases exists_rule_identity_witness f hf with
    ⟨x, A, tA, tB, t, hAcard, htA, htB, hcolorA, hcolorB, hcolor, hcross⟩
  refine ⟨x, A, tA, tB, t, hAcard, htA, htB, ?_, ?_, ?_, hcross⟩
  · exact cycleColor_eq_mem_cycleNamed f hf hcolorA
  · exact cycleColor_eq_mem_cycleNamed f hf hcolorB
  · exact cycleColor_eq_mem_cycleNamed f hf hcolor

theorem final_witness_top_left_middle_left_contradiction
    (f : VotingRule) (hf : IsVotingRule f) (hcond : CondorcetConsistency f)
    (hrein : Reinforcement f) {x : Fin 3} {A : Finset (Fin 8)}
    {tA tB t : OrderedTriple8}
    (hAcard : A.card = 4)
    (htA : tA.support ⊆ A)
    (htB : ∀ v ∈ tB.support, v ∉ A)
    (hxA : x ∈ f (cycleNamedProfile x tA.support (topVoter x tA) (bottomVoter x tA)))
    (hxB : x ∈ f (cycleNamedProfile x tB.support (topVoter x tB) (bottomVoter x tB)))
    (hxT : x ∈ f (cycleNamedProfile x t.support (topVoter x t) (bottomVoter x t)))
    (hpA : topVoter x t ∈ A) (hqNotA : bottomVoter x t ∉ A)
    (hrA : middleVoter x t ∈ A) :
    False := by
  classical
  let p := topVoter x t
  let q := bottomVoter x t
  let r := middleVoter x t
  have hpA' : p ∈ A := by simpa [p] using hpA
  have hqB : q ∈ otherSide A := (mem_otherSide_iff A q).mpr (by simpa [q] using hqNotA)
  have hrA' : r ∈ A := by simpa [r] using hrA
  have hpr : p ≠ r := by simpa [p, r] using topVoter_ne_middleVoter x t
  rcases exists_four_eq_of_card_four_of_two_mem A hAcard p r hpA' hrA' hpr with
    ⟨u, d, hAeq, hpu, hpd, hur, hud, hrd⟩
  rcases exists_four_eq_of_card_four_of_one_mem (otherSide A) (otherSide_card hAcard) q hqB with
    ⟨a, b, e, hBeq, hqa, hqb, hqe, hab, hae, hbe⟩
  have huA : u ∈ A := by rw [hAeq]; simp [hpu.symm, hur]
  have hdA : d ∈ A := by rw [hAeq]; simp [hpd.symm, hrd.symm, hud.symm]
  have haB : a ∈ otherSide A := by rw [hBeq]; simp [hqa.symm, hab]
  have hbB : b ∈ otherSide A := by rw [hBeq]; simp [hqb.symm, hab.symm, hbe]
  have heB : e ∈ otherSide A := by rw [hBeq]; simp [hqe.symm, hae.symm, hbe.symm]
  have hleft_right_ne {l s : Fin 8} (hl : l ∈ A) (hs : s ∈ otherSide A) : l ≠ s := by
    intro hls
    have hsnot : s ∉ A := (mem_otherSide_iff A s).mp hs
    exact hsnot (by simpa [hls] using hl)
  have hde' : d ≠ e := hleft_right_ne hdA heB
  have hP2 :
      f (p2NamedProfile x ({p, u, r, d} : Finset (Fin 8)) p u) =
        {prevCandidate x} := by
    have hdisj : ∀ z ∈ tB.support, z ∉ ({p, u, r, d} : Finset (Fin 8)) := by
      intro z hz hmem
      exact htB z hz (by simpa [hAeq] using hmem)
    exact p2Named_eq_singleton_prev_of_disjoint_cycle f hf hcond hrein x hpu hpr
      hpd (hleft_right_ne hpA' heB)
      hur hud (hleft_right_ne huA heB) hrd (hleft_right_ne hrA' heB)
      hde' hdisj hxB
  have hP3raw :
      f (p3NamedProfile x ({a, b, q, e} : Finset (Fin 8)) q e) =
        {prevCandidate x} := by
    have hdisj : ∀ z ∈ tA.support, z ∉ ({a, b, q, e} : Finset (Fin 8)) := by
      intro z hz hmem
      have hzA : z ∈ A := htA hz
      have hzB : z ∈ otherSide A := by
        rw [hBeq]
        simpa [or_assoc, or_left_comm, or_comm] using hmem
      exact ((mem_otherSide_iff A z).mp hzB) hzA
    exact p3Named_eq_singleton_prev_of_disjoint_cycle f hf hcond hrein x hab hqa.symm
      hae (hleft_right_ne hpA' haB).symm hqb.symm hbe
      (hleft_right_ne hpA' hbB).symm hqe (hleft_right_ne hpA' hqB).symm
      (hleft_right_ne hpA' heB).symm hdisj hxA
  have hP3 :
      f (p3NamedProfile x ({q, a, b, e} : Finset (Fin 8)) q e) =
        {prevCandidate x} := by
    have hset : ({a, b, q, e} : Finset (Fin 8)) = ({q, a, b, e} : Finset (Fin 8)) := by
      ext s
      simp [or_assoc, or_left_comm, or_comm]
    rw [← hset]
    exact hP3raw
  have hxT' :
      x ∈ f (cycleNamedProfile x ({p, q, r} : Finset (Fin 8)) p q) := by
    change x ∈ f (cycleNamedProfile x
      ({topVoter x t, bottomVoter x t, middleVoter x t} : Finset (Fin 8))
      (topVoter x t) (bottomVoter x t))
    rw [← support_eq_top_bottom_middle x t]
    exact hxT
  exact finalProfile_middle_left_contradiction f hcond hrein x
    (by simpa [p, q] using topVoter_ne_bottomVoter x t)
    hpr hpu
    (hleft_right_ne hpA' haB) (hleft_right_ne hpA' hbB) hpd (hleft_right_ne hpA' heB)
    (by simpa [q, r] using bottomVoter_ne_middleVoter x t)
    (hleft_right_ne huA hqB).symm hqa hqb (hleft_right_ne hdA hqB).symm hqe
    hur.symm (hleft_right_ne hrA' haB) (hleft_right_ne hrA' hbB) hrd (hleft_right_ne hrA' heB)
    (hleft_right_ne huA haB) (hleft_right_ne huA hbB) hud (hleft_right_ne huA heB)
    hab (hleft_right_ne hdA haB).symm hae
    (hleft_right_ne hdA hbB).symm hbe hde'
    hP2 hP3 hxT'

theorem final_witness_top_left_middle_right_contradiction
    (f : VotingRule) (hf : IsVotingRule f) (hcond : CondorcetConsistency f)
    (hrein : Reinforcement f) {x : Fin 3} {A : Finset (Fin 8)}
    {tA tB t : OrderedTriple8}
    (hAcard : A.card = 4)
    (htA : tA.support ⊆ A)
    (htB : ∀ v ∈ tB.support, v ∉ A)
    (hxA : x ∈ f (cycleNamedProfile x tA.support (topVoter x tA) (bottomVoter x tA)))
    (hxB : x ∈ f (cycleNamedProfile x tB.support (topVoter x tB) (bottomVoter x tB)))
    (hxT : x ∈ f (cycleNamedProfile x t.support (topVoter x t) (bottomVoter x t)))
    (hpA : topVoter x t ∈ A) (hqNotA : bottomVoter x t ∉ A)
    (hrNotA : middleVoter x t ∉ A) :
    False := by
  classical
  let p := topVoter x t
  let q := bottomVoter x t
  let r := middleVoter x t
  have hpA' : p ∈ A := by simpa [p] using hpA
  have hqB : q ∈ otherSide A := (mem_otherSide_iff A q).mpr (by simpa [q] using hqNotA)
  have hrB : r ∈ otherSide A := (mem_otherSide_iff A r).mpr (by simpa [r] using hrNotA)
  rcases exists_four_eq_of_card_four_of_one_mem A hAcard p hpA' with
    ⟨u, d, e, hAeq, hpu, hpd, hpe, hud, hue, hde⟩
  have hqr : q ≠ r := by simpa [q, r] using bottomVoter_ne_middleVoter x t
  rcases exists_four_eq_of_card_four_of_two_mem (otherSide A) (otherSide_card hAcard) q r hqB hrB hqr with
    ⟨a, b, hBeq, hqa, hqb, har, hab, hrb⟩
  have huA : u ∈ A := by rw [hAeq]; simp [hpu.symm, hud]
  have hdA : d ∈ A := by rw [hAeq]; simp [hpd.symm, hud.symm, hde]
  have heA : e ∈ A := by rw [hAeq]; simp [hpe.symm, hue.symm, hde.symm]
  have haB : a ∈ otherSide A := by rw [hBeq]; simp [hqa.symm, har]
  have hbB : b ∈ otherSide A := by rw [hBeq]; simp [hqb.symm, hab.symm, hrb]
  have hleft_right_ne {l s : Fin 8} (hl : l ∈ A) (hs : s ∈ otherSide A) : l ≠ s := by
    intro hls
    have hsnot : s ∉ A := (mem_otherSide_iff A s).mp hs
    exact hsnot (by simpa [hls] using hl)
  have hP2 :
      f (p2NamedProfile x ({p, u, d, e} : Finset (Fin 8)) p u) =
        {prevCandidate x} := by
    have hdisj : ∀ z ∈ tB.support, z ∉ ({p, u, d, e} : Finset (Fin 8)) := by
      intro z hz hmem
      exact htB z hz (by simpa [hAeq] using hmem)
    exact p2Named_eq_singleton_prev_of_disjoint_cycle f hf hcond hrein x hpu hpd
      hpe (hleft_right_ne hpA' hqB) hud hue (hleft_right_ne huA hqB)
      hde (hleft_right_ne hdA hqB) (hleft_right_ne heA hqB) hdisj hxB
  have hP3raw :
      f (p3NamedProfile x ({a, b, q, r} : Finset (Fin 8)) q r) =
        {prevCandidate x} := by
    have hdisj : ∀ z ∈ tA.support, z ∉ ({a, b, q, r} : Finset (Fin 8)) := by
      intro z hz hmem
      have hzA : z ∈ A := htA hz
      have hzB : z ∈ otherSide A := by
        rw [hBeq]
        simpa [or_assoc, or_left_comm, or_comm] using hmem
      exact ((mem_otherSide_iff A z).mp hzB) hzA
    exact p3Named_eq_singleton_prev_of_disjoint_cycle f hf hcond hrein x hab hqa.symm
      har (hleft_right_ne hpA' haB).symm hqb.symm hrb.symm
      (hleft_right_ne hpA' hbB).symm hqr (hleft_right_ne hpA' hqB).symm
      (hleft_right_ne hpA' hrB).symm hdisj hxA
  have hP3 :
      f (p3NamedProfile x ({q, r, a, b} : Finset (Fin 8)) q r) =
        {prevCandidate x} := by
    have hset : ({a, b, q, r} : Finset (Fin 8)) = ({q, r, a, b} : Finset (Fin 8)) := by
      ext s
      simp [or_assoc, or_left_comm, or_comm]
    rw [← hset]
    exact hP3raw
  have hxT' :
      x ∈ f (cycleNamedProfile x ({p, q, r} : Finset (Fin 8)) p q) := by
    change x ∈ f (cycleNamedProfile x
      ({topVoter x t, bottomVoter x t, middleVoter x t} : Finset (Fin 8))
      (topVoter x t) (bottomVoter x t))
    rw [← support_eq_top_bottom_middle x t]
    exact hxT
  exact finalProfile_middle_right_contradiction f hcond hrein x
    (by simpa [p, q] using topVoter_ne_bottomVoter x t)
    (hleft_right_ne hpA' hrB) hpu
    (hleft_right_ne hpA' haB) (hleft_right_ne hpA' hbB) hpd hpe
    hqr (hleft_right_ne huA hqB).symm hqa hqb (hleft_right_ne hdA hqB).symm
    (hleft_right_ne heA hqB).symm
    (hleft_right_ne huA hrB).symm har.symm hrb (hleft_right_ne hdA hrB).symm
    (hleft_right_ne heA hrB).symm
    (hleft_right_ne huA haB) (hleft_right_ne huA hbB) hud hue
    hab (hleft_right_ne hdA haB).symm (hleft_right_ne heA haB).symm
    (hleft_right_ne hdA hbB).symm (hleft_right_ne heA hbB).symm hde
    hP2 hP3 hxT'

/-- The n=8 Condorcet-reinforcement impossibility statement. -/
def CondorcetReinforcementN8Impossible : Prop :=
  ∀ (f : VotingRule), IsVotingRule f → CondorcetConsistency f → Reinforcement f → False

theorem condorcetReinforcementN8_impossible : CondorcetReinforcementN8Impossible := by
  intro f hf hcond hrein
  rcases exists_rule_identity_witness_with_membership f hf with
    ⟨x, A, tA, tB, t, hAcard, htA, htB, hxA, hxB, hxT, hcross⟩
  rcases (edgeCrosses_iff_top_bottom A x t).mp hcross with htopLeft | htopRight
  · rcases htopLeft with ⟨hpA, hqNotA⟩
    by_cases hrA : middleVoter x t ∈ A
    · exact final_witness_top_left_middle_left_contradiction f hf hcond hrein hAcard
        htA htB hxA hxB hxT hpA hqNotA hrA
    · exact final_witness_top_left_middle_right_contradiction f hf hcond hrein hAcard
        htA htB hxA hxB hxT hpA hqNotA hrA
  · rcases htopRight with ⟨hpNotA, hqA⟩
    let B : Finset (Fin 8) := otherSide A
    have hBcard : B.card = 4 := by
      simpa [B] using otherSide_card hAcard
    have htBsub : tB.support ⊆ B := by
      simpa [B] using support_subset_otherSide_of_forall_not_mem htB
    have htAnotB : ∀ v ∈ tA.support, v ∉ B := by
      intro v hv hvB
      have hvNotA : v ∉ A := (mem_otherSide_iff A v).mp (by simpa [B] using hvB)
      exact hvNotA (htA hv)
    have hpB : topVoter x t ∈ B := by
      simpa [B] using (mem_otherSide_iff A (topVoter x t)).mpr hpNotA
    have hqNotB : bottomVoter x t ∉ B := by
      intro hqB
      have hqNotA : bottomVoter x t ∉ A :=
        (mem_otherSide_iff A (bottomVoter x t)).mp (by simpa [B] using hqB)
      exact hqNotA hqA
    by_cases hrB : middleVoter x t ∈ B
    · exact final_witness_top_left_middle_left_contradiction f hf hcond hrein hBcard
        htBsub htAnotB hxB hxA hxT hpB hqNotB hrB
    · exact final_witness_top_left_middle_right_contradiction f hf hcond hrein hBcard
        htBsub htAnotB hxB hxA hxT hpB hqNotB hrB

end Main
end CondorcetReinforcementN8
end SocialChoice
