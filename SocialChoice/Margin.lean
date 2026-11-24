import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import SocialChoice.Profile
import SocialChoice.Axioms.Participation
import SocialChoice.Axioms.Reversal

namespace SocialChoice

open Finset

noncomputable def margin {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) : Int := by
  classical
  exact
    Int.ofNat ((Finset.univ.filter (fun v => Prefers P v a b)).card) -
      Int.ofNat ((Finset.univ.filter (fun v => Prefers P v b a)).card)

def margin_pos {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) : Prop :=
  0 < margin P a b

@[simp] lemma prefers_permuteCandidates_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) (v : V) (a b : A) :
    Prefers (permuteCandidates P σ) v a b ↔ Prefers P v (σ.symm a) (σ.symm b) := by
  rfl

@[simp] lemma prefers_relabelProfile_iff {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
    (P : Profile V A) (e : A ≃ B) (v : V) (a b : B) :
    Prefers (relabelProfile P e) v a b ↔ Prefers P v (e.symm a) (e.symm b) := by
  rfl

@[simp] lemma margin_permuteCandidates {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) (a b : A) :
    margin (permuteCandidates P σ) a b = margin P (σ.symm a) (σ.symm b) := by
  classical
  simp [margin]

/-- Margins do not depend on how voters are labelled: relabelling the electorate along an
equivalence preserves every margin. -/
lemma margin_eq_of_equiv {V W A : Type} [Fintype V] [Fintype W] [Fintype A]
    (P : Profile V A) (Q : Profile W A) (e : V ≃ W) (h : ∀ v, Q.pref (e v) = P.pref v)
    (a b : A) : margin Q a b = margin P a b := by
  classical
  have key : ∀ x y : A, (univ.filter fun w => Prefers Q w x y).card =
      (univ.filter fun v => Prefers P v x y).card := by
    intro x y
    simp only [card_filter]
    rw [← Equiv.sum_comp e]
    exact Finset.sum_congr rfl fun v _ => by unfold Prefers; rw [h v]
  simp only [margin, key]

@[simp] lemma margin_permuteVoters {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm V) (a b : A) :
    margin (permuteVoters P σ) a b = margin P a b :=
  margin_eq_of_equiv P _ σ.symm (fun v => by simp [permuteVoters]) a b

@[simp] lemma margin_relabelProfile {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
    (P : Profile V A) (e : A ≃ B) (a b : B) :
    margin (relabelProfile P e) a b = margin P (e.symm a) (e.symm b) := by
  classical
  simp [margin]

@[simp] lemma margin_pos_permuteCandidates_iff {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (σ : Equiv.Perm A) (a b : A) :
    margin_pos (permuteCandidates P σ) a b ↔ margin_pos P (σ.symm a) (σ.symm b) := by
  simp [margin_pos]

@[simp] lemma margin_pos_relabelProfile_iff {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
    (P : Profile V A) (e : A ≃ B) (a b : B) :
    margin_pos (relabelProfile P e) a b ↔ margin_pos P (e.symm a) (e.symm b) := by
  simp [margin_pos]

def skew_symmetric {A : Type} (M : A -> A -> Int) : Prop :=
  forall a b, M a b = -(M b a)

theorem margin_antisymmetric {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) : skew_symmetric (margin P) := by
  classical
  intro a b
  dsimp [margin, skew_symmetric]
  ring

theorem self_margin_zero {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a : A) : margin P a a = 0 := by
  classical
  dsimp [margin]
  simp

theorem ne_of_margin_pos {V A : Type} [Fintype V] [Fintype A]
    {P : Profile V A} {a b : A} (h : margin_pos P a b) : a ≠ b := by
  intro hEq
  subst hEq
  have h0 : (0 : Int) < 0 := by
    simp [margin_pos, self_margin_zero] at h
  exact (lt_irrefl 0 h0)

lemma unanimous_margin_eq_card {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (x y : A) :
    (∀ v : V, Prefers P v x y) → margin P x y = (Fintype.card V : Int) := by
  classical
  intro hxy
  have hxy' : univ.filter (fun v => Prefers P v x y) = univ :=
    filter_true_of_mem fun v _ => hxy v
  have hyx' : univ.filter (fun v => Prefers P v y x) = ∅ :=
    filter_false_of_mem fun v _ => @lt_asymm A (P.pref v).toPreorder x y (hxy v)
  simp [margin, hxy', hyx']

lemma unanimous_margin {V A : Type} [Fintype V] [Fintype A] [Nonempty V]
    (P : Profile V A) (x y : A) :
    (∀ v : V, Prefers P v x y) → margin_pos P x y := by
  intro hxy
  rw [margin_pos, unanimous_margin_eq_card P x y hxy]
  exact_mod_cast Fintype.card_pos

lemma margin_reverse_eq {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) :
    margin (reverse_profile P) b a = margin P a b := by
  classical
  simp [margin, prefers_reverse_profile]

lemma margin_le_card {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) :
    margin P a b ≤ (Fintype.card V : Int) := by
  classical
  have := card_le_univ (univ.filter fun v => Prefers P v a b)
  simp only [margin, Int.ofNat_eq_natCast]
  omega

lemma unanimous_of_margin_ge_card {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (a b : A) :
    (Fintype.card V : Int) ≤ margin P a b → ∀ v : V, Prefers P v a b := by
  classical
  intro hle v
  by_contra hnot
  have hlt : (univ.filter fun v => Prefers P v a b).card < Fintype.card V :=
    card_lt_univ_of_notMem (x := v) (by simp [hnot])
  simp only [margin, Int.ofNat_eq_natCast] at hle
  omega

lemma margin_pos_irrefl {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) : ∀ x, ¬ margin_pos P x x := by
  intro x
  simp [margin_pos, self_margin_zero]

lemma margin_pos_asymm {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) : ∀ x y, margin_pos P x y → ¬ margin_pos P y x := by
  intro x y hxy hyx
  rw [margin_pos] at hxy hyx
  linarith [margin_antisymmetric P x y]

@[simp] lemma prefers_addVoter_inl {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (ballot : LinearOrder A) (v : V) (a b : A) :
    Prefers (addVoter P ballot) (Sum.inl v) a b ↔ Prefers P v a b := Iff.rfl

@[simp] lemma prefers_addVoter_inr {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (ballot : LinearOrder A) (u : Unit) (a b : A) :
    Prefers (addVoter P ballot) (Sum.inr u) a b ↔ ballot.lt a b := Iff.rfl

@[simp] lemma prefers_unionProfiles_inl {V W A : Type} [Fintype V] [Fintype W] [Fintype A]
    (P : Profile V A) (Q : Profile W A) (v : V) (a b : A) :
    Prefers (unionProfiles P Q) (Sum.inl v) a b ↔ Prefers P v a b := Iff.rfl

@[simp] lemma prefers_unionProfiles_inr {V W A : Type} [Fintype V] [Fintype W] [Fintype A]
    (P : Profile V A) (Q : Profile W A) (w : W) (a b : A) :
    Prefers (unionProfiles P Q) (Sum.inr w) a b ↔ Prefers Q w a b := Iff.rfl

/-- Counting the elements of a sum type that satisfy `p` splits along the two summands. -/
lemma card_filter_univ_sum {V W : Type} [Fintype V] [Fintype W]
    (p : V ⊕ W → Prop) [DecidablePred p] :
    (univ.filter p).card =
      (univ.filter fun v => p (Sum.inl v)).card + (univ.filter fun w => p (Sum.inr w)).card := by
  simp only [card_filter, Fintype.sum_sum_type]

lemma margin_addVoter_eq_of_prefers {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (ballot : LinearOrder A) (a b : A) (h : ballot.lt a b) :
    margin (addVoter P ballot) a b = margin P a b + 1 := by
  classical
  have hba : ¬ ballot.lt b a := fun hba => (@lt_asymm A _ a b h) hba
  simp [margin, card_filter_univ_sum, h, hba]
  ring

lemma margin_addVoter_eq_of_prefers_rev {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (ballot : LinearOrder A) (a b : A) (h : ballot.lt b a) :
    margin (addVoter P ballot) a b = margin P a b - 1 := by
  have h1 := margin_addVoter_eq_of_prefers P ballot b a h
  have h2 := margin_antisymmetric (addVoter P ballot) a b
  have h3 := margin_antisymmetric P a b
  linarith

lemma margin_le_addVoter {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (ballot : LinearOrder A) (a b : A) :
    margin P a b ≤ margin (addVoter P ballot) a b + 1 := by
  rcases eq_or_ne a b with rfl | hab
  · simp [self_margin_zero]
  rcases @lt_or_gt_of_ne A ballot a b hab with h | h
  · linarith [margin_addVoter_eq_of_prefers P ballot a b h]
  · linarith [margin_addVoter_eq_of_prefers_rev P ballot a b h]

lemma margin_addVoter_le {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (ballot : LinearOrder A) (a b : A) :
    margin (addVoter P ballot) a b ≤ margin P a b + 1 := by
  rcases eq_or_ne a b with rfl | hab
  · simp [self_margin_zero]
  rcases @lt_or_gt_of_ne A ballot a b hab with h | h
  · linarith [margin_addVoter_eq_of_prefers P ballot a b h]
  · linarith [margin_addVoter_eq_of_prefers_rev P ballot a b h]

/-- Adding a new voter to an electorate `V` has the same effect on margins as `addVoter`. -/
lemma margin_add_newVoter_eq_margin_addVoter {U A : Type} [DecidableEq U] [Fintype A]
    {V : Finset U} {u : U} (hu : u ∉ V)
    (P : Profile (Electorate U V) A)
    (Q : Profile (Electorate U (insert u V)) A)
    (hagree : ∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v) (a b : A) :
    margin Q a b = margin (addVoter P (Q.pref (newVoter u hu))) a b :=
  margin_eq_of_equiv _ Q (insertElectorateEquiv hu)
    (by rintro (v | ⟨⟩) <;> simp [addVoter, hagree]) a b

lemma margin_add_newVoter_eq_of_prefers {U A : Type} [DecidableEq U] [Fintype A]
    {V : Finset U} {u : U} (hu : u ∉ V)
    (P : Profile (Electorate U V) A)
    (Q : Profile (Electorate U (insert u V)) A)
    (hagree : ∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v)
    (a b : A) (h : (Q.pref (newVoter (u := u) (V := V) hu)).lt a b) :
    margin Q a b = margin P a b + 1 := by
  rw [margin_add_newVoter_eq_margin_addVoter hu P Q hagree]
  exact margin_addVoter_eq_of_prefers P _ a b h

lemma margin_add_newVoter_eq_of_prefers_rev {U A : Type} [DecidableEq U] [Fintype A]
    {V : Finset U} {u : U} (hu : u ∉ V)
    (P : Profile (Electorate U V) A)
    (Q : Profile (Electorate U (insert u V)) A)
    (hagree : ∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v)
    (a b : A) (h : (Q.pref (newVoter (u := u) (V := V) hu)).lt b a) :
    margin Q a b = margin P a b - 1 := by
  rw [margin_add_newVoter_eq_margin_addVoter hu P Q hagree]
  exact margin_addVoter_eq_of_prefers_rev P _ a b h

lemma margin_le_add_newVoter {U A : Type} [DecidableEq U] [Fintype A]
    {V : Finset U} {u : U} (hu : u ∉ V)
    (P : Profile (Electorate U V) A)
    (Q : Profile (Electorate U (insert u V)) A)
    (hagree : ∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v)
    (a b : A) :
    margin P a b ≤ margin Q a b + 1 := by
  rw [margin_add_newVoter_eq_margin_addVoter hu P Q hagree]
  exact margin_le_addVoter P _ a b

lemma margin_add_newVoter_le {U A : Type} [DecidableEq U] [Fintype A]
    {V : Finset U} {u : U} (hu : u ∉ V)
    (P : Profile (Electorate U V) A)
    (Q : Profile (Electorate U (insert u V)) A)
    (hagree : ∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v)
    (a b : A) :
    margin Q a b ≤ margin P a b + 1 := by
  rw [margin_add_newVoter_eq_margin_addVoter hu P Q hagree]
  exact margin_addVoter_le P _ a b

/-- The margin is the number of voters preferring `a` to `b` minus the number preferring `b`
to `a`. -/
lemma margin_eq_card_diff {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) (a b : A) :
    margin P a b =
      Int.ofNat (votersPreferring P a b).card - Int.ofNat (votersPreferring P b a).card := by
  classical
  simp [margin, votersPreferring]

lemma margin_lemma {V A : Type} [Fintype V] [Fintype A]
    (P P' : Profile V A) (a b : A) (_ : a ≠ b) :
    (∀ v : V, (Prefers P v a b → Prefers P' v a b) ∧
      (Prefers P' v b a → Prefers P v b a)) →
    margin P a b ≤ margin P' a b := by
  classical
  intro lift
  have h1 := card_le_card (monotone_filter_right univ fun v _ h => (lift v).1 h)
  have h2 := card_le_card (monotone_filter_right univ fun v _ h => (lift v).2 h)
  simp only [margin, Int.ofNat_eq_natCast]
  omega

lemma margin_eq_margin_restrictProfile {V A : Type} [Fintype V] [Fintype A] [DecidableEq A]
    {P : Profile V A} {c : A} {a b : {x : A // x ≠ c}} :
    margin P a b = margin (restrictProfile P c) a b := by
  classical
  have h1 :
      (Finset.univ.filter (fun v => Prefers P v a b)).card =
        (Finset.univ.filter (fun v => Prefers (restrictProfile P c) v a b)).card := by
    refine cardinality_lemma2 (p := fun v => Prefers P v a b)
      (q := fun v => Prefers (restrictProfile P c) v a b) ?_
    intro v
    simp
  have h2 :
      (Finset.univ.filter (fun v => Prefers P v b a)).card =
        (Finset.univ.filter (fun v => Prefers (restrictProfile P c) v b a)).card := by
    refine cardinality_lemma2 (p := fun v => Prefers P v b a)
      (q := fun v => Prefers (restrictProfile P c) v b a) ?_
    intro v
    simp
  dsimp [margin]
  simp [h1, h2]

lemma margin_eq_margin_restrictCandidates {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (p : A → Prop) [DecidablePred p]
    {a b : {x : A // p x}} :
    margin P a b = margin (restrictCandidates P p) a b := by
  classical
  have h1 :
      (Finset.univ.filter (fun v => Prefers P v a b)).card =
        (Finset.univ.filter (fun v => Prefers (restrictCandidates P p) v a b)).card := by
    refine cardinality_lemma2 (p := fun v => Prefers P v a b)
      (q := fun v => Prefers (restrictCandidates P p) v a b) ?_
    intro v
    simp
  have h2 :
      (Finset.univ.filter (fun v => Prefers P v b a)).card =
        (Finset.univ.filter (fun v => Prefers (restrictCandidates P p) v b a)).card := by
    refine cardinality_lemma2 (p := fun v => Prefers P v b a)
      (q := fun v => Prefers (restrictCandidates P p) v b a) ?_
    intro v
    simp
  dsimp [margin]
  simp [h1, h2]

/-! ### Constant profiles and unions -/

lemma margin_constantProfile_of_lt {V A : Type} [Fintype V] [Fintype A]
    (r : LinearOrder A) {a b : A} (h : r.lt a b) :
    margin (constantProfile (V := V) (A := A) r) a b = (Fintype.card V : Int) := by
  classical
  apply unanimous_margin_eq_card
  intro v
  simp [Prefers]
  exact h

lemma margin_constantProfile_of_gt {V A : Type} [Fintype V] [Fintype A]
    (r : LinearOrder A) {a b : A} (h : r.lt b a) :
    margin (constantProfile (V := V) (A := A) r) a b = -(Fintype.card V : Int) := by
  classical
  have hba :
      margin (constantProfile (V := V) (A := A) r) b a = (Fintype.card V : Int) :=
    margin_constantProfile_of_lt (V := V) (A := A) r h
  have hskew :
      margin (constantProfile (V := V) (A := A) r) a b =
        - margin (constantProfile (V := V) (A := A) r) b a := by
    simpa [skew_symmetric] using
      (margin_antisymmetric (P := constantProfile (V := V) (A := A) r)) a b
  calc
    margin (constantProfile (V := V) (A := A) r) a b =
        - margin (constantProfile (V := V) (A := A) r) b a := hskew
    _ = -(Fintype.card V : Int) := by simp [hba]

lemma card_votersPreferring_unionProfiles {V W A : Type} [Fintype V] [Fintype W] [Fintype A]
    (P : Profile V A) (Q : Profile W A) (a b : A) :
    (votersPreferring (unionProfiles P Q) a b).card =
      (votersPreferring P a b).card + (votersPreferring Q a b).card := by
  classical
  simp [votersPreferring, card_filter_univ_sum]

lemma margin_unionProfiles {V W A : Type} [Fintype V] [Fintype W] [Fintype A]
    (P : Profile V A) (Q : Profile W A) (a b : A) :
    margin (unionProfiles P Q) a b = margin P a b + margin Q a b := by
  classical
  simp [margin, card_filter_univ_sum]
  ring

end SocialChoice
