import SocialChoice.Profile
import SocialChoice.Axioms.Core
import SocialChoice.SetExtensions
import SocialChoice.Meta

namespace SocialChoice

abbrev Electorate (U : Type) (S : Finset U) := {u // u ∈ S}

instance (U : Type) [DecidableEq U] (S : Finset U) : Fintype (Electorate U S) := by
  classical
  simpa [Electorate] using (Fintype.subtype S (by intro x; rfl))

def liftVoter {U : Type} [DecidableEq U] {V : Finset U} (u : U) (v : Electorate U V) :
    Electorate U (insert u V) :=
  ⟨v.1, Finset.mem_insert.mpr (Or.inr v.2)⟩

def newVoter {U : Type} [DecidableEq U] {V : Finset U} (u : U) (hu : u ∉ V) :
    Electorate U (insert u V) :=
  ⟨u, by simp [hu]⟩

lemma liftVoter_injective {U : Type} [DecidableEq U] {V : Finset U} (u : U) :
    Function.Injective (liftVoter (u := u) : Electorate U V → Electorate U (insert u V)) := by
  intro v w h
  cases v with
  | mk v hv =>
      cases w with
      | mk w hw =>
          cases h
          rfl

lemma liftVoter_ne_newVoter {U : Type} [DecidableEq U] {V : Finset U} {u : U} (hu : u ∉ V)
    (v : Electorate U V) :
    liftVoter (u := u) v ≠ newVoter (u := u) (V := V) hu := by
  intro h
  have hval : v.1 = u := congrArg Subtype.val h
  exact hu (by simpa [hval] using v.2)

@[scAxiom]
def PositiveInvolvement (f : VotingRule) : Prop :=
  ∀ {U A : Type} [DecidableEq U] [Fintype A]
      (V : Finset U) (u : U) (hu : u ∉ V)
      (P : Profile (Electorate U V) A)
      (Q : Profile (Electorate U (insert u V)) A) (c : A),
    (∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v) →
    c ∈ f P →
    BallotTop (Q.pref (newVoter (u := u) (V := V) hu)) c →
    c ∈ f Q

@[scAxiom]
def SingletonPositiveInvolvement (f : VotingRule) : Prop :=
  ∀ {U A : Type} [DecidableEq U] [Fintype A]
      (V : Finset U) (u : U) (hu : u ∉ V)
      (P : Profile (Electorate U V) A)
      (Q : Profile (Electorate U (insert u V)) A) (c : A),
    (∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v) →
    f P = {c} →
    BallotTop (Q.pref (newVoter (u := u) (V := V) hu)) c →
    c ∈ f Q

@[scAxiom]
def NegativeInvolvement (f : VotingRule) : Prop :=
  ∀ {U A : Type} [DecidableEq U] [Fintype A]
      (V : Finset U) (u : U) (hu : u ∉ V)
      (P : Profile (Electorate U V) A)
      (Q : Profile (Electorate U (insert u V)) A) (c : A),
    (∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v) →
    c ∉ f P →
    BallotBottom (Q.pref (newVoter (u := u) (V := V) hu)) c →
    c ∉ f Q

def StrongParticipation (E : ∀ {A : Type}, LinearOrder A → SetExtension A) (f : VotingRule) :
    Prop :=
  ∀ {U A : Type} [DecidableEq U] [Fintype A] [Nonempty A] [DecidableEq A]
      (V : Finset U) (u : U) (hu : u ∉ V)
    (P : Profile (Electorate U V) A)
    (Q : Profile (Electorate U (insert u V)) A),
    (∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v) →
    (E (Q.pref (newVoter (u := u) (V := V) hu))).weak (f Q) (f P)

def WeakParticipation (E : ∀ {A : Type}, LinearOrder A → SetExtension A) (f : VotingRule) :
    Prop :=
  ∀ {U A : Type} [DecidableEq U] [Fintype A] [Nonempty A] [DecidableEq A]
      (V : Finset U) (u : U) (hu : u ∉ V)
      (P : Profile (Electorate U V) A)
      (Q : Profile (Electorate U (insert u V)) A),
    (∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v) →
    ¬ (E (Q.pref (newVoter (u := u) (V := V) hu))).strict (f Q) (f P)

@[scAxiom]
def OptimistParticipation (f : VotingRule) : Prop :=
  StrongParticipation (fun {A} r => OptimistExtension (A := A) r) f

@[scAxiom]
def PessimistParticipation (f : VotingRule) : Prop :=
  StrongParticipation (fun {A} r => PessimistExtension (A := A) r) f

@[scAxiom]
def StrongKellyParticipation (f : VotingRule) : Prop :=
  StrongParticipation (fun {A} r => KellyExtension (A := A) r) f

@[scAxiom]
def WeakKellyParticipation (f : VotingRule) : Prop :=
  WeakParticipation (fun {A} r => KellyExtension (A := A) r) f

@[scAxiom]
def StrongFishburnParticipation (f : VotingRule) : Prop :=
  StrongParticipation (fun {A} r => FishburnExtension (A := A) r) f

@[scAxiom]
def WeakFishburnParticipation (f : VotingRule) : Prop :=
  WeakParticipation (fun {A} r => FishburnExtension (A := A) r) f

noncomputable def restrictElectorate {U A : Type} [DecidableEq U] [Fintype A] {W : Finset U}
    (Q : Profile (Electorate U W) A) (S : Finset U) (hS : S ⊆ W) :
    Profile (Electorate U S) A :=
  { pref := fun v => Q.pref ⟨v.1, hS v.2⟩ }

lemma restrictElectorate_agrees {U A : Type} [DecidableEq U] [Fintype A] {W S : Finset U}
    (Q : Profile (Electorate U W) A) (hS : S ⊆ W) (u : U)
    (hSu : insert u S ⊆ W) :
    ∀ v : Electorate U S,
      (restrictElectorate Q (insert u S) hSu).pref (liftVoter (u := u) v) =
        (restrictElectorate Q S hS).pref v := by
  intro v
  rfl

lemma restrictElectorate_self {U A : Type} [DecidableEq U] [Fintype A] {W : Finset U}
    (Q : Profile (Electorate U W) A) :
    restrictElectorate Q W (by intro x hx; exact hx) = Q := by
  cases Q
  rfl

lemma restrictElectorate_eq_of_subset_proof {U A : Type} [DecidableEq U] [Fintype A] {W : Finset U}
    (Q : Profile (Electorate U W) A) {S : Finset U} (h₁ h₂ : S ⊆ W) :
    restrictElectorate Q S h₁ = restrictElectorate Q S h₂ := by
  cases Q with
  | mk pref =>
      apply congrArg (fun f => Profile.mk f)
      funext v
      have hsub : (⟨v.1, h₁ v.2⟩ : Electorate U W) = ⟨v.1, h₂ v.2⟩ := by
        apply Subtype.ext
        rfl
      simp [hsub]

noncomputable def castProfile {U A : Type} [DecidableEq U] [Fintype A] {S T : Finset U}
    (h : S = T) (P : Profile (Electorate U S) A) : Profile (Electorate U T) A :=
  { pref := fun v =>
      P.pref ⟨v.1, by
        have h' := congrArg (fun s => v.1 ∈ s) h.symm
        exact Eq.mp h' v.2⟩ }

@[simp] lemma castProfile_rfl {U A : Type} [DecidableEq U] [Fintype A] {S : Finset U}
    (P : Profile (Electorate U S) A) : castProfile (S := S) (T := S) rfl P = P := by
  ext v
  rfl

lemma votingRule_castProfile {f : VotingRule} {U A : Type} [DecidableEq U] [Fintype A]
    {S T : Finset U} (h : S = T) (P : Profile (Electorate U S) A) :
    f (castProfile h P) = f P := by
  cases h
  simp [castProfile_rfl]

noncomputable def addCopiesProfile {U A : Type} [DecidableEq U] [Fintype A]
    (V W : Finset U) (P : Profile (Electorate U V) A) (r : LinearOrder A) :
    Profile (Electorate U (V ∪ W)) A :=
  { pref := fun v => if h : v.1 ∈ V then P.pref ⟨v.1, h⟩ else r }
lemma positiveInvolvement_addCopiesProfile {f : VotingRule} (hpos : PositiveInvolvement f) :
    ∀ {U A : Type} [DecidableEq U] [Fintype A]
        (V W : Finset U) (_ : Disjoint V W)
        (P : Profile (Electorate U V) A) (r : LinearOrder A) (c : A),
      BallotTop r c →
      c ∈ f P →
      c ∈ f (addCopiesProfile V W P r) := by
  intro U A _ _ V W hVW P r c htop hc
  classical
  induction W using Finset.induction_on with
  | empty =>
      have hEq : V ∪ (∅ : Finset U) = V := by simp
      let Q0 : Profile (Electorate U V) A :=
        castProfile (S := V ∪ (∅ : Finset U)) (T := V) hEq (addCopiesProfile V (∅ : Finset U) P r)
      have hEqprof : Q0 = P := by
        apply Profile.ext
        intro v
        have hv : v.1 ∈ V := v.2
        simp [Q0, castProfile, addCopiesProfile]
      have hc' : c ∈ f Q0 := by
        simpa [hEqprof] using hc
      have hcast : f Q0 = f (addCopiesProfile V (∅ : Finset U) P r) := by
        simpa [Q0] using
          (votingRule_castProfile (f := f) hEq (addCopiesProfile V (∅ : Finset U) P r))
      simpa [hcast] using hc'
  | insert w s hw ih =>
      have hVS : Disjoint V s := by
        refine Finset.disjoint_left.mpr ?_
        intro x hxV hxS
        exact (Finset.disjoint_left.mp hVW) hxV (by simp [hxS])
      have hwV : w ∉ V := by
        intro hwV
        exact (Finset.disjoint_left.mp hVW) hwV (by simp)
      have hwV' : w ∉ V ∪ s := by
        intro hwV'
        rcases Finset.mem_union.mp hwV' with hwV' | hwS
        · exact hwV hwV'
        · exact hw hwS
      have hEq : insert w (V ∪ s) = V ∪ insert w s := by
        simp [Finset.union_insert]
      let Qbig : Profile (Electorate U (insert w (V ∪ s))) A :=
        castProfile (S := V ∪ insert w s) (T := insert w (V ∪ s)) hEq.symm
          (addCopiesProfile (V := V) (W := insert w s) P r)
      let Qsmall : Profile (Electorate U (V ∪ s)) A :=
        addCopiesProfile (V := V) (W := s) P r
      have hagree :
          ∀ v : Electorate U (V ∪ s),
            Qbig.pref (liftVoter (u := w) v) = Qsmall.pref v := by
        intro v
        by_cases hv : v.1 ∈ V
        · simp [Qbig, Qsmall, castProfile, addCopiesProfile, liftVoter, hv]
        · simp [Qbig, Qsmall, castProfile, addCopiesProfile, liftVoter, hv]
      have hnew : Qbig.pref (newVoter (u := w) (V := V ∪ s) hwV') = r := by
        simp [Qbig, castProfile, addCopiesProfile, newVoter, hwV]
      have htop' :
          BallotTop (Qbig.pref (newVoter (u := w) (V := V ∪ s) hwV')) c := by
        simpa [hnew] using htop
      have hc' : c ∈ f Qsmall := ih hVS
      have hmem : c ∈ f Qbig := by
        apply hpos (V := V ∪ s) (u := w) hwV' Qsmall Qbig c
        · exact hagree
        · exact hc'
        · exact htop'
      have hcast : f Qbig = f (addCopiesProfile V (insert w s) P r) := by
        simpa [Qbig] using
          (votingRule_castProfile (f := f) hEq.symm
            (addCopiesProfile (V := V) (W := insert w s) P r))
      simpa [hcast] using hmem

lemma positiveInvolvement_add_copies {f : VotingRule} (hpos : PositiveInvolvement f) :
    ∀ {U A : Type} [DecidableEq U] [Fintype A]
        (V W : Finset U) (_ : Disjoint V W)
        (P : Profile (Electorate U V) A)
        (Q : Profile (Electorate U (V ∪ W)) A) (c : A) (r : LinearOrder A),
      restrictElectorate Q V (by
        intro x hx
        exact Finset.mem_union.mpr (Or.inl hx)) = P →
      (∀ w (hw : w ∈ W),
        Q.pref ⟨w, Finset.mem_union.mpr (Or.inr hw)⟩ = r) →
      BallotTop r c →
      c ∈ f P →
      c ∈ f Q := by
  intro U A _ _ V W hVW P Q c r hrest hnew htop hc
  classical
  have hcanon : c ∈ f (addCopiesProfile V W P r) :=
    positiveInvolvement_addCopiesProfile (f := f) hpos V W hVW P r c htop hc
  have hQeq : Q = addCopiesProfile V W P r := by
    apply Profile.ext
    intro v
    by_cases hv : v.1 ∈ V
    · have hrestpref' :=
        congrArg (fun prof => prof.pref ⟨v.1, hv⟩) hrest
      have hrestpref :
          Q.pref ⟨v.1, Finset.mem_union.mpr (Or.inl hv)⟩ = P.pref ⟨v.1, hv⟩ := by
        simp [restrictElectorate] at hrestpref'
        exact hrestpref'
      have hvsub :
          (⟨v.1, Finset.mem_union.mpr (Or.inl hv)⟩ : Electorate U (V ∪ W)) = v := by
        apply Subtype.ext
        rfl
      have hQpref : Q.pref v = P.pref ⟨v.1, hv⟩ := by
        cases hvsub
        exact hrestpref
      have hAddpref : (addCopiesProfile V W P r).pref v = P.pref ⟨v.1, hv⟩ := by
        simp [addCopiesProfile, hv]
      exact hQpref.trans hAddpref.symm
    · have hWmem : v.1 ∈ W := by
        rcases Finset.mem_union.mp v.2 with hv' | hw'
        · exact (hv hv').elim
        · exact hw'
      have hnew' :
          Q.pref ⟨v.1, Finset.mem_union.mpr (Or.inr hWmem)⟩ = r := hnew _ hWmem
      have hvsub :
          (⟨v.1, Finset.mem_union.mpr (Or.inr hWmem)⟩ : Electorate U (V ∪ W)) = v := by
        apply Subtype.ext
        rfl
      have hQpref : Q.pref v = r := by
        cases hvsub
        exact hnew'
      have hAddpref : (addCopiesProfile V W P r).pref v = r := by
        simp [addCopiesProfile, hv]
      exact hQpref.trans hAddpref.symm
  simpa [hQeq] using hcanon

def UpperSet {A : Type} [DecidableEq A] (r : LinearOrder A) (S : Finset A) : Prop :=
  ∀ ⦃x y : A⦄, r.lt x y → y ∈ S → x ∈ S

lemma upperSet_mem_of_not_lt {A : Type} [DecidableEq A]
    {r : LinearOrder A} {S : Finset A} (hS : UpperSet r S)
    {x y : A} (hx : x ∈ S) (hnot : ¬ r.lt x y) : y ∈ S := by
  by_cases hxy : y = x
  · simpa [hxy] using hx
  · have hlt_or_gt : r.lt y x ∨ r.lt x y := lt_or_gt_of_ne hxy
    cases hlt_or_gt with
    | inl hlt => exact hS hlt hx
    | inr hgt => exact (False.elim (hnot hgt))

@[scAxiom]
def ResoluteParticipation (f : VotingRule) (_hf : Resolute f) : Prop :=
  ∀ {U A : Type} [DecidableEq U] [Fintype A]
      (V : Finset U) (u : U) (hu : u ∉ V)
      (P : Profile (Electorate U V) A)
      (Q : Profile (Electorate U (insert u V)) A) (x y : A),
    (∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v) →
    f P = {x} →
    f Q = {y} →
    ¬ (Q.pref (newVoter (u := u) (V := V) hu)).lt x y

lemma resoluteParticipation_leaving {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) :
    ∀ {U A : Type} [DecidableEq U] [Fintype A]
        (V : Finset U) (u : U) (hu : u ∉ V)
        (P : Profile (Electorate U V) A)
        (Q : Profile (Electorate U (insert u V)) A) (x y : A),
      (∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v) →
      f Q = {x} →
      f P = {y} →
      ¬ (Q.pref (newVoter (u := u) (V := V) hu)).lt y x := by
  intro U A _ _ V u hu P Q x y hagree hx hy
  apply hpart (V := V) (u := u) hu P Q y x
  · exact hagree
  · exact hy
  · exact hx

lemma resoluteParticipation_superset {f : VotingRule} (hf : Resolute f)
    (hpart : ResoluteParticipation f hf) :
    ∀ {U A : Type} [DecidableEq U] [Fintype A] [Nonempty A] [DecidableEq A]
        (V W : Finset U) (hVW : V ⊆ W)
        (Q : Profile (Electorate U W) A) (S : Finset A) (x : A),
      f (restrictElectorate Q V hVW) = {x} →
      x ∈ S →
      (∀ w (hw : w ∈ W \ V),
        UpperSet (Q.pref ⟨w, (Finset.mem_sdiff.mp hw).1⟩) S) →
      f Q ⊆ S := by
  intro U A _ _ _ _ V W hVW Q S x hx hxS hUpper
  classical
  let T : Finset U := W \ V
  have hEqset0 : V ∪ (∅ : Finset U) = V := by simp
  have hVW' : V ∪ (∅ : Finset U) ⊆ W := by
    intro z hz
    exact hVW (by simpa using hz)
  have hx0 : f (restrictElectorate Q (V ∪ (∅ : Finset U)) hVW') = {x} := by
    convert hx
  have hTsub : T ⊆ W := by
    simp [T]
  have hVunion : ∀ s : Finset U, s ⊆ T → V ∪ s ⊆ W := by
    intro s hs
    exact Finset.union_subset hVW (Finset.Subset.trans hs hTsub)
  have hprop :
      ∀ s : Finset U, ∀ hs : s ⊆ T,
        ∀ y, f (restrictElectorate Q (V ∪ s) (hVunion s hs)) = {y} → y ∈ S := by
    intro s hs
    revert hs
    refine Finset.induction_on s ?base ?step
    · intro _ y hy
      have hx1 :
          f (restrictElectorate Q (V ∪ (∅ : Finset U)) (hVunion ∅ (by simp [T]))) = {x} := by
        have hEqprof :
            restrictElectorate Q (V ∪ (∅ : Finset U)) hVW' =
              restrictElectorate Q (V ∪ (∅ : Finset U)) (hVunion ∅ (by simp [T])) := by
          exact restrictElectorate_eq_of_subset_proof Q _ _
        simpa [hEqprof] using hx0
      have hxy : x = y := by
        have hxy' : ({x} : Finset A) = {y} := by simpa [hx1] using hy
        have hxmem : x ∈ ({y} : Finset A) := by
          simpa [hxy'] using (by simp : x ∈ ({x} : Finset A))
        simpa using hxmem
      simpa [hxy] using hxS
    · intro a s ha ih hs y hy
      have hsT : s ⊆ T := by
        intro z hz
        exact hs (by simp [hz])
      have haT : a ∈ T := by
        exact hs (by simp)
      let Ssmall : Finset U := V ∪ s
      have hSsmall : Ssmall ⊆ W := hVunion s hsT
      let Sbig : Finset U := insert a Ssmall
      have haW : a ∈ W := hTsub haT
      have hSbig : Sbig ⊆ W := Finset.insert_subset haW hSsmall
      have hcard_small : (f (restrictElectorate Q Ssmall hSsmall)).card = 1 := by
        simpa using (hf (restrictElectorate Q Ssmall hSsmall))
      rcases Finset.card_eq_one.mp hcard_small with ⟨x', hx'⟩
      have hx'_mem : x' ∈ S := by
        apply ih hsT x' hx'
      have hagree :
          ∀ v : Electorate U Ssmall,
            (restrictElectorate Q Sbig hSbig).pref (liftVoter (u := a) v) =
              (restrictElectorate Q Ssmall hSsmall).pref v := by
        intro v
        rfl
      have hy' : f (restrictElectorate Q Sbig hSbig) = {y} := by
        convert hy
        · simp [Sbig, Ssmall]
        · simp [Sbig, Ssmall]
      have hnot :
          ¬ ((restrictElectorate Q Sbig hSbig).pref
              (newVoter (u := a) (V := Ssmall) (by
                have haV : a ∉ V := (Finset.mem_sdiff.mp (by simpa [T] using haT)).2
                simp [Ssmall, haV, ha]))).lt x' y := by
        apply hpart (V := Ssmall) (u := a) ?_ (restrictElectorate Q Ssmall hSsmall)
            (restrictElectorate Q Sbig hSbig) x' y
        · exact hagree
        · exact hx'
        · exact hy'
        ·
          have haV : a ∉ V := (Finset.mem_sdiff.mp (by simpa [T] using haT)).2
          simp [Ssmall, haV, ha]
      have hUpper_a : UpperSet (Q.pref ⟨a, haW⟩) S := by
        exact hUpper a (by simpa [T] using haT)
      have hnot' :
          ¬ (Q.pref ⟨a, haW⟩).lt x' y := by
        exact hnot
      exact upperSet_mem_of_not_lt hUpper_a hx'_mem hnot'
  have hW : V ∪ T = W := by
    simpa [T] using (Finset.union_sdiff_of_subset hVW)
  have hWT : V ∪ T ⊆ W := by
    simp [hW]
  have hsubset : f (restrictElectorate Q (V ∪ T) hWT) ⊆ S := by
    intro y hy
    have hcard : (f (restrictElectorate Q (V ∪ T) hWT)).card = 1 := by
      simpa using (hf (restrictElectorate Q (V ∪ T) hWT))
    rcases Finset.card_eq_one.mp hcard with ⟨z, hz⟩
    have hy' : f (restrictElectorate Q (V ∪ T) hWT) = {y} := by
      have hy'' : y ∈ ({z} : Finset A) := by simpa [hz] using hy
      have hyz : y = z := by simpa using hy''
      simp [hz, hyz]
    exact hprop T (by simp [T]) y hy'
  have hQeq : f (restrictElectorate Q (V ∪ T) hWT) = f Q := by
    rw [← restrictElectorate_self Q]
    convert rfl
    · exact hW.symm
    · exact (restrictElectorate_self Q).symm
    · exact hW.symm
  rw [← hQeq]
  exact hsubset

lemma tieBrokenVotingRule_resoluteParticipation (f : VotingRule) (hf : IsVotingRule f)
    (hpart : StrongFishburnParticipation f) :
    ResoluteParticipation (SocialChoice.tieBrokenVotingRule f hf)
      (SocialChoice.tieBrokenVotingRule_resolute f hf) := by
  intro U A _ _ V u hu P Q x y hagree hx hy
  classical
  by_cases hA : Nonempty A
  · letI : Nonempty A := hA
    let r := Q.pref (newVoter (u := u) (V := V) hu)
    letI : LinearOrder A := r
    have hfish : FishburnWeak r (f Q) (f P) := by
      simpa [StrongFishburnParticipation, StrongParticipation, FishburnExtension] using
        (hpart (V := V) (u := u) hu P Q hagree)
    let tb := SocialChoice.canonicalLinearOrder (A := A)
    have hx' : tieBrokenRule tb f hf P = {x} := by
      simpa [tieBrokenVotingRule, hA, tb] using hx
    have hy' : tieBrokenRule tb f hf Q = {y} := by
      simpa [tieBrokenVotingRule, hA, tb] using hy
    have hneP : (f P).Nonempty := hf P
    have hneQ : (f Q).Nonempty := hf Q
    have hmin :
        r.le (@Finset.min' A tb (f Q) hneQ) (@Finset.min' A tb (f P) hneP) :=
      @fishburn_min_tb_le A (fun a b => @LinearOrder.toDecidableEq A r a b)
        tb r (f Q) (f P) hneQ hneP hfish
    have hyset : ({y} : Finset A) = {@Finset.min' A tb (f Q) hneQ} := by
      simpa [tieBrokenRule] using hy'.symm
    have hxset : ({x} : Finset A) = {@Finset.min' A tb (f P) hneP} := by
      simpa [tieBrokenRule] using hx'.symm
    have hymin : y = @Finset.min' A tb (f Q) hneQ := by
      have hymem : y ∈ ({@Finset.min' A tb (f Q) hneQ} : Finset A) := by
        simpa [hyset] using (Finset.mem_singleton_self y)
      exact Finset.mem_singleton.mp hymem
    have hxmin : x = @Finset.min' A tb (f P) hneP := by
      have hxmem : x ∈ ({@Finset.min' A tb (f P) hneP} : Finset A) := by
        simpa [hxset] using (Finset.mem_singleton_self x)
      exact Finset.mem_singleton.mp hxmem
    have hle : r.le y x := by
      simpa [hymin, hxmin] using hmin
    letI : LinearOrder A := r
    exact not_lt.mpr (by simpa using hle)
  ·
    have hA' : IsEmpty A := (not_nonempty_iff.mp hA)
    exact IsEmpty.elim hA' x

end SocialChoice
