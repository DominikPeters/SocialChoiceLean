import Mathlib.Tactic
import Mathlib.Tactic.FinCases
import SocialChoice.Axioms.Participation
import SocialChoice.Axioms.Implications
import SocialChoice.Axioms.InformationalBasis
import SocialChoice.ListBallot
import SocialChoice.Rules.Nanson.Defs
import SocialChoice.Rules.Nanson.Condorcet
import SocialChoice.Rules.Nanson.InformationalBasis

namespace SocialChoice

open Finset
open Classical

attribute [instance] Classical.decEq Classical.decPred

set_option maxHeartbeats 5000000

/-!
# Nanson fails negative involvement

Counterexample with 4 candidates and 4 voters:

Full profile (4 voters):
1 voter : 0 > 3 > 2 > 1
1 voter : 1 > 0 > 3 > 2
1 voter : 2 > 1 > 0 > 3
1 voter : 3 > 2 > 1 > 0
Nanson selects {0,1,2,3}.

Remove the voter with ballot 3 > 2 > 1 > 0:
Nanson selects {1}.

Read backwards, this violates Negative Involvement for candidate 0.
-/

namespace NansonNegativeInvolvementCounterexample

abbrev A4 := Fin 4

def ballot0321 : ListBallot 4 := ListBallot.mk' [0, 3, 2, 1]
def ballot1032 : ListBallot 4 := ListBallot.mk' [1, 0, 3, 2]
def ballot2103 : ListBallot 4 := ListBallot.mk' [2, 1, 0, 3]
def ballot3210 : ListBallot 4 := ListBallot.mk' [3, 2, 1, 0]

def ballots4 : Fin 4 → ListBallot 4
  | ⟨0, _⟩ => ballot0321
  | ⟨1, _⟩ => ballot1032
  | ⟨2, _⟩ => ballot2103
  | ⟨3, _⟩ => ballot3210

def ballots3 : Fin 3 → ListBallot 4
  | ⟨0, _⟩ => ballot0321
  | ⟨1, _⟩ => ballot1032
  | ⟨2, _⟩ => ballot2103

noncomputable def profile4_list : Profile (Fin 4) A4 :=
  profileOfListBallots ballots4

noncomputable def profile3_list : Profile (Fin 3) A4 :=
  profileOfListBallots ballots3

def voters3 : Finset (Fin 4) := {0, 1, 2}
def voters4 : Finset (Fin 4) := insert (3 : Fin 4) voters3

lemma voters3_not_mem : (3 : Fin 4) ∉ voters3 := by
  simp [voters3]

lemma voters4_eq_univ : (voters4 : Finset (Fin 4)) = Finset.univ := by
  ext x
  fin_cases x <;> simp [voters4, voters3]

noncomputable def fullProfile : Profile (Electorate (Fin 4) (Finset.univ)) A4 :=
  { pref := fun v => (ballots4 v.1).toLinearOrder }

noncomputable def profile3 : Profile (Electorate (Fin 4) voters3) A4 :=
  restrictElectorate fullProfile voters3 (by
    intro x hx; exact (Finset.mem_univ x))

noncomputable def profile4 : Profile (Electorate (Fin 4) voters4) A4 :=
  restrictElectorate fullProfile voters4 (by
    intro x hx; exact (Finset.mem_univ x))

noncomputable def e4 : Fin 4 ≃ Electorate (Fin 4) voters4 :=
  { toFun := fun x => ⟨x, by simp [voters4_eq_univ]⟩
    invFun := fun v => v.1
    left_inv := by intro x; rfl
    right_inv := by intro v; cases v; rfl }

noncomputable def e3_to : Fin 3 → Electorate (Fin 4) voters3
  | ⟨0, _⟩ => ⟨0, by simp [voters3]⟩
  | ⟨1, _⟩ => ⟨1, by simp [voters3]⟩
  | ⟨2, _⟩ => ⟨2, by simp [voters3]⟩

noncomputable def e3_inv : Electorate (Fin 4) voters3 → Fin 3
  | ⟨0, _⟩ => ⟨0, by decide⟩
  | ⟨1, _⟩ => ⟨1, by decide⟩
  | ⟨2, _⟩ => ⟨2, by decide⟩
  | ⟨3, h⟩ => (False.elim (by simp [voters3] at h))

noncomputable def e3 : Fin 3 ≃ Electorate (Fin 4) voters3 :=
  { toFun := e3_to
    invFun := e3_inv
    left_inv := by
      intro v
      fin_cases v <;> rfl
    right_inv := by
      intro v
      cases v with
      | mk val hmem =>
          fin_cases val <;> simp [e3_to, e3_inv, voters3] at hmem ⊢ }

lemma relabel_profile4_eq_profile4_list :
    relabelProfileVoters e4 profile4 = profile4_list := by
  ext v
  rfl

lemma relabel_profile3_eq_profile3_list :
    relabelProfileVoters e3 profile3 = profile3_list := by
  ext v
  fin_cases v <;> rfl

lemma margin_profile4_eq_list (a b : A4) :
    margin profile4 a b = margin profile4_list a b := by
  have h :=
    margin_relabelProfileVoters (e := e4) (P := profile4) (a := a) (b := b)
  have h' : margin profile4_list a b = margin profile4 a b := by
    simpa [relabel_profile4_eq_profile4_list] using h
  simpa using h'.symm

lemma margin_profile3_eq_list (a b : A4) :
    margin profile3 a b = margin profile3_list a b := by
  have h :=
    margin_relabelProfileVoters (e := e3) (P := profile3) (a := a) (b := b)
  have h' : margin profile3_list a b = margin profile3 a b := by
    simpa [relabel_profile3_eq_profile3_list] using h
  simpa using h'.symm

lemma profiles_agree :
    ∀ v : Electorate (Fin 4) voters3,
      profile4.pref (liftVoter (u := (3 : Fin 4)) v) = profile3.pref v := by
  intro v
  simpa [profile3, profile4, voters4] using
    (restrictElectorate_agrees (Q := fullProfile) (S := voters3)
      (hS := by intro x hx; exact (Finset.mem_univ x))
      (u := (3 : Fin 4))
      (hSu := by intro x hx; exact (Finset.mem_univ x)) v)

private lemma ballot3210_bottom_0 : BallotBottom (ballot3210.toLinearOrder) (0 : Fin 4) := by
  intro d hd
  fin_cases d
  · cases hd rfl
  ·
    have hlt :
        ballot3210.ranking.idxOf (1 : Fin 4) < ballot3210.ranking.idxOf (0 : Fin 4) := by
      decide
    simpa [ballot3210, ListBallot.lt_iff_idxOf] using hlt
  ·
    have hlt :
        ballot3210.ranking.idxOf (2 : Fin 4) < ballot3210.ranking.idxOf (0 : Fin 4) := by
      decide
    simpa [ballot3210, ListBallot.lt_iff_idxOf] using hlt
  ·
    have hlt :
        ballot3210.ranking.idxOf (3 : Fin 4) < ballot3210.ranking.idxOf (0 : Fin 4) := by
      decide
    simpa [ballot3210, ListBallot.lt_iff_idxOf] using hlt

lemma newVoter_bottom_0 :
    BallotBottom
      (profile4.pref (newVoter (u := (3 : Fin 4)) (V := voters3) voters3_not_mem))
      (0 : Fin 4) := by
  change BallotBottom ballot3210.toLinearOrder (0 : Fin 4)
  exact ballot3210_bottom_0

/-! ## Margins and C2Borda scores for the full profile (4 voters) -/

private lemma marginList_profile4_0_1 :
    marginList (fun v => (ballots4 v).ranking) (0 : Fin 4) (1 : Fin 4) = -2 := by
  decide

private lemma marginList_profile4_0_2 :
    marginList (fun v => (ballots4 v).ranking) (0 : Fin 4) (2 : Fin 4) = 0 := by
  decide

private lemma marginList_profile4_0_3 :
    marginList (fun v => (ballots4 v).ranking) (0 : Fin 4) (3 : Fin 4) = 2 := by
  decide

private lemma marginList_profile4_1_2 :
    marginList (fun v => (ballots4 v).ranking) (1 : Fin 4) (2 : Fin 4) = -2 := by
  decide

private lemma marginList_profile4_1_3 :
    marginList (fun v => (ballots4 v).ranking) (1 : Fin 4) (3 : Fin 4) = 0 := by
  decide

private lemma marginList_profile4_2_3 :
    marginList (fun v => (ballots4 v).ranking) (2 : Fin 4) (3 : Fin 4) = -2 := by
  decide

private lemma margin_profile4_0_1 : margin profile4_list (0 : Fin 4) (1 : Fin 4) = -2 := by
  have h :=
    margin_eq_marginList (ballots := ballots4) (a := (0 : Fin 4)) (b := (1 : Fin 4))
  simpa [profile4_list, marginList_profile4_0_1] using h

private lemma margin_profile4_0_2 : margin profile4_list (0 : Fin 4) (2 : Fin 4) = 0 := by
  have h :=
    margin_eq_marginList (ballots := ballots4) (a := (0 : Fin 4)) (b := (2 : Fin 4))
  simpa [profile4_list, marginList_profile4_0_2] using h

private lemma margin_profile4_0_3 : margin profile4_list (0 : Fin 4) (3 : Fin 4) = 2 := by
  have h :=
    margin_eq_marginList (ballots := ballots4) (a := (0 : Fin 4)) (b := (3 : Fin 4))
  simpa [profile4_list, marginList_profile4_0_3] using h

private lemma margin_profile4_1_2 : margin profile4_list (1 : Fin 4) (2 : Fin 4) = -2 := by
  have h :=
    margin_eq_marginList (ballots := ballots4) (a := (1 : Fin 4)) (b := (2 : Fin 4))
  simpa [profile4_list, marginList_profile4_1_2] using h

private lemma margin_profile4_1_3 : margin profile4_list (1 : Fin 4) (3 : Fin 4) = 0 := by
  have h :=
    margin_eq_marginList (ballots := ballots4) (a := (1 : Fin 4)) (b := (3 : Fin 4))
  simpa [profile4_list, marginList_profile4_1_3] using h

private lemma margin_profile4_2_3 : margin profile4_list (2 : Fin 4) (3 : Fin 4) = -2 := by
  have h :=
    margin_eq_marginList (ballots := ballots4) (a := (2 : Fin 4)) (b := (3 : Fin 4))
  simpa [profile4_list, marginList_profile4_2_3] using h

private lemma margin_profile4_1_0 : margin profile4_list (1 : Fin 4) (0 : Fin 4) = 2 := by
  have h := margin_antisymmetric (P := profile4_list) (1 : Fin 4) (0 : Fin 4)
  simpa [margin_profile4_0_1] using h

private lemma margin_profile4_2_0 : margin profile4_list (2 : Fin 4) (0 : Fin 4) = 0 := by
  have h := margin_antisymmetric (P := profile4_list) (2 : Fin 4) (0 : Fin 4)
  simpa [margin_profile4_0_2] using h

private lemma margin_profile4_3_0 : margin profile4_list (3 : Fin 4) (0 : Fin 4) = -2 := by
  have h := margin_antisymmetric (P := profile4_list) (3 : Fin 4) (0 : Fin 4)
  simpa [margin_profile4_0_3] using h

private lemma margin_profile4_2_1 : margin profile4_list (2 : Fin 4) (1 : Fin 4) = 2 := by
  have h := margin_antisymmetric (P := profile4_list) (2 : Fin 4) (1 : Fin 4)
  simpa [margin_profile4_1_2] using h

private lemma margin_profile4_3_1 : margin profile4_list (3 : Fin 4) (1 : Fin 4) = 0 := by
  have h := margin_antisymmetric (P := profile4_list) (3 : Fin 4) (1 : Fin 4)
  simpa [margin_profile4_1_3] using h

private lemma margin_profile4_3_2 : margin profile4_list (3 : Fin 4) (2 : Fin 4) = 2 := by
  have h := margin_antisymmetric (P := profile4_list) (3 : Fin 4) (2 : Fin 4)
  simpa [margin_profile4_2_3] using h

private lemma c2Borda_profile4_0 : c2BordaScore profile4_list (0 : Fin 4) = 0 := by
  simp [c2BordaScore, Fin.sum_univ_four, self_margin_zero, margin_profile4_0_1,
    margin_profile4_0_2, margin_profile4_0_3]

private lemma c2Borda_profile4_1 : c2BordaScore profile4_list (1 : Fin 4) = 0 := by
  simp [c2BordaScore, Fin.sum_univ_four, self_margin_zero, margin_profile4_1_0,
    margin_profile4_1_2, margin_profile4_1_3]

private lemma c2Borda_profile4_2 : c2BordaScore profile4_list (2 : Fin 4) = 0 := by
  simp [c2BordaScore, Fin.sum_univ_four, self_margin_zero, margin_profile4_2_0,
    margin_profile4_2_1, margin_profile4_2_3]

private lemma c2Borda_profile4_3 : c2BordaScore profile4_list (3 : Fin 4) = 0 := by
  simp [c2BordaScore, Fin.sum_univ_four, self_margin_zero, margin_profile4_3_0,
    margin_profile4_3_1, margin_profile4_3_2]

lemma nanson_profile4_list : nanson profile4_list = (Finset.univ : Finset A4) := by
  classical
  have hall : ∀ x, c2BordaScore profile4_list x = 0 := by
    intro x
    fin_cases x <;> simp [c2Borda_profile4_0, c2Borda_profile4_1,
      c2Borda_profile4_2, c2Borda_profile4_3]
  simp [nanson, nansonAux, hall]

lemma nanson_profile4 : nanson profile4 = (Finset.univ : Finset A4) := by
  classical
  have hmargin : ∀ a b, margin profile4 a b = margin profile4_list a b := by
    intro a b
    exact margin_profile4_eq_list a b
  have hEq : nanson profile4 = nanson profile4_list := by
    apply nanson_marginBased (P₁ := profile4) (P₂ := profile4_list)
    intro a b
    exact hmargin a b
  simp [hEq, nanson_profile4_list]

/-! ## Margins and C2Borda scores for the reduced profile (3 voters) -/

private lemma marginList_profile3_0_1 :
    marginList (fun v => (ballots3 v).ranking) (0 : Fin 4) (1 : Fin 4) = -1 := by
  decide

private lemma marginList_profile3_0_2 :
    marginList (fun v => (ballots3 v).ranking) (0 : Fin 4) (2 : Fin 4) = 1 := by
  decide

private lemma marginList_profile3_0_3 :
    marginList (fun v => (ballots3 v).ranking) (0 : Fin 4) (3 : Fin 4) = 3 := by
  decide

private lemma marginList_profile3_1_2 :
    marginList (fun v => (ballots3 v).ranking) (1 : Fin 4) (2 : Fin 4) = -1 := by
  decide

private lemma marginList_profile3_1_3 :
    marginList (fun v => (ballots3 v).ranking) (1 : Fin 4) (3 : Fin 4) = 1 := by
  decide

private lemma marginList_profile3_2_3 :
    marginList (fun v => (ballots3 v).ranking) (2 : Fin 4) (3 : Fin 4) = -1 := by
  decide

private lemma margin_profile3_0_1 : margin profile3_list (0 : Fin 4) (1 : Fin 4) = -1 := by
  have h :=
    margin_eq_marginList (ballots := ballots3) (a := (0 : Fin 4)) (b := (1 : Fin 4))
  simpa [profile3_list, marginList_profile3_0_1] using h

private lemma margin_profile3_0_2 : margin profile3_list (0 : Fin 4) (2 : Fin 4) = 1 := by
  have h :=
    margin_eq_marginList (ballots := ballots3) (a := (0 : Fin 4)) (b := (2 : Fin 4))
  simpa [profile3_list, marginList_profile3_0_2] using h

private lemma margin_profile3_0_3 : margin profile3_list (0 : Fin 4) (3 : Fin 4) = 3 := by
  have h :=
    margin_eq_marginList (ballots := ballots3) (a := (0 : Fin 4)) (b := (3 : Fin 4))
  simpa [profile3_list, marginList_profile3_0_3] using h

private lemma margin_profile3_1_2 : margin profile3_list (1 : Fin 4) (2 : Fin 4) = -1 := by
  have h :=
    margin_eq_marginList (ballots := ballots3) (a := (1 : Fin 4)) (b := (2 : Fin 4))
  simpa [profile3_list, marginList_profile3_1_2] using h

private lemma margin_profile3_1_3 : margin profile3_list (1 : Fin 4) (3 : Fin 4) = 1 := by
  have h :=
    margin_eq_marginList (ballots := ballots3) (a := (1 : Fin 4)) (b := (3 : Fin 4))
  simpa [profile3_list, marginList_profile3_1_3] using h

private lemma margin_profile3_2_3 : margin profile3_list (2 : Fin 4) (3 : Fin 4) = -1 := by
  have h :=
    margin_eq_marginList (ballots := ballots3) (a := (2 : Fin 4)) (b := (3 : Fin 4))
  simpa [profile3_list, marginList_profile3_2_3] using h

private lemma margin_profile3_1_0 : margin profile3_list (1 : Fin 4) (0 : Fin 4) = 1 := by
  have h := margin_antisymmetric (P := profile3_list) (1 : Fin 4) (0 : Fin 4)
  simpa [margin_profile3_0_1] using h

private lemma margin_profile3_2_0 : margin profile3_list (2 : Fin 4) (0 : Fin 4) = -1 := by
  have h := margin_antisymmetric (P := profile3_list) (2 : Fin 4) (0 : Fin 4)
  simpa [margin_profile3_0_2] using h

private lemma margin_profile3_3_0 : margin profile3_list (3 : Fin 4) (0 : Fin 4) = -3 := by
  have h := margin_antisymmetric (P := profile3_list) (3 : Fin 4) (0 : Fin 4)
  simpa [margin_profile3_0_3] using h

private lemma margin_profile3_2_1 : margin profile3_list (2 : Fin 4) (1 : Fin 4) = 1 := by
  have h := margin_antisymmetric (P := profile3_list) (2 : Fin 4) (1 : Fin 4)
  simpa [margin_profile3_1_2] using h

private lemma margin_profile3_3_1 : margin profile3_list (3 : Fin 4) (1 : Fin 4) = -1 := by
  have h := margin_antisymmetric (P := profile3_list) (3 : Fin 4) (1 : Fin 4)
  simpa [margin_profile3_1_3] using h

private lemma margin_profile3_3_2 : margin profile3_list (3 : Fin 4) (2 : Fin 4) = 1 := by
  have h := margin_antisymmetric (P := profile3_list) (3 : Fin 4) (2 : Fin 4)
  simpa [margin_profile3_2_3] using h

private lemma c2Borda_profile3_0 : c2BordaScore profile3_list (0 : Fin 4) = 3 := by
  simp [c2BordaScore, Fin.sum_univ_four, self_margin_zero, margin_profile3_0_1,
    margin_profile3_0_2, margin_profile3_0_3]

private lemma c2Borda_profile3_1 : c2BordaScore profile3_list (1 : Fin 4) = 1 := by
  simp [c2BordaScore, Fin.sum_univ_four, self_margin_zero, margin_profile3_1_0,
    margin_profile3_1_2, margin_profile3_1_3]

private lemma c2Borda_profile3_2 : c2BordaScore profile3_list (2 : Fin 4) = -1 := by
  simp [c2BordaScore, Fin.sum_univ_four, self_margin_zero, margin_profile3_2_0,
    margin_profile3_2_1, margin_profile3_2_3]

private lemma c2Borda_profile3_3 : c2BordaScore profile3_list (3 : Fin 4) = -3 := by
  simp [c2BordaScore, Fin.sum_univ_four, self_margin_zero, margin_profile3_3_0,
    margin_profile3_3_1, margin_profile3_3_2]

abbrev PosCand := {x : A4 // c2BordaScore profile3_list x > 0}

@[reducible] noncomputable def profilePos : Profile (Fin 3) PosCand :=
  restrictCandidates profile3_list (fun x => c2BordaScore profile3_list x > 0)

def cand0 : PosCand := ⟨0, by linarith [c2Borda_profile3_0]⟩
def cand1 : PosCand := ⟨1, by linarith [c2Borda_profile3_1]⟩

lemma univ_profilePos_eq : (Finset.univ : Finset PosCand) = {cand0, cand1} := by
  classical
  ext x
  constructor
  · intro _
    rcases x with ⟨x, hxpos⟩
    fin_cases x
    · simp [cand0, cand1]
    · simp [cand0, cand1]
    ·
      have : (0 : Int) < c2BordaScore profile3_list (2 : Fin 4) := hxpos
      linarith [c2Borda_profile3_2]
    ·
      have : (0 : Int) < c2BordaScore profile3_list (3 : Fin 4) := hxpos
      linarith [c2Borda_profile3_3]
  · intro hx
    simp at hx
    simp

lemma margin_profilePos_cand0_cand1 : margin profilePos cand0 cand1 = -1 := by
  have h :=
    margin_eq_margin_restrictCandidates (P := profile3_list)
      (p := fun x => c2BordaScore profile3_list x > 0) (a := cand0) (b := cand1)
  simpa [profilePos, cand0, cand1, margin_profile3_0_1] using h.symm

lemma margin_profilePos_cand1_cand0 : margin profilePos cand1 cand0 = 1 := by
  have h := margin_antisymmetric (P := profilePos) cand1 cand0
  simpa [margin_profilePos_cand0_cand1] using h

lemma c2Borda_profilePos_cand0 : c2BordaScore profilePos cand0 = -1 := by
  classical
  have hne : cand0 ≠ cand1 := by decide
  have hsum :
      c2BordaScore profilePos cand0 =
        ∑ x ∈ ({cand1} : Finset PosCand), margin profilePos cand0 x := by
    simp [c2BordaScore, univ_profilePos_eq, self_margin_zero,
      Finset.sum_singleton, cand0, cand1]
  calc
    c2BordaScore profilePos cand0 =
        ∑ x ∈ ({cand1} : Finset PosCand), margin profilePos cand0 x := hsum
    _ = margin profilePos cand0 cand1 := by
        simp [Finset.sum_singleton]
    _ = -1 := by simp [margin_profilePos_cand0_cand1]

lemma c2Borda_profilePos_cand1 : c2BordaScore profilePos cand1 = 1 := by
  classical
  have hne : cand0 ≠ cand1 := by decide
  have hsum :
      c2BordaScore profilePos cand1 =
        ∑ x ∈ ({cand0} : Finset PosCand), margin profilePos cand1 x := by
    unfold c2BordaScore
    have hunivSum := congrArg
      (fun s : Finset PosCand => Finset.sum s (fun x => margin profilePos cand1 x))
      univ_profilePos_eq
    calc
      ∑ x : PosCand, margin profilePos cand1 x =
          ∑ x ∈ ({cand0, cand1} : Finset PosCand), margin profilePos cand1 x := hunivSum
      _ = ∑ x ∈ ({cand0} : Finset PosCand), margin profilePos cand1 x := by
        rw [Finset.sum_insert (by simpa using hne)]
        simp [self_margin_zero]
  calc
    c2BordaScore profilePos cand1 =
        ∑ x ∈ ({cand0} : Finset PosCand), margin profilePos cand1 x := hsum
    _ = margin profilePos cand1 cand0 := by
        simp [Finset.sum_singleton]
    _ = 1 := by simp [margin_profilePos_cand1_cand0]

abbrev PosCand' := {x : PosCand // c2BordaScore profilePos x > 0}

@[reducible] noncomputable def profilePos' : Profile (Fin 3) PosCand' :=
  restrictCandidates profilePos (fun x => c2BordaScore profilePos x > 0)

def cand1' : PosCand' := ⟨cand1, by linarith [c2Borda_profilePos_cand1]⟩

lemma poscand'_eq_cand1 (x : PosCand') : x.1 = cand1 := by
  classical
  rcases x with ⟨x, hxpos⟩
  have hx' : x ∈ (Finset.univ : Finset PosCand) := by simp
  have hx'' : x ∈ ({cand0, cand1} : Finset PosCand) := by
    simpa [univ_profilePos_eq] using hx'
  have hx''' : x = cand0 ∨ x = cand1 := by
    simpa [Finset.mem_insert, Finset.mem_singleton] using hx''
  cases hx''' with
  | inl hx0 =>
      have : (0 : Int) < c2BordaScore profilePos cand0 := by simpa [hx0] using hxpos
      linarith [c2Borda_profilePos_cand0]
  | inr hx1 =>
      exact hx1

lemma univ_profilePos'_eq : (Finset.univ : Finset PosCand') = {cand1'} := by
  classical
  ext x
  constructor
  · intro _
    have hx : x.1 = cand1 := poscand'_eq_cand1 x
    apply Finset.mem_singleton.mpr
    apply Subtype.ext
    simp [cand1', hx]
  · intro hx
    simp at hx
    simp

lemma poscand'_subsingleton : Subsingleton PosCand' := by
  classical
  refine ⟨?_⟩
  intro x y
  have hx : x.1 = cand1 := poscand'_eq_cand1 x
  have hy : y.1 = cand1 := poscand'_eq_cand1 y
  apply Subtype.ext
  simp [hx, hy]

lemma c2Borda_profilePos'_all_zero (x : PosCand') : c2BordaScore profilePos' x = 0 := by
  classical
  haveI : Subsingleton PosCand' := poscand'_subsingleton
  exact c2BordaScore_eq_zero_of_subsingleton (P := profilePos') (a := x)

lemma nansonAux_profilePos : nansonAux 3 PosCand profilePos = ({cand1} : Finset PosCand) := by
  classical
  have hnotall : ¬ ∀ x : PosCand, c2BordaScore profilePos x = 0 := by
    intro hall
    have := hall cand1
    linarith [c2Borda_profilePos_cand1]
  have hsurv :
      (Finset.univ.filter (fun x => c2BordaScore profilePos x > 0)).Nonempty := by
    refine ⟨cand1, ?_⟩
    simp [c2Borda_profilePos_cand1]
  have haux :
      nansonAux 3 PosCand profilePos =
        liftWinners (nansonAux 2 PosCand' profilePos') := by
    by_cases hall : ∀ x : PosCand, c2BordaScore profilePos x = 0
    · exact (hnotall hall).elim
    ·
      have hsurv' :
          (Finset.univ.filter (fun x => c2BordaScore profilePos x > 0)).Nonempty := hsurv
      have haux' :
          nansonAux 3 PosCand profilePos =
            liftWinners
              (nansonAux 2 {x : PosCand // c2BordaScore profilePos x > 0}
                (restrictCandidates profilePos (fun x => c2BordaScore profilePos x > 0))) := by
        have hall' :
            ¬ ∀ (a : A4) (b : 0 < c2BordaScore profile3_list a),
              c2BordaScore profilePos ⟨a, b⟩ = 0 := by
          simpa [PosCand] using hall
        have hsurv'' :
            (Finset.univ.filter (fun x : PosCand => c2BordaScore profilePos x > 0)).Nonempty :=
          hsurv'
        simp [nansonAux, hall', hsurv'']
      simpa [PosCand', profilePos'] using haux'
  have haux' : nansonAux 2 PosCand' profilePos' = (Finset.univ : Finset PosCand') := by
    have hall' : ∀ x : PosCand', c2BordaScore profilePos' x = 0 := by
      intro x
      exact c2Borda_profilePos'_all_zero x
    simp [nansonAux, hall']
  calc
    nansonAux 3 PosCand profilePos =
        liftWinners (nansonAux 2 PosCand' profilePos') := haux
    _ = liftWinners (Finset.univ : Finset PosCand') := by simp [haux']
    _ = ({cand1} : Finset PosCand) := by
      simp [liftWinners, univ_profilePos'_eq, cand1']

lemma nanson_profile3_list : nanson profile3_list = ({1} : Finset A4) := by
  classical
  have hnotall : ¬ ∀ x, c2BordaScore profile3_list x = 0 := by
    intro hall
    have := hall (0 : Fin 4)
    linarith [c2Borda_profile3_0]
  have hsurv :
      (Finset.univ.filter (fun x => c2BordaScore profile3_list x > 0)).Nonempty := by
    refine ⟨(0 : Fin 4), ?_⟩
    simp [c2Borda_profile3_0]
  have haux : nanson profile3_list = liftWinners (nansonAux 3 PosCand profilePos) := by
    change nansonAux 4 A4 profile3_list = liftWinners (nansonAux 3 PosCand profilePos)
    simp [nansonAux, hnotall, hsurv, profilePos]
  calc
    nanson profile3_list = liftWinners (nansonAux 3 PosCand profilePos) := haux
    _ = liftWinners ({cand1} : Finset PosCand) := by
      simp [nansonAux_profilePos]
    _ = ({1} : Finset A4) := by
      ext x
      fin_cases x <;>
        simp [liftWinners, cand1]

lemma nanson_profile3 : nanson profile3 = ({1} : Finset A4) := by
  classical
  have hmargin : ∀ a b, margin profile3 a b = margin profile3_list a b := by
    intro a b
    exact margin_profile3_eq_list a b
  have hEq : nanson profile3 = nanson profile3_list := by
    apply nanson_marginBased (P₁ := profile3) (P₂ := profile3_list)
    intro a b
    exact hmargin a b
  simp [hEq, nanson_profile3_list]

lemma nanson_profile3_not_0 : (0 : Fin 4) ∉ nanson profile3 := by
  simp [nanson_profile3]

lemma nanson_profile4_has_0 : (0 : Fin 4) ∈ nanson profile4 := by
  simp [nanson_profile4]

end NansonNegativeInvolvementCounterexample

open NansonNegativeInvolvementCounterexample

theorem nanson_not_negativeInvolvement : ¬ NegativeInvolvement nanson := by
  intro hneg
  have hnotmem : (0 : Fin 4) ∉ nanson profile3 := nanson_profile3_not_0
  have hbottom :
      BallotBottom
        (profile4.pref (newVoter (u := (3 : Fin 4)) (V := voters3) voters3_not_mem))
        (0 : Fin 4) :=
    newVoter_bottom_0
  have hmem : (0 : Fin 4) ∈ nanson profile4 := nanson_profile4_has_0
  have hcontra :=
    hneg (V := voters3) (u := (3 : Fin 4)) (hu := voters3_not_mem)
      (P := profile3) (Q := profile4) (c := (0 : Fin 4))
      profiles_agree hnotmem hbottom
  exact hcontra hmem

end SocialChoice
