import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Prod.Lex
import SocialChoice.Rules.River.Defs
import SocialChoice.Cycles

namespace SocialChoice

open Finset

noncomputable def edgeIndex {A : Type} [Fintype A] (e : A × A) :
    Fin (Fintype.card (A × A)) :=
  Fintype.equivFin (A × A) e

lemma edgeIndex_injective {A : Type} [Fintype A] :
    Function.Injective (edgeIndex (A := A)) := by
  intro a b h
  exact (Fintype.equivFin (A × A)).injective (by simpa [edgeIndex] using h)

noncomputable def edgeKey {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (e : A × A) :
    (OrderDual Int ×ₗ Fin (Fintype.card (A × A))) :=
  toLex ((edgeWeight P e : OrderDual Int), edgeIndex (A := A) e)

def edgeOrder {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (e1 e2 : A × A) : Prop :=
  edgeKey (P := P) e1 ≤ edgeKey (P := P) e2

noncomputable instance edgeOrder_decidable {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) :
    DecidableRel (edgeOrder (P := P)) := by
  classical
  intro a b
  dsimp [edgeOrder]
  infer_instance

instance edgeOrder_trans {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) :
    IsTrans (A × A) (edgeOrder (P := P)) := by
  refine ⟨?_⟩
  intro a b c hab hbc
  exact le_trans hab hbc

instance edgeOrder_total {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) :
    Std.Total (edgeOrder (P := P)) := by
  refine ⟨?_⟩
  intro a b
  exact le_total _ _

instance edgeOrder_antisymm {V A : Type} [Fintype V] [Fintype A] (P : Profile V A) :
    Std.Antisymm (edgeOrder (P := P)) := by
  refine ⟨?_⟩
  intro a b hab hba
  have hkey : edgeKey (P := P) a = edgeKey (P := P) b := le_antisymm hab hba
  have hpair : ofLex (edgeKey (P := P) a) = ofLex (edgeKey (P := P) b) := by
    simpa using congrArg ofLex hkey
  have hidx : edgeIndex (A := A) a = edgeIndex (A := A) b := by
    simpa [edgeKey] using congrArg Prod.snd hpair
  exact edgeIndex_injective (A := A) hidx

lemma edgeOrder_implies_weight_ge {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) {e1 e2 : A × A} :
    edgeOrder (P := P) e1 e2 → edgeWeight P e1 >= edgeWeight P e2 := by
  intro h
  have hlex :
      (ofLex (edgeKey (P := P) e1)).1 < (ofLex (edgeKey (P := P) e2)).1 ∨
      (ofLex (edgeKey (P := P) e1)).1 = (ofLex (edgeKey (P := P) e2)).1 ∧
      (ofLex (edgeKey (P := P) e1)).2 ≤ (ofLex (edgeKey (P := P) e2)).2 := by
    simpa using
      (Prod.Lex.le_iff (x := edgeKey (P := P) e1) (y := edgeKey (P := P) e2)).1 h
  cases hlex with
  | inl hlt =>
      have hlt' : edgeWeight P e2 < edgeWeight P e1 := by
        simp [edgeKey] at hlt
        exact hlt
      exact (le_of_lt hlt')
  | inr hEq =>
      have hEq' : edgeWeight P e1 = edgeWeight P e2 := by
        simp [edgeKey] at hEq
        exact hEq.1
      have hle : edgeWeight P e2 ≤ edgeWeight P e1 := by
        rw [hEq']
      exact hle

lemma pairwise_edgeOrder_to_weight {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) :
    ∀ {l : List (A × A)}, l.Pairwise (edgeOrder (P := P)) →
      l.Pairwise (fun e1 e2 => edgeWeight P e1 >= edgeWeight P e2) := by
  intro l hpair
  induction hpair with
  | nil =>
      exact List.Pairwise.nil
  | @cons a l hrel hpair ih =>
      exact List.Pairwise.cons (fun b hb =>
        edgeOrder_implies_weight_ge (P := P) (hrel b hb)) ih

noncomputable def riverTiebreaker {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) : List (A × A) :=
  Finset.sort (marginEdges P) (edgeOrder (P := P))

lemma riverTiebreaker_isTiebreaker {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) : isTiebreaker (P := P) (riverTiebreaker (P := P)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simp [riverTiebreaker]
  · simp [riverTiebreaker]
  · have hpair :
        (riverTiebreaker (P := P)).Pairwise (edgeOrder (P := P)) := by
      simp [riverTiebreaker]
    exact pairwise_edgeOrder_to_weight (P := P) hpair

lemma acyclic_of_not_hasCycle {A : Type} {E : Finset (A × A)} :
    ¬ hasCycle (A := A) E → acyclic (edgeRel (A := A) E) := by
  intro h c hc
  exact h ⟨c, hc⟩

lemma riverAddEdge_noCycle {A : Type} (E : Finset (A × A)) (e : A × A) :
    ¬ hasCycle (A := A) E → ¬ hasCycle (A := A) (riverAddEdge (A := A) E e) := by
  classical
  intro h
  by_cases hcond : hasIncoming (A := A) E e.2 ∨ hasCycle (A := A) (insert e E)
  · simp [riverAddEdge, hcond, h]
  · have hnocycle : ¬ hasCycle (A := A) (insert e E) := (not_or.mp hcond).2
    have hstep : riverAddEdge (A := A) E e = insert e E := by
      simp [riverAddEdge, hcond]
    simpa [hstep] using hnocycle

lemma riverDiagram_noCycle_from {A : Type} (tau : List (A × A)) (E : Finset (A × A)) :
    ¬ hasCycle (A := A) E →
      ¬ hasCycle (A := A) (tau.foldl (riverAddEdge (A := A)) E) := by
  classical
  induction tau generalizing E with
  | nil =>
      intro h
      simpa using h
  | cons e t ih =>
      intro h
      have h' : ¬ hasCycle (A := A) (riverAddEdge (A := A) E e) :=
        riverAddEdge_noCycle (A := A) E e h
      simpa [List.foldl] using (ih (E := riverAddEdge (A := A) E e) h')

lemma riverDiagram_noCycle {A : Type} (tau : List (A × A)) :
    ¬ hasCycle (A := A) (riverDiagram (A := A) tau) := by
  classical
  have h0 : ¬ hasCycle (A := A) (Finset.empty : Finset (A × A)) := by
    intro h
    rcases h with ⟨c, hcycle⟩
    rcases hcycle with ⟨hne, hchain⟩
    cases c with
    | nil => cases hne rfl
    | cons a t =>
        have hmem : (List.getLast (a :: t) (by simp), a) ∈
            (Finset.empty : Finset (A × A)) := by
          simpa [edgeRel] using (List.IsChain.rel hchain)
        exact (notMem_empty _ hmem)
  have := riverDiagram_noCycle_from (A := A) (tau := tau)
    (E := (Finset.empty : Finset (A × A))) h0
  simpa [riverDiagram] using this

lemma riverDiagram_acyclic {A : Type} (tau : List (A × A)) :
    acyclic (edgeRel (A := A) (riverDiagram (A := A) tau)) := by
  exact acyclic_of_not_hasCycle (riverDiagram_noCycle (A := A) tau)

lemma riverWinners_nonempty {A : Type} [Fintype A] [Nonempty A]
    (tau : List (A × A)) : (riverWinners (A := A) tau).Nonempty := by
  classical
  by_contra hne
  have hforall : ∀ x : A, ∃ y : A, (y, x) ∈ riverDiagram (A := A) tau := by
    intro x
    by_contra hnone
    have hx : x ∈ riverWinners (A := A) tau := by
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_univ x, ?_⟩
      simpa [hasIncoming] using hnone
    exact hne ⟨x, hx⟩
  let x0 : A := Classical.choice (inferInstance : Nonempty A)
  rcases cycle_of_forall_defeater (x0 := x0)
      (R := edgeRel (A := A) (riverDiagram (A := A) tau)) hforall with ⟨c, hcycle⟩
  exact (riverDiagram_acyclic (A := A) tau) _ hcycle

lemma river_nonempty_of_tiebreaker {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (P : Profile V A) (tau : List (A × A)) (htau : isTiebreaker (P := P) tau) :
    (river P).Nonempty := by
  classical
  obtain ⟨a, ha⟩ := riverWinners_nonempty (A := A) (tau := tau)
  refine ⟨a, ?_⟩
  refine Finset.mem_filter.mpr ?_
  refine ⟨Finset.mem_univ a, ?_⟩
  exact ⟨tau, htau, ha⟩

theorem river_isVotingRule : IsVotingRule river := by
  intro V A _ _ _ P
  classical
  have htau : isTiebreaker (P := P) (riverTiebreaker (P := P)) :=
    riverTiebreaker_isTiebreaker (P := P)
  simpa using
    (river_nonempty_of_tiebreaker (P := P) (tau := riverTiebreaker (P := P)) htau)

end SocialChoice
