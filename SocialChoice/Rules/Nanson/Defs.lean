import SocialChoice.Rules.ScoringRules.Borda.C2Borda
import SocialChoice.Meta

namespace SocialChoice

/-!
# Nanson's Rule

Nanson's rule uses C2Borda scores to iteratively eliminate all candidates with
nonpositive scores. If every candidate has C2Borda score 0, all candidates win.
-/

noncomputable def nansonAux {V : Type} [Fintype V]
    (n : Nat) (A : Type) [Fintype A] [DecidableEq A] :
    Profile V A → Finset A :=
  match n with
  | 0 => fun _ => Finset.univ
  | Nat.succ n =>
      fun P => by
        classical
        let score : A → Int := fun a => c2BordaScore P a
        by_cases hall : ∀ a : A, score a = 0
        · exact Finset.univ
        · by_cases hsurv : (Finset.univ.filter (fun a => score a > 0)).Nonempty
          · let P' : Profile V {a : A // score a > 0} :=
              restrictCandidates P (fun a => score a > 0)
            exact liftWinners (nansonAux n {a : A // score a > 0} P')
          · exact Finset.univ

/-- Nanson's rule based on C2Borda scores. -/
@[scRule]
noncomputable def nanson : VotingRule :=
  fun {V A} _ _ (P : Profile V A) => by
    classical
    exact nansonAux (Fintype.card A) A P

lemma liftWinners_nonempty {A : Type} {p : A → Prop} [DecidablePred p]
    {s : Finset {a // p a}} (hs : s.Nonempty) :
    (liftWinners s).Nonempty := by
  classical
  rcases hs with ⟨x, hx⟩
  refine ⟨x.1, ?_⟩
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem nanson_isVotingRule : IsVotingRule nanson := by
  intro V A _ _ _ P
  classical
  have hnonempty_aux :
      ∀ n : Nat, ∀ {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
        (P : Profile V A), (nansonAux n A P).Nonempty := by
    intro n
    induction n with
    | zero =>
        intro A _ _ _ P
        have hnonempty : (Finset.univ : Finset A).Nonempty :=
          (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty)
        simp [nansonAux, hnonempty]
    | succ n ih =>
        intro A _ _ _ P
        classical
        by_cases hall : ∀ a : A, c2BordaScore P a = 0
        ·
          have hnonempty : (Finset.univ : Finset A).Nonempty :=
            (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty)
          simp [nansonAux, hall, hnonempty]
        · by_cases hsurv : (Finset.univ.filter (fun a => c2BordaScore P a > 0)).Nonempty
          ·
            let P' : Profile V {a : A // c2BordaScore P a > 0} :=
              restrictCandidates P (fun a => c2BordaScore P a > 0)
            have : Nonempty {a : A // c2BordaScore P a > 0} := by
              rcases hsurv with ⟨a, ha⟩
              exact ⟨⟨a, (Finset.mem_filter.mp ha).2⟩⟩
            have hnonempty' :
                (nansonAux n {a : A // c2BordaScore P a > 0} P').Nonempty :=
              ih (A := {a : A // c2BordaScore P a > 0}) (P := P')
            have hnonempty'' :
                (liftWinners (nansonAux n {a : A // c2BordaScore P a > 0} P')).Nonempty :=
              liftWinners_nonempty (p := fun a => c2BordaScore P a > 0)
                (s := nansonAux n {a : A // c2BordaScore P a > 0} P') hnonempty'
            simpa [nansonAux, hall, hsurv] using hnonempty''
          ·
            have hnonempty : (Finset.univ : Finset A).Nonempty :=
              (Finset.univ_nonempty : (Finset.univ : Finset A).Nonempty)
            simp [nansonAux, hall, hsurv, hnonempty]
  simpa [nanson] using (hnonempty_aux (Fintype.card A) (P := P))

end SocialChoice
