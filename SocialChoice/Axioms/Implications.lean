import SocialChoice.Profile
import SocialChoice.Margin
import SocialChoice.Meta
import SocialChoice.Axioms.Pareto
import SocialChoice.Axioms.Unanimity
import SocialChoice.Axioms.Majority
import SocialChoice.Axioms.Condorcet
import SocialChoice.Axioms.Independence
import SocialChoice.Axioms.InformationalBasis
import SocialChoice.Axioms.Anonymity
import SocialChoice.Axioms.Reinforcement
import SocialChoice.Axioms.Reversal
import SocialChoice.Axioms.Participation
import SocialChoice.SetExtensions
import SocialChoice.Axioms.Smith
import SocialChoice.Rules.TopCycle.Defs
import SocialChoice.Rules.TopCycle.Condorcet
import SocialChoice.Rules.TopCycle.CondorcetLoser
import SocialChoice.Rules.TopCycle.MutualMajority

namespace SocialChoice

lemma not_mem_liftWinners_of_not_pred {A : Type} {p : A → Prop} [DecidablePred p]
    {s : Finset {a : A // p a}} {c : A} (hc : ¬ p c) :
    c ∉ liftWinners s := by
  classical
  intro hc'
  rcases Finset.mem_image.mp hc' with ⟨x, hx, hxc⟩
  have : p c := by
    simpa [hxc] using x.property
  exact hc this

theorem independenceOfDominated_implies_paretoEfficiency :
    Implies IndependenceOfDominated ParetoEfficiency := by
  intro f _ hInd V A _ _ _ P c d hpref
  classical
  letI : DecidableEq A := Classical.decEq A
  have hEq := hInd (P := P) (c := c) (d := d) hpref
  have hnot :
      d ∉ liftWinners (f (restrictCandidates P (fun a => a ≠ d))) :=
    not_mem_liftWinners_of_not_pred (p := fun a => a ≠ d)
      (s := f (restrictCandidates P (fun a => a ≠ d))) (by simp)
  simpa [hEq] using hnot

theorem independenceOfDominated_implies_independenceOfUniversallyLeastPreferred :
    Implies IndependenceOfDominated IndependenceOfUniversallyLeastPreferred := by
  intro f _ hInd V A _ _ _ _ P c d hcd hbot
  exact hInd (P := P) (c := c) (d := d) (fun v => hbot v c hcd)

theorem paretoEfficiency_implies_unanimity :
    Implies ParetoEfficiency Unanimity := by
  intro f hf hPar V A _ _ _ P c htop
  classical
  let _ : Nonempty A := ⟨c⟩
  have hsubset : f P ⊆ ({c} : Finset A) := by
    intro x hx
    by_contra hxne
    have hxne' : x ≠ c := by
      simpa using hxne
    have hxnot : x ∉ f P := by
      have hpref : ∀ v : V, Prefers P v c x := by
        intro v
        exact htop v x hxne'
      exact hPar (P := P) (c := c) (d := x) hpref
    exact hxnot hx
  have hnonempty : (f P).Nonempty := hf P
  rcases hnonempty with ⟨x, hx⟩
  have hx' : x = c := by
    have : x ∈ ({c} : Finset A) := hsubset hx
    simpa using this
  have hc : c ∈ f P := by
    simpa [hx'] using hx
  have hsup : ({c} : Finset A) ⊆ f P := by
    intro y hy
    have hy' : y = c := by
      simpa using hy
    subst hy'
    exact hc
  apply Finset.ext
  intro y
  constructor
  · intro hy
    exact hsubset hy
  · intro hy
    exact hsup hy

theorem mutualMajorityCriterion_implies_majorityCriterion_Imp :
    Implies MutualMajorityCriterion MajorityCriterion := by
  intro f hf hmut
  exact mutualMajorityCriterion_implies_majorityCriterion f hmut hf

theorem mutualMajorityCriterion_implies_majorityLoserCriterion_Imp :
    Implies MutualMajorityCriterion MajorityLoserCriterion := by
  intro f _ hmut
  exact mutualMajorityCriterion_implies_majorityLoserCriterion f hmut

theorem majorityCriterion_implies_unanimity :
    Implies MajorityCriterion Unanimity := by
  intro f hf hmaj V A _ _ _ P c htop
  classical
  have htop_set : votersTop P c = Finset.univ := by
    ext v
    constructor
    · intro hv
      exact Finset.mem_univ v
    · intro hv
      exact Finset.mem_filter.mpr ⟨hv, htop v⟩
  have hmaj' : StrictMajority (votersTop P c) := by
    have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ‹Nonempty V›
    have hlt : Fintype.card V < 2 * Fintype.card V := by
      have hlt' : Fintype.card V < Fintype.card V + Fintype.card V :=
        Nat.lt_add_of_pos_right (n := Fintype.card V) (k := Fintype.card V) hpos
      simpa [Nat.two_mul] using hlt'
    simpa [StrictMajority, htop_set] using hlt
  exact hmaj P c hmaj'

theorem condorcetConsistency_implies_majorityCriterion :
    Implies CondorcetConsistency MajorityCriterion := by
  intro f _ hcond V A _ _ P c hmaj
  classical
  have hcw : CondorcetWinner P c := by
    intro d hne
    have hsubset : votersTop P c ⊆ votersPreferring P c d := by
      intro v hv
      have hv_top : TopRank P v c := (Finset.mem_filter.mp hv).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv_top d hne⟩
    have hle : (votersTop P c).card ≤ (votersPreferring P c d).card :=
      Finset.card_le_card hsubset
    have hlt : Fintype.card V < 2 * (votersTop P c).card := by
      simpa [StrictMajority] using hmaj
    have hle' : 2 * (votersTop P c).card ≤ 2 * (votersPreferring P c d).card :=
      Nat.mul_le_mul_left 2 hle
    have hlt' : Fintype.card V < 2 * (votersPreferring P c d).card :=
      Nat.lt_of_lt_of_le hlt hle'
    simpa [StrictMajority] using hlt'
  exact hcond P c hcw

theorem condorcetLoserCriterion_implies_majorityLoserCriterion :
    Implies CondorcetLoserCriterion MajorityLoserCriterion := by
  intro f _ hcond V A _ _ P c hmaj hne
  classical
  have hloser : CondorcetLoser P c := by
    refine ⟨?_, hne⟩
    intro d hdc
    have hsubset : votersBottom P c ⊆ votersPreferring P d c := by
      intro v hv
      have hv_bottom : BottomRank P v c := (Finset.mem_filter.mp hv).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv_bottom d hdc⟩
    have hle : (votersBottom P c).card ≤ (votersPreferring P d c).card :=
      Finset.card_le_card hsubset
    have hlt : Fintype.card V < 2 * (votersBottom P c).card := by
      simp [StrictMajority] at hmaj
      exact hmaj
    have hle' : 2 * (votersBottom P c).card ≤ 2 * (votersPreferring P d c).card :=
      Nat.mul_le_mul_left 2 hle
    have hlt' : Fintype.card V < 2 * (votersPreferring P d c).card :=
      Nat.lt_of_lt_of_le hlt hle'
    simpa [StrictMajority] using hlt'
  exact hcond P c hloser

theorem smithCriterion_implies_mutualMajorityCriterion_Imp :
    Implies SmithCriterion MutualMajorityCriterion := by
  intro f hf hsmith
  exact mutualMajorityCriterion_preservedUnderRefinement
    f topCycle hf topCycle_isVotingRule hsmith topCycle_mutualMajorityCriterion

theorem smithCriterion_implies_condorcetConsistency_Imp :
    Implies SmithCriterion CondorcetConsistency := by
  intro f hf hsmith
  apply PreservedUnderRefinement.apply condorcetConsistency_preservedUnderRefinement
    (f := f) (g := topCycle)
  · exact hf
  · exact topCycle_isVotingRule
  · exact hsmith
  · exact topCycle_condorcetConsistency

theorem smithCriterion_implies_condorcetLoserCriterion_Imp :
    Implies SmithCriterion CondorcetLoserCriterion := by
  intro f hf hsmith
  apply PreservedUnderRefinement.apply condorcetLoserCriterion_preservedUnderRefinement
    (f := f) (g := topCycle)
  · exact hf
  · exact topCycle_isVotingRule
  · exact hsmith
  · exact topCycle_condorcetLoser_criterion

theorem reversalSymmetry_implies_singletonReversalSymmetry :
    Implies ReversalSymmetry SingletonReversalSymmetry := by
  intro f _ hrev V A _ _ P x hnontriv hx
  classical
  letI : DecidableEq A := Classical.decEq A
  have hnot_univ : f P ≠ (Finset.univ : Finset A) := by
    rcases hnontriv with ⟨y, hy⟩
    intro hEq
    have hy_mem : y ∈ f P := by
      simp [hEq]
    have hy' : y = x := by
      simp [hx] at hy_mem
      exact hy_mem
    exact hy hy'.symm
  have hdisj := hrev (P := P) hnot_univ
  have hxmem : x ∈ f P := by
    simp [hx]
  intro hxrev
  have hxinter : x ∈ f P ∩ f (reverse_profile P) := by
    exact Finset.mem_inter.mpr ⟨hxmem, hxrev⟩
  have : x ∈ (∅ : Finset A) := by
    rw [hdisj] at hxinter
    exact hxinter
  simp at this

noncomputable def relabelProfileVoters {V W A : Type} [Fintype V] [Fintype W] [Fintype A]
    (e : W ≃ V) (P : Profile V A) : Profile W A :=
  { pref := fun w => P.pref (e w) }

lemma margin_relabelProfileVoters {V W A : Type} [Fintype V] [Fintype W] [Fintype A]
    (e : W ≃ V) (P : Profile V A) (a b : A) :
    margin (relabelProfileVoters e P) a b = margin P a b := by
  classical
  have hcard_ab :
      (Finset.univ.filter (fun w => Prefers (relabelProfileVoters e P) w a b)).card =
        (Finset.univ.filter (fun v => Prefers P v a b)).card := by
    refine Finset.card_bij
      (s := Finset.univ.filter (fun w => Prefers (relabelProfileVoters e P) w a b))
      (t := Finset.univ.filter (fun v => Prefers P v a b))
      (i := fun w _ => e w) ?_ ?_ ?_
    · intro w hw
      have hw' : Prefers (relabelProfileVoters e P) w a b := (Finset.mem_filter.mp hw).2
      have hw'' : Prefers P (e w) a b := by
        exact hw'
      exact Finset.mem_filter.mpr ⟨by simp, hw''⟩
    · intro w1 _ w2 _ h
      exact e.injective h
    · intro v hv
      have hv' : Prefers P v a b := (Finset.mem_filter.mp hv).2
      refine ⟨e.symm v, ?_, by simp⟩
      have : Prefers (relabelProfileVoters e P) (e.symm v) a b := by
        unfold Prefers at hv' ⊢
        rw [show (relabelProfileVoters e P).pref (e.symm v) = P.pref v by
          simp [relabelProfileVoters]]
        exact hv'
      exact Finset.mem_filter.mpr ⟨by simp, this⟩
  have hcard_ba :
      (Finset.univ.filter (fun w => Prefers (relabelProfileVoters e P) w b a)).card =
        (Finset.univ.filter (fun v => Prefers P v b a)).card := by
    refine Finset.card_bij
      (s := Finset.univ.filter (fun w => Prefers (relabelProfileVoters e P) w b a))
      (t := Finset.univ.filter (fun v => Prefers P v b a))
      (i := fun w _ => e w) ?_ ?_ ?_
    · intro w hw
      have hw' : Prefers (relabelProfileVoters e P) w b a := (Finset.mem_filter.mp hw).2
      have hw'' : Prefers P (e w) b a := by
        exact hw'
      exact Finset.mem_filter.mpr ⟨by simp, hw''⟩
    · intro w1 _ w2 _ h
      exact e.injective h
    · intro v hv
      have hv' : Prefers P v b a := (Finset.mem_filter.mp hv).2
      refine ⟨e.symm v, ?_, by simp⟩
      have : Prefers (relabelProfileVoters e P) (e.symm v) b a := by
        unfold Prefers at hv' ⊢
        rw [show (relabelProfileVoters e P).pref (e.symm v) = P.pref v by
          simp [relabelProfileVoters]]
        exact hv'
      exact Finset.mem_filter.mpr ⟨by simp, this⟩
  simp [margin, hcard_ab, hcard_ba]

noncomputable def inlElectorateEquiv {U : Type} [DecidableEq U] (V : Finset U) :
    Electorate (U ⊕ Unit) (V.image Sum.inl) ≃ Electorate U V := by
  classical
  refine
    { toFun := fun v =>
        let hx : ∃ u, u ∈ V ∧ Sum.inl u = v.1 := by
          rcases Finset.mem_image.mp v.2 with ⟨u, huV, huv⟩
          exact ⟨u, huV, huv⟩
        let u := Classical.choose hx
        have huV : u ∈ V := (Classical.choose_spec hx).1
        ⟨u, huV⟩
      invFun := fun v => ⟨Sum.inl v.1, Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro v
    cases v with
    | mk v hv =>
        -- Unpack the chosen witness from `toFun`.
        let hx : ∃ u, u ∈ V ∧ Sum.inl u = v := by
          rcases Finset.mem_image.mp hv with ⟨u, huV, huv⟩
          exact ⟨u, huV, huv⟩
        have hval : Sum.inl (Classical.choose hx) = v :=
          (Classical.choose_spec hx).2
        apply Subtype.ext
        exact hval
  · intro v
    -- Unfold the chosen witness from `toFun (invFun v)`.
    let hx : ∃ u, u ∈ V ∧ Sum.inl (β := Unit) u = Sum.inl (β := Unit) v.1 :=
      ⟨v.1, v.2, rfl⟩
    have hval : Sum.inl (β := Unit) (Classical.choose hx) = Sum.inl (β := Unit) v.1 :=
      (Classical.choose_spec hx).2
    apply Subtype.ext
    exact Sum.inl.inj hval

theorem reinforcement_implies_subsetReinforcement :
    Implies Reinforcement SubsetReinforcement := by
  intro f _ href
  exact reinforcement_subset (f := f) href

theorem marginBased_implies_anonymity :
    Implies MarginBased Anonymity := by
  intro f _ hmargin V A _ _ P σ
  classical
  apply hmargin (P₁ := permuteVoters P σ) (P₂ := P)
  intro x y
  simp

theorem marginBased_implies_neutralReversal :
    Implies MarginBased NeutralReversal := by
  intro f _ hmargin V A _ _ P r
  classical
  refine hmargin (P₁ := P)
    (P₂ := addVoter (addVoter P r) (reverse_ballot r)) ?_
  intro a b
  by_cases hEq : a = b
  · subst hEq
    simp [self_margin_zero]
  · let _ := r
    have htr : a < b ∨ b < a := lt_or_gt_of_ne hEq
    cases htr with
    | inl hlt =>
        have h1 : margin (addVoter P r) a b = margin P a b + 1 :=
          margin_addVoter_eq_of_prefers P r a b (by simpa using hlt)
        have hrev : (reverse_ballot r).lt b a := by
          exact hlt
        have h2 :
            margin (addVoter (addVoter P r) (reverse_ballot r)) a b =
              margin (addVoter P r) a b - 1 :=
          margin_addVoter_eq_of_prefers_rev
            (P := addVoter P r) (ballot := reverse_ballot r) a b hrev
        symm
        calc
          margin (addVoter (addVoter P r) (reverse_ballot r)) a b
              = margin (addVoter P r) a b - 1 := h2
          _ = margin P a b + 1 - 1 := by simp [h1]
          _ = margin P a b := by simp
    | inr hgt =>
        have h1 : margin (addVoter P r) a b = margin P a b - 1 :=
          margin_addVoter_eq_of_prefers_rev P r a b (by simpa using hgt)
        have hrev : (reverse_ballot r).lt a b := by
          exact hgt
        have h2 :
            margin (addVoter (addVoter P r) (reverse_ballot r)) a b =
              margin (addVoter P r) a b + 1 :=
          margin_addVoter_eq_of_prefers
            (P := addVoter P r) (ballot := reverse_ballot r) a b hrev
        symm
        calc
          margin (addVoter (addVoter P r) (reverse_ballot r)) a b
              = margin (addVoter P r) a b + 1 := h2
          _ = margin P a b - 1 + 1 := by simp [h1]
          _ = margin P a b := by simp

theorem topsOnly_implies_anonymity :
    Implies TopsOnly Anonymity := by
  intro f _ htops V A _ _ P σ
  classical
  apply htops (P₁ := permuteVoters P σ) (P₂ := P)
  intro a
  simp

-- Ding, Holliday, and Pacuit, "An Axiomatic Characterization of Split Cycle"
-- (proposition on Neutral Reversal implying Positive/Negative Involvement equivalence).
theorem marginBased_positiveInvolvement_iff_negativeInvolvement :
    Implies MarginBased (fun f => PositiveInvolvement f ↔ NegativeInvolvement f) := by
  intro f _ hmargin
  classical
  constructor
  · intro hpos
    by_contra hneg
    -- Extract a counterexample to Negative Involvement.
    rcases (by
      simpa [NegativeInvolvement] using hneg) with
      ⟨U, A, _instDecEqU, _instFintypeA, V, u, hu, P, Q,
        hagree, c, hcP, hbot, hcQ⟩
    -- Embed the electorate into a disjoint sum so we can add the reverse ballot.
    have hagree' :
        ∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v := by
      intro v
      simpa using (hagree v.1 v.2)
    let V' : Finset (U ⊕ Unit) := (insert u V).image Sum.inl
    let eV' : Electorate (U ⊕ Unit) V' ≃ Electorate U (insert u V) :=
      inlElectorateEquiv (U := U) (V := insert u V)
    let Q' : Profile (Electorate (U ⊕ Unit) V') A :=
      relabelProfileVoters eV' Q
    have hmarginQ' : ∀ a b, margin Q' a b = margin Q a b := by
      intro a b
      simpa using margin_relabelProfileVoters (e := eV') (P := Q) a b
    have hQeq : f Q' = f Q := by
      apply hmargin (P₁ := Q') (P₂ := Q)
      intro a b
      simpa using hmarginQ' a b
    have hcQ' : c ∈ f Q' := by
      simpa [hQeq] using hcQ
    -- Now add the reverse ballot as a new voter.
    let w : U ⊕ Unit := Sum.inr ()
    have hw : w ∉ V' := by
      simp [V']
    let Q'' : Profile (Electorate (U ⊕ Unit) (insert w V')) A :=
      { pref := fun v => if h : v.1 ∈ V' then Q'.pref ⟨v.1, h⟩
          else reverse_ballot (Q.pref (newVoter (u := u) (V := V) hu)) }
    have hagree'' :
        ∀ v : Electorate (U ⊕ Unit) V',
          Q''.pref (liftVoter (u := w) v) = Q'.pref v := by
      intro v
      have hv : (liftVoter (u := w) v).1 ∈ V' := v.2
      simp [Q'', liftVoter]
    have hnew :
        Q''.pref (newVoter (u := w) (V := V') hw) =
          reverse_ballot (Q.pref (newVoter (u := u) (V := V) hu)) := by
      simp [Q'', newVoter, hw]
    have htop' :
        BallotTop (Q''.pref (newVoter (u := w) (V := V') hw)) c := by
      have htop' : BallotTop (reverse_ballot (Q.pref (newVoter (u := u) (V := V) hu))) c := by
        intro d hd
        have := hbot d hd
        exact this
      simpa [hnew] using htop'
    -- Show c ∉ f Q'' using MarginBased (margins are unchanged from P).
    have hmarginP :
        ∀ a b, margin Q'' a b = margin P a b := by
      intro a b
      by_cases hEq : a = b
      · subst hEq
        simp [self_margin_zero]
      ·
        let L := Q.pref (newVoter (u := u) (V := V) hu)
        let _ := L
        have htr : L.lt a b ∨ L.lt b a := lt_or_gt_of_ne hEq
        cases htr with
        | inl hlt =>
            have hQP :
                margin Q a b = margin P a b + 1 :=
              margin_add_newVoter_eq_of_prefers
                (u := u) (V := V) hu P Q hagree' a b (by simpa [L] using hlt)
            have hQ'P :
                margin Q' a b = margin P a b + 1 := by
              calc
                margin Q' a b = margin Q a b := hmarginQ' a b
                _ = margin P a b + 1 := hQP
            have hrev : (reverse_ballot L).lt b a := by
              exact hlt
            have hrev' :
                (Q''.pref (newVoter (u := w) (V := V') hw)).lt b a := by
              rw [hnew]
              exact hrev
            have hQ'' :
                margin Q'' a b = margin Q' a b - 1 :=
              margin_add_newVoter_eq_of_prefers_rev
                (u := w) (V := V') hw Q' Q'' hagree'' a b hrev'
            calc
              margin Q'' a b = margin Q' a b - 1 := hQ''
              _ = margin P a b + 1 - 1 := by simp [hQ'P]
              _ = margin P a b := by simp
        | inr hgt =>
            have hQP :
                margin Q a b = margin P a b - 1 :=
              margin_add_newVoter_eq_of_prefers_rev
                (u := u) (V := V) hu P Q hagree' a b (by simpa [L] using hgt)
            have hQ'P :
                margin Q' a b = margin P a b - 1 := by
              calc
                margin Q' a b = margin Q a b := hmarginQ' a b
                _ = margin P a b - 1 := hQP
            have hrev : (reverse_ballot L).lt a b := by
              exact hgt
            have hrev' :
                (Q''.pref (newVoter (u := w) (V := V') hw)).lt a b := by
              rw [hnew]
              exact hrev
            have hQ'' :
                margin Q'' a b = margin Q' a b + 1 :=
              margin_add_newVoter_eq_of_prefers
                (u := w) (V := V') hw Q' Q'' hagree'' a b hrev'
            calc
              margin Q'' a b = margin Q' a b + 1 := hQ''
              _ = margin P a b - 1 + 1 := by simp [hQ'P]
              _ = margin P a b := by simp
    have hQ''eq : f Q'' = f P := by
      apply hmargin (P₁ := Q'') (P₂ := P)
      intro a b
      simpa using hmarginP a b
    have hcQ'' : c ∉ f Q'' := by
      simpa [hQ''eq] using hcP
    -- This contradicts Positive Involvement.
    have hcQ''mem : c ∈ f Q'' :=
      hpos (V := V') (u := w) hw Q' Q'' c hagree'' hcQ' htop'
    exact (hcQ'' hcQ''mem).elim
  · intro hneg
    by_contra hpos
    -- Extract a counterexample to Positive Involvement.
    rcases (by
      simpa [PositiveInvolvement] using hpos) with
      ⟨U, A, _instDecEqU, _instFintypeA, V, u, hu, P, Q,
        hagree, c, hcP, htop, hcQ⟩
    -- Embed the electorate into a disjoint sum so we can add the reverse ballot.
    have hagree' :
        ∀ v : Electorate U V, Q.pref (liftVoter (u := u) v) = P.pref v := by
      intro v
      simpa using (hagree v.1 v.2)
    let V' : Finset (U ⊕ Unit) := (insert u V).image Sum.inl
    let eV' : Electorate (U ⊕ Unit) V' ≃ Electorate U (insert u V) :=
      inlElectorateEquiv (U := U) (V := insert u V)
    let Q' : Profile (Electorate (U ⊕ Unit) V') A :=
      relabelProfileVoters eV' Q
    have hmarginQ' : ∀ a b, margin Q' a b = margin Q a b := by
      intro a b
      simpa using margin_relabelProfileVoters (e := eV') (P := Q) a b
    have hQeq : f Q' = f Q := by
      apply hmargin (P₁ := Q') (P₂ := Q)
      intro a b
      simpa using hmarginQ' a b
    have hcQ' : c ∉ f Q' := by
      simpa [hQeq] using hcQ
    -- Add the reverse ballot as a new voter.
    let w : U ⊕ Unit := Sum.inr ()
    have hw : w ∉ V' := by
      simp [V']
    let Q'' : Profile (Electorate (U ⊕ Unit) (insert w V')) A :=
      { pref := fun v => if h : v.1 ∈ V' then Q'.pref ⟨v.1, h⟩
          else reverse_ballot (Q.pref (newVoter (u := u) (V := V) hu)) }
    have hagree'' :
        ∀ v : Electorate (U ⊕ Unit) V',
          Q''.pref (liftVoter (u := w) v) = Q'.pref v := by
      intro v
      have hv : (liftVoter (u := w) v).1 ∈ V' := v.2
      simp [Q'', liftVoter]
    have hnew :
        Q''.pref (newVoter (u := w) (V := V') hw) =
          reverse_ballot (Q.pref (newVoter (u := u) (V := V) hu)) := by
      simp [Q'', newVoter, hw]
    have hbot' :
        BallotBottom (Q''.pref (newVoter (u := w) (V := V') hw)) c := by
      have hbot' : BallotBottom (reverse_ballot (Q.pref (newVoter (u := u) (V := V) hu))) c := by
        intro d hd
        have := htop d hd
        exact this
      simpa [hnew] using hbot'
    -- Show c ∈ f Q'' using MarginBased (margins are unchanged from P).
    have hmarginP :
        ∀ a b, margin Q'' a b = margin P a b := by
      intro a b
      by_cases hEq : a = b
      · subst hEq
        simp [self_margin_zero]
      ·
        let L := Q.pref (newVoter (u := u) (V := V) hu)
        let _ := L
        have htr : L.lt a b ∨ L.lt b a := lt_or_gt_of_ne hEq
        cases htr with
        | inl hlt =>
            have hQP :
                margin Q a b = margin P a b + 1 :=
              margin_add_newVoter_eq_of_prefers
                (u := u) (V := V) hu P Q hagree' a b (by simpa [L] using hlt)
            have hQ'P :
                margin Q' a b = margin P a b + 1 := by
              calc
                margin Q' a b = margin Q a b := hmarginQ' a b
                _ = margin P a b + 1 := hQP
            have hrev : (reverse_ballot L).lt b a := by
              exact hlt
            have hrev' :
                (Q''.pref (newVoter (u := w) (V := V') hw)).lt b a := by
              rw [hnew]
              exact hrev
            have hQ'' :
                margin Q'' a b = margin Q' a b - 1 :=
              margin_add_newVoter_eq_of_prefers_rev
                (u := w) (V := V') hw Q' Q'' hagree'' a b hrev'
            calc
              margin Q'' a b = margin Q' a b - 1 := hQ''
              _ = margin P a b + 1 - 1 := by simp [hQ'P]
              _ = margin P a b := by simp
        | inr hgt =>
            have hQP :
                margin Q a b = margin P a b - 1 :=
              margin_add_newVoter_eq_of_prefers_rev
                (u := u) (V := V) hu P Q hagree' a b (by simpa [L] using hgt)
            have hQ'P :
                margin Q' a b = margin P a b - 1 := by
              calc
                margin Q' a b = margin Q a b := hmarginQ' a b
                _ = margin P a b - 1 := hQP
            have hrev : (reverse_ballot L).lt a b := by
              exact hgt
            have hrev' :
                (Q''.pref (newVoter (u := w) (V := V') hw)).lt a b := by
              rw [hnew]
              exact hrev
            have hQ'' :
                margin Q'' a b = margin Q' a b + 1 :=
              margin_add_newVoter_eq_of_prefers
                (u := w) (V := V') hw Q' Q'' hagree'' a b hrev'
            calc
              margin Q'' a b = margin Q' a b + 1 := hQ''
              _ = margin P a b - 1 + 1 := by simp [hQ'P]
              _ = margin P a b := by simp
    have hQ''eq : f Q'' = f P := by
      apply hmargin (P₁ := Q'') (P₂ := P)
      intro a b
      simpa using hmarginP a b
    have hcQ'' : c ∈ f Q'' := by
      simpa [hQ''eq] using hcP
    -- This contradicts Negative Involvement.
    have hcQ''not : c ∉ f Q'' :=
      hneg (V := V') (u := w) hw Q' Q'' c hagree'' hcQ' hbot'
    exact (hcQ''not hcQ'').elim

theorem strongParticipation_implies_of_weakRefinement
    (E₁ E₂ : ∀ {A : Type}, LinearOrder A → SetExtension A)
    (href :
      ∀ {A : Type} [DecidableEq A] (r : LinearOrder A) (s t : Finset A),
        s.Nonempty → t.Nonempty →
        (E₁ (A := A) r).weak s t → (E₂ (A := A) r).weak s t) :
    Implies (StrongParticipation E₁) (StrongParticipation E₂) := by
  intro f hf hpart U A _ _ _ _ V u hu P Q hagree
  have hQ : (f Q).Nonempty := hf Q
  have hP : (f P).Nonempty := hf P
  exact href (Q.pref (newVoter (u := u) (V := V) hu)) (f Q) (f P) hQ hP
    (hpart (V := V) (u := u) hu P Q hagree)

theorem strongFishburnParticipation_implies_optimistParticipation :
    Implies StrongFishburnParticipation OptimistParticipation := by
  apply strongParticipation_implies_of_weakRefinement
    (E₁ := fun {A} r => FishburnExtension (A := A) r)
    (E₂ := fun {A} r => OptimistExtension (A := A) r)
  intro A _ r s t hs ht hfish
  letI : DecidableEq A := r.toDecidableEq
  have hfish' : (FishburnExtension (A := A) r).weak s t := by
    simpa using hfish
  exact fishburnExtension_weak_implies_optimistExtension_weak
    (r := r) hs ht hfish'

theorem strongFishburnParticipation_implies_positiveInvolvement :
    Implies StrongFishburnParticipation PositiveInvolvement := by
  intro f hf hpart U A _ _ V u hu P Q c hagree hc htop
  classical
  let _ : Nonempty A := ⟨c⟩
  let r := Q.pref (newVoter (u := u) (V := V) hu)
  letI : LinearOrder A := r
  have hfish : FishburnWeak r (f Q) (f P) := by
    simpa [StrongFishburnParticipation, StrongParticipation, FishburnExtension, r] using
      (hpart (V := V) (u := u) hu P Q hagree)
  by_contra hcQ
  have hneQ : (f Q).Nonempty := hf Q
  rcases hneQ with ⟨x, hx⟩
  have hxne : x ≠ c := by
    intro hxc
    exact hcQ (by simpa [hxc] using hx)
  have hcs : c ∈ f P \ f Q := by
    exact Finset.mem_sdiff.mpr ⟨hc, hcQ⟩
  obtain ⟨h1, h2, h3⟩ := hfish
  have hle : r.le x c := by
    by_cases hxP : x ∈ f P
    · have hxst : x ∈ f Q ∩ f P := Finset.mem_inter.mpr ⟨hx, hxP⟩
      exact h2 x hxst c hcs
    · have hxst : x ∈ f Q \ f P := Finset.mem_sdiff.mpr ⟨hx, hxP⟩
      exact h3 x hxst c hcs
  have hlt : r.lt c x := htop x hxne
  exact (not_le_of_gt hlt) hle

theorem strongFishburnParticipation_implies_negativeInvolvement :
    Implies StrongFishburnParticipation NegativeInvolvement := by
  intro f hf hpart U A _ _ V u hu P Q c hagree hc hbot
  classical
  let _ : Nonempty A := ⟨c⟩
  let r := Q.pref (newVoter (u := u) (V := V) hu)
  letI : LinearOrder A := r
  have hfish : FishburnWeak r (f Q) (f P) := by
    simpa [StrongFishburnParticipation, StrongParticipation, FishburnExtension, r] using
      (hpart (V := V) (u := u) hu P Q hagree)
  by_contra hcQ
  have hcQ' : c ∈ f Q := by
    simpa using hcQ
  have hneP : (f P).Nonempty := hf P
  rcases hneP with ⟨x, hx⟩
  have hxne : x ≠ c := by
    intro hxc
    exact hc (by simpa [hxc] using hx)
  have hcs : c ∈ f Q \ f P := by
    exact Finset.mem_sdiff.mpr ⟨hcQ', hc⟩
  obtain ⟨h1, h2, h3⟩ := hfish
  have hle : r.le c x := by
    by_cases hxQ : x ∈ f Q
    · have hxst : x ∈ f Q ∩ f P := Finset.mem_inter.mpr ⟨hxQ, hx⟩
      exact h1 c hcs x hxst
    · have hxst : x ∈ f P \ f Q := Finset.mem_sdiff.mpr ⟨hx, hxQ⟩
      exact h3 c hcs x hxst
  have hlt : r.lt x c := hbot x hxne
  exact (not_le_of_gt hlt) hle

theorem optimistParticipation_implies_positiveInvolvement :
    Implies OptimistParticipation PositiveInvolvement := by
  intro f _ hopt U A _ _ V u hu P Q c hagree hc htop
  classical
  let _ : Nonempty A := ⟨c⟩
  let r := Q.pref (newVoter (u := u) (V := V) hu)
  letI : LinearOrder A := r
  have hopt' : OptimistWeak r (f Q) (f P) := by
    simpa [OptimistParticipation, StrongParticipation, OptimistExtension, r] using
      (hopt (V := V) (u := u) hu P Q hagree)
  rcases hopt' with ⟨a, b, haQ, hbP, hle⟩
  have hb_eq : b = c := by
    by_contra hbc
    have hbc' : b < c := by
      simpa using (hbP.2 c hc (by simpa [eq_comm] using hbc))
    have hcb : c < b := by
      simpa using (htop b hbc)
    exact (lt_asymm hbc' hcb).elim
  have ha_eq : a = c := by
    have hle' : a ≤ c := by
      simpa [hb_eq] using hle
    by_contra hac
    have hca : c < a := by
      simpa using (htop a hac)
    exact (not_le_of_gt hca) hle'
  simpa [ha_eq] using haQ.1

theorem positiveInvolvement_implies_singletonPositiveInvolvement :
    Implies PositiveInvolvement SingletonPositiveInvolvement := by
  intro f _ hpos V A _ _ V' u hu P Q c hagree hfP htop
  apply hpos (V := V') (u := u) hu P Q c hagree
  · rw [hfP]
    exact Finset.mem_singleton_self c
  · exact htop

end SocialChoice
