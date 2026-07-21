import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Duplicate
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import SocialChoice.Margin

namespace SocialChoice

section SchulzePath

variable {V A : Type} [Fintype V] [Fintype A]

noncomputable def pathStrengthAux (P : Profile V A) :
    A -> List A -> Int -> Int
  | _, [], m => m
  | a, b :: t, m => pathStrengthAux P b t (min m (margin P a b))

noncomputable def pathStrength (P : Profile V A) : List A -> Int
  | [] => 0
  | [_] => 0
  | a :: b :: t => pathStrengthAux P b t (margin P a b)

noncomputable def pathMargins (P : Profile V A) : List A -> List Int
  | [] => []
  | [_] => []
  | a :: b :: t => margin P a b :: pathMargins P (b :: t)

def minList : List Int -> Int
  | [] => 0
  | m :: ms => List.foldl min m ms

noncomputable def listsOfLength (n : Nat) : Finset (List A) := by
  classical
  exact (Finset.univ : Finset (Fin n → A)).image (fun f => List.ofFn f)

noncomputable def pathsOfLength (n : Nat) (a b : A) : Finset (List A) := by
  classical
  exact (listsOfLength (A := A) n).filter (fun l =>
    l.length = n ∧ l.head? = some a ∧ l.getLast? = some b ∧ l.Nodup)

noncomputable def pathsOfLengthAny (n : Nat) (a b : A) : Finset (List A) := by
  classical
  exact (listsOfLength (A := A) n).filter (fun l =>
    l.length = n ∧ l.head? = some a ∧ l.getLast? = some b)

noncomputable def pathsUpTo (n : Nat) (a b : A) : Finset (List A) := by
  classical
  let lengths := (Finset.range (n + 1)).filter (fun k => 2 ≤ k)
  exact lengths.biUnion (fun k => pathsOfLength k a b)

noncomputable def pathsUpToAny (n : Nat) (a b : A) : Finset (List A) := by
  classical
  let lengths := (Finset.range (n + 1)).filter (fun k => 2 ≤ k)
  exact lengths.biUnion (fun k => pathsOfLengthAny k a b)

noncomputable def strongestPath (P : Profile V A) (a b : A) : Int := by
  classical
  let paths := pathsUpTo (Fintype.card A) a b
  by_cases hne : paths.Nonempty
  · let strengths := paths.image (fun l => pathStrength P l)
    have hstrengths : strengths.Nonempty := by
      rcases hne with ⟨l, hl⟩
      exact ⟨pathStrength P l, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩
    exact Finset.max' strengths hstrengths
  · exact margin P a b

noncomputable def strongestPathAny (P : Profile V A) (a b : A) : Int := by
  classical
  let paths := pathsUpToAny (Fintype.card A) a b
  by_cases hne : paths.Nonempty
  · let strengths := paths.image (fun l => pathStrength P l)
    have hstrengths : strengths.Nonempty := by
      rcases hne with ⟨l, hl⟩
      exact ⟨pathStrength P l, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩
    exact Finset.max' strengths hstrengths
  · exact margin P a b

@[simp] lemma pathStrength_nil (P : Profile V A) :
    pathStrength P [] = 0 := by
  simp [pathStrength]

@[simp] lemma pathStrength_singleton (P : Profile V A) (a : A) :
    pathStrength P [a] = 0 := by
  simp [pathStrength]

@[simp] lemma pathStrength_two (P : Profile V A) (a b : A) :
    pathStrength P [a, b] = margin P a b := by
  simp [pathStrength, pathStrengthAux]

lemma pathStrengthAux_eq_foldl (P : Profile V A) :
    ∀ a l m, pathStrengthAux P a l m = List.foldl min m (pathMargins P (a :: l))
  | a, [], m => by
      simp [pathStrengthAux, pathMargins]
  | a, b :: t, m => by
      simp [pathStrengthAux, pathMargins, pathStrengthAux_eq_foldl (a := b) (l := t)
        (m := min m (margin P a b))]

lemma pathStrength_eq_minList (P : Profile V A) :
    ∀ l, pathStrength P l = minList (pathMargins P l)
  | [] => by
      simp [pathStrength, pathMargins, minList]
  | [a] => by
      simp [pathStrength, pathMargins, minList]
  | a :: b :: t => by
      simp [pathStrength, pathMargins, minList, pathStrengthAux_eq_foldl]

lemma foldl_min_eq_min (m : Int) :
    ∀ t, t ≠ [] → List.foldl min m t = min m (minList t)
  | [], ht => (ht rfl).elim
  | n :: ns, _ => by
      cases ns with
      | nil =>
          simp [minList]
      | cons x xs =>
          have ih1 : List.foldl min (min m n) (x :: xs) =
              min (min m n) (minList (x :: xs)) :=
            (foldl_min_eq_min (m := min m n) (t := x :: xs) (by simp))
          have hminlist : List.foldl min n (x :: xs) = min n (minList (x :: xs)) :=
            (foldl_min_eq_min (m := n) (t := x :: xs) (by simp))
          calc
            List.foldl min m (n :: x :: xs)
                = List.foldl min (min m n) (x :: xs) := by rfl
            _ = min (min m n) (minList (x :: xs)) := ih1
            _ = min m (min n (minList (x :: xs))) := by simp [min_assoc]
            _ = min m (List.foldl min n (x :: xs)) := by simp [hminlist]
            _ = min m (minList (n :: x :: xs)) := by simp [minList]

lemma minList_append (s t : List Int) (hs : s ≠ []) (ht : t ≠ []) :
    minList (s ++ t) = min (minList s) (minList t) := by
  cases s with
  | nil =>
      exact (hs rfl).elim
  | cons m ms =>
      cases t with
      | nil =>
          exact (ht rfl).elim
      | cons n ns =>
          have : List.foldl min m (ms ++ n :: ns) =
              min (List.foldl min m ms) (minList (n :: ns)) := by
            have hfold :
                List.foldl min m (ms ++ n :: ns) =
                  List.foldl min (List.foldl min m ms) (n :: ns) := by
                simp [List.foldl_append]
            have hmin :
                List.foldl min (List.foldl min m ms) (n :: ns) =
                  min (List.foldl min m ms) (minList (n :: ns)) :=
                (foldl_min_eq_min (m := List.foldl min m ms) (t := n :: ns) (by simp))
            exact hfold.trans hmin
          simpa [minList] using this


lemma pathMargins_append_cons (P : Profile V A) :
    ∀ l b u, l ≠ [] →
      pathMargins P (l ++ b :: u) =
        pathMargins P (l ++ [b]) ++ pathMargins P (b :: u)
  | [], _b, _u, hl => (hl rfl).elim
  | [a], b, u, _ => by
      simp [pathMargins]
  | a :: c :: t, b, u, _ => by
      have ih := pathMargins_append_cons (P := P) (l := c :: t) (b := b) (u := u) (by simp)
      have ih' :
          pathMargins P (c :: t ++ b :: u) =
            pathMargins P (c :: t ++ [b]) ++ pathMargins P (b :: u) := by
        simpa [List.cons_append] using ih
      simpa [pathMargins, List.cons_append, List.append_assoc, ih']

lemma pathStrength_remove_repeat_ge (P : Profile V A) (l1 l2 l3 : List A) (x : A)
    (hl1 : l1 ≠ []) (hl3 : l3 ≠ []) :
    pathStrength P (l1 ++ x :: l2 ++ x :: l3) ≤ pathStrength P (l1 ++ x :: l3) := by
  classical
  cases l1 with
  | nil => cases hl1 rfl
  | cons a t1 =>
      cases l3 with
      | nil => cases hl3 rfl
      | cons c t3 =>
          have hpm1 :
              pathMargins P ((a :: t1) ++ x :: l2 ++ x :: (c :: t3)) =
                pathMargins P ((a :: t1) ++ [x]) ++ pathMargins P (x :: l2 ++ x :: (c :: t3)) := by
            have h := pathMargins_append_cons (P := P) (l := a :: t1) (b := x) (u := l2 ++ x :: c :: t3)
              (by simp)
            simpa [List.append_assoc] using h
          have hpm2 :
              pathMargins P ((a :: t1) ++ x :: (c :: t3)) =
                pathMargins P ((a :: t1) ++ [x]) ++ pathMargins P (x :: (c :: t3)) := by
            exact pathMargins_append_cons (P := P) (l := a :: t1) (b := x) (u := c :: t3) (by simp)
          have hpm3 :
              pathMargins P (x :: l2 ++ x :: (c :: t3)) =
                pathMargins P ((x :: l2) ++ [x]) ++ pathMargins P (x :: (c :: t3)) := by
            exact pathMargins_append_cons (P := P) (l := x :: l2) (b := x) (u := c :: t3) (by simp)
          have hpm1' :
              pathMargins P (a :: (t1 ++ x :: l2 ++ x :: c :: t3)) =
                pathMargins P (a :: (t1 ++ [x])) ++ pathMargins P (x :: (l2 ++ x :: c :: t3)) := by
            simpa [List.cons_append, List.append_assoc] using hpm1
          have hpm1'' :
              pathMargins P (a :: (t1 ++ x :: (l2 ++ x :: c :: t3))) =
                pathMargins P (a :: (t1 ++ [x])) ++ pathMargins P (x :: (l2 ++ x :: c :: t3)) := by
            simpa [List.append_assoc] using hpm1'
          have hpm2' :
              pathMargins P (a :: (t1 ++ x :: c :: t3)) =
                pathMargins P (a :: (t1 ++ [x])) ++ pathMargins P (x :: c :: t3) := by
            simpa [List.cons_append, List.append_assoc] using hpm2
          have hpm3' :
              pathMargins P (x :: (l2 ++ x :: c :: t3)) =
                pathMargins P (x :: (l2 ++ [x])) ++ pathMargins P (x :: c :: t3) := by
            simpa [List.cons_append, List.append_assoc] using hpm3
          have hnon_s : pathMargins P ((a :: t1) ++ [x]) ≠ [] := by
            cases t1 with
            | nil => simp [pathMargins]
            | cons d t1' => simp [pathMargins]
          have hnon_t2 : pathMargins P (x :: (c :: t3)) ≠ [] := by
            simp [pathMargins]
          have hnon_mid : pathMargins P (x :: l2 ++ x :: (c :: t3)) ≠ [] := by
            cases l2 with
            | nil => simp [pathMargins]
            | cons d t2' => simp [pathMargins]
          have hmin_total :
              minList (pathMargins P (a :: (t1 ++ x :: l2 ++ x :: c :: t3))) =
                min (minList (pathMargins P (a :: (t1 ++ [x]))))
                  (minList (pathMargins P (x :: (l2 ++ x :: c :: t3)))) := by
            have h := minList_append
              (s := pathMargins P (a :: (t1 ++ [x])))
              (t := pathMargins P (x :: (l2 ++ x :: c :: t3))) hnon_s hnon_mid
            calc
              minList (pathMargins P (a :: (t1 ++ x :: l2 ++ x :: c :: t3))) =
                  minList (pathMargins P (a :: (t1 ++ [x])) ++
                    pathMargins P (x :: (l2 ++ x :: c :: t3))) := by
                      simp [hpm1'']
              _ = min (minList (pathMargins P (a :: (t1 ++ [x]))))
                    (minList (pathMargins P (x :: (l2 ++ x :: c :: t3)))) := by
                      simpa using h
          have hmin_mid :
              minList (pathMargins P (x :: (l2 ++ x :: c :: t3))) =
                min (minList (pathMargins P (x :: (l2 ++ [x]))))
                  (minList (pathMargins P (x :: c :: t3))) := by
            have h := minList_append
              (s := pathMargins P (x :: (l2 ++ [x])))
              (t := pathMargins P (x :: c :: t3))
              (by
                cases l2 with
                | nil => simp [pathMargins]
                | cons d t2' => simp [pathMargins])
              hnon_t2
            calc
              minList (pathMargins P (x :: (l2 ++ x :: c :: t3))) =
                  minList (pathMargins P (x :: (l2 ++ [x])) ++ pathMargins P (x :: c :: t3)) := by
                      simp [hpm3']
              _ = min (minList (pathMargins P (x :: (l2 ++ [x]))))
                    (minList (pathMargins P (x :: c :: t3))) := by
                      simpa using h
          have hmid_le :
              minList (pathMargins P (x :: l2 ++ x :: (c :: t3))) ≤
                minList (pathMargins P (x :: (c :: t3))) := by
            calc
              minList (pathMargins P (x :: l2 ++ x :: (c :: t3))) =
                  min (minList (pathMargins P ((x :: l2) ++ [x])))
                    (minList (pathMargins P (x :: (c :: t3)))) := hmin_mid
              _ ≤ minList (pathMargins P (x :: (c :: t3))) := by
                  exact min_le_right _ _
          have htotal_le :
              minList (pathMargins P ((a :: t1) ++ x :: l2 ++ x :: (c :: t3))) ≤
                min (minList (pathMargins P ((a :: t1) ++ [x])))
                  (minList (pathMargins P (x :: (c :: t3)))) := by
            calc
              minList (pathMargins P ((a :: t1) ++ x :: l2 ++ x :: (c :: t3))) =
                  min (minList (pathMargins P ((a :: t1) ++ [x])))
                    (minList (pathMargins P (x :: l2 ++ x :: (c :: t3)))) := hmin_total
              _ ≤ min (minList (pathMargins P ((a :: t1) ++ [x])))
                    (minList (pathMargins P (x :: (c :: t3)))) :=
                  min_le_min_left _ hmid_le
          have hmin_short :
              minList (pathMargins P (a :: (t1 ++ x :: c :: t3))) =
                min (minList (pathMargins P (a :: (t1 ++ [x]))))
                  (minList (pathMargins P (x :: c :: t3))) := by
            have h := minList_append
              (s := pathMargins P (a :: (t1 ++ [x])))
              (t := pathMargins P (x :: c :: t3)) hnon_s hnon_t2
            calc
              minList (pathMargins P (a :: (t1 ++ x :: c :: t3))) =
                  minList (pathMargins P (a :: (t1 ++ [x])) ++ pathMargins P (x :: c :: t3)) := by
                      simp [hpm2']
              _ = min (minList (pathMargins P (a :: (t1 ++ [x]))))
                    (minList (pathMargins P (x :: c :: t3))) := by
                      simpa using h
          have hle :
              minList (pathMargins P ((a :: t1) ++ x :: l2 ++ x :: (c :: t3))) ≤
                minList (pathMargins P ((a :: t1) ++ x :: (c :: t3))) := by
            simpa [hmin_short] using htotal_le
          simpa [pathStrength_eq_minList] using hle

lemma pathStrength_remove_repeat_ge_head (P : Profile V A) (l2 l3 : List A) (x : A)
    (hl3 : l3 ≠ []) :
    pathStrength P (x :: (l2 ++ x :: l3)) ≤ pathStrength P (x :: l3) := by
  have hpm :
      pathMargins P (x :: (l2 ++ x :: l3)) =
        pathMargins P (x :: (l2 ++ [x])) ++ pathMargins P (x :: l3) := by
    simpa [List.append_assoc] using
      (pathMargins_append_cons (P := P) (l := x :: l2) (b := x) (u := l3) (by simp))
  have hnon_left : pathMargins P ((x :: l2) ++ [x]) ≠ [] := by
    cases l2 with
    | nil => simp [pathMargins]
    | cons a t => simp [pathMargins]
  have hnon_right : pathMargins P (x :: l3) ≠ [] := by
    cases l3 with
    | nil => cases hl3 rfl
    | cons a t => simp [pathMargins]
  have hmin :
      minList (pathMargins P (x :: (l2 ++ x :: l3))) =
        min (minList (pathMargins P (x :: (l2 ++ [x]))))
          (minList (pathMargins P (x :: l3))) := by
    have h :=
      minList_append
        (s := pathMargins P ((x :: l2) ++ [x]))
        (t := pathMargins P (x :: l3))
        hnon_left hnon_right
    calc
      minList (pathMargins P (x :: (l2 ++ x :: l3))) =
          minList (pathMargins P (x :: (l2 ++ [x])) ++ pathMargins P (x :: l3)) := by
            simp [hpm]
      _ = min (minList (pathMargins P (x :: (l2 ++ [x]))))
            (minList (pathMargins P (x :: l3))) := by
            simpa [List.append_assoc] using h
  have hle :
      minList (pathMargins P (x :: (l2 ++ x :: l3))) ≤
        minList (pathMargins P (x :: l3)) := by
    simp [hmin]
  simpa [pathStrength_eq_minList] using hle

omit [Fintype V] [Fintype A] in
lemma mem_split {x : A} {l : List A} (h : x ∈ l) :
    ∃ l1 l2, l = l1 ++ x :: l2 := by
  induction l with
  | nil => cases h
  | cons a t ih =>
      have h' : x = a ∨ x ∈ t := by
        simpa using h
      cases h' with
      | inl hx =>
          subst hx
          exact ⟨[], t, by simp⟩
      | inr hmem =>
          rcases ih hmem with ⟨l1, l2, rfl⟩
          exact ⟨a :: l1, l2, by simp [List.cons_append]⟩

omit [Fintype V] [Fintype A] in
lemma duplicate_split {x : A} {l : List A} (h : List.Duplicate x l) :
    ∃ l1 l2 l3, l = l1 ++ x :: l2 ++ x :: l3 := by
  induction h with
  | cons_mem hmem =>
      rcases mem_split (x := x) hmem with ⟨l2, l3, hsplit⟩
      refine ⟨[], l2, l3, ?_⟩
      simp [hsplit]
  | cons_duplicate hdup ih =>
      rename_i y l
      rcases ih with ⟨l1, l2, l3, hsplit⟩
      refine ⟨y :: l1, l2, l3, ?_⟩
      calc
        y :: l = y :: (l1 ++ x :: l2 ++ x :: l3) := by simp [hsplit]
        _ = (y :: l1) ++ x :: l2 ++ x :: l3 := by
          simp [List.cons_append, List.append_assoc]

omit [Fintype V] [Fintype A] in
lemma head?_remove_repeat (l1 l2 l3 : List A) (x : A) :
    (l1 ++ x :: l2 ++ x :: l3).head? = (l1 ++ x :: l3).head? := by
  cases l1 with
  | nil =>
      simp
  | cons a t =>
      simp [List.cons_append]

omit [Fintype V] [Fintype A] in
lemma getLast?_remove_repeat (l1 l2 l3 : List A) (x : A) :
    (l1 ++ x :: l2 ++ x :: l3).getLast? = (l1 ++ x :: l3).getLast? := by
  cases l3 with
  | nil =>
      have h1 :
          (l1 ++ x :: l2 ++ [x]).getLast? = ([x] : List A).getLast? := by
        calc
          (l1 ++ x :: l2 ++ [x]).getLast? = (x :: l2 ++ [x]).getLast? := by
            simpa [List.append_assoc] using
              (List.getLast?_append_of_ne_nil l1 (by simp))
          _ = ([x] : List A).getLast? := by
            exact List.getLast?_append_of_ne_nil (x :: l2) (by simp)
      have h2 : (l1 ++ [x]).getLast? = ([x] : List A).getLast? := by
        exact (List.getLast?_append_of_ne_nil l1 (by simp))
      exact h1.trans h2.symm
  | cons c t3 =>
      have hne1 : (x :: c :: t3 : List A) ≠ [] := by simp
      have h1 :
          (l1 ++ x :: l2 ++ x :: c :: t3).getLast? = (x :: c :: t3).getLast? := by
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (l1 ++ x :: l2) hne1)
      have h2 :
          (l1 ++ x :: c :: t3).getLast? = (c :: t3).getLast? := by
        have hne2 : (c :: t3 : List A) ≠ [] := by simp
        simpa [List.append_assoc] using
          (List.getLast?_append_of_ne_nil (l1 ++ [x]) hne2)
      have h3 : (x :: c :: t3).getLast? = (c :: t3).getLast? := by
        have hne3 : (c :: t3 : List A) ≠ [] := by simp
        exact (List.getLast?_append_of_ne_nil ([x] : List A) hne3)
      exact h1.trans (h3.trans h2.symm)

lemma pathStrength_concat_of_append_cons (P : Profile V A) (l : List A) (b : A) (u : List A)
    (hl : l ≠ []) (hu : u ≠ []) :
    min (pathStrength P (l ++ [b])) (pathStrength P (b :: u)) ≤
      pathStrength P (l ++ b :: u) := by
  have hml :
      pathMargins P (l ++ [b]) ≠ [] := by
    cases l with
    | nil => exact (hl rfl).elim
    | cons a t =>
        cases t with
        | nil =>
            simp [pathMargins]
        | cons c t' =>
            simp [pathMargins]
  have hmr :
      pathMargins P (b :: u) ≠ [] := by
    cases u with
    | nil => exact (hu rfl).elim
    | cons c u' =>
        simp [pathMargins]
  have hpm :
      pathMargins P (l ++ b :: u) =
        pathMargins P (l ++ [b]) ++ pathMargins P (b :: u) := by
    exact pathMargins_append_cons (P := P) (l := l) (b := b) (u := u) hl
  have hmin :
      minList (pathMargins P (l ++ b :: u)) =
        min (minList (pathMargins P (l ++ [b]))) (minList (pathMargins P (b :: u))) := by
    have h :=
      minList_append
        (s := pathMargins P (l ++ [b]))
        (t := pathMargins P (b :: u))
        (hs := hml)
        (ht := hmr)
    simpa [hpm] using h
  have hpsl := pathStrength_eq_minList (P := P) (l := l ++ [b])
  have hpsr := pathStrength_eq_minList (P := P) (l := b :: u)
  have hpsc := pathStrength_eq_minList (P := P) (l := l ++ b :: u)
  have hle :
      min (minList (pathMargins P (l ++ [b]))) (minList (pathMargins P (b :: u))) ≤
        minList (pathMargins P (l ++ b :: u)) := by
    simp [hmin]
  simpa [hpsl, hpsr, hpsc] using hle

lemma mem_pathsOfLength_two_of_ne (a b : A) (h : a ≠ b) :
    [a, b] ∈ pathsOfLength (A := A) 2 a b := by
  classical
  refine Finset.mem_filter.mpr ?_
  refine ⟨?_, ?_⟩
  · refine Finset.mem_image.mpr ?_
    classical
    let f : Fin 2 → A := Fin.cons a (fun _ : Fin 1 => b)
    refine ⟨f, ?_, ?_⟩
    · simp
    · simp [f]
  · constructor
    · simp
    · constructor
      · simp
      · constructor
        · simp
        · simp [List.nodup_cons, h]

lemma pathsUpTo_nonempty_of_ne (a b : A) (h : a ≠ b) :
    (pathsUpTo (A := A) (Fintype.card A) a b).Nonempty := by
  classical
  refine ⟨[a, b], ?_⟩
  unfold pathsUpTo
  refine Finset.mem_biUnion.mpr ?_
  refine ⟨2, ?_, ?_⟩
  ·
    have hcard : 2 ≤ Fintype.card A := by
      classical
      have hinj : Function.Injective (Fin.cons a (fun _ : Fin 1 => b)) := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp at hij <;> try rfl
        · exact (h hij).elim
        · exact (h hij.symm).elim
      simpa using
        (Fintype.card_le_of_injective (f := Fin.cons a (fun _ : Fin 1 => b)) hinj)
    have hmem :
        2 ∈ (Finset.range (Fintype.card A + 1)).filter (fun k => 2 ≤ k) := by
      simp [Finset.mem_range, Nat.lt_succ_of_le hcard]
    exact hmem
  · exact mem_pathsOfLength_two_of_ne (A := A) a b h

lemma margin_le_strongestPath_of_ne (P : Profile V A) (a b : A) (h : a ≠ b) :
    margin P a b ≤ strongestPath P a b := by
  classical
  by_cases hne : (pathsUpTo (A := A) (Fintype.card A) a b).Nonempty
  ·
    have hmem :
        [a, b] ∈ pathsUpTo (A := A) (Fintype.card A) a b := by
      unfold pathsUpTo
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨2, ?_, ?_⟩
      ·
        have hcard : 2 ≤ Fintype.card A := by
          classical
          have hinj : Function.Injective (Fin.cons a (fun _ : Fin 1 => b)) := by
            intro i j hij
            fin_cases i <;> fin_cases j <;> simp at hij <;> try rfl
            · exact (h hij).elim
            · exact (h hij.symm).elim
          simpa using
            (Fintype.card_le_of_injective (f := Fin.cons a (fun _ : Fin 1 => b)) hinj)
        have hmem :
            2 ∈ (Finset.range (Fintype.card A + 1)).filter (fun k => 2 ≤ k) := by
          simp [Finset.mem_range, Nat.lt_succ_of_le hcard]
        exact hmem
      · exact mem_pathsOfLength_two_of_ne (A := A) a b h
    have hmem' :
        pathStrength P [a, b] ∈
          (pathsUpTo (A := A) (Fintype.card A) a b).image (fun l => pathStrength P l) := by
      exact Finset.mem_image.mpr ⟨[a, b], hmem, rfl⟩
    have hle : pathStrength P [a, b] ≤
        Finset.max'
          ((pathsUpTo (A := A) (Fintype.card A) a b).image (fun l => pathStrength P l))
          (by
            rcases hne with ⟨l, hl⟩
            exact ⟨pathStrength P l, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩) := by
      exact Finset.le_max' _ _ hmem'
    have hle' : margin P a b ≤
        Finset.max'
          ((pathsUpTo (A := A) (Fintype.card A) a b).image (fun l => pathStrength P l))
          (by
            rcases hne with ⟨l, hl⟩
            exact ⟨pathStrength P l, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩) := by
      simpa [pathStrength_two] using hle
    simpa [strongestPath, hne] using hle'
  · simp [strongestPath, hne]

lemma pathStrength_of_mem_pathsUpTo_le_strongestPath (P : Profile V A) (a b : A) (l : List A)
    (hl : l ∈ pathsUpTo (A := A) (Fintype.card A) a b) :
    pathStrength P l ≤ strongestPath P a b := by
  classical
  have hne : (pathsUpTo (A := A) (Fintype.card A) a b).Nonempty :=
    ⟨l, hl⟩
  have hmem' :
      pathStrength P l ∈
        (pathsUpTo (A := A) (Fintype.card A) a b).image (fun t => pathStrength P t) := by
    exact Finset.mem_image.mpr ⟨l, hl, rfl⟩
  have hle : pathStrength P l ≤
      Finset.max'
        ((pathsUpTo (A := A) (Fintype.card A) a b).image (fun t => pathStrength P t))
        (by
          rcases hne with ⟨t, ht⟩
          exact ⟨pathStrength P t, Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩) := by
    exact Finset.le_max' _ _ hmem'
  simpa [strongestPath, hne] using hle

lemma exists_path_strength_eq_strongestPath (P : Profile V A) (a b : A)
    (hne : (pathsUpTo (A := A) (Fintype.card A) a b).Nonempty) :
    ∃ l ∈ pathsUpTo (A := A) (Fintype.card A) a b, pathStrength P l = strongestPath P a b := by
  classical
  let paths := pathsUpTo (A := A) (Fintype.card A) a b
  let strengths := paths.image (fun l => pathStrength P l)
  have hstrengths : strengths.Nonempty := by
    rcases hne with ⟨l, hl⟩
    exact ⟨pathStrength P l, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩
  have hmem : strengths.max' hstrengths ∈ strengths := Finset.max'_mem _ _
  rcases Finset.mem_image.mp hmem with ⟨l, hl, hstrength⟩
  refine ⟨l, hl, ?_⟩
  have hmax : strengths.max' hstrengths = strongestPath P a b := by
    simp [strongestPath, hne, strengths, paths]
  simpa [hmax] using hstrength


lemma pathStrength_concat_le_strongestPath (P : Profile V A) (a c : A) (l : List A) (b : A)
    (u : List A) (hl : l ≠ []) (hu : u ≠ [])
    (hmem : l ++ b :: u ∈ pathsUpTo (A := A) (Fintype.card A) a c) :
    min (pathStrength P (l ++ [b])) (pathStrength P (b :: u)) ≤ strongestPath P a c := by
  have hconcat : min (pathStrength P (l ++ [b])) (pathStrength P (b :: u)) ≤
      pathStrength P (l ++ b :: u) := by
    exact pathStrength_concat_of_append_cons (P := P) (l := l) (b := b) (u := u) hl hu
  have hle := pathStrength_of_mem_pathsUpTo_le_strongestPath
    (P := P) (a := a) (b := c) (l := l ++ b :: u) hmem
  exact le_trans hconcat hle

lemma length_le_card_of_nodup (l : List A) (h : l.Nodup) :
    l.length ≤ Fintype.card A := by
  classical
  have hinj : Function.Injective l.get := (List.nodup_iff_injective_get.mp h)
  have hcard := Fintype.card_le_of_injective (f := l.get) hinj
  simpa using hcard

lemma path_props_of_mem_pathsUpTo (l : List A) (a b : A)
    (hl : l ∈ pathsUpTo (A := A) (Fintype.card A) a b) :
    l.head? = some a ∧ l.getLast? = some b ∧ l.Nodup ∧ 2 ≤ l.length := by
  classical
  unfold pathsUpTo at hl
  rcases Finset.mem_biUnion.mp hl with ⟨k, hklen, hmem⟩
  have hk2 : 2 ≤ k := (Finset.mem_filter.mp hklen).2
  rcases Finset.mem_filter.mp hmem with ⟨_hmem_list, hprops⟩
  rcases hprops with ⟨hlen, hhead, hlast, hnodup⟩
  have hlen' : 2 ≤ l.length := by
    simpa [hlen] using hk2
  exact ⟨hhead, hlast, hnodup, hlen'⟩

lemma path_props_of_mem_pathsUpToAny (l : List A) (a b : A) (n : Nat)
    (hl : l ∈ pathsUpToAny (A := A) n a b) :
    l.head? = some a ∧ l.getLast? = some b ∧ 2 ≤ l.length ∧ l.length ≤ n := by
  classical
  unfold pathsUpToAny at hl
  rcases Finset.mem_biUnion.mp hl with ⟨k, hklen, hmem⟩
  have hk2 : 2 ≤ k := (Finset.mem_filter.mp hklen).2
  have hk_range : k ∈ Finset.range (n + 1) := (Finset.mem_filter.mp hklen).1
  rcases Finset.mem_filter.mp hmem with ⟨_hmem_list, hprops⟩
  rcases hprops with ⟨hlen, hhead, hlast⟩
  have hlen' : 2 ≤ l.length := by
    simpa [hlen] using hk2
  have hk_le : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk_range)
  have hlen_le : l.length ≤ n := by
    simpa [hlen] using hk_le
  exact ⟨hhead, hlast, hlen', hlen_le⟩

lemma exists_max_path_props (P : Profile V A) (a b : A)
    (hne : (pathsUpTo (A := A) (Fintype.card A) a b).Nonempty) :
    ∃ l, l ∈ pathsUpTo (A := A) (Fintype.card A) a b ∧
      l.head? = some a ∧ l.getLast? = some b ∧ l.Nodup ∧ 2 ≤ l.length ∧
      pathStrength P l = strongestPath P a b := by
  rcases exists_path_strength_eq_strongestPath (P := P) (a := a) (b := b) hne with
    ⟨l, hl, hstrength⟩
  rcases path_props_of_mem_pathsUpTo (l := l) (a := a) (b := b) hl with
    ⟨hhead, hlast, hnodup, hlen⟩
  exact ⟨l, hl, hhead, hlast, hnodup, hlen, hstrength⟩

lemma mem_pathsUpTo_of_props (l : List A) (a b : A)
    (hhead : l.head? = some a) (hlast : l.getLast? = some b)
    (hnodup : l.Nodup) (hlen : 2 ≤ l.length) :
    l ∈ pathsUpTo (A := A) (Fintype.card A) a b := by
  classical
  have hlen_le : l.length ≤ Fintype.card A := length_le_card_of_nodup (l := l) hnodup
  have hmem_list : l ∈ listsOfLength (A := A) l.length := by
    refine Finset.mem_image.mpr ?_
    refine ⟨(fun i : Fin l.length => l[(i : Nat)]), ?_, ?_⟩
    · simp
    · exact (List.ofFn_getElem (xs := l))
  have hmem_len : l ∈ pathsOfLength (A := A) l.length a b := by
    refine Finset.mem_filter.mpr ?_
    exact ⟨hmem_list, ⟨rfl, hhead, hlast, hnodup⟩⟩
  unfold pathsUpTo
  refine Finset.mem_biUnion.mpr ?_
  refine ⟨l.length, ?_, hmem_len⟩
  have hmem_range : l.length ∈ Finset.range (Fintype.card A + 1) := by
    simp [Finset.mem_range, Nat.lt_succ_of_le hlen_le]
  exact Finset.mem_filter.mpr ⟨hmem_range, hlen⟩

lemma mem_pathsUpToAny_of_props (l : List A) (a b : A) (n : Nat)
    (hhead : l.head? = some a) (hlast : l.getLast? = some b)
    (hlen : 2 ≤ l.length) (hlen_le : l.length ≤ n) :
    l ∈ pathsUpToAny (A := A) n a b := by
  classical
  have hmem_list : l ∈ listsOfLength (A := A) l.length := by
    refine Finset.mem_image.mpr ?_
    refine ⟨(fun i : Fin l.length => l[(i : Nat)]), ?_, ?_⟩
    · simp
    · exact (List.ofFn_getElem (xs := l))
  have hmem_len : l ∈ pathsOfLengthAny (A := A) l.length a b := by
    refine Finset.mem_filter.mpr ?_
    exact ⟨hmem_list, ⟨rfl, hhead, hlast⟩⟩
  unfold pathsUpToAny
  refine Finset.mem_biUnion.mpr ?_
  refine ⟨l.length, ?_, hmem_len⟩
  have hmem_range : l.length ∈ Finset.range (n + 1) := by
    simp [Finset.mem_range, Nat.lt_succ_of_le hlen_le]
  exact Finset.mem_filter.mpr ⟨hmem_range, hlen⟩

lemma mem_pathsUpToAny_of_mem_pathsUpTo (l : List A) (a b : A)
    (hl : l ∈ pathsUpTo (A := A) (Fintype.card A) a b) :
    l ∈ pathsUpToAny (A := A) (Fintype.card A) a b := by
  classical
  rcases path_props_of_mem_pathsUpTo (l := l) (a := a) (b := b) hl with
    ⟨hhead, hlast, hnodup, hlen⟩
  have hlen_le : l.length ≤ Fintype.card A := length_le_card_of_nodup (l := l) hnodup
  exact mem_pathsUpToAny_of_props (l := l) (a := a) (b := b)
    (n := Fintype.card A) hhead hlast hlen hlen_le

lemma mem_pathsUpTo_concat_of_disjoint (a b c : A) (l u : List A)
    (hl : l ++ [b] ∈ pathsUpTo (A := A) (Fintype.card A) a b)
    (hu : b :: u ∈ pathsUpTo (A := A) (Fintype.card A) b c)
    (hdis : List.Disjoint l u) :
    l ++ b :: u ∈ pathsUpTo (A := A) (Fintype.card A) a c := by
  classical
  rcases path_props_of_mem_pathsUpTo (l := l ++ [b]) (a := a) (b := b) hl with
    ⟨hhead_l, hlast_l, hnodup_l, hlen_l⟩
  rcases path_props_of_mem_pathsUpTo (l := b :: u) (a := b) (b := c) hu with
    ⟨hhead_u, hlast_u, hnodup_u, hlen_u⟩
  have hbnot : b ∉ l := by
    have hdis_lb : List.Disjoint l ([b] : List A) := (List.nodup_append'.1 hnodup_l).2.2
    exact (List.disjoint_cons_right.mp hdis_lb).1
  have hdis' : List.Disjoint l (b :: u) := by
    exact (List.disjoint_cons_right.mpr ⟨hbnot, hdis⟩)
  have hnodup_concat : (l ++ b :: u).Nodup :=
    (List.nodup_append'.2 ⟨(List.nodup_append'.1 hnodup_l).1, hnodup_u, hdis'⟩)
  have hhead' : (l ++ b :: u).head? = some a := by
    have hlne : l ≠ [] := by
      intro hnil
      have hlen1 : (l ++ [b]).length = 1 := by simp [hnil]
      have hcontr : (2 : Nat) ≤ 1 := by
        have hlen_l' := hlen_l
        rw [hlen1] at hlen_l'
        exact hlen_l'
      exact (by decide : ¬ ((2 : Nat) ≤ 1)) hcontr
    have hhead_l' : l.head? = some a := by
      have hhead'' := List.head?_append_of_ne_nil (l₁ := l) (l₂ := [b]) hlne
      calc
        l.head? = (l ++ [b]).head? := hhead''.symm
        _ = some a := hhead_l
    have hhead'' := List.head?_append_of_ne_nil (l₁ := l) (l₂ := b :: u) hlne
    calc
      (l ++ b :: u).head? = l.head? := hhead''
      _ = some a := hhead_l'
  have hlast' : (l ++ b :: u).getLast? = some c := by
    rw [List.getLast?_append_cons]
    exact hlast_u
  have hlen' : 2 ≤ (l ++ b :: u).length := by
    have hle : (b :: u).length ≤ (l ++ b :: u).length := by
      simp [List.length_append]
    exact le_trans hlen_u hle
  exact mem_pathsUpTo_of_props (l := l ++ b :: u) (a := a) (b := c)
    hhead' hlast' hnodup_concat hlen'

lemma pathStrengthAux_le_init (P : Profile V A) (a : A) (l : List A) (m : Int) :
    pathStrengthAux P a l m ≤ m := by
  induction l generalizing a m with
  | nil =>
      simp [pathStrengthAux]
  | cons x xs ih =>
      have h' : pathStrengthAux P a (x :: xs) m ≤ min m (margin P a x) := by
        simpa [pathStrengthAux] using (ih (a := x) (m := min m (margin P a x)))
      exact le_trans h' (min_le_left _ _)

lemma pathStrengthAux_min_left (P : Profile V A) (a : A) (l : List A) (m1 m2 : Int) :
    pathStrengthAux P a l (min m1 m2) =
      min (pathStrengthAux P a l m1) (pathStrengthAux P a l m2) := by
  induction l generalizing a m1 m2 with
  | nil =>
      simp [pathStrengthAux]
  | cons x xs ih =>
      simp [pathStrengthAux, ih, min_assoc, min_left_comm]

lemma pathStrengthAux_min_left_simple (P : Profile V A) (a : A) (l : List A) (m1 m2 : Int) :
    pathStrengthAux P a l (min m1 m2) =
      min m1 (pathStrengthAux P a l m2) := by
  induction l generalizing a m1 m2 with
  | nil =>
      simp [pathStrengthAux]
  | cons x xs ih =>
      have hle :
          pathStrengthAux P x xs (min m2 (margin P a x)) ≤ margin P a x := by
        have hle' :
            pathStrengthAux P x xs (min m2 (margin P a x)) ≤ min m2 (margin P a x) := by
          simpa [pathStrengthAux] using
            (pathStrengthAux_le_init (P := P) (a := x) (l := xs) (m := min m2 (margin P a x)))
        exact le_trans hle' (min_le_right _ _)
      have hy :
          min (margin P a x) (pathStrengthAux P x xs (min m2 (margin P a x))) =
            pathStrengthAux P x xs (min m2 (margin P a x)) := by
        apply min_eq_right
        exact hle
      simp [pathStrengthAux, ih, min_assoc]

lemma pathStrength_cons_cons_cons (P : Profile V A) (a b c : A) (t : List A) :
    pathStrength P (a :: b :: c :: t) =
      min (margin P a b) (pathStrength P (b :: c :: t)) := by
  cases t with
  | nil =>
      simp [pathStrength, pathStrengthAux]
  | cons d t' =>
      have hmin :
          min (min (margin P a b) (margin P b c)) (margin P c d) =
            min (margin P a b) (min (margin P b c) (margin P c d)) := by
        simp [min_assoc]
      simp [pathStrength, pathStrengthAux, hmin, pathStrengthAux_min_left_simple]

lemma pathStrengthAux_append_le (P : Profile V A) (a : A) (l r : List A) (m : Int) :
    pathStrengthAux P a (l ++ r) m ≤ pathStrengthAux P a l m := by
  induction l generalizing a m with
  | nil =>
      simpa [pathStrengthAux] using (pathStrengthAux_le_init (P := P) a r m)
  | cons x xs ih =>
      simpa [pathStrengthAux] using
        (ih (a := x) (m := min m (margin P a x)))

lemma pathStrength_append_le_left (P : Profile V A) (l r : List A) (hlen : 2 ≤ l.length) :
    pathStrength P (l ++ r) ≤ pathStrength P l := by
  cases l with
  | nil =>
      simp at hlen
  | cons a l' =>
      cases l' with
      | nil =>
          simp at hlen
      | cons b t =>
          simp [pathStrength, pathStrengthAux_append_le]

lemma pathStrength_remove_repeat_ge_tail (P : Profile V A) (l1 l2 : List A) (x : A)
    (hl1 : l1 ≠ []) :
    pathStrength P (l1 ++ x :: l2 ++ [x]) ≤ pathStrength P (l1 ++ [x]) := by
  have hlen : 2 ≤ (l1 ++ [x]).length := by
    cases l1 with
    | nil => cases hl1 rfl
    | cons a t => simp [List.length_append]
  have hle :
      pathStrength P (l1 ++ [x] ++ l2 ++ [x]) ≤ pathStrength P (l1 ++ [x]) := by
    simpa [List.append_assoc] using
      (pathStrength_append_le_left (P := P) (l := l1 ++ [x]) (r := l2 ++ [x]) hlen)
  simpa [List.append_assoc] using hle

lemma exists_nodup_strength_ge (P : Profile V A) (a c : A) (l : List A)
    (hhead : l.head? = some a) (hlast : l.getLast? = some c) (hne : a ≠ c) :
    ∃ l', l'.Nodup ∧ l'.head? = some a ∧ l'.getLast? = some c ∧
      pathStrength P l ≤ pathStrength P l' ∧ l'.length ≤ l.length := by
  classical
  refine (Nat.strongRecOn
      (motive := fun n =>
        ∀ l, l.length = n → l.head? = some a → l.getLast? = some c → a ≠ c →
          ∃ l', l'.Nodup ∧ l'.head? = some a ∧ l'.getLast? = some c ∧
            pathStrength P l ≤ pathStrength P l' ∧ l'.length ≤ n)
      l.length ?_) l rfl hhead hlast hne
  intro n ih l hlen hhead hlast hne
  by_cases hnodup : l.Nodup
  · exact ⟨l, hnodup, hhead, hlast, le_rfl, by simp [hlen]⟩
  rcases (List.exists_duplicate_iff_not_nodup).2 hnodup with ⟨x, hxdup⟩
  rcases duplicate_split (x := x) hxdup with ⟨l1, l2, l3, hdecomp⟩
  let lshort := l1 ++ x :: l3
  have hhead_short : lshort.head? = some a := by
    have hhead_eq := head?_remove_repeat (l1 := l1) (l2 := l2) (l3 := l3) (x := x)
    calc
      lshort.head? = (l1 ++ x :: l2 ++ x :: l3).head? := by
        simp [lshort, hhead_eq.symm]
      _ = l.head? := by simp [hdecomp]
      _ = some a := hhead
  have hlast_short : lshort.getLast? = some c := by
    have hlast_eq := getLast?_remove_repeat (l1 := l1) (l2 := l2) (l3 := l3) (x := x)
    calc
      lshort.getLast? = (l1 ++ x :: l2 ++ x :: l3).getLast? := by
        simp [lshort, hlast_eq.symm]
      _ = l.getLast? := by simp [hdecomp]
      _ = some c := hlast
  have hlen_eq : l.length = lshort.length + (l2.length + 1) := by
    simp [lshort, hdecomp, List.length_append, List.length_cons, Nat.add_left_comm, Nat.add_comm]
  have hlen_short : lshort.length < n := by
    have hpos : 0 < l2.length + 1 := Nat.succ_pos _
    have hlt : lshort.length < lshort.length + (l2.length + 1) :=
      Nat.lt_add_of_pos_right (n := lshort.length) (k := l2.length + 1) hpos
    have hlt' : lshort.length < l.length := by
      rw [hlen_eq]
      exact hlt
    -- rewrite the goal using hlen
    simpa [hlen] using hlt'
  have hstrength_le : pathStrength P l ≤ pathStrength P lshort := by
    cases l1 with
    | nil =>
        cases l3 with
        | nil =>
            have hheadx : l.head? = some x := by
              simp [hdecomp]
            have hlastx : l.getLast? = some x := by
              have hlast' : l.getLast? = ([x] : List A).getLast? := by
                rw [hdecomp]
                exact List.getLast?_append_of_ne_nil (x :: l2) (by simp)
              calc
                l.getLast? = ([x] : List A).getLast? := hlast'
                _ = some x := by simp
            have ha : a = x := by
              symm
              apply Option.some.inj
              simpa [hheadx] using hhead
            have hc : c = x := by
              symm
              apply Option.some.inj
              simpa [hlastx] using hlast
            exact (hne (ha.trans hc.symm)).elim
        | cons c t3 =>
            have h := pathStrength_remove_repeat_ge_head (P := P) (l2 := l2)
              (l3 := c :: t3) (x := x) (by simp)
            simpa [hdecomp, lshort] using h
    | cons a t1 =>
        cases l3 with
        | nil =>
            have h := pathStrength_remove_repeat_ge_tail (P := P) (l1 := a :: t1) (l2 := l2)
              (x := x) (by simp)
            simpa [hdecomp, lshort] using h
        | cons c t3 =>
            have h := pathStrength_remove_repeat_ge (P := P) (l1 := a :: t1) (l2 := l2)
              (l3 := c :: t3) (x := x) (by simp) (by simp)
            simpa [hdecomp, lshort] using h
  rcases ih lshort.length hlen_short lshort rfl hhead_short hlast_short hne with
    ⟨l', hnodup', hhead', hlast', hstrength', hlen'⟩
  refine ⟨l', hnodup', hhead', hlast', ?_, ?_⟩
  · exact le_trans hstrength_le hstrength'
  · exact le_trans hlen' (Nat.le_of_lt hlen_short)

omit [Fintype V] [Fintype A] in
lemma length_ge_two_of_head_last_ne (l : List A) (a b : A)
    (hhead : l.head? = some a) (hlast : l.getLast? = some b) (hne : a ≠ b) :
    2 ≤ l.length := by
  cases l with
  | nil =>
      simp at hhead
  | cons x xs =>
      cases xs with
      | nil =>
          have ha : a = x := by
            apply Option.some.inj
            simpa using hhead.symm
          have hb : b = x := by
            apply Option.some.inj
            simpa using hlast.symm
          exact (hne (ha.trans hb.symm)).elim
      | cons y ys =>
          simp

lemma pathStrength_of_mem_pathsUpToAny_le_strongestPath_of_ne (P : Profile V A) (a b : A)
    (l : List A) (hl : l ∈ pathsUpToAny (A := A) (Fintype.card A) a b) (hne : a ≠ b) :
    pathStrength P l ≤ strongestPath P a b := by
  classical
  rcases path_props_of_mem_pathsUpToAny (l := l) (a := a) (b := b)
      (n := Fintype.card A) hl with ⟨hhead, hlast, _hlen, _hlen_le⟩
  rcases exists_nodup_strength_ge (P := P) (a := a) (c := b) (l := l)
      hhead hlast hne with
    ⟨l', hnodup', hhead', hlast', hstrength_le, hlen_le'⟩
  have hlen' : 2 ≤ l'.length :=
    length_ge_two_of_head_last_ne (l := l') (a := a) (b := b) hhead' hlast' hne
  have hmem' : l' ∈ pathsUpTo (A := A) (Fintype.card A) a b :=
    mem_pathsUpTo_of_props (l := l') (a := a) (b := b) hhead' hlast' hnodup' hlen'
  have hle' : pathStrength P l' ≤ strongestPath P a b :=
    pathStrength_of_mem_pathsUpTo_le_strongestPath (P := P) (a := a) (b := b) (l := l') hmem'
  exact le_trans hstrength_le hle'

lemma pathsUpToAny_nonempty_of_ne (a b : A) (h : a ≠ b) :
    (pathsUpToAny (A := A) (Fintype.card A) a b).Nonempty := by
  rcases pathsUpTo_nonempty_of_ne (A := A) a b h with ⟨l, hl⟩
  exact ⟨l, mem_pathsUpToAny_of_mem_pathsUpTo (l := l) (a := a) (b := b) hl⟩

lemma strongestPathAny_eq_strongestPath_of_ne (P : Profile V A) (a b : A) (h : a ≠ b) :
    strongestPathAny P a b = strongestPath P a b := by
  -- We only relate the two notions for distinct endpoints.
  classical
  have hne_any : (pathsUpToAny (A := A) (Fintype.card A) a b).Nonempty :=
    pathsUpToAny_nonempty_of_ne (A := A) a b h
  have hne : (pathsUpTo (A := A) (Fintype.card A) a b).Nonempty :=
    pathsUpTo_nonempty_of_ne (A := A) a b h
  have hle : strongestPathAny P a b ≤ strongestPath P a b := by
    let paths := pathsUpToAny (A := A) (Fintype.card A) a b
    let strengths := paths.image (fun l => pathStrength P l)
    have hstrengths : strengths.Nonempty := by
      rcases hne_any with ⟨l, hl⟩
      exact ⟨pathStrength P l, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩
    have hmax_le : strengths.max' hstrengths ≤ strongestPath P a b := by
      refine (Finset.max'_le_iff (s := strengths) (H := hstrengths)).2 ?_
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨l, hl, rfl⟩
      exact pathStrength_of_mem_pathsUpToAny_le_strongestPath_of_ne
        (P := P) (a := a) (b := b) (l := l) hl h
    simpa [strongestPathAny, hne_any, strengths, paths] using hmax_le
  have hge : strongestPath P a b ≤ strongestPathAny P a b := by
    rcases exists_path_strength_eq_strongestPath (P := P) (a := a) (b := b) hne with
      ⟨l, hl, hstrength⟩
    let paths := pathsUpToAny (A := A) (Fintype.card A) a b
    let strengths := paths.image (fun t => pathStrength P t)
    have hstrengths : strengths.Nonempty := by
      rcases hne_any with ⟨t, ht⟩
      exact ⟨pathStrength P t, Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩
    have hl_any : l ∈ paths := mem_pathsUpToAny_of_mem_pathsUpTo (l := l) (a := a) (b := b) hl
    have hmem : pathStrength P l ∈ strengths :=
      Finset.mem_image.mpr ⟨l, hl_any, rfl⟩
    have hle' : pathStrength P l ≤ strengths.max' hstrengths :=
      Finset.le_max' _ _ hmem
    simpa [strongestPathAny, hne_any, strengths, paths, hstrength] using hle'
  exact le_antisymm hle hge

end SchulzePath

end SocialChoice
