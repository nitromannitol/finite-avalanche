import FiniteAvalanches.Wilson.StackRows.Driver
import FiniteAvalanches.Wilson.StackRows.ProductEvents
import FiniteAvalanches.Wilson.CyclePopping.ErasureNaturality

/-! Wilson's protocol with every walk read from vertex stacks of incident copies, and its
comparison with the classical protocol in which every walk uses a fresh independent row.
The stack walk from a vertex uses the stack driver at the current cursor; the next cursor
leaves the retained loop-erased branch unconsumed, as in cycle popping. The stack protocol
depends only on stack entries at nonroot vertices above the cursor, while a stack word
event depends only on the finitely many entries it reads, which lie below the next cursor
or at the new roots. Hence the first walk and the rest are independent, and induction on
the order list gives the same law of complete outputs for both protocols. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CopiedNetwork

open MeasureTheory ProbabilityTheory FiniteAvalanches.Trees FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

variable {V E I : Type} [Fintype V] [Fintype E] (G : Multigraph V E) (ι : E ↪ I)

/-- The stack cursor after the walk from `x` to `R`, with the retained branch unconsumed. -/
def stackCursor (σ : CopyStacks G) (R : Set V) (k : Cursor V) (x : V) : Cursor V :=
  letI : Quiver V := instructionQuiver (incidentCopyHead G)
  if h : ∃ n, (stackTrace G σ k x n).1 ∈ R then
    erasedCursor k (stackTrace G σ k x (Nat.find h)).2
  else k

/-- Wilson's protocol in which every walk reads the vertex stacks. -/
def stackRun (σ : CopyStacks G) : State (V := V) (E := E) (I := I) → Cursor V → List V →
    Option (State (V := V) (E := E) (I := I))
  | s, _, [] => some s
  | s, k, x :: xs => if x ∈ s.roots then stackRun σ s k xs else
      (query G ι s x (stackDriver G σ k x)).bind
        (fun t => stackRun σ t (stackCursor G σ s.roots k x) xs)

variable {G} in
/-- One step of a stack trace, given the entry read at its endpoint. -/
private def traceStep {x : V}
    (t : Σ y : V, @Quiver.Path V (instructionQuiver (incidentCopyHead G)) x y)
    (a : IncidentCopy G t.1) :
    Σ y : V, @Quiver.Path V (instructionQuiver (incidentCopyHead G)) x y :=
  letI : Quiver V := instructionQuiver (incidentCopyHead G)
  ⟨incidentCopyHead G t.1 a, t.2.cons ⟨a, rfl⟩⟩

/-- A stack trace depends only on the entries it reads. -/
theorem stackTrace_eq_of_agree (σ σ' : CopyStacks G) (k : Cursor V) (x : V) (n : ℕ)
    (h : ∀ i < n,
      σ ((stackTrace G σ k x i).1, traceCursor G σ k x i (stackTrace G σ k x i).1) =
        σ' ((stackTrace G σ k x i).1, traceCursor G σ k x i (stackTrace G σ k x i).1)) :
    stackTrace G σ k x n = stackTrace G σ' k x n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have ih' := ih (fun i hi => h i (Nat.lt_succ_of_lt hi))
    change traceStep (stackTrace G σ k x n)
        (σ ((stackTrace G σ k x n).1, traceCursor G σ k x n (stackTrace G σ k x n).1)) =
      traceStep (stackTrace G σ' k x n)
        (σ' ((stackTrace G σ' k x n).1, traceCursor G σ' k x n (stackTrace G σ' k x n).1))
    rw [h n (Nat.lt_succ_self n)]
    letI : Quiver V := instructionQuiver (incidentCopyHead G)
    exact congrArg (fun t : Σ y : V, Quiver.Path x y => traceStep t (σ' (t.1, consume k t.2 t.1))) ih'

theorem traceCursor_ge (σ : CopyStacks G) (k : Cursor V) (x : V) (n : ℕ) :
    k ≤ traceCursor G σ k x n := by
  letI : Quiver V := instructionQuiver (incidentCopyHead G)
  intro v
  change k v ≤ consume k (stackTrace G σ k x n).2 v
  rw [consume_apply]
  exact Nat.le_add_right _ _

/-- Before the first visit to `R`, the stack trace agrees for stacks agreeing at nonroot
vertices above the cursor. -/
theorem stackTrace_eq_of_agree_off (σ σ' : CopyStacks G) (R : Set V) (k : Cursor V) (x : V)
    (hσ : ∀ v j, v ∉ R → k v ≤ j → σ (v, j) = σ' (v, j)) (n : ℕ)
    (hn : ∀ i < n, (stackTrace G σ k x i).1 ∉ R) :
    stackTrace G σ k x n = stackTrace G σ' k x n :=
  stackTrace_eq_of_agree G σ σ' k x n (fun i hi =>
    hσ _ _ (hn i hi) (traceCursor_ge G σ k x i _))

/-- The cursor after a hit consumes at least the initial cursor. -/
theorem stackCursor_ge (σ : CopyStacks G) (R : Set V) (k : Cursor V) (x : V) :
    k ≤ stackCursor G σ R k x := by
  letI : Quiver V := instructionQuiver (incidentCopyHead G)
  unfold stackCursor
  split_ifs with h
  · obtain ⟨hrun, _, _⟩ := instructionTrace_erasure R (incidentCopyHead G) (fun v i => σ (v, i))
      k x (Nat.find h) (instructionTrace_departures_avoid R (incidentCopyHead G)
        (fun v i => σ (v, i)) k x (Nat.find h) (fun i hi => Nat.find_min h hi))
    exact pop_run_le R (incidentCopyHead G) (fun v i => σ (v, i)) hrun
  · exact le_rfl

theorem hits_stackDriver_iff (σ : CopyStacks G) (R : Set V) (k : Cursor V) (x : V) :
    hits G R x (stackDriver G σ k x) ↔ ∃ n, (stackTrace G σ k x n).1 ∈ R := by
  simp only [hits, position_stackDriver]

/-- A stack walk with first hit at time `N` attaches its walk stopped at `N`. -/
theorem query_stackDriver_of_hit (s : State (V := V) (E := E) (I := I)) (σ : CopyStacks G)
    (k : Cursor V) (x : V) (hx : x ∉ s.roots) (N : ℕ) (hN : (stackTrace G σ k x N).1 ∈ s.roots)
    (hmin : ∀ i < N, (stackTrace G σ k x i).1 ∉ s.roots) :
    query G ι s x (stackDriver G σ k x) = some (attachAt G ι s x (stackDriver G σ k x) N) := by
  have hh : hits G s.roots x (stackDriver G σ k x) := ⟨N, by rw [position_stackDriver]; exact hN⟩
  have hf : Nat.find hh = N := by
    apply (Nat.find_eq_iff hh).mpr
    refine ⟨by rw [position_stackDriver]; exact hN, fun i hi => ?_⟩
    rw [position_stackDriver]
    exact hmin i hi
  rw [query, if_neg hx, dif_pos hh, hf]

/-- A stack walk which never hits fails. -/
theorem query_stackDriver_of_not_hit (s : State (V := V) (E := E) (I := I)) (σ : CopyStacks G)
    (k : Cursor V) (x : V) (hx : x ∉ s.roots) (h : ∀ n, (stackTrace G σ k x n).1 ∉ s.roots) :
    query G ι s x (stackDriver G σ k x) = none := by
  apply query_of_not_hits G ι s x hx
  rw [hits_stackDriver_iff]
  rintro ⟨n, hn⟩
  exact h n hn

/-- After a first hit at time `N`, the cursor is the erased cursor of the trace. -/
theorem stackCursor_of_hit (σ : CopyStacks G) (R : Set V) (k : Cursor V) (x : V) (N : ℕ)
    (hN : (stackTrace G σ k x N).1 ∈ R) (hmin : ∀ i < N, (stackTrace G σ k x i).1 ∉ R) :
    stackCursor G σ R k x =
      (letI : Quiver V := instructionQuiver (incidentCopyHead G)
       erasedCursor k (stackTrace G σ k x N).2) := by
  have hh : ∃ n, (stackTrace G σ k x n).1 ∈ R := ⟨N, hN⟩
  have hf : Nat.find hh = N := (Nat.find_eq_iff hh).mpr ⟨hN, hmin⟩
  unfold stackCursor
  rw [dif_pos hh, hf]

theorem traceCursor_congr (σ σ' : CopyStacks G) (k : Cursor V) (x : V) (n : ℕ)
    (h : stackTrace G σ k x n = stackTrace G σ' k x n) :
    traceCursor G σ k x n = traceCursor G σ' k x n := by
  unfold traceCursor
  rw [h]

/-- The stack protocol depends only on stack entries at nonroot vertices above the
cursor. -/
theorem stackRun_congr (L : List V) : ∀ (s : State (V := V) (E := E) (I := I)) (k : Cursor V)
    (σ σ' : CopyStacks G), (∀ v j, v ∉ s.roots → k v ≤ j → σ (v, j) = σ' (v, j)) →
    stackRun G ι σ s k L = stackRun G ι σ' s k L := by
  induction L with
  | nil => intro s k σ σ' _; rfl
  | cons x xs ih =>
    intro s k σ σ' hσ
    by_cases hx : x ∈ s.roots
    · simp only [stackRun, if_pos hx]
      exact ih s k σ σ' hσ
    · simp only [stackRun, if_neg hx]
      by_cases hh : ∃ n, (stackTrace G σ k x n).1 ∈ s.roots
      · let N := Nat.find hh
        have hNm : (stackTrace G σ k x N).1 ∈ s.roots := Nat.find_spec hh
        have hmin : ∀ i < N, (stackTrace G σ k x i).1 ∉ s.roots := fun i hi => Nat.find_min hh hi
        have htr : ∀ n ≤ N, stackTrace G σ k x n = stackTrace G σ' k x n := fun n hn =>
          stackTrace_eq_of_agree_off G σ σ' s.roots k x hσ n (fun i hi => hmin i (by omega))
        have hNm' : (stackTrace G σ' k x N).1 ∈ s.roots := by rw [← htr N le_rfl]; exact hNm
        have hmin' : ∀ i < N, (stackTrace G σ' k x i).1 ∉ s.roots := by
          intro i hi
          rw [← htr i hi.le]
          exact hmin i hi
        have hused : ∀ i < N, stackDriver G σ k x i (position G x (stackDriver G σ k x) i) =
            stackDriver G σ' k x i (position G x (stackDriver G σ k x) i) := by
          intro i hi
          rw [position_stackDriver]
          have hc := traceCursor_congr G σ σ' k x i (htr i hi.le)
          change σ ((stackTrace G σ k x i).1, traceCursor G σ k x i (stackTrace G σ k x i).1) =
            σ' ((stackTrace G σ k x i).1, traceCursor G σ' k x i (stackTrace G σ k x i).1)
          rw [← hc]
          exact hσ _ _ (hmin i hi) (traceCursor_ge G σ k x i _)
        rw [query_stackDriver_of_hit G ι s σ k x hx N hNm hmin,
          query_stackDriver_of_hit G ι s σ' k x hx N hNm' hmin',
          ← attachAt_eq_of_used G ι s x _ _ N hused, Option.bind_some, Option.bind_some,
          stackCursor_of_hit G σ s.roots k x N hNm hmin,
          stackCursor_of_hit G σ' s.roots k x N hNm' hmin', ← htr N le_rfl]
        apply ih
        intro v j hv hj
        have hroots : s.roots ⊆ (attachAt G ι s x (stackDriver G σ k x) N).roots :=
          Set.subset_union_left
        have hge := stackCursor_ge G σ s.roots k x
        rw [stackCursor_of_hit G σ s.roots k x N hNm hmin] at hge
        exact hσ v j (fun h => hv (hroots h)) ((hge v).trans hj)
      · have hnot : ∀ n, (stackTrace G σ k x n).1 ∉ s.roots := fun n hn => hh ⟨n, hn⟩
        have hnot' : ∀ n, (stackTrace G σ' k x n).1 ∉ s.roots := by
          intro n
          rw [← stackTrace_eq_of_agree_off G σ σ' s.roots k x hσ n (fun i _ => hnot i)]
          exact hnot n
        rw [query_stackDriver_of_not_hit G ι s σ k x hx hnot,
          query_stackDriver_of_not_hit G ι s σ' k x hx hnot']
        rfl

/-- The cursor after a stack walk realizing the word `L`. -/
def wordCursor (R : Set V) (k : Cursor V) (x : V) (L : List E) : Cursor V :=
  if h : {σ : CopyStacks G | stackDriver G σ k x ∈ rowCyl G R x L}.Nonempty then
    stackCursor G h.some R k x
  else k

/-- A stack walk realizing a word first hits the roots at the end of the word. -/
theorem stackTrace_hit_of_mem (σ : CopyStacks G) (R : Set V) (k : Cursor V) (x : V)
    (L : List E) (hσ : stackDriver G σ k x ∈ rowCyl G R x L) :
    (stackTrace G σ k x L.length).1 ∈ R ∧ ∀ i < L.length, (stackTrace G σ k x i).1 ∉ R := by
  obtain ⟨_, hR, hav⟩ := hσ
  rw [position_stackDriver] at hR
  refine ⟨hR, fun i hi => ?_⟩
  have h := hav i hi
  rwa [position_stackDriver] at h

/-- Two stack configurations realizing the same word have the same trace along it. -/
theorem stackTrace_eq_of_mem (σ σ' : CopyStacks G) (R : Set V) (k : Cursor V) (x : V)
    (L : List E) (hσ : stackDriver G σ k x ∈ rowCyl G R x L)
    (hσ' : stackDriver G σ' k x ∈ rowCyl G R x L) :
    stackTrace G σ k x L.length = stackTrace G σ' k x L.length := by
  apply stackTrace_eq_of_agree
  intro i hi
  obtain ⟨h1, h2⟩ := stackTrace_eq_wordWalk G σ k x L i (fun j hj => hσ.1 j (hj.trans hi))
  have ha : ((stackTrace G σ k x i).1, traceCursor G σ k x i (stackTrace G σ k x i).1) =
      wordAddr G x k L i := by
    change _ = ((wordWalk G x k L i).1, (wordWalk G x k L i).2 (wordWalk G x k L i).1)
    rw [h2, h1]
  rw [ha]
  have e1 := ((stackDriver_mem_rowCyl_iff G σ R k x L).mp hσ).2 i hi
  have e2 := ((stackDriver_mem_rowCyl_iff G σ' R k x L).mp hσ').2 i hi
  rw [e1, Option.some.injEq] at e2
  exact Subtype.ext e2

theorem stackCursor_eq_wordCursor (σ : CopyStacks G) (R : Set V) (k : Cursor V) (x : V)
    (L : List E) (hσ : stackDriver G σ k x ∈ rowCyl G R x L) :
    stackCursor G σ R k x = wordCursor G R k x L := by
  have hne : {σ : CopyStacks G | stackDriver G σ k x ∈ rowCyl G R x L}.Nonempty := ⟨σ, hσ⟩
  have h₀ : stackDriver G hne.some k x ∈ rowCyl G R x L := hne.some_mem
  obtain ⟨hN, hmin⟩ := stackTrace_hit_of_mem G σ R k x L hσ
  obtain ⟨hN₀, hmin₀⟩ := stackTrace_hit_of_mem G hne.some R k x L h₀
  rw [wordCursor, dif_pos hne, stackCursor_of_hit G σ R k x L.length hN hmin,
    stackCursor_of_hit G hne.some R k x L.length hN₀ hmin₀,
    stackTrace_eq_of_mem G σ hne.some R k x L hσ h₀]

/-- On a stack word event the stack protocol continues from the attached state. -/
theorem stackRun_cons_of_mem (s : State (V := V) (E := E) (I := I)) (k : Cursor V) (x : V)
    (xs : List V) (hx : x ∉ s.roots) (L : List E) (σ : CopyStacks G)
    (hσ : stackDriver G σ k x ∈ rowCyl G s.roots x L) :
    stackRun G ι σ s k (x :: xs) =
      stackRun G ι σ (wordAttach G ι s x L) (wordCursor G s.roots k x L) xs := by
  simp only [stackRun, if_neg hx]
  rw [query_eq_wordAttach G ι s x hx L _ hσ, Option.bind_some,
    stackCursor_eq_wordCursor G σ s.roots k x L hσ]

/-- Without a hit the stack protocol fails. -/
theorem stackRun_cons_of_not_hits (s : State (V := V) (E := E) (I := I)) (k : Cursor V)
    (x : V) (xs : List V) (hx : x ∉ s.roots) (σ : CopyStacks G)
    (hh : ¬ hits G s.roots x (stackDriver G σ k x)) :
    stackRun G ι σ s k (x :: xs) = none := by
  simp only [stackRun, if_neg hx]
  rw [query_of_not_hits G ι s x hx _ hh]
  rfl

/-- On a word event for the first row the classical protocol continues from the attached
state with the remaining rows. -/
theorem classicalExplore_cons_of_mem (s : State (V := V) (E := E) (I := I)) (x : V)
    (xs : List V) (hx : x ∉ s.roots) (L : List E) (ω : ℕ → Driver G)
    (hω : ω 0 ∈ rowCyl G s.roots x L) :
    classicalExplore G ι s (x :: xs) ω =
      classicalExplore G ι (wordAttach G ι s x L) xs (fun i => ω (i + 1)) := by
  simp only [classicalExplore, if_neg hx]
  rw [query_eq_wordAttach G ι s x hx L _ hω, Option.bind_some]

/-- Without a hit of the first row the classical protocol fails. -/
theorem classicalExplore_cons_of_not_hits (s : State (V := V) (E := E) (I := I)) (x : V)
    (xs : List V) (hx : x ∉ s.roots) (ω : ℕ → Driver G)
    (hh : ¬ hits G s.roots x (ω 0)) :
    classicalExplore G ι s (x :: xs) ω = none := by
  simp only [classicalExplore, if_neg hx]
  rw [query_of_not_hits G ι s x hx _ hh]
  rfl

/-- The vertices of the walk of the stack driver are those of the stack trace. -/
theorem walkPath_vertices_stackDriver (σ : CopyStacks G) (k : Cursor V) (x : V) (n : ℕ) :
    @Quiver.Path.vertices (ULift.{0} V) (pathQuiver G) _ _ (walkPath G x (stackDriver G σ k x) n) =
      (@Quiver.Path.vertices V (instructionQuiver (incidentCopyHead G)) _ _
        (stackTrace G σ k x n).2).map ULift.up := by
  letI : Quiver V := instructionQuiver (incidentCopyHead G)
  letI : Quiver (ULift.{0} V) := pathQuiver G
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : (walkPath G x (stackDriver G σ k x) (n + 1)).vertices =
        (walkPath G x (stackDriver G σ k x) n).vertices.concat
          (ULift.up (position G x (stackDriver G σ k x) (n + 1))) := rfl
    have h2 : (stackTrace G σ k x (n + 1)).2.vertices =
        (stackTrace G σ k x n).2.vertices.concat (stackTrace G σ k x (n + 1)).1 := rfl
    rw [h1, h2, List.map_concat, ih, position_stackDriver]

/-- A stack coordinate read by a walk realizing a word is either at a new root or strictly
below the next cursor. -/
theorem wordAddr_root_or_lt (s : State (V := V) (E := E) (I := I)) (k : Cursor V) (x : V)
    (hx : x ∉ s.roots) (L : List E) (σ : CopyStacks G)
    (hσ : stackDriver G σ k x ∈ rowCyl G s.roots x L) (i : ℕ) (hi : i < L.length) :
    (wordAddr G x k L i).1 ∈ (wordAttach G ι s x L).roots ∨
      (wordAddr G x k L i).2 < wordCursor G s.roots k x L (wordAddr G x k L i).1 := by
  letI : Quiver V := instructionQuiver (incidentCopyHead G)
  letI : Quiver (ULift.{0} V) := pathQuiver G
  obtain ⟨hN, hmin⟩ := stackTrace_hit_of_mem G σ s.roots k x L hσ
  have hattach : wordAttach G ι s x L = attachAt G ι s x (stackDriver G σ k x) L.length := by
    have h := (query_eq_wordAttach G ι s x hx L _ hσ).symm.trans
      (query_stackDriver_of_hit G ι s σ k x hx L.length hN hmin)
    exact Option.some.inj h
  have hcur : wordCursor G s.roots k x L = erasedCursor k (stackTrace G σ k x L.length).2 := by
    rw [← stackCursor_eq_wordCursor G σ s.roots k x L hσ,
      stackCursor_of_hit G σ s.roots k x L.length hN hmin]
  let v := (wordAddr G x k L i).1
  by_cases hv : v ∈ (wordAttach G ι s x L).roots
  · exact Or.inl hv
  · right
    have hle : (loopErase (stackTrace G σ k x L.length).2).vertices.map ULift.up =
        (loopErase (walkPath G x (stackDriver G σ k x) L.length)).vertices :=
      loopErase_vertices_map_eq ULift.up ULift.up_injective _ _
        (walkPath_vertices_stackDriver G σ k x L.length).symm
    have hnot : v ∉ (loopErase (stackTrace G σ k x L.length).2).vertices := by
      intro hmem
      apply hv
      rw [hattach]
      refine Or.inr ?_
      change ULift.up v ∈ (loopErase (walkPath G x (stackDriver G σ k x) L.length)).vertices
      rw [← hle]
      exact List.mem_map_of_mem hmem
    have hcount : (departures (loopErase (stackTrace G σ k x L.length).2)).count v = 0 :=
      List.count_eq_zero_of_not_mem (fun hd => hnot (List.mem_of_mem_dropLast hd))
    obtain ⟨_, h2⟩ := stackTrace_eq_wordWalk G σ k x L L.length hσ.1
    have hcv : wordCursor G s.roots k x L v = (wordWalk G x k L L.length).2 v := by
      rw [hcur, erasedCursor, hcount, Nat.sub_zero, ← h2]
      rfl
    rw [hcv]
    have hstep : (wordWalk G x k L i).2 v < (wordWalk G x k L (i + 1)).2 v := by
      change (wordWalk G x k L i).2 v < pop (wordWalk G x k L i).2 {(wordWalk G x k L i).1} v
      rw [pop_apply_of_mem _ _
        (show v ∈ ({(wordWalk G x k L i).1} : Finset V) from Finset.mem_singleton.mpr rfl)]
      exact Nat.lt_succ_self _
    exact lt_of_lt_of_le hstep (wordState_cursor_mono _ _ _ _ (Nat.succ_le_of_lt hi) v)

theorem measurableSet_rowCyl (R : Set V) (x : V) (L : List E) :
    MeasurableSet (rowCyl G R x L) := by
  rw [rowCyl_eq]
  have he : {ω : Driver G | ValidWord G R x L ∧
      ∀ i < L.length, L[i]? = some (ω i (wordPos G x L i)).val} =
      {_ω | ValidWord G R x L} ∩ ⋂ i ∈ Finset.range L.length,
        (fun ω : Driver G => ω i) ⁻¹' {a | L[i]? = some (a (wordPos G x L i)).val} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_range,
      Set.mem_preimage]
  rw [he]
  exact (MeasurableSet.const _).inter
    (Finset.measurableSet_biInter _ fun i _ => measurable_pi_apply i trivial)

/-- The first row is independent of the remaining rows. -/
theorem driversLaw_head_tail (μ : Measure (Letter G)) [IsProbabilityMeasure μ]
    (A : Set (Driver G)) (C : Set (ℕ → Driver G)) (hA : MeasurableSet A)
    (hC : MeasurableSet C) :
    driversLaw G μ ({ω | ω 0 ∈ A} ∩ {ω | (fun i => ω (i + 1)) ∈ C}) =
      driverLaw G μ A * driversLaw G μ C := by
  have hi : IndepFun (fun ω : ℕ → Driver G => ω 0) (rowsAfter G 1) (driversLaw G μ) :=
    (rowsBefore_indep_tail G μ 1).comp
      (measurable_pi_apply (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1)) measurable_id
  have ht : Measurable (rowsAfter G 1) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (1 + i))
  have hshift : {ω : ℕ → Driver G | (fun i => ω (i + 1)) ∈ C} = rowsAfter G 1 ⁻¹' C := by
    ext ω
    change (fun i => ω (i + 1)) ∈ C ↔ (fun i => ω (1 + i)) ∈ C
    rw [show (fun i => ω (1 + i)) = fun i => ω (i + 1) from funext fun i => by rw [Nat.add_comm]]
  rw [hshift, show {ω : ℕ → Driver G | ω 0 ∈ A} = (fun ω => ω 0) ⁻¹' A from rfl,
    hi.measure_inter_preimage_eq_mul A C hA hC,
    ← Measure.map_apply (measurable_pi_apply 0) hA, ← Measure.map_apply ht hC, rowsAfter_law,
    show (driversLaw G μ).map (fun ω => ω 0) = driverLaw G μ from Measure.infinitePi_map_eval _ 0]

end
end FiniteAvalanches.Wilson.CopiedNetwork
