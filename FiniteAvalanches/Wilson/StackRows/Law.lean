import FiniteAvalanches.Wilson.StackRows.Run

/-! The Wilson protocol reading vertex stacks of independent uniform incident copies and
the classical protocol using a fresh row of independent uniform letters for every walk
have the same law of complete outputs, including histories and failure. The proof splits
both protocols along the word of copies read by the first walk; the two word events have
the same mass, and in both protocols the first word is independent of what follows. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CopiedNetwork

open MeasureTheory ProbabilityTheory FiniteAvalanches.Trees FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

variable {V E I : Type} [Fintype V] [Fintype E] (G : Multigraph V E) (ι : E ↪ I)
variable [∀ v, Nonempty (IncidentCopy G v)]

/-- A stack word event is independent of the stack protocol continuing after it. -/
theorem variableStackLaw_stackCyl_inter (s : State (V := V) (E := E) (I := I)) (k : Cursor V)
    (x : V) (xs : List V) (hx : x ∉ s.roots) (L : List E)
    (B : Set (Option (State (V := V) (E := E) (I := I))))
    (hB : MeasurableSet {σ : CopyStacks G |
      stackRun G ι σ (wordAttach G ι s x L) (wordCursor G s.roots k x L) xs ∈ B}) :
    variableStackLaw (IncidentCopy G)
        ({σ | stackDriver G σ k x ∈ rowCyl G s.roots x L} ∩
          {σ | stackRun G ι σ (wordAttach G ι s x L) (wordCursor G s.roots k x L) xs ∈ B}) =
      variableStackLaw (IncidentCopy G) {σ | stackDriver G σ k x ∈ rowCyl G s.roots x L} *
        variableStackLaw (IncidentCopy G)
          {σ | stackRun G ι σ (wordAttach G ι s x L) (wordCursor G s.roots k x L) xs ∈ B} := by
  by_cases hne : {σ : CopyStacks G | stackDriver G σ k x ∈ rowCyl G s.roots x L}.Nonempty
  · obtain ⟨σ₀, hσ₀⟩ := hne
    let ω₀ : CopyStacks G := fun p => Classical.choice (inferInstance : Nonempty (IncidentCopy G p.1))
    unfold variableStackLaw
    refine infinitePi_inter_eq_mul_of_disjoint _
      (((Finset.range L.length).image (wordAddr G x k L) : Finset (V × ℕ)) : Set (V × ℕ))
      {p | p.1 ∉ (wordAttach G ι s x L).roots ∧ wordCursor G s.roots k x L p.1 ≤ p.2}
      ?_ ω₀ _ _ (measurableSet_stackCyl G s.roots k x L) hB ?_ ?_
    · rw [Set.disjoint_left]
      intro p hp hpT
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp)
      rcases wordAddr_root_or_lt G ι s k x hx L σ₀ hσ₀ i (Finset.mem_range.mp hi) with h | h
      · exact hpT.1 h
      · exact absurd hpT.2 (not_le.mpr h)
    · intro σ σ' h
      apply stackDriver_mem_rowCyl_congr
      intro i hi
      exact h _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi)))
    · intro σ σ' h
      simp only [Set.mem_setOf_eq]
      rw [stackRun_congr G ι xs _ _ σ σ' (fun v j hv hj => h (v, j) ⟨hv, hj⟩)]
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Set.empty_inter, measure_empty, zero_mul]

variable [Countable I] [Nontrivial V] (hconn : ∀ x y, G.reaches Finset.univ x y)

/-- The stack protocol and the classical row protocol have the same law of complete
outputs, from every state, every stack cursor and every order list. -/
theorem stackRun_law (L : List V) : ∀ (s : State (V := V) (E := E) (I := I)) (k : Cursor V)
    (B : Set (Option (State (V := V) (E := E) (I := I)))),
    MeasurableSet {σ : CopyStacks G | stackRun G ι σ s k L ∈ B} ∧
      variableStackLaw (IncidentCopy G) {σ | stackRun G ι σ s k L ∈ B} =
        driversLaw G (uniformLetterLaw G hconn) {ω | classicalExplore G ι s L ω ∈ B} := by
  letI : Nonempty (Letter G) := ⟨fun v => @Classical.ofNonempty _ (incident_nonempty G hconn v)⟩
  induction L with
  | nil =>
    intro s k B
    by_cases hs : some s ∈ B
    · have h1 : {σ : CopyStacks G | stackRun G ι σ s k [] ∈ B} = Set.univ := by
        ext σ
        simp only [stackRun, Set.mem_setOf_eq, hs, Set.mem_univ]
      have h2 : {ω : ℕ → Driver G | classicalExplore G ι s [] ω ∈ B} = Set.univ := by
        ext ω
        simp only [classicalExplore, Set.mem_setOf_eq, hs, Set.mem_univ]
      rw [h1, h2]
      exact ⟨MeasurableSet.univ, by rw [measure_univ, measure_univ]⟩
    · have h1 : {σ : CopyStacks G | stackRun G ι σ s k [] ∈ B} = ∅ := by
        ext σ
        simp only [stackRun, Set.mem_setOf_eq, hs, Set.mem_empty_iff_false]
      have h2 : {ω : ℕ → Driver G | classicalExplore G ι s [] ω ∈ B} = ∅ := by
        ext ω
        simp only [classicalExplore, Set.mem_setOf_eq, hs, Set.mem_empty_iff_false]
      rw [h1, h2]
      exact ⟨MeasurableSet.empty, by rw [measure_empty, measure_empty]⟩
  | cons x xs ih =>
    intro s k B
    by_cases hx : x ∈ s.roots
    · have h1 : {σ : CopyStacks G | stackRun G ι σ s k (x :: xs) ∈ B} =
          {σ | stackRun G ι σ s k xs ∈ B} := by
        ext σ
        simp only [Set.mem_setOf_eq, stackRun, if_pos hx]
      have h2 : {ω : ℕ → Driver G | classicalExplore G ι s (x :: xs) ω ∈ B} =
          {ω | classicalExplore G ι s xs ω ∈ B} := by
        ext ω
        simp only [Set.mem_setOf_eq, classicalExplore, if_pos hx]
      rw [h1, h2]
      exact ih s k B
    · let R := s.roots
      let D : List E → Set (ℕ → Driver G) := fun L =>
        {ω | classicalExplore G ι (wordAttach G ι s x L) xs ω ∈ B}
      let A : List E → Set (CopyStacks G) := fun L => {σ | stackDriver G σ k x ∈ rowCyl G R x L}
      let C : List E → Set (CopyStacks G) := fun L =>
        {σ | stackRun G ι σ (wordAttach G ι s x L) (wordCursor G R k x L) xs ∈ B}
      let A' : List E → Set (ℕ → Driver G) := fun L => {ω | ω 0 ∈ rowCyl G R x L}
      let C' : List E → Set (ℕ → Driver G) := fun L => {ω | (fun i => ω (i + 1)) ∈ D L}
      have hDm : ∀ L, MeasurableSet (D L) := fun L =>
        measurable_classicalExplore G ι (wordAttach G ι s x L) xs trivial
      have hshift : Measurable (fun ω : ℕ → Driver G => fun i => ω (i + 1)) :=
        measurable_pi_lambda _ (fun i => measurable_pi_apply (i + 1))
      have hS : {σ : CopyStacks G | stackRun G ι σ s k (x :: xs) ∈ B} =
          (⋃ L, A L ∩ C L) ∪ ((⋃ L, A L)ᶜ ∩ {_σ | none ∈ B}) := by
        ext σ
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
          Set.mem_compl_iff, not_exists, A, C]
        by_cases hh : hits G R x (stackDriver G σ k x)
        · obtain ⟨L, hL⟩ := (hits_iff_exists_rowCyl G R x _).mp hh
          rw [stackRun_cons_of_mem G ι s k x xs hx L σ hL]
          constructor
          · intro hBm
            exact Or.inl ⟨L, hL, hBm⟩
          · rintro (⟨L', hL', hBm⟩ | ⟨hno, _⟩)
            · have he : L' = L := by
                by_contra hne
                exact Set.disjoint_left.mp (rowCyl_disjoint G R x hne) hL' hL
              rw [he] at hBm
              exact hBm
            · exact absurd hL (hno L)
        · have hnoL : ∀ L, stackDriver G σ k x ∉ rowCyl G R x L := fun L hL =>
            hh ((hits_iff_exists_rowCyl G R x _).mpr ⟨L, hL⟩)
          rw [stackRun_cons_of_not_hits G ι s k x xs hx σ hh]
          constructor
          · intro hBm
            exact Or.inr ⟨hnoL, hBm⟩
          · rintro (⟨L, hL, _⟩ | ⟨_, hBm⟩)
            · exact absurd hL (hnoL L)
            · exact hBm
      have hS' : {ω : ℕ → Driver G | classicalExplore G ι s (x :: xs) ω ∈ B} =
          (⋃ L, A' L ∩ C' L) ∪ ((⋃ L, A' L)ᶜ ∩ {_ω | none ∈ B}) := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
          Set.mem_compl_iff, not_exists, A', C', D]
        by_cases hh : hits G R x (ω 0)
        · obtain ⟨L, hL⟩ := (hits_iff_exists_rowCyl G R x _).mp hh
          rw [classicalExplore_cons_of_mem G ι s x xs hx L ω hL]
          constructor
          · intro hBm
            exact Or.inl ⟨L, hL, hBm⟩
          · rintro (⟨L', hL', hBm⟩ | ⟨hno, _⟩)
            · have he : L' = L := by
                by_contra hne
                exact Set.disjoint_left.mp (rowCyl_disjoint G R x hne) hL' hL
              rw [he] at hBm
              exact hBm
            · exact absurd hL (hno L)
        · have hnoL : ∀ L, ω 0 ∉ rowCyl G R x L := fun L hL =>
            hh ((hits_iff_exists_rowCyl G R x _).mpr ⟨L, hL⟩)
          rw [classicalExplore_cons_of_not_hits G ι s x xs hx ω hh]
          constructor
          · intro hBm
            exact Or.inr ⟨hnoL, hBm⟩
          · rintro (⟨L, hL, _⟩ | ⟨_, hBm⟩)
            · exact absurd hL (hnoL L)
            · exact hBm
      have hAd : Pairwise (Function.onFun Disjoint A) := fun L L' h =>
        (rowCyl_disjoint G R x h).preimage (fun σ => stackDriver G σ k x)
      have hAd' : Pairwise (Function.onFun Disjoint A') := fun L L' h =>
        (rowCyl_disjoint G R x h).preimage (fun ω : ℕ → Driver G => ω 0)
      obtain ⟨hm, hP⟩ := measure_firstStep (variableStackLaw (IncidentCopy G)) A C
        (fun L => measurableSet_stackCyl G R k x L) (fun L => (ih _ _ B).1) hAd (none ∈ B) _ hS
      obtain ⟨_, hQ⟩ := measure_firstStep (driversLaw G (uniformLetterLaw G hconn)) A' C'
        (fun L => measurable_pi_apply 0 (measurableSet_rowCyl G R x L))
        (fun L => hshift (hDm L)) hAd' (none ∈ B) _ hS'
      have hrow : ∀ L, driversLaw G (uniformLetterLaw G hconn) (A' L) =
          driverLaw G (uniformLetterLaw G hconn) (rowCyl G R x L) := by
        intro L
        change driversLaw G (uniformLetterLaw G hconn) ((fun ω => ω 0) ⁻¹' rowCyl G R x L) = _
        rw [← Measure.map_apply (measurable_pi_apply 0) (measurableSet_rowCyl G R x L),
          show (driversLaw G (uniformLetterLaw G hconn)).map (fun ω => ω 0) =
            driverLaw G (uniformLetterLaw G hconn) from Measure.infinitePi_map_eval _ 0]
      have hA : ∀ L, variableStackLaw (IncidentCopy G) (A L) =
          driversLaw G (uniformLetterLaw G hconn) (A' L) := by
        intro L
        rw [hrow L]
        exact (variableStackLaw_stackCyl G R k x L).trans (driverLaw_rowCyl G hconn R x L).symm
      have hAC : ∀ L, variableStackLaw (IncidentCopy G) (A L ∩ C L) =
          driversLaw G (uniformLetterLaw G hconn) (A' L ∩ C' L) := by
        intro L
        rw [variableStackLaw_stackCyl_inter G ι s k x xs hx L B ((ih _ _ B).1),
          driversLaw_head_tail G (uniformLetterLaw G hconn) _ _ (measurableSet_rowCyl G R x L)
            (hDm L)]
        change variableStackLaw (IncidentCopy G) (A L) * variableStackLaw (IncidentCopy G) (C L) = _
        rw [hA L, hrow L, (ih _ _ B).2]
      refine ⟨hm, ?_⟩
      rw [hP, hQ, tsum_congr hAC, tsum_congr hA]

end
end FiniteAvalanches.Wilson.CopiedNetwork
