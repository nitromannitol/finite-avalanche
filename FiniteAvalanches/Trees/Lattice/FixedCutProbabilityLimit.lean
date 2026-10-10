import FiniteAvalanches.Trees.Lattice.FiniteFixedCut

set_option autoImplicit false
open LatticeProb MeasureTheory Filter
open scoped Classical ENNReal

namespace FixedCutLimit12
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Sandpile TreeMeasurability11
noncomputable section

/-- The manuscript's complete fixed-original-edge probability limit, at every
source and every nonnegative integer threshold, from actual wired tree laws. -/
theorem actual_fixed_cut_probability_limit (o : Site 2) (f : LatticeEdge) (M : ℕ) :
    Tendsto (fun N : ℕ => (WiredTrees.law N) (finiteCutEscape o f M N)) atTop
      (nhds (endedUST (infiniteCutEscape o f M))) := by
  let A : Bool → Set EndedTree := fun b =>
    if b then infiniteCutEscape o f M else (infiniteCutEscape o f M)ᶜ
  let AN : Bool → (N : ℕ) → Set (WiredTrees.graph N).SpanningTree := fun b N =>
    if b then finiteCutEscape o f M N else (finiteCutEscape o f M N)ᶜ
  -- Open unions of actual finite-coordinate cylinders whose local determination
  -- is valid in both genuine carriers. These are internal approximation sets;
  -- every source-tree witness is constructed from the proved certificates below.
  let G : Bool → ℕ → Set EdgeField := fun b R =>
    ⋃ F : Finset LatticeEdge, ⋃ p : F → Bool,
      ⋃ (_hInf : ∀ T : EndedTree, T.val ∈ cylinder F p → T ∈ A b),
      ⋃ (_hFin : ∀ N ≥ R, ∀ t : (WiredTrees.graph N).SpanningTree,
        wiredField t ∈ cylinder F p → t ∈ AN b N), cylinder F p
  have hOpen (b : Bool) (R : ℕ) : IsOpen (G b R) :=
    isOpen_iUnion fun F => isOpen_iUnion fun p => isOpen_iUnion fun _ =>
      isOpen_iUnion fun _ => (isClopen_cylinder F p).isOpen
  have hmono (b : Bool) : Monotone (G b) := by
    intro R S hRS ω hω
    simp only [G, Set.mem_iUnion] at hω ⊢
    obtain ⟨F, p, hInf, hFin, hw⟩ := hω
    exact ⟨F, p, hInf, fun N hN t ht => hFin N (hRS.trans hN) t ht, hw⟩
  have hclass (b : Bool) (R : ℕ) (T : EndedTree) (hT : T.val ∈ G b R) : T ∈ A b := by
    simp only [G, Set.mem_iUnion] at hT
    obtain ⟨F, p, hInf, _hFin, hw⟩ := hT
    exact hInf T hw
  have hfinite (b : Bool) (R N : ℕ) (hN : R ≤ N)
      (t : (WiredTrees.graph N).SpanningTree) (ht : wiredField t ∈ G b R) : t ∈ AN b N := by
    simp only [G, Set.mem_iUnion] at ht
    obtain ⟨F, p, _hInf, hFin, hw⟩ := ht
    exact hFin N hN t hw
  have hcover (b : Bool) (T : EndedTree) (hT : T ∈ A b) : ∃ R, T.val ∈ G b R := by
    obtain ⟨F₁, hF₁⟩ := FixedCutCertificate11.exists_finite_fixed_cut_certificate T o f M
    obtain ⟨F₂, R, hF₂⟩ := exists_finite_wired_fixed_cut_certificate T o f M
    let F := F₁ ∪ F₂
    let p : F → Bool := F.restrict T.val
    have hInf : ∀ T' : EndedTree, T'.val ∈ cylinder F p → T' ∈ A b := by
      intro T' hp
      have he := hF₁ T' (fun e he => congrFun hp ⟨e, Finset.mem_union_left _ he⟩)
      cases b
      · exact fun ht => hT (he.mp ht)
      · exact he.mpr hT
    have hFin : ∀ N ≥ R, ∀ t : (WiredTrees.graph N).SpanningTree,
        wiredField t ∈ cylinder F p → t ∈ AN b N := by
      intro N hN t hp
      have he := hF₂ N hN t (fun e he => congrFun hp ⟨e, Finset.mem_union_right _ he⟩)
      cases b
      · exact fun ht => hT (he.mp ht)
      · exact he.mpr hT
    refine ⟨R, ?_⟩
    simp only [G, Set.mem_iUnion]
    exact ⟨F, p, hInf, hFin, rfl⟩
  have hpreimage (b : Bool) :
      (Subtype.val : EndedTree → EdgeField) ⁻¹' (⋃ R, G b R) = A b := by
    ext T
    constructor
    · intro hT
      obtain ⟨R, hR⟩ := Set.mem_iUnion.mp hT
      exact hclass b R T hR
    · intro hT
      obtain ⟨R, hR⟩ := hcover b T hT
      exact Set.mem_iUnion.mpr ⟨R, hR⟩
  have hmass (b : Bool) :
      (⨆ R, (squareLatticeUST : Measure EdgeField) (G b R)) = endedUST (A b) := by
    rw [← (hmono b).measure_iUnion]
    rw [← endedUST_map,
      Measure.map_apply measurable_subtype_coe (isOpen_iUnion (hOpen b)).measurableSet,
      hpreimage b]
  have hlower (b : Bool) :
      endedUST (A b) ≤ liminf (fun N => (WiredTrees.law N) (AN b N)) atTop := by
    rw [← hmass b]
    apply iSup_le
    intro R
    apply (ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      squareLatticeUST_tendsto (hOpen b R)).trans
    refine liminf_le_liminf ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [eventually_ge_atTop R] with N hN
    change finiteLaw N (G b R) ≤ _
    rw [finiteLaw_apply N _ (hOpen b R).measurableSet]
    exact measure_mono (fun t ht => hfinite b R N hN t ht)
  have hmeas : MeasurableSet (infiniteCutEscape o f M) := measurableSet_infiniteCutEscape o f M
  have hcompl : endedUST (A false) = 1 - endedUST (A true) := by
    simpa only [A, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, measure_univ] using
      measure_compl hmeas (measure_lt_top endedUST _).ne
  have hncompl (N : ℕ) :
      (WiredTrees.law N) (AN true N) = 1 - (WiredTrees.law N) (AN false N) := by
    simpa only [AN, Bool.false_eq_true, Bool.true_eq, ↓reduceIte, compl_compl, measure_univ] using
      measure_compl ((Set.toFinite (finiteCutEscape o f M N)).measurableSet.compl)
        (measure_lt_top (WiredTrees.law N) _).ne
  have hupper : limsup (fun N => (WiredTrees.law N) (AN true N)) atTop ≤ endedUST (A true) := by
    simp_rw [hncompl]
    rw [ENNReal.limsup_const_sub atTop _ ENNReal.one_ne_top]
    apply (tsub_le_tsub_left (hlower false) 1).trans_eq
    rw [hcompl]
    apply ENNReal.sub_sub_cancel ENNReal.one_ne_top
    simpa only [measure_univ] using
      (measure_mono (Set.subset_univ (A true)) : endedUST (A true) ≤ endedUST Set.univ)
  exact tendsto_of_le_liminf_of_limsup_le (hlower true) hupper

end
end FixedCutLimit12
