import FiniteAvalanches.Wilson.Lattice.WiredArrowEquiv

/-! The finite wired cycle-popping law on original rooted copied forests. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open MeasureTheory ProbabilityTheory FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open Function
open scoped Classical ENNReal

noncomputable section

/-- Stack configurations whose terminal arrows select the given original-copy forest. -/
def wiredStackForestEvent (R : RootPair) (N : ℕ) (k : Cursor (FiniteWired.Vertex N))
    (F : FiniteForest R N) : Set (FiniteWired.Vertex N × ℕ → FiniteWired.Direction) :=
  {σ | ∃ a : GoodArrows (wiredRoots R N).val (wiredHead N),
    wiredArrowForest R N a = F ∧
    σ ∈ terminalOutputEvent (wiredRoots R N).val (wiredHead N) k (fun v i σ => σ (v, i)) a}

/-- A terminal forest event is partitioned by its arbitrary root directions. -/
theorem wiredStackForestEvent_eq_iUnion (R : RootPair) (N : ℕ)
    (k : Cursor (FiniteWired.Vertex N)) (F : FiniteForest R N) :
    wiredStackForestEvent R N k F = ⋃ d : WiredRootDirections R N,
      terminalOutputEvent (wiredRoots R N).val (wiredHead N) k (fun v i σ => σ (v, i))
        (forestDirectionsWithRoots R N F d) := by
  ext σ
  simp only [wiredStackForestEvent, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨a, ha, hσ⟩
    refine ⟨fun r => a.val r.val, ?_⟩
    have he : forestDirectionsWithRoots R N F (fun r => a.val r.val) = a := by
      have h := (wiredArrowForestEquiv R N).left_inv a
      change forestDirectionsWithRoots R N (wiredArrowForest R N a) (fun r => a.val r.val) = a at h
      rwa [ha] at h
    rw [he]
    exact hσ
  · rintro ⟨d, hd⟩
    exact ⟨forestDirectionsWithRoots R N F d,
      wiredArrowForest_forestDirectionsWithRoots R N F d, hd⟩

/-- The terminal rooted forest in a wired box is uniform on the original copied forests. -/
theorem directionStackLaw_forest_uniform (R : RootPair) (N : ℕ)
    (k : Cursor (FiniteWired.Vertex N)) (F : FiniteForest R N) :
    directionStackLaw (FiniteWired.Vertex N) (wiredStackForestEvent R N k F) =
      1 / (Fintype.card (FiniteForest R N) : ℝ≥0∞) := by
  let Q : WiredRootDirections R N → Set (FiniteWired.Vertex N × ℕ → FiniteWired.Direction) :=
    fun d => terminalOutputEvent (wiredRoots R N).val (wiredHead N) k
      (fun v i σ => σ (v, i)) (forestDirectionsWithRoots R N F d)
  have hinj : Function.Injective (forestDirectionsWithRoots R N F) := by
    intro d e hde
    have h := congrArg (fun a => (wiredArrowForestEquiv R N a).2) hde
    have hd := (wiredArrowForestEquiv R N).right_inv (F, d)
    have he := (wiredArrowForestEquiv R N).right_inv (F, e)
    exact (congrArg Prod.snd hd).symm.trans (h.trans (congrArg Prod.snd he))
  have hdis : Pairwise (Disjoint on Q) := by
    intro d e hde
    exact disjoint_terminalOutputEvent (wiredRoots R N).val (wiredHead N) k
      (fun v i (σ : FiniteWired.Vertex N × ℕ → FiniteWired.Direction) => σ (v, i))
      (fun h => hde (hinj h))
  have hmeas : ∀ d, MeasurableSet (Q d) := by
    intro d
    apply measurableSet_terminalOutputEvent
    intro v i
    exact measurable_pi_apply (v, i)
  have hunion : wiredStackForestEvent R N k F = ⋃ d, Q d :=
    wiredStackForestEvent_eq_iUnion R N k F
  rw [hunion, measure_iUnion hdis hmeas, tsum_fintype]
  simp_rw [show ∀ d, directionStackLaw (FiniteWired.Vertex N) (Q d) =
      1 / (Fintype.card (GoodArrows (wiredRoots R N).val (wiredHead N)) : ℝ≥0∞) from
    fun d => wiredStack_terminal_uniform R N k (forestDirectionsWithRoots R N F d)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : Fintype.card (GoodArrows (wiredRoots R N).val (wiredHead N)) =
      Fintype.card (FiniteForest R N) * Fintype.card (WiredRootDirections R N) := by
    rw [Fintype.card_congr (wiredArrowForestEquiv R N), Fintype.card_prod]
  rw [hcard, Nat.cast_mul]
  letI : Nonempty (WiredRootDirections R N) := ⟨fun _ => (0, false)⟩
  have hne : (Fintype.card (WiredRootDirections R N) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have htop : (Fintype.card (WiredRootDirections R N) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc
    (Fintype.card (WiredRootDirections R N) : ℝ≥0∞) *
        (1 / ((Fintype.card (FiniteForest R N) : ℝ≥0∞) *
          (Fintype.card (WiredRootDirections R N) : ℝ≥0∞))) =
      (1 * (Fintype.card (WiredRootDirections R N) : ℝ≥0∞)) /
        ((Fintype.card (FiniteForest R N) : ℝ≥0∞) *
          (Fintype.card (WiredRootDirections R N) : ℝ≥0∞)) := by
            simp only [one_mul, div_eq_mul_inv]
    _ = 1 / (Fintype.card (FiniteForest R N) : ℝ≥0∞) :=
      ENNReal.mul_div_mul_right 1 _ hne htop


/-- Every terminal forest event is measurable. -/
theorem measurableSet_wiredStackForestEvent (R : RootPair) (N : ℕ)
    (k : Cursor (FiniteWired.Vertex N)) (F : FiniteForest R N) :
    MeasurableSet (wiredStackForestEvent R N k F) := by
  rw [wiredStackForestEvent_eq_iUnion R N k F]
  apply MeasurableSet.iUnion
  intro d
  apply measurableSet_terminalOutputEvent
  intro v i
  exact measurable_pi_apply (v, i)

/-- Distinct forests give disjoint terminal stack events. -/
theorem disjoint_wiredStackForestEvent (R : RootPair) (N : ℕ)
    (k : Cursor (FiniteWired.Vertex N)) : Pairwise (Disjoint on wiredStackForestEvent R N k) := by
  intro F H hne
  apply Set.disjoint_left.mpr
  intro σ hF hH
  obtain ⟨a, ha, hσa⟩ := hF
  obtain ⟨b, hb, hσb⟩ := hH
  by_cases hab : a = b
  · subst b
    exact hne (ha.symm.trans hb)
  · exact Set.disjoint_left.mp
      (disjoint_terminalOutputEvent (wiredRoots R N).val (wiredHead N) k
        (fun v i (σ : FiniteWired.Vertex N × ℕ → FiniteWired.Direction) => σ (v, i)) hab) hσa hσb

/-- The finite wired terminal-forest distribution is the repository's uniform
law on original copied forests. -/
theorem directionStackLaw_forestEvent_eq (R : RootPair) (N : ℕ)
    (k : Cursor (FiniteWired.Vertex N)) (S : Set (FiniteForest R N)) :
    directionStackLaw (FiniteWired.Vertex N)
        {σ | ∃ a : GoodArrows (wiredRoots R N).val (wiredHead N),
          wiredArrowForest R N a ∈ S ∧
          σ ∈ terminalOutputEvent (wiredRoots R N).val (wiredHead N) k (fun v i σ => σ (v, i)) a} =
      finiteUniformLaw R N S := by
  have he : {σ | ∃ a : GoodArrows (wiredRoots R N).val (wiredHead N),
        wiredArrowForest R N a ∈ S ∧
        σ ∈ terminalOutputEvent (wiredRoots R N).val (wiredHead N) k (fun v i σ => σ (v, i)) a} =
      ⋃ F : S, wiredStackForestEvent R N k F.val := by
    ext σ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, wiredStackForestEvent]
    constructor
    · rintro ⟨a, ha, hσ⟩
      exact ⟨⟨wiredArrowForest R N a, ha⟩, a, rfl, hσ⟩
    · rintro ⟨⟨F, hF⟩, a, ha, hσ⟩
      exact ⟨a, ha.symm ▸ hF, hσ⟩
  have hdis : Pairwise (Disjoint on fun F : S => wiredStackForestEvent R N k F.val) := by
    intro F H hne
    apply disjoint_wiredStackForestEvent R N k
    intro heq
    exact hne (Subtype.ext heq)
  rw [he, measure_iUnion hdis (fun F => measurableSet_wiredStackForestEvent R N k F.val),
    tsum_fintype, finiteUniformLaw, FiniteAvalanches.uniformMeasure_apply]
  simp_rw [directionStackLaw_forest_uniform R N k]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  simp only [one_mul, div_eq_mul_inv]

end
end FiniteAvalanches.Wilson.Lattice
