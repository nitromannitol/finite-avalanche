import FiniteAvalanches.Electrical.Geometry.BSST
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Lean

namespace FiniteAvalanches.Electrical.ChartExistence
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- Ordinary compact separation supplies every trace-box field once an actual
parametrized arc has been straightened. No graph-topology result is assumed. -/
theorem edgeChart_of_straightening (D : Drawing J) (e : E) (c : OrientedChart)
    (hs : ∀ t : ArcParameter, c.map (D.curve e t) = (t.val, 0)) :
    Nonempty (EdgeChart D e) := by
  let tmid : ArcParameter := ⟨1/2, by constructor <;> norm_num⟩
  let K : Set Plane := Set.range D.point ∪
    ⋃ f : {f : E // f ≠ e}, Set.range (D.curve f.val)
  have hK : IsCompact K :=
    (Set.finite_range D.point).isCompact.union
      (isCompact_iUnion fun f : {f : E // f ≠ e} => isCompact_range (D.continuous f.val))
  have hmid : D.curve e tmid ∉ K := by
    rintro (⟨v, hv⟩ | h)
    · exact D.avoids e tmid (by norm_num [tmid]) (by norm_num [tmid]) v hv.symm
    · obtain ⟨f, t, ht⟩ := Set.mem_iUnion.mp h
      have hi := (D.intersects e f.val (Ne.symm f.property) tmid t ht.symm).1
      norm_num [tmid] at hi
  have hq : (1/2, 0) ∉ c.map '' K := by
    rintro ⟨z, hz, he⟩
    apply hmid
    have heq : z = D.curve e tmid := c.map.injective (he.trans (hs tmid).symm)
    exact heq ▸ hz
  have hopen : IsOpen (c.map '' K)ᶜ := (hK.image c.map.continuous).isClosed.isOpen_compl
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.isOpen_iff.mp hopen (1/2, 0) hq
  let r : ℝ := min (epsilon / 2) (1/8)
  have hr : 0 < r := lt_min (half_pos hepsilon) (by norm_num)
  have hsmall : r < 1/4 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hrepsilon : r < epsilon := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨⟨c, r, hr, hsmall, fun t _ => hs t, ?_⟩⟩
  intro z hx hy
  have hzball : z ∈ Metric.ball (1/2, 0) epsilon := by
    change dist z (1/2, 0) < epsilon
    have hd : dist z (1/2, 0) < r := by
      simpa only [Prod.dist_eq, Real.dist_eq, sub_zero] using max_lt hx hy
    exact lt_trans hd hrepsilon
  have hzK : c.map.symm z ∉ K := by
    intro hz
    exact hball hzball ⟨c.map.symm z, hz, c.map.apply_symm_apply z⟩
  constructor
  · rintro (⟨v, hv⟩ | h)
    · exact (hzK (Or.inl ⟨v, hv⟩)).elim
    · obtain ⟨f, t, ht⟩ := Set.mem_iUnion.mp h
      by_cases hfe : f = e
      · subst f
        have he : z = (t.val, 0) := by
          rw [← hs t, ht, c.map.apply_symm_apply]
        exact congrArg Prod.snd he
      · exact (hzK (Or.inr (Set.mem_iUnion.mpr ⟨⟨f, hfe⟩, t, ht⟩))).elim
  · intro hz
    have ht : z.1 ∈ Set.Icc (0 : ℝ) 1 := by
      have h := abs_lt.mp hx
      constructor <;> linarith [hsmall]
    let t : ArcParameter := ⟨z.1, ht⟩
    have he : D.curve e t = c.map.symm z := by
      apply c.map.injective
      rw [hs t, c.map.apply_symm_apply]
      exact Prod.ext rfl hz.symm
    exact Or.inr (Set.mem_iUnion.mpr ⟨e, t, he⟩)

/-- Same original drawing and copy IDs; this packages EXISTING edge charts only. -/
def planeEmbeddingOfCharts (D : Drawing J) (hloop : ∀ e, J.left e ≠ J.right e)
    (charts : ∀ e, EdgeChart D e) : PlaneEmbedding J where
  drawing := D
  edge_injective := fun e => D.nonloop_curve_injective e (hloop e)
  edgeChart := charts

/-- Exact intended application of the proposed PURE parametrized-arc standard.
This is conditional on that unregistered standard, not source chart existence. -/
theorem consume_arc_straightening
    (straighten : ∀ gamma : ArcParameter → Plane,
      Continuous gamma → Function.Injective gamma →
        ∃ c : OrientedChart, ∀ t : ArcParameter, c.map (gamma t) = (t.val, 0))
    (D : Drawing J) (hloop : ∀ e, J.left e ≠ J.right e) :
    Nonempty (∀ e, EdgeChart D e) := by
  have h : ∀ e, Nonempty (EdgeChart D e) := by
    intro e
    obtain ⟨c, hc⟩ := straighten (D.curve e) (D.continuous e)
      (D.nonloop_curve_injective e (hloop e))
    exact edgeChart_of_straightening D e c hc
  exact ⟨fun e => Classical.choice (h e)⟩

/-- The same single pure standard applies to the ACTUAL auxiliary drawing,
including all original copies and the new alpha-to-beta arc. -/
theorem consume_auxiliary_straightening
    (straighten : ∀ gamma : ArcParameter → Plane,
      Continuous gamma → Function.Injective gamma →
        ∃ c : OrientedChart, ∀ t : ArcParameter, c.map (gamma t) = (t.val, 0))
    (D : Drawing J) (hloop : ∀ e, J.left e ≠ J.right e)
    (alpha beta : V) (hne : alpha ≠ beta) (F : BSST.Face D)
    (A : BSST.AuxiliaryArc D F alpha beta) :
    Nonempty (∀ z : E ⊕ Unit, EdgeChart A.drawing z) := by
  apply consume_arc_straightening straighten A.drawing
  intro z
  cases z with
  | inl e => exact hloop e
  | inr _ => exact hne

end
end FiniteAvalanches.Electrical.ChartExistence

#print axioms FiniteAvalanches.Electrical.ChartExistence.edgeChart_of_straightening
#print axioms FiniteAvalanches.Electrical.ChartExistence.consume_arc_straightening
#print axioms FiniteAvalanches.Electrical.ChartExistence.consume_auxiliary_straightening
