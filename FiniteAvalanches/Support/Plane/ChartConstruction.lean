import FiniteAvalanches.Support.Plane.GeometricDual
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Edge charts from local trace containment

A straight parametrized edge determines the whole local trace once the trace
is known to lie on the corresponding coordinate axis.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb

open Set Source

/-- A one-sided local trace condition suffices to construct an edge chart. -/
noncomputable def edgeChartOfTraceSubset {V E : Type} [Fintype V] [Fintype E]
    {J : CopiedGraph V E} (D : Drawing J) (e : E) (chart : OrientedChart)
    (r : ℝ) (hr : 0 < r) (hrsmall : r < 1 / 4)
    (hstraight : ∀ t : ArcParameter, |t.val - 1 / 2| < r →
      chart.map (D.curve e t) = (t.val, 0))
    (htrace : ∀ z : Plane, |z.1 - 1 / 2| < r → |z.2| < r →
      chart.map.symm z ∈ drawingTrace D → z.2 = 0) : EdgeChart D e where
  chart := chart
  radius := r
  radius_pos := hr
  radius_small := hrsmall
  straight := hstraight
  trace_box := by
    intro z hz1 hz2
    constructor
    · exact htrace z hz1 hz2
    · intro hz
      have hx := abs_lt.mp hz1
      let t : ArcParameter := ⟨z.1, by constructor <;> linarith [hx.1, hx.2]⟩
      have ht : |t.val - 1 / 2| < r := hz1
      have heq : chart.map (D.curve e t) = z := by
        rw [hstraight t ht]
        exact Prod.ext rfl hz.symm
      have heq' : chart.map.symm z = D.curve e t := by
        rw [← heq, Homeomorph.symm_apply_apply]
      rw [heq']
      exact Or.inr (mem_iUnion.mpr ⟨e, ⟨t, rfl⟩⟩)

/-- Rotation clockwise through an angle around the midpoint of the standard edge. -/
noncomputable def midpointRotation (θ : ℝ) : Plane ≃ₜ Plane where
  toFun z := (1 / 2 + Real.cos θ * (z.1 - 1 / 2) + Real.sin θ * z.2,
    -Real.sin θ * (z.1 - 1 / 2) + Real.cos θ * z.2)
  invFun z := (1 / 2 + Real.cos θ * (z.1 - 1 / 2) - Real.sin θ * z.2,
    Real.sin θ * (z.1 - 1 / 2) + Real.cos θ * z.2)
  left_inv z := by
    have h := Real.sin_sq_add_cos_sq θ
    have h₁ := congrArg (fun x : ℝ => x * (z.1 - 1 / 2)) h
    have h₂ := congrArg (fun x : ℝ => x * z.2) h
    apply Prod.ext <;> dsimp <;> nlinarith [h₁, h₂]
  right_inv z := by
    have h := Real.sin_sq_add_cos_sq θ
    have h₁ := congrArg (fun x : ℝ => x * (z.1 - 1 / 2)) h
    have h₂ := congrArg (fun x : ℝ => x * z.2) h
    apply Prod.ext <;> dsimp <;> nlinarith [h₁, h₂]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The clockwise quarter turn is isotopic to the identity. -/
noncomputable def midpointQuarterTurn : OrientedChart where
  map := midpointRotation (Real.pi / 2)
  isotopy t := midpointRotation ((t : ℝ) * (Real.pi / 2))
  continuous := by
    change Continuous (fun p : ArcParameter × Plane =>
      (1 / 2 + Real.cos ((p.1 : ℝ) * (Real.pi / 2)) * (p.2.1 - 1 / 2) +
        Real.sin ((p.1 : ℝ) * (Real.pi / 2)) * p.2.2,
       -Real.sin ((p.1 : ℝ) * (Real.pi / 2)) * (p.2.1 - 1 / 2) +
        Real.cos ((p.1 : ℝ) * (Real.pi / 2)) * p.2.2))
    fun_prop
  inverse_continuous := by
    change Continuous (fun p : ArcParameter × Plane =>
      (1 / 2 + Real.cos ((p.1 : ℝ) * (Real.pi / 2)) * (p.2.1 - 1 / 2) -
        Real.sin ((p.1 : ℝ) * (Real.pi / 2)) * p.2.2,
       Real.sin ((p.1 : ℝ) * (Real.pi / 2)) * (p.2.1 - 1 / 2) +
        Real.cos ((p.1 : ℝ) * (Real.pi / 2)) * p.2.2))
    fun_prop
  start := by
    ext z <;> simp [midpointRotation]
  finish := by simp

/-- The quarter turn sends the vertical crossing to the standard horizontal edge. -/
theorem midpointQuarterTurn_apply (z : Plane) :
    midpointQuarterTurn.map z = (1 / 2 + z.2, 1 / 2 - z.1) := by
  simp [midpointQuarterTurn, midpointRotation, Real.cos_pi_div_two, Real.sin_pi_div_two]

/-- Compose two oriented charts by composing their isotopies pointwise. -/
noncomputable def _root_.FiniteAvalanches.Electrical.Source.OrientedChart.trans (c d : OrientedChart) : OrientedChart where
  map := c.map.trans d.map
  isotopy t := (c.isotopy t).trans (d.isotopy t)
  continuous := d.continuous.comp (continuous_fst.prodMk c.continuous)
  inverse_continuous := c.inverse_continuous.comp
    (continuous_fst.prodMk d.inverse_continuous)
  start := by rw [c.start, d.start]; rfl
  finish := by rw [c.finish, d.finish]

/-- Rotating an oriented chart straightens a vertical crossing. -/
theorem orientedChart_quarterTurn_apply (c : OrientedChart) (z : Plane) :
    (c.trans midpointQuarterTurn).map z =
      (1 / 2 + (c.map z).2, 1 / 2 - (c.map z).1) := by
  exact midpointQuarterTurn_apply (c.map z)

/-- A vertical crossing whose local trace is vertical yields an oriented edge chart. -/
noncomputable def edgeChartOfVerticalTrace {V E : Type} [Fintype V] [Fintype E]
    {J : CopiedGraph V E} (D : Drawing J) (e : E) (c : OrientedChart)
    (r : ℝ) (hr : 0 < r) (hrsmall : r < 1 / 4)
    (hstraight : ∀ t : ArcParameter, |t.val - 1 / 2| < r →
      c.map (D.curve e t) = (1 / 2, t.val - 1 / 2))
    (htrace : ∀ z : Plane, |z.1 - 1 / 2| < r → |z.2| < r →
      c.map.symm z ∈ drawingTrace D → z.1 = 1 / 2) : EdgeChart D e := by
  apply edgeChartOfTraceSubset D e (c.trans midpointQuarterTurn) r hr hrsmall
  · intro t ht
    rw [orientedChart_quarterTurn_apply, hstraight t ht]
    congr 1 <;> dsimp <;> ring
  · intro z hz1 hz2 hztrace
    let w := c.map ((c.trans midpointQuarterTurn).map.symm z)
    have hw : (1 / 2 + w.2, 1 / 2 - w.1) = z := by
      calc
        _ = (c.trans midpointQuarterTurn).map ((c.trans midpointQuarterTurn).map.symm z) :=
          (orientedChart_quarterTurn_apply c _).symm
        _ = z := (c.trans midpointQuarterTurn).map.apply_symm_apply z
    have hw1 : |w.1 - 1 / 2| < r := by
      have h := congrArg Prod.snd hw
      dsimp only at h
      have hh : w.1 - 1 / 2 = -z.2 := by linarith
      simpa only [hh, abs_neg] using hz2
    have hw2 : |w.2| < r := by
      have h := congrArg Prod.fst hw
      dsimp only at h
      have hh : w.2 = z.1 - 1 / 2 := by linarith
      simpa only [hh] using hz1
    have hwtrace : c.map.symm w ∈ drawingTrace D := by
      simpa only [w, Homeomorph.symm_apply_apply] using hztrace
    have h := htrace w hw1 hw2 hwtrace
    have hz := congrArg Prod.snd hw
    dsimp only at hz
    linarith

/-- A locally vertical edge has a quarter-turned chart on a sufficiently small box. -/
theorem exists_edgeChart_of_vertical_straight_with_chart {V E : Type} [Fintype V] [Fintype E]
    {J : CopiedGraph V E} (D : Drawing J) (e : E) (c : OrientedChart)
    (δ : ℝ) (hδ : 0 < δ)
    (hstraight : ∀ t : ArcParameter, |t.val - 1 / 2| < δ →
      c.map (D.curve e t) = (1 / 2, t.val - 1 / 2)) :
    ∃ c' : EdgeChart D e, c'.chart = c.trans midpointQuarterTurn := by
  let d := c.trans midpointQuarterTurn
  let m : ArcParameter := ⟨1 / 2, by norm_num⟩
  have hs : ∀ t : ArcParameter, |t.val - m.val| < δ →
      d.map (D.curve e t) = (t.val, 0) := by
    intro t ht
    rw [show d.map (D.curve e t) =
      (1 / 2 + (c.map (D.curve e t)).2, 1 / 2 - (c.map (D.curve e t)).1) from
        orientedChart_quarterTurn_apply c _]
    rw [hstraight t ht]
    congr 1 <;> dsimp <;> ring
  obtain ⟨r, hr, hbox, hlinear⟩ :=
    exists_trace_box_of_straightened_subarc D e m (by norm_num [m]) (by norm_num [m])
      d.map δ hδ hs
  let a : ℝ := min (r / 2) (1 / 8)
  have ha : 0 < a := lt_min (by linarith) (by norm_num)
  have har : a < r := by dsimp [a]; linarith [min_le_left (r / 2) (1 / 8)]
  have hasmall : a < 1 / 4 := by dsimp [a]; linarith [min_le_right (r / 2) (1 / 8)]
  refine ⟨edgeChartOfTraceSubset D e d a ha hasmall ?_ ?_, rfl⟩
  · intro t ht
    exact hlinear t (lt_trans ht har)
  · intro z hz1 hz2 hztrace
    have hx := abs_lt.mp (lt_trans hz1 har)
    have hy := abs_lt.mp (lt_trans hz2 har)
    apply (hbox z ?_).mp hztrace
    change (1 / 2 - r < z.1 ∧ z.1 < 1 / 2 + r) ∧ -r < z.2 ∧ z.2 < r
    constructor <;> constructor <;> linarith

/-- A locally vertical edge has an oriented chart on a sufficiently small box. -/
theorem exists_edgeChart_of_vertical_straight {V E : Type} [Fintype V] [Fintype E]
    {J : CopiedGraph V E} (D : Drawing J) (e : E) (c : OrientedChart)
    (δ : ℝ) (hδ : 0 < δ)
    (hstraight : ∀ t : ArcParameter, |t.val - 1 / 2| < δ →
      c.map (D.curve e t) = (1 / 2, t.val - 1 / 2)) :
    Nonempty (EdgeChart D e) := by
  obtain ⟨c', _⟩ := exists_edgeChart_of_vertical_straight_with_chart D e c δ hδ hstraight
  exact ⟨c'⟩


/-- Near a vertical crossing, the original edge enters the positive and negative
faces of the rotated dual chart on its initial and final sides respectively. -/
theorem exists_edgeChart_with_original_edge_sides {V W E : Type}
    [Fintype V] [Fintype W] [Fintype E]
    {J : CopiedGraph V E} {J' : CopiedGraph W E}
    (D : Drawing J) (D' : Drawing J') (e : E) (c : EdgeChart D e)
    (δ : ℝ) (hδ : 0 < δ)
    (hstraight : ∀ t : ArcParameter, |t.val - 1 / 2| < δ →
      c.chart.map (D'.curve e t) = (1 / 2, t.val - 1 / 2)) :
    ∃ c' : EdgeChart D' e, ∃ ε : ℝ, 0 < ε ∧
      ∀ t : ArcParameter, |t.val - 1 / 2| < ε →
        (t.val < 1 / 2 → D.curve e t ∈ BSST.faceRegion D' (BSST.positiveChartFace D' e c')) ∧
        (1 / 2 < t.val → D.curve e t ∈ BSST.faceRegion D' (BSST.negativeChartFace D' e c')) := by
  obtain ⟨c', hc'⟩ :=
    exists_edgeChart_of_vertical_straight_with_chart D' e c.chart δ hδ hstraight
  refine ⟨c', min c.radius c'.radius, lt_min c.radius_pos c'.radius_pos, ?_⟩
  intro t ht
  have ht₁ : |t.val - 1 / 2| < c.radius := lt_of_lt_of_le ht (min_le_left _ _)
  have ht₂ : |t.val - 1 / 2| < c'.radius := lt_of_lt_of_le ht (min_le_right _ _)
  have hmap : c'.chart.map (D.curve e t) = (1 / 2, 1 / 2 - t.val) := by
    rw [hc', orientedChart_quarterTurn_apply, c.straight t ht₁]
    simp
  have heq : c'.chart.map.symm (1 / 2, 1 / 2 - t.val) = D.curve e t := by
    rw [← hmap, Homeomorph.symm_apply_apply]
  have hb := abs_lt.mp ht₂
  constructor
  · intro h
    rw [← heq]
    apply (chart_half_boxes_subset_faces D' e c').1
    refine ⟨(1 / 2, 1 / 2 - t.val), ?_, rfl⟩
    change (1 / 2 - c'.radius < 1 / 2 ∧ 1 / 2 < 1 / 2 + c'.radius) ∧
      (0 < 1 / 2 - t.val ∧ 1 / 2 - t.val < c'.radius)
    constructor <;> constructor <;> linarith [c'.radius_pos]
  · intro h
    rw [← heq]
    apply (chart_half_boxes_subset_faces D' e c').2
    refine ⟨(1 / 2, 1 / 2 - t.val), ?_, rfl⟩
    change (1 / 2 - c'.radius < 1 / 2 ∧ 1 / 2 < 1 / 2 + c'.radius) ∧
      (-c'.radius < 1 / 2 - t.val ∧ 1 / 2 - t.val < 0)
    constructor <;> constructor <;> linarith [c'.radius_pos]

/-- A connected edge segment avoiding a drawing stays in the face of any one
of its points. -/
theorem edge_segment_subset_face {V W E E' : Type}
    [Fintype V] [Fintype W] [Fintype E] [Fintype E']
    {J : CopiedGraph V E} {J' : CopiedGraph W E'}
    (D : Drawing J) (D' : Drawing J') (e : E) (F : BSST.Face D')
    {a b : ArcParameter} (hab : a ≤ b)
    (hoff : ∀ t ∈ Set.Icc a b, D.curve e t ∉ drawingTrace D')
    (hface : D.curve e a ∈ BSST.faceRegion D' F) :
    ∀ t ∈ Set.Icc a b, D.curve e t ∈ BSST.faceRegion D' F := by
  obtain ⟨ha, hF⟩ := hface
  have hsub : (D.curve e) '' Set.Icc a b ⊆ (drawingTrace D')ᶜ := by
    rintro z ⟨t, ht, rfl⟩
    exact hoff t ht
  have hconn : IsPreconnected ((D.curve e) '' Set.Icc a b) :=
    isPreconnected_Icc.image _ (D.continuous e).continuousOn
  have hbase : D.curve e a ∈ (D.curve e) '' Set.Icc a b :=
    ⟨a, ⟨le_rfl, hab⟩, rfl⟩
  have hcomponent := hconn.subset_connectedComponentIn hbase hsub
  have hreg := faceRegion_mk D' ⟨D.curve e a, ha⟩
  rw [hF] at hreg
  intro t ht
  rw [hreg]
  exact hcomponent ⟨t, ht, rfl⟩

/-- If an original edge avoids the dual trace away from its crossing, the
local chart faces contain the corresponding original endpoints. -/
theorem exists_edgeChart_with_original_endpoints {V W E : Type}
    [Fintype V] [Fintype W] [Fintype E]
    {J : CopiedGraph V E} {J' : CopiedGraph W E}
    (D : Drawing J) (D' : Drawing J') (e : E) (c : EdgeChart D e)
    (δ : ℝ) (hδ : 0 < δ)
    (hstraight : ∀ t : ArcParameter, |t.val - 1 / 2| < δ →
      c.chart.map (D'.curve e t) = (1 / 2, t.val - 1 / 2))
    (hoff : ∀ t : ArcParameter, t.val ≠ 1 / 2 → D.curve e t ∉ drawingTrace D') :
    ∃ c' : EdgeChart D' e,
      D.point (J.left e) ∈ BSST.faceRegion D' (BSST.positiveChartFace D' e c') ∧
      D.point (J.right e) ∈ BSST.faceRegion D' (BSST.negativeChartFace D' e c') := by
  obtain ⟨c', ε, hε, hlocal⟩ :=
    exists_edgeChart_with_original_edge_sides D D' e c δ hδ hstraight
  let η : ℝ := min ε (1 / 2) / 2
  have hη : 0 < η := by dsimp [η]; positivity
  have hηε : η < ε := by dsimp [η]; linarith [min_le_left ε (1 / 2)]
  have hηhalf : η < 1 / 2 := by dsimp [η]; linarith [min_le_right ε (1 / 2)]
  let a : ArcParameter := ⟨1 / 2 - η, by constructor <;> linarith⟩
  let b : ArcParameter := ⟨1 / 2 + η, by constructor <;> linarith⟩
  have ha : |a.val - 1 / 2| < ε := by
    change |1 / 2 - η - 1 / 2| < ε
    rw [show (1 / 2 : ℝ) - η - 1 / 2 = -η by ring, abs_neg, abs_of_pos hη]
    exact hηε
  have hb : |b.val - 1 / 2| < ε := by
    change |1 / 2 + η - 1 / 2| < ε
    rw [show (1 / 2 : ℝ) + η - 1 / 2 = η by ring, abs_of_pos hη]
    exact hηε
  have haF := (hlocal a ha).1 (by change 1 / 2 - η < 1 / 2; linarith)
  have hbF := (hlocal b hb).2 (by change 1 / 2 < 1 / 2 + η; linarith)
  refine ⟨c', ?_, ?_⟩
  · have hconn : IsPreconnected ((D.curve e) '' Set.Icc (0 : ArcParameter) a) :=
      isPreconnected_Icc.image _ (D.continuous e).continuousOn
    obtain ⟨hatrace, haid⟩ := haF
    have hsub : (D.curve e) '' Set.Icc (0 : ArcParameter) a ⊆ (drawingTrace D')ᶜ := by
      rintro z ⟨t, ht, rfl⟩
      apply hoff t
      have ht' : t.val ≤ 1 / 2 - η := ht.2
      linarith
    have hamem : D.curve e a ∈ (D.curve e) '' Set.Icc (0 : ArcParameter) a := by
      refine ⟨a, ⟨?_, le_rfl⟩, rfl⟩
      change (0 : ℝ) ≤ 1 / 2 - η
      linarith
    have hreg := faceRegion_mk D' ⟨D.curve e a, hatrace⟩
    rw [haid] at hreg
    rw [← D.start e, hreg]
    apply hconn.subset_connectedComponentIn hamem hsub
    exact ⟨0, ⟨le_rfl, by change (0 : ℝ) ≤ 1 / 2 - η; linarith⟩, rfl⟩
  · have hseg := edge_segment_subset_face D D' e _
      (a := b) (b := (1 : ArcParameter)) (by change 1 / 2 + η ≤ (1 : ℝ); linarith)
      (by
        intro t ht
        apply hoff t
        have ht' : 1 / 2 + η ≤ t.val := ht.1
        linarith) hbF
    rw [← D.finish e]
    apply hseg 1
    exact ⟨by change 1 / 2 + η ≤ (1 : ℝ); linarith, le_rfl⟩

/-- Away from the designated crossings, an original edge avoids the dual trace
when dual vertices lie outside the original trace. -/
theorem original_edge_off_dual_trace {V W E : Type}
    [Fintype V] [Fintype W] [Fintype E]
    {J : CopiedGraph V E} {J' : CopiedGraph W E}
    (D : Drawing J) (D' : Drawing J')
    (hpoint : ∀ w, D'.point w ∉ drawingTrace D)
    (hcross : ∀ e f s t, D.curve e s = D'.curve f t → s.val = 1 / 2)
    (e : E) (t : ArcParameter) (ht : t.val ≠ 1 / 2) :
    D.curve e t ∉ drawingTrace D' := by
  rintro (⟨w, hw⟩ | hedge)
  · apply hpoint w
    exact Or.inr (Set.mem_iUnion.mpr ⟨e, ⟨t, hw.symm⟩⟩)
  · obtain ⟨f, s, hs⟩ := Set.mem_iUnion.mp hedge
    exact ht (hcross e f t s hs.symm)

/-- A drawing with the prescribed crossings has dual chart faces containing
the corresponding original endpoints. -/
theorem exists_edgeChart_with_endpoints_of_crossings {V W E : Type}
    [Fintype V] [Fintype W] [Fintype E]
    {J : CopiedGraph V E} {J' : CopiedGraph W E}
    (D : Drawing J) (D' : Drawing J') (e : E) (c : EdgeChart D e)
    (δ : ℝ) (hδ : 0 < δ)
    (hstraight : ∀ t : ArcParameter, |t.val - 1 / 2| < δ →
      c.chart.map (D'.curve e t) = (1 / 2, t.val - 1 / 2))
    (hpoint : ∀ w, D'.point w ∉ drawingTrace D)
    (hcross : ∀ e f s t, D.curve e s = D'.curve f t → s.val = 1 / 2) :
    ∃ c' : EdgeChart D' e,
      D.point (J.left e) ∈ BSST.faceRegion D' (BSST.positiveChartFace D' e c') ∧
      D.point (J.right e) ∈ BSST.faceRegion D' (BSST.negativeChartFace D' e c') := by
  exact exists_edgeChart_with_original_endpoints D D' e c δ hδ hstraight
    (original_edge_off_dual_trace D D' hpoint hcross e)

/-- Every vertex of a connected copied graph with an edge is incident to a copy. -/
theorem exists_incident_copy {V E : Type} [Fintype V] [Fintype E] [Nonempty E]
    (J : CopiedGraph V E) (hconn : (supportGraph J.left J.right).Preconnected)
    (v : V) : ∃ e, J.left e = v ∨ J.right e = v := by
  obtain ⟨e₀⟩ := ‹Nonempty E›
  by_cases h : J.left e₀ = v
  · exact ⟨e₀, Or.inl h⟩
  · have : Nontrivial V := nontrivial_of_ne (J.left e₀) v h
    obtain ⟨w, hw⟩ := hconn.exists_adj_of_nontrivial v
    obtain ⟨_, e, he⟩ := hw
    exact ⟨e, he.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)⟩

/-- A connected original drawing with the designated crossings has a
well-defined dual face at each original vertex, and the dual chart faces
agree with those vertex faces. -/
theorem exists_vertex_faces_with_oriented_charts {V W E : Type}
    [Fintype V] [Fintype W] [Fintype E] [Nonempty E]
    {J : CopiedGraph V E} {J' : CopiedGraph W E}
    (D : Drawing J) (D' : Drawing J') (c : ∀ e, EdgeChart D e)
    (hconn : (supportGraph J.left J.right).Preconnected)
    (δ : E → ℝ) (hδ : ∀ e, 0 < δ e)
    (hstraight : ∀ (e : E) (t : ArcParameter), |t.val - 1 / 2| < δ e →
      (c e).chart.map (D'.curve e t) = (1 / 2, t.val - 1 / 2))
    (hpoint : ∀ w, D'.point w ∉ drawingTrace D)
    (hcross : ∀ e f s t, D.curve e s = D'.curve f t → s.val = 1 / 2) :
    ∃ (vertexFace : V → BSST.Face D') (dualCharts : ∀ e, EdgeChart D' e),
      (∀ v, D.point v ∈ BSST.faceRegion D' (vertexFace v)) ∧
      (∀ e, BSST.positiveChartFace D' e (dualCharts e) = vertexFace (J.left e) ∧
        BSST.negativeChartFace D' e (dualCharts e) = vertexFace (J.right e)) := by
  have hoff : ∀ v, D.point v ∉ drawingTrace D' := by
    intro v
    obtain ⟨e, h | h⟩ := exists_incident_copy J hconn v
    · rw [← h, ← D.start e]
      exact original_edge_off_dual_trace D D' hpoint hcross e 0 (by norm_num)
    · rw [← h, ← D.finish e]
      exact original_edge_off_dual_trace D D' hpoint hcross e 1 (by norm_num)
  let vertexFace : V → BSST.Face D' := fun v => ConnectedComponents.mk ⟨D.point v, hoff v⟩
  have hex : ∀ e, ∃ c' : EdgeChart D' e,
      D.point (J.left e) ∈ BSST.faceRegion D' (BSST.positiveChartFace D' e c') ∧
      D.point (J.right e) ∈ BSST.faceRegion D' (BSST.negativeChartFace D' e c') :=
    fun e => exists_edgeChart_with_endpoints_of_crossings D D' e (c e) (δ e) (hδ e)
      (hstraight e) hpoint hcross
  choose dualCharts hl hr using hex
  refine ⟨vertexFace, dualCharts, ?_, ?_⟩
  · intro v
    exact ⟨hoff v, rfl⟩
  · intro e
    exact ⟨(hl e).2.symm, (hr e).2.symm⟩

end FiniteAvalanches.Electrical.StatementGeometry
