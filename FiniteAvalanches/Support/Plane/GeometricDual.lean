import FiniteAvalanches.Support.Plane.IntervalNormalization
import FiniteAvalanches.Support.Plane.PuncturedTransport
import FiniteAvalanches.Support.Plane.LocalFaceIncidence
import LatticeProb.Topology.DiskArcPair
import FiniteAvalanches.Support.Plane.TopoSep
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Geometric facts for plane dual drawings

Ported from Lattice-Probability `LatticeProb/Topology/PlaneGraph/GeometricDual.lean`
at commit `ba2b67f3`.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb
open Source BSST Set

private theorem nowhereDense_union {s t : Set Plane} (hs : IsNowhereDense s)
    (ht : IsNowhereDense t) : IsNowhereDense (s ∪ t) := by
  unfold IsNowhereDense at *
  rw [closure_union, interior_union_isClosed_of_interior_empty isClosed_closure ht, hs]

private theorem nowhereDense_iUnion {ι : Type} [Fintype ι] (s : ι → Set Plane)
    (hs : ∀ i, IsNowhereDense (s i)) : IsNowhereDense (⋃ i, s i) := by
  classical
  have h : ∀ a : Finset ι, IsNowhereDense (⋃ i ∈ a, s i) := by
    intro a
    induction a using Finset.induction_on with
    | empty => simp
    | @insert i a hi ih =>
      simpa only [Finset.mem_insert, iUnion_or, iUnion_union_distrib, iUnion_iUnion_eq_left] using
        nowhereDense_union (hs i) ih
  simpa using h Finset.univ

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- Each face region is path connected. -/
theorem faceRegion_isPathConnected (D : Drawing J) (F : Face D) :
    IsPathConnected (faceRegion D F) :=
  (punctured_faceRegion_isOpen D F).isConnected_iff_isPathConnected.mp
    (faceRegion_isConnected D F)

/-- The two open halves of an edge chart lie in their respective chart faces. -/
theorem chart_half_boxes_subset_faces (D : Drawing J) (e : E) (c : EdgeChart D e) :
    c.chart.map.symm '' PlaneTopology.upperHalfBox (1 / 2) c.radius ⊆
        faceRegion D (positiveChartFace D e c) ∧
    c.chart.map.symm '' PlaneTopology.lowerHalfBox (1 / 2) c.radius ⊆
        faceRegion D (negativeChartFace D e c) := by
  have htrace : ∀ z ∈ PlaneTopology.axisBox (1 / 2) c.radius,
      c.chart.map.symm z ∈ drawingTrace D ↔ z.2 = 0 := by
    intro z hz
    apply c.trace_box
    · rw [abs_lt]
      constructor <;> linarith [hz.1.1, hz.1.2]
    · rw [abs_lt]
      exact hz.2
  constructor
  · change c.chart.map.symm '' PlaneTopology.upperHalfBox (1 / 2) c.radius ⊆
      faceRegion D (ConnectedComponents.mk ⟨_, positive_chart_point_off_trace D e c⟩)
    rw [faceRegion_mk]
    exact PlaneTopology.upper_half_box_subset_component _ _ _ _ c.radius_pos htrace
  · change c.chart.map.symm '' PlaneTopology.lowerHalfBox (1 / 2) c.radius ⊆
      faceRegion D (ConnectedComponents.mk ⟨_, negative_chart_point_off_trace D e c⟩)
    rw [faceRegion_mk]
    exact PlaneTopology.lower_half_box_subset_component _ _ _ _ c.radius_pos htrace

/-- A vertical segment in an edge chart crosses the trace only at the edge midpoint. -/
theorem chart_vertical_crossing (D : Drawing J) (e : E) (c : EdgeChart D e) :
    Function.Injective (fun y : ℝ => c.chart.map.symm (1 / 2, y)) ∧
    c.chart.map.symm (1 / 2, 0) =
      D.curve e ⟨1 / 2, by constructor <;> norm_num⟩ ∧
    ∀ y : ℝ, |y| < c.radius →
      (c.chart.map.symm (1 / 2, y) ∈ drawingTrace D ↔ y = 0) ∧
      (y < 0 → c.chart.map.symm (1 / 2, y) ∈
        faceRegion D (negativeChartFace D e c)) ∧
      (0 < y → c.chart.map.symm (1 / 2, y) ∈
        faceRegion D (positiveChartFace D e c)) := by
  have hmid : |(1 / 2 : ℝ) - 1 / 2| < c.radius := by simpa using c.radius_pos
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    exact congrArg Prod.snd (c.chart.map.symm.injective h)
  · rw [← c.straight ⟨1 / 2, by constructor <;> norm_num⟩ hmid,
      Homeomorph.symm_apply_apply]
  · intro y hy
    refine ⟨c.trace_box (1 / 2, y) hmid hy, ?_, ?_⟩
    · intro hneg
      apply (chart_half_boxes_subset_faces D e c).2
      refine ⟨(1 / 2, y), ?_, rfl⟩
      change (1 / 2 : ℝ) ∈ Set.Ioo (1 / 2 - c.radius) (1 / 2 + c.radius) ∧
        y ∈ Set.Ioo (-c.radius) 0
      have hy' := abs_lt.mp hy
      constructor <;> constructor <;> linarith [c.radius_pos]
    · intro hpos
      apply (chart_half_boxes_subset_faces D e c).1
      refine ⟨(1 / 2, y), ?_, rfl⟩
      change (1 / 2 : ℝ) ∈ Set.Ioo (1 / 2 - c.radius) (1 / 2 + c.radius) ∧
        y ∈ Set.Ioo 0 c.radius
      have hy' := abs_lt.mp hy
      constructor <;> constructor <;> linarith [c.radius_pos]

/-- Small opposite imaginary offsets from an edge midpoint lie in the two
corresponding chart faces. -/
theorem chart_complex_offsets_mem_faces (D : Drawing J) (e : E) (c : EdgeChart D e)
    {a : ℝ} (ha : 0 < a) (har : a < c.radius) :
    Complex.equivRealProdCLM (c.chart.symm.complexMap
        ((1 / 2 : ℂ) + (a : ℂ) / Complex.I)) ∈
        faceRegion D (negativeChartFace D e c) ∧
    Complex.equivRealProdCLM (c.chart.symm.complexMap
        ((1 / 2 : ℂ) + -(a : ℂ) / Complex.I)) ∈
        faceRegion D (positiveChartFace D e c) := by
  have hn := (chart_vertical_crossing D e c).2.2 (-a) (by simpa [abs_neg, abs_of_pos ha] using har)
  have hp := (chart_vertical_crossing D e c).2.2 a (by simpa [abs_of_pos ha] using har)
  have hneg : Complex.equivRealProdCLM
      ((1 / 2 : ℂ) + (a : ℂ) / Complex.I) = (1 / 2, -a) := by
    ext <;> simp [Complex.div_I]
  have hpos : Complex.equivRealProdCLM
      ((1 / 2 : ℂ) + -(a : ℂ) / Complex.I) = (1 / 2, a) := by
    ext <;> simp [Complex.div_I]
  constructor
  · change c.chart.map.symm (Complex.equivRealProdCLM
        ((1 / 2 : ℂ) + (a : ℂ) / Complex.I)) ∈ _
    rw [hneg]
    exact hn.2.1 (neg_lt_zero.mpr ha)
  · change c.chart.map.symm (Complex.equivRealProdCLM
        ((1 / 2 : ℂ) + -(a : ℂ) / Complex.I)) ∈ _
    rw [hpos]
    exact hp.2.2 ha

/-- The chart crossing meets exactly the corresponding edge at its midpoint. -/
theorem curve_eq_chart_vertical_crossing (D : Drawing J) (e f : E)
    (c : EdgeChart D e) (s : ArcParameter) (y : ℝ) (hy : |y| < c.radius) :
    D.curve f s = c.chart.map.symm (1 / 2, y) ↔
      f = e ∧ s.val = 1 / 2 ∧ y = 0 := by
  let m : ArcParameter := ⟨1 / 2, by constructor <;> norm_num⟩
  have hm0 : 0 < m.val := by norm_num [m]
  have hm1 : m.val < 1 := by norm_num [m]
  have hmid := (chart_vertical_crossing D e c).2.1
  constructor
  · intro h
    have htrace : c.chart.map.symm (1 / 2, y) ∈ drawingTrace D := by
      rw [← h]
      exact Or.inr (Set.mem_iUnion.mpr ⟨f, s, rfl⟩)
    have hy0 := ((chart_vertical_crossing D e c).2.2 y hy).1.mp htrace
    have heq : D.curve f s = D.curve e m := by
      rw [hy0] at h
      exact h.trans hmid
    have hfe : f = e := by
      by_contra hne
      have hends := (D.intersects f e hne s m heq).2
      rcases hends with h0 | h1 <;> dsimp [m] at * <;> norm_num at *
    subst f
    have hs1 : s.val < 1 := by
      by_contra hn
      have hs : s.val = 1 := le_antisymm s.property.2 (le_of_not_gt hn)
      have hs' : s = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext hs
      rw [hs', D.finish] at heq
      exact D.avoids e m hm0 hm1 (J.right e) heq.symm
    have hsm : s = m := D.injective e hs1 hm1 heq
    exact ⟨rfl, congrArg Subtype.val hsm, hy0⟩
  · rintro ⟨rfl, hs, rfl⟩
    have hsm : s = m := Subtype.ext hs
    simpa only [hsm] using hmid.symm

/-- The trace inside a smaller closed chart box is exactly the corresponding edge segment. -/
theorem trace_in_closed_chart_box (D : Drawing J) (e : E) (c : EdgeChart D e)
    {r : ℝ} (hr : r < c.radius) {z : Plane}
    (hz : z ∈ Set.Icc (1 / 2 - r) (1 / 2 + r) ×ˢ Set.Icc (-r) r) :
    c.chart.map.symm z ∈ drawingTrace D ↔
      ∃ t : ArcParameter, |t.val - 1 / 2| ≤ r ∧ c.chart.map.symm z = D.curve e t := by
  have hx : |z.1 - 1 / 2| ≤ r := by
    rw [abs_le]; constructor <;> linarith [hz.1.1, hz.1.2]
  have hy : |z.2| ≤ r := by
    rw [abs_le]; exact hz.2
  have hxt : |z.1 - 1 / 2| < c.radius := lt_of_le_of_lt hx hr
  have hyt : |z.2| < c.radius := lt_of_le_of_lt hy hr
  constructor
  · intro htrace
    have hz0 : z.2 = 0 := (c.trace_box z hxt hyt).mp htrace
    have hz1 : z.1 ∈ Set.Icc (0 : ℝ) 1 := by
      have h := abs_lt.mp hxt
      constructor <;> linarith [c.radius_small]
    let t : ArcParameter := ⟨z.1, hz1⟩
    refine ⟨t, hx, ?_⟩
    apply c.chart.map.injective
    rw [c.chart.map.apply_symm_apply, c.straight t hxt]
    exact Prod.ext rfl hz0
  · rintro ⟨t, ht, heq⟩
    rw [heq]
    exact Or.inr (Set.mem_iUnion.mpr ⟨e, t, rfl⟩)

/-- A smaller closed chart box avoids every other edge of the drawing. -/
theorem closed_chart_box_disjoint_curve (D : Drawing J) (e f : E)
    (c : EdgeChart D e) (hef : e ≠ f) {r : ℝ} (hr : r < c.radius) :
    Disjoint
      (c.chart.map.symm ''
        (Set.Icc (1 / 2 - r) (1 / 2 + r) ×ˢ Set.Icc (-r) r))
      (Set.range (D.curve f)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨z, hz, rfl⟩ ⟨s, hs⟩
  have htrace : c.chart.map.symm z ∈ drawingTrace D :=
    Or.inr (Set.mem_iUnion.mpr ⟨f, s, hs⟩)
  obtain ⟨t, ht, hzt⟩ := (trace_in_closed_chart_box D e c hr hz).mp htrace
  have hcross := (D.intersects e f hef t s (hzt.symm.trans hs.symm)).1
  have ht' := abs_le.mp ht
  rcases hcross with h0 | h1 <;> linarith [c.radius_small]

/-- Edge charts can be restricted to pairwise disjoint boxes about their midpoints. -/
theorem exists_disjoint_chart_boxes (D : Drawing J) (charts : ∀ e, EdgeChart D e) :
    ∃ r : E → ℝ, (∀ e, 0 < r e ∧ r e < (charts e).radius) ∧
      ∀ e f, e ≠ f → Disjoint
        ((charts e).chart.map.symm '' PlaneTopology.axisBox (1 / 2) (r e))
        ((charts f).chart.map.symm '' PlaneTopology.axisBox (1 / 2) (r f)) := by
  let m : ArcParameter := ⟨1 / 2, by constructor <;> norm_num⟩
  let mid : E → Plane := fun e => D.curve e m
  have hmid : Function.Injective mid := by
    intro e f heq
    by_contra hne
    have h := (D.intersects e f hne m m heq).1
    norm_num [m] at h
  obtain ⟨U, hU, hdisj⟩ := (Set.finite_range mid).t2_separation
  have hsmall : ∀ e, ∃ r : ℝ, 0 < r ∧ r < (charts e).radius ∧
      (charts e).chart.map.symm '' PlaneTopology.axisBox (1 / 2) r ⊆ U (mid e) := by
    intro e
    let g : Plane ≃ₜ Plane := (charts e).chart.map.symm
    have hg0 : g (1 / 2, 0) = mid e := (chart_vertical_crossing D e (charts e)).2.1
    have hopen : IsOpen (g ⁻¹' U (mid e)) := (hU _).2.preimage g.continuous
    have hzero : (1 / 2, 0) ∈ g ⁻¹' U (mid e) := by
      simpa only [Set.mem_preimage, hg0] using (hU (mid e)).1
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopen (1 / 2, 0) hzero
    let r := min (ε / 2) ((charts e).radius / 2)
    have hr : 0 < r := lt_min (by linarith) (by linarith [(charts e).radius_pos])
    refine ⟨r, hr, ?_, ?_⟩
    · dsimp [r]; linarith [min_le_right (ε / 2) ((charts e).radius / 2), (charts e).radius_pos]
    · rintro z ⟨p, hp, rfl⟩
      apply hεsub
      have hrε : r < ε := by
        dsimp [r]; linarith [min_le_left (ε / 2) ((charts e).radius / 2)]
      have hx : |p.1 - 1 / 2| < r := by
        rw [abs_lt]; constructor <;> linarith [hp.1.1, hp.1.2]
      have hy : |p.2| < r := by
        rw [abs_lt]; exact hp.2
      have hpball : dist p (1 / 2, 0) < r := by
        simpa only [Prod.dist_eq, Real.dist_eq, sub_zero] using max_lt hx hy
      exact lt_trans hpball hrε
  choose r hrpos hrlt hrsub using hsmall
  refine ⟨r, fun e => ⟨hrpos e, hrlt e⟩, ?_⟩
  intro e f hef
  exact (hdisj (Set.mem_range_self e) (Set.mem_range_self f) (fun h => hef (hmid h))).mono
    (hrsub e) (hrsub f)

/-- The local vertical crossings can be chosen pairwise disjoint. -/
theorem exists_disjoint_chart_crossings (D : Drawing J) (charts : ∀ e, EdgeChart D e) :
    ∃ r : E → ℝ, (∀ e, 0 < r e ∧ r e < (charts e).radius) ∧
      ∀ e f, e ≠ f → Disjoint
        ((fun y : ℝ => (charts e).chart.map.symm (1 / 2, y)) '' Set.Ioo (-r e) (r e))
        ((fun y : ℝ => (charts f).chart.map.symm (1 / 2, y)) '' Set.Ioo (-r f) (r f)) := by
  obtain ⟨r, hr, hdisj⟩ := exists_disjoint_chart_boxes D charts
  refine ⟨r, hr, ?_⟩
  intro e f hef
  apply (hdisj e f hef).mono <;> rintro z ⟨y, hy, rfl⟩
  · exact ⟨(1 / 2, y), ⟨⟨by linarith [(hr e).1], by linarith [(hr e).1]⟩, hy⟩, rfl⟩
  · exact ⟨(1 / 2, y), ⟨⟨by linarith [(hr f).1], by linarith [(hr f).1]⟩, hy⟩, rfl⟩

/-- Closed midpoint boxes can be chosen disjoint from one another and from all vertices. -/
theorem exists_disjoint_closed_chart_boxes (D : Drawing J) (charts : ∀ e, EdgeChart D e) :
    ∃ r : E → ℝ, (∀ e, 0 < r e ∧ r e < (charts e).radius) ∧
      (∀ e f, e ≠ f → Disjoint
        ((charts e).chart.map.symm ''
          (Set.Icc (1 / 2 - r e) (1 / 2 + r e) ×ˢ Set.Icc (-r e) (r e)))
        ((charts f).chart.map.symm ''
          (Set.Icc (1 / 2 - r f) (1 / 2 + r f) ×ˢ Set.Icc (-r f) (r f)))) ∧
      ∀ e, Disjoint
        ((charts e).chart.map.symm ''
          (Set.Icc (1 / 2 - r e) (1 / 2 + r e) ×ˢ Set.Icc (-r e) (r e)))
        (Set.range D.point) := by
  let m : ArcParameter := ⟨1 / 2, by constructor <;> norm_num⟩
  let mid : E → Plane := fun e => D.curve e m
  have hmid : Function.Injective mid := by
    intro e f heq
    by_contra hne
    have h := (D.intersects e f hne m m heq).1
    norm_num [m] at h
  have hvertex : ∀ e v, mid e ≠ D.point v := by
    intro e v
    exact D.avoids e m (by norm_num [m]) (by norm_num [m]) v
  let S : Set Plane := Set.range mid ∪ Set.range D.point
  have hS : S.Finite := (Set.finite_range mid).union (Set.finite_range D.point)
  obtain ⟨U, hU, hdisj⟩ := hS.t2_separation
  have hsmall : ∀ e, ∃ r : ℝ, 0 < r ∧ r < (charts e).radius ∧
      (charts e).chart.map.symm ''
        (Set.Icc (1 / 2 - r) (1 / 2 + r) ×ˢ Set.Icc (-r) r) ⊆ U (mid e) := by
    intro e
    let g : Plane ≃ₜ Plane := (charts e).chart.map.symm
    have hg0 : g (1 / 2, 0) = mid e := (chart_vertical_crossing D e (charts e)).2.1
    have hopen : IsOpen (g ⁻¹' U (mid e)) := (hU _).2.preimage g.continuous
    have hzero : (1 / 2, 0) ∈ g ⁻¹' U (mid e) := by
      simpa only [Set.mem_preimage, hg0] using (hU (mid e)).1
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopen (1 / 2, 0) hzero
    let r := min (ε / 2) ((charts e).radius / 2)
    have hr : 0 < r := lt_min (by linarith) (by linarith [(charts e).radius_pos])
    refine ⟨r, hr, ?_, ?_⟩
    · dsimp [r]; linarith [min_le_right (ε / 2) ((charts e).radius / 2), (charts e).radius_pos]
    · rintro z ⟨p, hp, rfl⟩
      apply hεsub
      have hrε : r < ε := by
        dsimp [r]; linarith [min_le_left (ε / 2) ((charts e).radius / 2)]
      have hx : |p.1 - 1 / 2| ≤ r := by
        rw [abs_le]; constructor <;> linarith [hp.1.1, hp.1.2]
      have hy : |p.2| ≤ r := by
        rw [abs_le]; exact hp.2
      have hpball : dist p (1 / 2, 0) ≤ r := by
        simpa only [Prod.dist_eq, Real.dist_eq, sub_zero] using max_le hx hy
      exact lt_of_le_of_lt hpball hrε
  choose r hrpos hrlt hrsub using hsmall
  refine ⟨r, fun e => ⟨hrpos e, hrlt e⟩, ?_, ?_⟩
  · intro e f hef
    exact (hdisj (Or.inl (Set.mem_range_self e)) (Or.inl (Set.mem_range_self f))
      (fun h => hef (hmid h))).mono (hrsub e) (hrsub f)
  · intro e
    apply Set.disjoint_left.mpr
    intro z hz hzv
    obtain ⟨v, hv⟩ := hzv
    subst z
    exact (Set.disjoint_left.mp
      (hdisj (Or.inl (Set.mem_range_self e)) (Or.inr (Set.mem_range_self v))
        (hvertex e v))) (hrsub e hz) (hU (D.point v)).1

private theorem exists_unit_speed_compression (r : ℝ) (hr : 0 < r) (hrsmall : r < 1 / 4) :
    ∃ f : ℝ → ℝ, Continuous f ∧ StrictMono f ∧
      (∀ x, |x| ≤ 1 / 2 → |f x| < r) ∧
      (∀ x, |x| < r / 2 → f x = x) ∧ f 0 = 0 := by
  let c : ℝ → ℝ := fun x => max (-r / 2) (min (r / 2) x)
  let f : ℝ → ℝ := fun x => (1 - r) * c x + r * x
  have hc : Monotone c := by
    intro x y hxy
    exact max_le_max_left _ (min_le_min_left _ hxy)
  have hcl : ∀ x, -r / 2 ≤ c x := fun x => le_max_left _ _
  have hcu : ∀ x, c x ≤ r / 2 := by
    intro x
    apply max_le
    · linarith
    · exact min_le_left _ _
  have hid : ∀ x, |x| < r / 2 → c x = x := by
    intro x hx
    have hx' := abs_lt.mp hx
    dsimp [c]
    have hlo : -r / 2 ≤ x := by linarith
    rw [min_eq_right (le_of_lt hx'.2), max_eq_right hlo]
  refine ⟨f, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [f, c]; fun_prop
  · intro x y hxy
    dsimp [f]
    have hcx := hc (le_of_lt hxy)
    nlinarith
  · intro x hx
    have hx' := abs_le.mp hx
    have hc₁ := hcl x
    have hc₂ := hcu x
    dsimp [f]
    rw [abs_lt]
    constructor <;> nlinarith
  · intro x hx
    dsimp [f]
    rw [hid x hx]
    ring
  · dsimp [f]
    rw [hid 0 (by simpa using (half_pos hr))]
    ring

/-- Pairwise disjoint parametrized crossings with unit speed near their midpoints. -/
theorem exists_disjoint_parametrized_crossings (D : Drawing J)
    (charts : ∀ e, EdgeChart D e) :
    ∃ r : E → ℝ, ∃ q : E → ArcParameter → Plane,
      (∀ e, 0 < r e ∧ r e < (charts e).radius) ∧
      (∀ e, Continuous (q e) ∧ Function.Injective (q e)) ∧
      (∀ e t, ((charts e).chart.map (q e t)).1 = 1 / 2) ∧
      (∀ e f, e ≠ f → Disjoint (Set.range (q e)) (Set.range (q f))) ∧
      (∀ e, Disjoint (Set.range (q e)) (Set.range D.point)) ∧
      (∀ e f s t, D.curve f s = q e t ↔
        f = e ∧ s.val = 1 / 2 ∧ t.val = 1 / 2) ∧
      (∀ e t, (t.val < 1 / 2 → q e t ∈ faceRegion D (negativeChartFace D e (charts e))) ∧
        (1 / 2 < t.val → q e t ∈ faceRegion D (positiveChartFace D e (charts e)))) ∧
      (∀ e t, |t.val - 1 / 2| < r e / 2 →
        (charts e).chart.map (q e t) = (1 / 2, t.val - 1 / 2)) := by
  obtain ⟨r, hr, hdisj, hvertex⟩ := exists_disjoint_closed_chart_boxes D charts
  have hex : ∀ e, ∃ f : ℝ → ℝ, Continuous f ∧ StrictMono f ∧
      (∀ x, |x| ≤ 1 / 2 → |f x| < r e) ∧
      (∀ x, |x| < r e / 2 → f x = x) ∧ f 0 = 0 := by
    intro e
    exact exists_unit_speed_compression (r e) (hr e).1
      (lt_trans (hr e).2 (charts e).radius_small)
  choose f hfc hfm hfb hfid hf0 using hex
  let q : E → ArcParameter → Plane := fun e t =>
    (charts e).chart.map.symm (1 / 2, f e (t.val - 1 / 2))
  have hinterval : ∀ t : ArcParameter, |t.val - 1 / 2| ≤ 1 / 2 := by
    intro t
    rw [abs_le]
    constructor <;> linarith [t.property.1, t.property.2]
  have hbound : ∀ e (t : ArcParameter),
      |f e (t.val - 1 / 2)| < (charts e).radius := by
    intro e t
    exact lt_trans (hfb e _ (hinterval t)) (hr e).2
  have hbox : ∀ e, Set.range (q e) ⊆
      (charts e).chart.map.symm ''
        (Set.Icc (1 / 2 - r e) (1 / 2 + r e) ×ˢ Set.Icc (-r e) (r e)) := by
    intro e z hz
    obtain ⟨t, rfl⟩ := hz
    refine ⟨(1 / 2, f e (t.val - 1 / 2)), ?_, rfl⟩
    constructor
    · constructor <;> linarith [(hr e).1]
    · have h := abs_lt.mp (hfb e _ (hinterval t))
      constructor <;> linarith
  refine ⟨r, q, hr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e
    constructor
    · exact (charts e).chart.map.symm.continuous.comp
        (continuous_const.prodMk ((hfc e).comp (by fun_prop)))
    · intro s t h
      have he := congrArg Prod.snd ((charts e).chart.map.symm.injective h)
      have he' := (hfm e).injective he
      apply Subtype.ext
      linarith
  · intro e t
    simp only [q, Homeomorph.apply_symm_apply]
  · intro e f hef
    exact (hdisj e f hef).mono (hbox e) (hbox f)
  · intro e
    exact (hvertex e).mono_left (hbox e)
  · intro e g s t
    rw [curve_eq_chart_vertical_crossing D e g (charts e) s _ (hbound e t)]
    have hy : f e (t.val - 1 / 2) = 0 ↔ t.val = 1 / 2 := by
      constructor
      · intro h
        have hh := (hfm e).injective (h.trans (hf0 e).symm)
        linarith
      · intro h
        rw [h, sub_self, hf0]
    rw [hy]
  · intro e t
    have h := (chart_vertical_crossing D e (charts e)).2.2 _ (hbound e t)
    constructor
    · intro ht
      apply h.2.1
      rw [← hf0 e]
      exact (hfm e) (by linarith)
    · intro ht
      apply h.2.2
      rw [← hf0 e]
      exact (hfm e) (by linarith)
  · intro e t ht
    dsimp only [q]
    rw [Homeomorph.apply_symm_apply, hfid e _ ht]

/-- Face regions determine their connected-component labels. -/
theorem faceRegion_injective (D : Drawing J) : Function.Injective (faceRegion D) := by
  intro F G h
  obtain ⟨a, rfl⟩ := ConnectedComponents.surjective_coe F
  have ha : a.val ∈ faceRegion D (ConnectedComponents.mk a) := ⟨a.property, rfl⟩
  rw [h] at ha
  obtain ⟨ha', haG⟩ := ha
  have heq : (⟨a.val, ha'⟩ : {z // z ∉ drawingTrace D}) = a := Subtype.ext rfl
  simpa only [heq] using haG

/-- Away from the drawing, a point in a face closure belongs to that face. -/
theorem mem_faceRegion_of_mem_closure (D : Drawing J) (F : Face D) {z : Plane}
    (hz : z ∉ drawingTrace D) (hcl : z ∈ closure (faceRegion D F)) :
    z ∈ faceRegion D F := by
  let G : Face D := ConnectedComponents.mk ⟨z, hz⟩
  have hzG : z ∈ faceRegion D G := ⟨hz, rfl⟩
  obtain ⟨w, hwG, hwF⟩ := mem_closure_iff.mp hcl _ (punctured_faceRegion_isOpen D G) hzG
  obtain ⟨hw₁, heG⟩ := hwG
  obtain ⟨hw₂, heF⟩ := hwF
  have he : (⟨w, hw₁⟩ : {x // x ∉ drawingTrace D}) = ⟨w, hw₂⟩ := Subtype.ext rfl
  have hGF : G = F := heG.symm.trans ((congrArg ConnectedComponents.mk he).trans heF)
  rwa [hGF] at hzG

/-- The frontier of every face is contained in the drawing trace. -/
theorem frontier_faceRegion_subset_trace (D : Drawing J) (F : Face D) :
    frontier (faceRegion D F) ⊆ drawingTrace D := by
  intro z hz
  by_contra htrace
  rw [frontier, (punctured_faceRegion_isOpen D F).interior_eq] at hz
  exact hz.2 (mem_faceRegion_of_mem_closure D F htrace hz.1)

/-- When the drawing is nonempty, every face has a boundary point on its trace. -/
theorem exists_mem_frontier_faceRegion (D : Drawing J) (F : Face D)
    (htrace : (drawingTrace D).Nonempty) :
    ∃ z, z ∈ frontier (faceRegion D F) ∧ z ∈ drawingTrace D := by
  have hnonempty : (faceRegion D F).Nonempty := (faceRegion_isConnected D F).nonempty
  have hproper : faceRegion D F ≠ Set.univ := by
    obtain ⟨z, hz⟩ := htrace
    intro h
    have hzF : z ∈ faceRegion D F := by rw [h]; exact Set.mem_univ z
    exact hzF.1 hz
  obtain ⟨z, hz⟩ := nonempty_frontier_iff.mpr ⟨hnonempty, hproper⟩
  exact ⟨z, hz, frontier_faceRegion_subset_trace D F hz⟩

/-- Every face meets an edge interior in its frontier when an edge exists. -/
theorem exists_edge_interior_mem_frontier (D : Drawing J) [Nonempty E] (F : Face D) :
    ∃ (e : E) (t : ArcParameter), 0 < t.val ∧ t.val < 1 ∧
      D.curve e t ∈ frontier (faceRegion D F) := by
  classical
  have hfront : ¬ frontier (faceRegion D F) ⊆ Set.range D.point := by
    intro hsub
    let S : Set Plane := (Set.range D.point)ᶜ
    have hconn : IsPreconnected S :=
      (PlaneTopology.isPathConnected_compl_range D.point).isConnected.isPreconnected
    obtain ⟨a, ha⟩ := (faceRegion_isConnected D F).nonempty
    have haS : a ∈ S := by
      intro h
      exact ha.1 (Or.inl h)
    have hclosure : closure (faceRegion D F) ∩ S ⊆ faceRegion D F := by
      rintro z ⟨hz, hzS⟩
      by_contra hzF
      apply hzS
      apply hsub
      rw [frontier, (punctured_faceRegion_isOpen D F).interior_eq]
      exact ⟨hz, hzF⟩
    have hSF : S ⊆ faceRegion D F :=
      hconn.subset_of_closure_inter_subset (punctured_faceRegion_isOpen D F) ⟨a, haS, ha⟩ hclosure
    let e : E := Classical.choice inferInstance
    let t : ArcParameter := ⟨1 / 2, by constructor <;> norm_num⟩
    have htS : D.curve e t ∈ S := by
      rintro ⟨v, hv⟩
      exact D.avoids e t (by norm_num [t]) (by norm_num [t]) v hv.symm
    exact (hSF htS).1 (Or.inr (Set.mem_iUnion.mpr ⟨e, ⟨t, rfl⟩⟩))
  obtain ⟨z, hz, hzv⟩ := Set.not_subset.mp hfront
  have htrace := frontier_faceRegion_subset_trace D F hz
  rcases htrace with hv | he
  · exact (hzv hv).elim
  · obtain ⟨e, t, ht⟩ := Set.mem_iUnion.mp he
    have ht0 : 0 < t.val := by
      by_contra h
      have h0 : t.val = 0 := le_antisymm (le_of_not_gt h) t.property.1
      have ht' : t = ⟨0, by constructor <;> norm_num⟩ := Subtype.ext h0
      apply hzv
      refine ⟨J.left e, ?_⟩
      rw [← ht, ht', D.start]
    have ht1 : t.val < 1 := by
      by_contra h
      have h1 : t.val = 1 := le_antisymm t.property.2 (le_of_not_gt h)
      have ht' : t = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext h1
      apply hzv
      refine ⟨J.right e, ?_⟩
      rw [← ht, ht', D.finish]
    exact ⟨e, t, ht0, ht1, ht ▸ hz⟩

/-- Propagation of interior incidence to chart faces implies finiteness of faces. -/
theorem finite_faces_of_interior_incidence (D : Drawing J) [Nonempty E]
    (charts : ∀ e, EdgeChart D e)
    (hinc : ∀ (F : Face D) (e : E) (t : ArcParameter),
      0 < t.val → t.val < 1 → D.curve e t ∈ frontier (faceRegion D F) →
      F = positiveChartFace D e (charts e) ∨ F = negativeChartFace D e (charts e)) :
    Finite (Face D) := by
  let pos : E → Face D := fun e => positiveChartFace D e (charts e)
  let neg : E → Face D := fun e => negativeChartFace D e (charts e)
  apply Finite.of_finite_univ
  apply ((Set.finite_range pos).union (Set.finite_range neg)).subset
  intro F _
  obtain ⟨e, t, ht0, ht1, ht⟩ := exists_edge_interior_mem_frontier D F
  rcases hinc F e t ht0 ht1 ht with hp | hn
  · exact Or.inl ⟨e, hp.symm⟩
  · exact Or.inr ⟨e, hn.symm⟩

/-- Within an edge chart, exactly the two chart faces accumulate at the edge. -/
theorem mem_closure_faceRegion_iff_chart_face (D : Drawing J) (e : E)
    (c : EdgeChart D e) (F : Face D) (t : ArcParameter)
    (ht : |t.val - 1 / 2| < c.radius) :
    D.curve e t ∈ closure (faceRegion D F) ↔
      F = positiveChartFace D e c ∨ F = negativeChartFace D e c := by
  have htrace : ∀ z ∈ PlaneTopology.axisBox (1 / 2) c.radius,
      c.chart.map.symm z ∈ drawingTrace D ↔ z.2 = 0 := by
    intro z hz
    apply c.trace_box
    · rw [abs_lt]
      constructor <;> linarith [hz.1.1, hz.1.2]
    · rw [abs_lt]
      exact hz.2
  have hx : t.val ∈ Set.Ioo (1 / 2 - c.radius) (1 / 2 + c.radius) := by
    rw [abs_lt] at ht
    constructor <;> linarith
  have hstraight : c.chart.map.symm (t.val, 0) = D.curve e t := by
    rw [← c.straight t ht, Homeomorph.symm_apply_apply]
  obtain ⟨a, rfl⟩ := ConnectedComponents.surjective_coe F
  have hp : faceRegion D (positiveChartFace D e c) =
      connectedComponentIn (drawingTrace D)ᶜ (c.chart.map.symm (1 / 2, c.radius / 2)) := by
    exact faceRegion_mk D _
  have hn : faceRegion D (negativeChartFace D e c) =
      connectedComponentIn (drawingTrace D)ᶜ (c.chart.map.symm (1 / 2, -(c.radius / 2))) := by
    exact faceRegion_mk D _
  rw [← hstraight, faceRegion_mk]
  rw [PlaneTopology.axis_mem_closure_component_iff _ _ _ _ c.radius_pos htrace _ _ hx]
  rw [← faceRegion_mk D a, ← hp, ← hn]
  simp only [faceRegion_injective D |>.eq_iff]

/-- A straightened edge subarc admits a box meeting the trace only on its axis. -/
theorem exists_trace_box_of_straightened_subarc (D : Drawing J) (e : E)
    (t : ArcParameter) (ht0 : 0 < t.val) (ht1 : t.val < 1)
    (h : Plane ≃ₜ Plane) (δ : ℝ) (hδ : 0 < δ)
    (hs : ∀ s : ArcParameter, |s.val - t.val| < δ → h (D.curve e s) = (s.val, 0)) :
    ∃ r : ℝ, 0 < r ∧
      (∀ z ∈ PlaneTopology.axisBox t.val r,
        h.symm z ∈ drawingTrace D ↔ z.2 = 0) ∧
      (∀ s : ArcParameter, |s.val - t.val| < r → h (D.curve e s) = (s.val, 0)) := by
  let U : Set ArcParameter := Subtype.val ⁻¹' Set.Ioo (t.val - δ) (t.val + δ)
  have hU : IsOpen U := isOpen_Ioo.preimage continuous_subtype_val
  have htU : t ∈ U := ⟨by linarith, by linarith⟩
  let K : Set Plane := Set.range D.point ∪
    (⋃ f : {f : E // f ≠ e}, Set.range (D.curve f.val)) ∪ D.curve e '' Uᶜ
  have hK : IsCompact K := by
    exact ((Set.finite_range D.point).isCompact.union
      (isCompact_iUnion fun f : {f : E // f ≠ e} => isCompact_range (D.continuous f.val))).union
        (by
          have hc : (Set.univ : Set ArcParameter) \ U = Uᶜ := by ext x; simp
          rw [← hc]
          exact (isCompact_univ.diff hU).image (D.continuous e))
  have htK : D.curve e t ∉ K := by
    rintro ((⟨v, hv⟩ | hf) | ⟨s, hsU, heq⟩)
    · exact D.avoids e t ht0 ht1 v hv.symm
    · obtain ⟨f, s, heq⟩ := Set.mem_iUnion.mp hf
      have hi := (D.intersects e f.val (Ne.symm f.property) t s heq.symm).1
      rcases hi with hi | hi <;> linarith
    · have hs1 : s.val < 1 := by
        by_contra hn
        have hsone : s.val = 1 := le_antisymm s.property.2 (le_of_not_gt hn)
        have hs' : s = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext hsone
        rw [hs', D.finish] at heq
        exact D.avoids e t ht0 ht1 (J.right e) heq.symm
      have he : s = t := D.injective e hs1 ht1 heq
      exact hsU (he ▸ htU)
  have htstraight : h (D.curve e t) = (t.val, 0) := hs t (by simpa using hδ)
  have htK' : (t.val, 0) ∉ h '' K := by
    rintro ⟨z, hz, he⟩
    have hz' : z = D.curve e t := h.injective (he.trans htstraight.symm)
    exact htK (hz' ▸ hz)
  have hopen : IsOpen (h '' K)ᶜ := (hK.image h.continuous).isClosed.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen (t.val, 0) htK'
  let r := min (ε / 2) (min (δ / 2) (min (t.val / 2) ((1 - t.val) / 2)))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrε : r < ε := by dsimp [r]; linarith [min_le_left (ε / 2) (min (δ / 2) (min (t.val / 2) ((1 - t.val) / 2)))]
  have hrδ : r < δ := by
    dsimp [r]; have := min_le_right (ε / 2) (min (δ / 2) (min (t.val / 2) ((1 - t.val) / 2)))
    have := min_le_left (δ / 2) (min (t.val / 2) ((1 - t.val) / 2))
    linarith
  have hrt : r < t.val := by
    dsimp [r]; have := min_le_right (ε / 2) (min (δ / 2) (min (t.val / 2) ((1 - t.val) / 2)))
    have := min_le_right (δ / 2) (min (t.val / 2) ((1 - t.val) / 2))
    have := min_le_left (t.val / 2) ((1 - t.val) / 2)
    linarith
  have hrone : r < 1 - t.val := by
    dsimp [r]; have := min_le_right (ε / 2) (min (δ / 2) (min (t.val / 2) ((1 - t.val) / 2)))
    have := min_le_right (δ / 2) (min (t.val / 2) ((1 - t.val) / 2))
    have := min_le_right (t.val / 2) ((1 - t.val) / 2)
    linarith
  refine ⟨r, hr, ?_, fun s hs' => hs s (lt_trans hs' hrδ)⟩
  intro z hz
  have hx : |z.1 - t.val| < r := by
    rw [abs_lt]; constructor <;> linarith [hz.1.1, hz.1.2]
  have hy : |z.2| < r := by rw [abs_lt]; exact hz.2
  have hzball : z ∈ Metric.ball (t.val, 0) ε := by
    change dist z (t.val, 0) < ε
    have hd : dist z (t.val, 0) < r := by
      simpa only [Prod.dist_eq, Real.dist_eq, sub_zero] using max_lt hx hy
    exact lt_trans hd hrε
  have hzK : h.symm z ∉ K := by
    intro hz'
    exact hball hzball ⟨h.symm z, hz', h.apply_symm_apply z⟩
  constructor
  · rintro (⟨v, hv⟩ | hf)
    · exact (hzK (Or.inl (Or.inl ⟨v, hv⟩))).elim
    · obtain ⟨f, s, heq⟩ := Set.mem_iUnion.mp hf
      by_cases hfe : f = e
      · subst f
        have hsU : s ∈ U := by
          by_contra hn
          exact hzK (Or.inr ⟨s, hn, heq⟩)
        have hsδ : |s.val - t.val| < δ := by
          rw [abs_lt]; constructor <;> linarith [hsU.1, hsU.2]
        have he : z = (s.val, 0) := by rw [← hs s hsδ, heq, h.apply_symm_apply]
        exact congrArg Prod.snd he
      · exact (hzK (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨⟨f, hfe⟩, s, heq⟩)))).elim
  · intro hz0
    have hzI : z.1 ∈ Set.Icc (0 : ℝ) 1 := by
      have hx' := abs_lt.mp hx
      constructor <;> linarith
    let s : ArcParameter := ⟨z.1, hzI⟩
    have he : D.curve e s = h.symm z := by
      apply h.injective
      rw [hs s (lt_trans hx hrδ), h.apply_symm_apply]
      exact Prod.ext rfl hz0.symm
    exact Or.inr (Set.mem_iUnion.mpr ⟨e, s, he⟩)

/-- Local regular charts along an edge propagate face incidence across its interior. -/
theorem closure_incidence_of_local_charts (D : Drawing J) (e : E) (F : Face D)
    (hcharts : ∀ (t : ArcParameter), 0 < t.val → t.val < 1 →
      ∃ (h : Plane ≃ₜ Plane) (r : ℝ), 0 < r ∧
        (∀ z ∈ PlaneTopology.axisBox t.val r,
          h.symm z ∈ drawingTrace D ↔ z.2 = 0) ∧
        (∀ s : ArcParameter, |s.val - t.val| < r → h (D.curve e s) = (s.val, 0)))
    (t u : ArcParameter) (ht0 : 0 < t.val) (ht1 : t.val < 1)
    (hu0 : 0 < u.val) (hu1 : u.val < 1) :
    D.curve e t ∈ closure (faceRegion D F) ↔
      D.curve e u ∈ closure (faceRegion D F) := by
  let I := Set.Ioo (0 : ℝ) 1
  let param : I → ArcParameter := fun x => ⟨x.val, ⟨x.property.1.le, x.property.2.le⟩⟩
  let f : I → Prop := fun x => D.curve e (param x) ∈ closure (faceRegion D F)
  have : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have hf : IsLocallyConstant f := by
    apply (IsLocallyConstant.iff_exists_open f).2
    intro x
    obtain ⟨h, r, hr, htrace, hstraight⟩ := hcharts (param x) x.property.1 x.property.2
    refine ⟨Subtype.val ⁻¹' Set.Ioo (x.val - r) (x.val + r),
      isOpen_Ioo.preimage continuous_subtype_val, ⟨by linarith, by linarith⟩, ?_⟩
    intro y hy
    have hy' : |(param y).val - (param x).val| < r := by
      rw [abs_lt]; constructor <;> linarith [hy.1, hy.2]
    have hx' : |(param x).val - (param x).val| < r := by simpa using hr
    have hyaxis : h.symm ((param y).val, 0) = D.curve e (param y) := by
      rw [← hstraight (param y) hy', Homeomorph.symm_apply_apply]
    have hxaxis : h.symm ((param x).val, 0) = D.curve e (param x) := by
      rw [← hstraight (param x) hx', Homeomorph.symm_apply_apply]
    obtain ⟨a, ha⟩ := ConnectedComponents.surjective_coe F
    have hcomp := PlaneTopology.axis_mem_closure_component_iff_axis_mem_closure_component
      (drawingTrace D) h (param x).val r hr htrace a.val (param y).val (param x).val
      hy ⟨by linarith, by linarith⟩
    apply propext
    dsimp only [f]
    rw [← ha, faceRegion_mk, ← hyaxis, ← hxaxis]
    exact hcomp
  let x : I := ⟨t.val, ht0, ht1⟩
  let y : I := ⟨u.val, hu0, hu1⟩
  have h := hf.apply_eq_of_preconnectedSpace x y
  change (D.curve e (param x) ∈ closure (faceRegion D F)) =
    (D.curve e (param y) ∈ closure (faceRegion D F)) at h
  have htx : param x = t := Subtype.ext rfl
  have huy : param y = u := Subtype.ext rfl
  rw [htx, huy] at h
  exact iff_of_eq h
/-- Regular charts at every interior edge point imply the finiteness of faces. -/
theorem finite_faces_of_local_charts (D : Drawing J) [Nonempty E]
    (charts : ∀ e, EdgeChart D e)
    (hcharts : ∀ (e : E) (t : ArcParameter), 0 < t.val → t.val < 1 →
      ∃ (h : Plane ≃ₜ Plane) (r : ℝ), 0 < r ∧
        (∀ z ∈ PlaneTopology.axisBox t.val r,
          h.symm z ∈ drawingTrace D ↔ z.2 = 0) ∧
        (∀ s : ArcParameter, |s.val - t.val| < r → h (D.curve e s) = (s.val, 0))) :
    Finite (Face D) := by
  apply finite_faces_of_interior_incidence D charts
  intro F e t ht0 ht1 ht
  let m : ArcParameter := ⟨1 / 2, by constructor <;> norm_num⟩
  have hm : D.curve e m ∈ closure (faceRegion D F) :=
    (closure_incidence_of_local_charts D e F (hcharts e) t m ht0 ht1
      (by norm_num [m]) (by norm_num [m])).mp (frontier_subset_closure ht)
  exact (mem_closure_faceRegion_iff_chart_face D e (charts e) F m
    (by simpa [m] using (charts e).radius_pos)).mp hm

/-- Straightenable subarcs at all interior edge points imply finiteness of faces. -/
theorem finite_faces_of_straightenable_subarcs (D : Drawing J) [Nonempty E]
    (charts : ∀ e, EdgeChart D e)
    (hstraight : ∀ (e : E) (t : ArcParameter), 0 < t.val → t.val < 1 →
      ∃ (h : Plane ≃ₜ Plane) (δ : ℝ), 0 < δ ∧
        ∀ s : ArcParameter, |s.val - t.val| < δ → h (D.curve e s) = (s.val, 0)) :
    Finite (Face D) := by
  apply finite_faces_of_local_charts D charts
  intro e t ht0 ht1
  obtain ⟨h, δ, hδ, hs⟩ := hstraight e t ht0 ht1
  obtain ⟨r, hr, htrace, hparam⟩ :=
    exists_trace_box_of_straightened_subarc D e t ht0 ht1 h δ hδ hs
  exact ⟨h, r, hr, htrace, hparam⟩

/-- One can choose a distinct point in each face to serve as a dual vertex. -/
theorem exists_injective_face_points (D : Drawing J) :
    ∃ p : Face D → Plane, Function.Injective p ∧ ∀ F, p F ∈ faceRegion D F := by
  classical
  have hex : ∀ F : Face D, ∃ z, z ∈ faceRegion D F := by
    intro F
    obtain ⟨a, rfl⟩ := ConnectedComponents.surjective_coe F
    exact ⟨a.val, a.property, rfl⟩
  choose p hp using hex
  refine ⟨p, ?_, hp⟩
  intro F G h
  obtain ⟨hF, eF⟩ := hp F
  obtain ⟨hG, eG⟩ := hp G
  have heq : (⟨p F, hF⟩ : {z // z ∉ drawingTrace D}) = ⟨p G, hG⟩ := Subtype.ext h
  exact eF.symm.trans ((congrArg ConnectedComponents.mk heq).trans eG)

/-- Distinct points in one face can be joined by an injective arc inside that face. -/
theorem exists_injective_face_path (D : Drawing J) (F : Face D) {x y : Plane}
    (hx : x ∈ faceRegion D F) (hy : y ∈ faceRegion D F) (hne : x ≠ y) :
    ∃ p : Path x y, Function.Injective p ∧ Set.range p ⊆ faceRegion D F := by
  obtain ⟨vs, hv, hsub, hhead, hlast⟩ :=
    LatticeProb.Topology.exists_polygonal_chain_of_isPreconnected
      (punctured_faceRegion_isOpen D F) (faceRegion_isConnected D F).isPreconnected hx hy
  have hvne : vs.head hv ≠ vs.getLast hv := by simpa only [hhead, hlast] using hne
  obtain ⟨us, hu, _, _, p, hinj, _, hp⟩ :=
    LatticeProb.Topology.DiskArcPair.coordinate_chain_consumer hv hvne
  let q := p.cast hhead.symm hlast.symm
  exact ⟨q, hinj, hp.trans hsub⟩

/-- Face points can be chosen outside any prescribed finite set. -/
theorem exists_injective_face_points_avoiding (D : Drawing J) {S : Set Plane} (hS : S.Finite) :
    ∃ p : Face D → Plane, Function.Injective p ∧
      (∀ F, p F ∈ faceRegion D F) ∧ ∀ F, p F ∉ S := by
  classical
  have hd : Dense Sᶜ := by
    rw [Set.compl_eq_univ_sdiff]
    exact dense_univ.sdiff_finite hS
  have hex : ∀ F : Face D, ∃ z, z ∈ faceRegion D F ∧ z ∉ S := by
    intro F
    obtain ⟨a, rfl⟩ := ConnectedComponents.surjective_coe F
    obtain ⟨z, hzF, hzS⟩ := hd.inter_open_nonempty _
      (punctured_faceRegion_isOpen D _) ⟨a.val, a.property, rfl⟩
    exact ⟨z, hzF, hzS⟩
  choose p hp using hex
  refine ⟨p, ?_, (fun F => (hp F).1), (fun F => (hp F).2)⟩
  intro F G h
  obtain ⟨hF, eF⟩ := (hp F).1
  obtain ⟨hG, eG⟩ := (hp G).1
  have heq : (⟨p F, hF⟩ : {z // z ∉ drawingTrace D}) = ⟨p G, hG⟩ := Subtype.ext h
  exact eF.symm.trans ((congrArg ConnectedComponents.mk heq).trans eG)

/-- Face points can be chosen outside a finite union of chart lines. -/
theorem exists_face_points_avoiding_chart_lines (D : Drawing J)
    (charts : ∀ e, EdgeChart D e) :
    ∃ p : Face D → Plane, Function.Injective p ∧
      (∀ F, p F ∈ faceRegion D F) ∧
      ∀ F e, ((charts e).chart.map (p F)).1 ≠ 1 / 2 := by
  classical
  let lines : E → Set Plane := fun e =>
    (fun z : Plane => ((charts e).chart.map z).1) ⁻¹' {(1 / 2 : ℝ)}
  have hline : ∀ e, IsNowhereDense (lines e) := by
    intro e
    have hd : Dense (lines e)ᶜ := by
      change Dense ((fun z : Plane => ((charts e).chart.map z).1) ⁻¹' ({(1 / 2 : ℝ)}ᶜ))
      exact (dense_compl_singleton (1 / 2 : ℝ)).preimage
        (isOpenMap_fst.comp (charts e).chart.map.isOpenMap)
    have hc : IsClosed (lines e) :=
      isClosed_singleton.preimage (continuous_fst.comp (charts e).chart.map.continuous)
    exact (hc.isNowhereDense_iff).2 (interior_eq_empty_iff_dense_compl.mpr hd)
  have hdense : Dense (⋃ e, lines e)ᶜ := by
    have hn := nowhereDense_iUnion lines hline
    have hc : IsClosed (⋃ e, lines e) := isClosed_iUnion_of_finite fun e =>
      isClosed_singleton.preimage (continuous_fst.comp (charts e).chart.map.continuous)
    exact interior_eq_empty_iff_dense_compl.mp ((hc.isNowhereDense_iff).mp hn)
  have hex : ∀ F : Face D, ∃ z, z ∈ faceRegion D F ∧ ∀ e, z ∉ lines e := by
    intro F
    obtain ⟨a, rfl⟩ := ConnectedComponents.surjective_coe F
    obtain ⟨z, hzF, hz⟩ := hdense.inter_open_nonempty _
      (punctured_faceRegion_isOpen D _) ⟨a.val, a.property, rfl⟩
    exact ⟨z, hzF, by simpa using hz⟩
  choose p hp using hex
  refine ⟨p, ?_, (fun F => (hp F).1), ?_⟩
  · intro F G h
    obtain ⟨hF, eF⟩ := (hp F).1
    obtain ⟨hG, eG⟩ := (hp G).1
    have heq : (⟨p F, hF⟩ : {z // z ∉ drawingTrace D}) = ⟨p G, hG⟩ := Subtype.ext h
    exact eF.symm.trans ((congrArg ConnectedComponents.mk heq).trans eG)
  · intro F e
    simpa [lines] using (hp F).2 e

/-- Removing finitely many points from a plane ball preserves path connectedness. -/
theorem isPathConnected_ball_sdiff_finite (x : Plane) {r : ℝ} (hr : 0 < r)
    {S : Set Plane} (hS : S.Finite) : IsPathConnected (Metric.ball x r \ S) := by
  let h : OpenPartialHomeomorph Plane Plane := OpenPartialHomeomorph.univBall x r
  have hinj : Function.Injective h := by
    intro a b hab
    have ha : a ∈ h.source := by simp [h]
    have hb : b ∈ h.source := by simp [h]
    exact (h.left_inv ha).symm.trans ((congrArg h.symm hab).trans (h.left_inv hb))
  have hfinite : (h ⁻¹' S).Finite := hS.preimage hinj.injOn
  have himage : h '' (h ⁻¹' S)ᶜ = Metric.ball x r \ S := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, hy⟩
      have hy' : y ∈ h.source := by simp [h]
      have := h.map_source hy'
      simpa [h, OpenPartialHomeomorph.univBall_target x hr] using this
    · rintro ⟨hz, hzS⟩
      have hz' : z ∈ h.target := by
        simpa [h, OpenPartialHomeomorph.univBall_target x hr] using hz
      refine ⟨h.symm z, ?_, h.right_inv hz'⟩
      change h (h.symm z) ∉ S
      rwa [h.right_inv hz']
  rw [← himage]
  exact (PlaneTopology.isPathConnected_compl_of_finite hfinite).image
    (OpenPartialHomeomorph.continuous_univBall x r)

/-- Removing finitely many points from an open preconnected plane set preserves preconnectedness. -/
theorem isPreconnected_sdiff_finite {U S : Set Plane} (hU : IsOpen U)
    (hc : IsPreconnected U) (hS : S.Finite) : IsPreconnected (U \ S) := by
  classical
  by_cases hempty : (U \ S).Nonempty
  · obtain ⟨a, ha⟩ := hempty
    let C := connectedComponentIn (U \ S) a
    have hCa : a ∈ C := mem_connectedComponentIn ha
    have hCsub : C ⊆ U \ S := connectedComponentIn_subset _ _
    have hdense : Dense Sᶜ := by
      rw [Set.compl_eq_univ_sdiff]
      exact dense_univ.sdiff_finite hS
    have hball : ∀ z ∈ U, ∀ r : ℝ, 0 < r → Metric.ball z r ⊆ U →
        (Metric.ball z r ∩ C).Nonempty → Metric.ball z r \ S ⊆ C := by
      intro z hz r hr hrU ⟨w, hwball, hwC⟩
      have hmem : w ∈ Metric.ball z r \ S := ⟨hwball, (hCsub hwC).2⟩
      have heq : connectedComponentIn (U \ S) a = connectedComponentIn (U \ S) w :=
        connectedComponentIn_eq hwC
      change Metric.ball z r \ S ⊆ connectedComponentIn (U \ S) a
      rw [heq]
      exact (isPathConnected_ball_sdiff_finite z hr hS).isConnected.isPreconnected.subset_connectedComponentIn
        hmem (by intro y hy; exact ⟨hrU hy.1, hy.2⟩)
    let W := U ∩ closure C
    have hWopen : IsOpen W := by
      rw [isOpen_iff_forall_mem_open]
      intro z hz
      obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z hz.1
      have hint : (Metric.ball z r ∩ C).Nonempty := by
        obtain ⟨w, hwball, hwC⟩ := mem_closure_iff.mp hz.2 _ Metric.isOpen_ball (Metric.mem_ball_self hr)
        exact ⟨w, hwball, hwC⟩
      have hsub := hball z hz.1 r hr hrU hint
      have hcl : Metric.ball z r ⊆ closure C := by
        have hd := hdense.open_subset_closure_inter (Metric.isOpen_ball : IsOpen (Metric.ball z r))
        apply hd.trans
        apply closure_mono
        intro y hy
        exact hsub ⟨hy.1, hy.2⟩
      exact ⟨Metric.ball z r, fun y hy => ⟨hrU hy, hcl hy⟩, Metric.isOpen_ball, Metric.mem_ball_self hr⟩
    have hUcl : U ⊆ W := hc.subset_of_closure_inter_subset hWopen
      ⟨a, ha.1, ha.1, subset_closure hCa⟩ (by
        intro z hz
        exact ⟨hz.2, by
          have h := (closure_mono (show W ⊆ closure C from Set.inter_subset_right)) hz.1
          simpa only [closure_closure] using h⟩)
    have heq : C = U \ S := by
      apply Set.Subset.antisymm hCsub
      intro z hz
      obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z hz.1
      have hzcl : z ∈ closure C := (hUcl hz.1).2
      obtain ⟨w, hwball, hwC⟩ := mem_closure_iff.mp hzcl _ Metric.isOpen_ball (Metric.mem_ball_self hr)
      exact hball z hz.1 r hr hrU ⟨w, hwball, hwC⟩ ⟨Metric.mem_ball_self hr, hz.2⟩
    rw [← heq]
    exact isPreconnected_connectedComponentIn
  · have : U \ S = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    rw [this]
    exact isPreconnected_empty

/-- Distinct points in a face can be joined by a simple polygonal arc avoiding a finite set. -/
theorem exists_injective_polygonal_face_path_avoiding (D : Drawing J) (F : Face D)
    {x y : Plane} {S : Set Plane} (hS : S.Finite)
    (hx : x ∈ faceRegion D F \ S) (hy : y ∈ faceRegion D F \ S) (hne : x ≠ y) :
    ∃ p : Path x y, ∃ vs : List Plane,
      LatticeProb.Topology.IsSimplePolygonalChain vs ∧ Function.Injective p ∧
      Set.range p = LatticeProb.Topology.polygonalChain vs ∧
      Set.range p ⊆ faceRegion D F \ S := by
  obtain ⟨vs, hv, hsub, hhead, hlast⟩ :=
    LatticeProb.Topology.exists_polygonal_chain_of_isPreconnected
      ((punctured_faceRegion_isOpen D F).sdiff hS.isClosed)
      (isPreconnected_sdiff_finite (punctured_faceRegion_isOpen D F)
        (faceRegion_isConnected D F).isPreconnected hS) hx hy
  have hvne : vs.head hv ≠ vs.getLast hv := by simpa only [hhead, hlast] using hne
  obtain ⟨us, hu, hs, hh, hl, hsub', hinj, hrange⟩ :=
    LatticeProb.Topology.exists_injective_polygonal_arc vs hv hvne
  let q := (LatticeProb.Topology.polygonalChainPath us hu).cast
    (hh.trans hhead).symm (hl.trans hlast).symm
  exact ⟨q, us, hs, hinj, hrange, hrange ▸ hsub'.trans hsub⟩

/-- Distinct points in a face can be joined by a simple arc avoiding a finite set. -/
theorem exists_injective_face_path_avoiding (D : Drawing J) (F : Face D)
    {x y : Plane} {S : Set Plane} (hS : S.Finite)
    (hx : x ∈ faceRegion D F \ S) (hy : y ∈ faceRegion D F \ S) (hne : x ≠ y) :
    ∃ p : Path x y, Function.Injective p ∧ Set.range p ⊆ faceRegion D F \ S := by
  obtain ⟨p, _, _, hp, _, hsub⟩ :=
    exists_injective_polygonal_face_path_avoiding D F hS hx hy hne
  exact ⟨p, hp, hsub⟩

/-- Distinct face regions are disjoint. -/
theorem faceRegion_disjoint (D : Drawing J) {F G : Face D} (h : F ≠ G) :
    Disjoint (faceRegion D F) (faceRegion D G) := by
  refine Set.disjoint_left.mpr ?_
  intro z hzF hzG
  obtain ⟨hzF, hF⟩ := hzF
  obtain ⟨hzG, hG⟩ := hzG
  apply h
  exact hF.symm.trans hG

/-- Disjoint local crossings admit individual simple paths to face points away from the crossings. -/
theorem exists_crossings_with_face_paths (D : Drawing J) (charts : ∀ e, EdgeChart D e) :
    ∃ r : E → ℝ, ∃ q : E → ArcParameter → Plane, ∃ p : Face D → Plane,
      let S := Set.range (fun e => q e ⟨0, by norm_num⟩) ∪
        Set.range (fun e => q e ⟨1, by norm_num⟩)
      (∀ e, 0 < r e ∧ r e < (charts e).radius) ∧
      (∀ e, Continuous (q e) ∧ Function.Injective (q e)) ∧
      (∀ e t, ((charts e).chart.map (q e t)).1 = 1 / 2) ∧
      (∀ e f, e ≠ f → Disjoint (Set.range (q e)) (Set.range (q f))) ∧
      (∀ e, Disjoint (Set.range (q e)) (Set.range D.point)) ∧
      (∀ e f s t, D.curve f s = q e t ↔
        f = e ∧ s.val = 1 / 2 ∧ t.val = 1 / 2) ∧
      (∀ e t, (t.val < 1 / 2 → q e t ∈ faceRegion D (negativeChartFace D e (charts e))) ∧
        (1 / 2 < t.val → q e t ∈ faceRegion D (positiveChartFace D e (charts e)))) ∧
      (∀ e t, |t.val - 1 / 2| < r e / 2 →
        (charts e).chart.map (q e t) = (1 / 2, t.val - 1 / 2)) ∧
      Function.Injective p ∧ (∀ F, p F ∈ faceRegion D F) ∧
      (∀ F e, p F ∉ Set.range (q e)) ∧
      (∀ e, (∃ a : Path (p (negativeChartFace D e (charts e))) (q e ⟨0, by norm_num⟩),
          Function.Injective a ∧ Set.range a ⊆
            faceRegion D (negativeChartFace D e (charts e)) \ (S \ {q e ⟨0, by norm_num⟩})) ∧
        (∃ b : Path (p (positiveChartFace D e (charts e))) (q e ⟨1, by norm_num⟩),
          Function.Injective b ∧ Set.range b ⊆
            faceRegion D (positiveChartFace D e (charts e)) \ (S \ {q e ⟨1, by norm_num⟩}))) := by
  obtain ⟨r, q, hr, hq, hline, hd, hv, hc, hf, hl⟩ :=
    exists_disjoint_parametrized_crossings D charts
  let neg : E → Plane := fun e => q e ⟨0, by norm_num⟩
  let pos : E → Plane := fun e => q e ⟨1, by norm_num⟩
  let S := Set.range neg ∪ Set.range pos
  have hS : S.Finite := (Set.finite_range neg).union (Set.finite_range pos)
  obtain ⟨p, hp, hpf, hpLine⟩ := exists_face_points_avoiding_chart_lines D charts
  have hpq : ∀ F e, p F ∉ Set.range (q e) := by
    intro F e ⟨t, ht⟩
    apply hpLine F e
    rw [← ht]
    exact hline e t
  have hpS : ∀ F, p F ∉ S := by
    intro F h
    rcases h with ⟨e, he⟩ | ⟨e, he⟩
    · exact hpq F e ⟨⟨0, by norm_num⟩, he⟩
    · exact hpq F e ⟨⟨1, by norm_num⟩, he⟩
  refine ⟨r, q, p, hr, hq, hline, hd, hv, hc, hf, hl, hp, hpf, hpq, fun e => ⟨?_, ?_⟩⟩
  · have hmem : neg e ∈ faceRegion D (negativeChartFace D e (charts e)) :=
      (hf e ⟨0, by norm_num⟩).1 (by norm_num)
    have hne : p (negativeChartFace D e (charts e)) ≠ neg e := by
      intro heq
      apply hpS (negativeChartFace D e (charts e))
      rw [heq]
      exact Or.inl ⟨e, rfl⟩
    apply exists_injective_face_path_avoiding D _ (hS.sdiff) _ _ hne
    · exact ⟨hpf _, fun h => hpS _ h.1⟩
    · exact ⟨hmem, by simp [neg]⟩
  · have hmem : pos e ∈ faceRegion D (positiveChartFace D e (charts e)) :=
      (hf e ⟨1, by norm_num⟩).2 (by norm_num)
    have hne : p (positiveChartFace D e (charts e)) ≠ pos e := by
      intro heq
      apply hpS (positiveChartFace D e (charts e))
      rw [heq]
      exact Or.inr ⟨e, rfl⟩
    apply exists_injective_face_path_avoiding D _ (hS.sdiff) _ _ hne
    · exact ⟨hpf _, fun h => hpS _ h.1⟩
    · exact ⟨hmem, by simp [pos]⟩

/-- Every chart side can be reached by a simple arc from a chosen point of its face. -/
theorem exists_chart_side_paths (D : Drawing J) (charts : ∀ e, EdgeChart D e) :
    ∃ p : Face D → Plane, Function.Injective p ∧ (∀ F, p F ∈ faceRegion D F) ∧
      ∀ e, (∃ q : Path (p (negativeChartFace D e (charts e)))
            ((charts e).chart.map.symm (1 / 2, -((charts e).radius / 2))),
            Function.Injective q ∧ Set.range q ⊆ faceRegion D (negativeChartFace D e (charts e))) ∧
        (∃ q : Path (p (positiveChartFace D e (charts e)))
            ((charts e).chart.map.symm (1 / 2, (charts e).radius / 2)),
            Function.Injective q ∧ Set.range q ⊆ faceRegion D (positiveChartFace D e (charts e))) := by
  let neg : E → Plane := fun e => (charts e).chart.map.symm (1 / 2, -((charts e).radius / 2))
  let pos : E → Plane := fun e => (charts e).chart.map.symm (1 / 2, (charts e).radius / 2)
  let S := Set.range neg ∪ Set.range pos
  have hS : S.Finite := (Set.finite_range neg).union (Set.finite_range pos)
  obtain ⟨p, hp, hpf, hpS⟩ := exists_injective_face_points_avoiding D hS
  refine ⟨p, hp, hpf, fun e => ⟨?_, ?_⟩⟩
  · have hmem : neg e ∈ faceRegion D (negativeChartFace D e (charts e)) :=
      ⟨negative_chart_point_off_trace D e (charts e), rfl⟩
    have hne : p (negativeChartFace D e (charts e)) ≠ neg e := by
      intro heq
      apply hpS (negativeChartFace D e (charts e))
      rw [heq]
      exact Or.inl ⟨e, rfl⟩
    exact exists_injective_face_path D _ (hpf _) hmem hne
  · have hmem : pos e ∈ faceRegion D (positiveChartFace D e (charts e)) :=
      ⟨positive_chart_point_off_trace D e (charts e), rfl⟩
    have hne : p (positiveChartFace D e (charts e)) ≠ pos e := by
      intro heq
      apply hpS (positiveChartFace D e (charts e))
      rw [heq]
      exact Or.inr ⟨e, rfl⟩
    exact exists_injective_face_path D _ (hpf _) hmem hne


/-- A finite drawing has at most one unbounded face. The argument uses Bonanno’s
`subset_connectedComponentIn_compl_of_unbounded` in `QuantumZipper.Proofs.Complex.TopoSep`. -/
theorem face_eq_of_unbounded (D : Drawing J) (F G : Face D)
    (hF : ¬ Bornology.IsBounded (faceRegion D F))
    (hG : ¬ Bornology.IsBounded (faceRegion D G)) : F = G := by
  let h : Plane ≃ₜ ℂ := Complex.equivRealProdCLM.symm.toHomeomorph
  let K : Set ℂ := h '' drawingTrace D
  let A : Set ℂ := h '' faceRegion D F
  let B : Set ℂ := h '' faceRegion D G
  have hK : IsCompact K := (drawingTrace_isCompact D).image h.continuous
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).mp hK.isBounded
  have hAu : ¬ Bornology.IsBounded A := by
    intro hb
    apply hF
    have hbi := Complex.lipschitz_equivRealProd.isBounded_image hb
    simpa [A, h, Set.image_image] using hbi
  obtain ⟨a, haA, ha⟩ : ∃ a ∈ A, R < ‖a‖ := by
    by_contra hc
    simp only [not_exists, not_and, not_lt] at hc
    apply hAu
    exact (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset (by
      intro z hz
      simpa only [Metric.mem_closedBall, dist_zero_right] using hc z hz)
  have hBpre : IsPreconnected B :=
    (faceRegion_isConnected D G).isPreconnected.image _ h.continuous.continuousOn
  have hBu : ¬ Bornology.IsBounded B := by
    intro hb
    apply hG
    have hbi := Complex.lipschitz_equivRealProd.isBounded_image hb
    simpa [B, h, Set.image_image] using hbi
  have hBK : Disjoint B K := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
    have : y = x := h.injective he
    subst y
    exact hx.1 hy
  have hsub : B ⊆ connectedComponentIn Kᶜ a :=
    QuantumZipper.CA.Topo.subset_connectedComponentIn_compl_of_unbounded hR hBpre hBu hBK ha
  obtain ⟨x, hx, hxa⟩ := haA
  obtain ⟨y, hy⟩ := (faceRegion_isConnected D G).nonempty
  have hycomp : h y ∈ connectedComponentIn Kᶜ a := hsub ⟨y, hy, rfl⟩
  have hback : h.symm '' Kᶜ ⊆ (drawingTrace D)ᶜ := by
    rintro z ⟨w, hw, rfl⟩ hz
    apply hw
    exact ⟨h.symm w, hz, h.apply_symm_apply w⟩
  have hycomp' : y ∈ connectedComponentIn (drawingTrace D)ᶜ x := by
    apply connectedComponentIn_mono _ hback
    have hi := h.symm.continuous.image_connectedComponentIn_subset
      (show a ∈ Kᶜ from by
        intro haK
        have := hR haK
        rw [Metric.mem_ball, dist_zero_right] at this
        exact (not_lt_of_ge (le_of_lt ha)) this)
    have hyimage : y ∈ h.symm '' connectedComponentIn Kᶜ a :=
      ⟨h y, hycomp, h.symm_apply_apply y⟩
    have hyresult := hi hyimage
    simpa only [← hxa, Homeomorph.symm_apply_apply] using hyresult
  have hxc : faceRegion D F = connectedComponentIn (drawingTrace D)ᶜ x := by
    obtain ⟨hx', hlabel⟩ := hx
    rw [← hlabel]
    exact faceRegion_mk D ⟨x, hx'⟩
  rw [← hxc] at hycomp'
  obtain ⟨hyF, hyFl⟩ := hycomp'
  obtain ⟨hyG, hyGl⟩ := hy
  have heq : (⟨y, hyF⟩ : {z // z ∉ drawingTrace D}) = ⟨y, hyG⟩ := Subtype.ext rfl
  exact hyFl.symm.trans ((congrArg ConnectedComponents.mk heq).trans hyGl)

/-- Every finite drawing has an unbounded face. -/
theorem exists_unbounded_face (D : Drawing J) :
    ∃ F : Face D, ¬ Bornology.IsBounded (faceRegion D F) := by
  let h : Plane ≃ₜ ℂ := Complex.equivRealProdCLM.symm.toHomeomorph
  let K : Set ℂ := h '' drawingTrace D
  have hK : IsCompact K := (drawingTrace_isCompact D).image h.continuous
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).mp hK.isBounded
  let U : Set ℂ := {z | R < ‖z‖}
  have hUu : ¬ Bornology.IsBounded U := by
    intro hb
    obtain ⟨M, hM⟩ := (isBounded_iff_forall_norm_le).mp hb
    let z : ℂ := ((|R| + |M| + 1 : ℝ) : ℂ)
    have hz : ‖z‖ = |R| + |M| + 1 := by
      simp only [z, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
    have hzU : z ∈ U := by
      change R < ‖z‖
      rw [hz]
      linarith [le_abs_self R, abs_nonneg M]
    have := hM z hzU
    rw [hz] at this
    linarith [le_abs_self M, abs_nonneg R]
  obtain ⟨a, ha⟩ : U.Nonempty := by
    by_contra hc
    apply hUu
    simp only [Set.not_nonempty_iff_eq_empty.mp hc, Bornology.isBounded_empty]
  have hUpre : IsPreconnected U := QuantumZipper.CA.Topo.isPreconnected_setOf_lt_norm R
  have hUoff : U ⊆ Kᶜ := QuantumZipper.CA.Topo.setOf_lt_norm_subset_compl hR
  have haoff : h.symm a ∉ drawingTrace D := by
    intro hx
    exact hUoff ha ⟨h.symm a, hx, h.apply_symm_apply a⟩
  let F : Face D := ConnectedComponents.mk ⟨h.symm a, haoff⟩
  refine ⟨F, ?_⟩
  intro hFb
  have hsub : h.symm '' U ⊆ faceRegion D F := by
    rw [show F = ConnectedComponents.mk ⟨h.symm a, haoff⟩ from rfl, faceRegion_mk]
    apply (hUpre.image _ h.symm.continuous.continuousOn).subset_connectedComponentIn
    · exact ⟨a, ha, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩ ht
      exact hUoff hz ⟨h.symm z, ht, h.apply_symm_apply z⟩
  have hbu : Bornology.IsBounded (h.symm '' U) := hFb.subset hsub
  have hbu' := (Complex.equivRealProdCLM.symm.toContinuousLinearMap.lipschitz).isBounded_image hbu
  apply hUu
  change Bornology.IsBounded (Complex.equivRealProdCLM.symm ''
    (Complex.equivRealProdCLM '' U)) at hbu'
  rw [Set.image_image] at hbu'
  have hid : (fun z : ℂ => Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM z)) = id :=
    funext Complex.equivRealProdCLM.symm_apply_apply
  simpa only [hid, Set.image_id] using hbu'


end FiniteAvalanches.Electrical.StatementGeometry
