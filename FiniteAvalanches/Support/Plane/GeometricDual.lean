import FiniteAvalanches.Support.Plane.PuncturedTransport
import FiniteAvalanches.Support.Plane.LocalFaceIncidence

/-!
# Geometric facts for plane dual drawings

Ported from Lattice-Probability `LatticeProb/Topology/PlaneGraph/GeometricDual.lean`
at commit `ba2b67f3`.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open LatticeProb
open Source BSST

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

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

end FiniteAvalanches.Electrical.StatementGeometry
