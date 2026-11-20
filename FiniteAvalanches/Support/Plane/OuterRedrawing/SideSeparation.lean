import FiniteAvalanches.Support.Plane.OuterRedrawing.StraightSetting
import FiniteAvalanches.Support.Plane.SelectedSimplePath

/-!
# Separation at an interior vertex of a straight boundary path

Let the unbounded complementary component of a drawing accumulate along a
straight path. If the collar above one path edge and the collar below the next
path edge both lie in that component, then the common vertex separates the two
neighbouring path vertices: a cycle through both edges would be a Jordan curve,
straight at the vertex, with the component on both of its sides.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing

open Set Metric Bornology
open FiniteAvalanches.Electrical.Source (drawingTrace)

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

omit [Fintype V] [Fintype E] in
/-- Copied reachability is symmetric. -/
theorem reaches_symm' {T : Finset E} {x y : V} (h : J.reaches T x y) : J.reaches T y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih =>
    obtain ⟨e, he, h1⟩ := hst
    refine Relation.ReflTransGen.head ⟨e, he, ?_⟩ ih
    rcases h1 with h1 | h1
    · exact Or.inr ⟨h1.2, h1.1⟩
    · exact Or.inl ⟨h1.2, h1.1⟩

/-- Reachable distinct vertices are joined by an injective path lying on the
curves of the selected edges. -/
theorem exists_simple_path_on_curves (D : Drawing J) (A : Finset E) {u v : V}
    (hne : u ≠ v) (h : J.reaches A u v) :
    ∃ q : Path (D.point u) (D.point v), Function.Injective q ∧
      range q ⊆ {z | ∃ e ∈ A, ∃ t, D.curve e t = z} := by
  let H := euclideanPlaneHomeomorph
  let F := H ∘ D.point
  let K := (J.selectedGraph A).map F
  obtain ⟨W, hW⟩ := J.selectedGraph_reaches A h
  have hR : K.Reaches (F u) (F v) := ⟨W, graph_walk_map F hW⟩
  obtain ⟨P, hP⟩ := hR.exists_isPath
  have hne' : F u ≠ F v := fun h => hne (D.point_injective (H.injective h))
  have hPne : P ≠ [] := hP.ne_nil hne'
  obtain ⟨f, hcont, hinj, him, hf0, hf1⟩ :=
    (D.selectedGraph_isDrawing A).path_isArcBetween hP hPne
  let q : Path (D.point u) (D.point v) :=
    ⟨⟨fun t => H.symm (f t), H.symm.continuous.comp (continuousOn_iff_continuous_restrict.mp hcont)⟩,
      by simpa [F, H] using congrArg H.symm hf0,
      by simpa [F, H] using congrArg H.symm hf1⟩
  refine ⟨q, ?_, ?_⟩
  · intro s t hst
    apply Subtype.ext
    exact hinj s.property t.property (H.symm.injective hst)
  · rintro z ⟨t, rfl⟩
    have hz : f t ∈ Graph.edgesCover D.selectedEdgeDrawing P := by
      rw [← him]
      exact ⟨t, t.property, rfl⟩
    obtain ⟨e, heP, hez⟩ := Graph.mem_edgesCover_iff.mp hz
    have he : e ∈ A ∧ J.left e ≠ J.right e := hP.edge_mem heP
    rw [D.selectedEdgeDrawing_arc] at hez
    obtain ⟨_, ⟨s, rfl⟩, hs⟩ := hez
    refine ⟨e, he.1, s, ?_⟩
    change D.curve e s = H.symm (f t)
    rw [← hs, Homeomorph.symm_apply_apply]

/-- The straight segment between two points of the horizontal line, as a path. -/
def hSegPath (x y : ℝ) : Path ((x, (0 : ℝ)) : ℝ × ℝ) (y, 0) where
  toFun t := (x + (t : ℝ) * (y - x), 0)
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

theorem hSegPath_injective {x y : ℝ} (hxy : x ≠ y) : Function.Injective (hSegPath x y) := by
  intro s t hst
  have h1 := congrArg Prod.fst hst
  simp only [hSegPath, Path.coe_mk', ContinuousMap.coe_mk] at h1
  have hyx : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  exact Subtype.ext (mul_right_cancel₀ hyx (add_left_cancel h1))

theorem mem_range_hSegPath {x y : ℝ} (hxy : x ≤ y) {w : ℝ × ℝ} :
    w ∈ range (hSegPath x y) ↔ w.2 = 0 ∧ x ≤ w.1 ∧ w.1 ≤ y := by
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨rfl, ?_, ?_⟩
    · show x ≤ x + (t : ℝ) * (y - x)
      nlinarith [t.2.1, sub_nonneg.mpr hxy]
    · show x + (t : ℝ) * (y - x) ≤ y
      nlinarith [t.2.2, sub_nonneg.mpr hxy]
  · rintro ⟨hw2, hw0, hw1⟩
    rcases eq_or_lt_of_le hxy with hxy' | hxy'
    · refine ⟨⟨0, by norm_num, by norm_num⟩, ?_⟩
      simp only [hSegPath, Path.coe_mk', ContinuousMap.coe_mk]
      exact Prod.ext (by simp only; linarith) hw2.symm
    · have hpos : 0 < y - x := sub_pos.mpr hxy'
      refine ⟨⟨(w.1 - x) / (y - x), div_nonneg (by linarith) hpos.le,
        (div_le_one hpos).mpr (by linarith)⟩, ?_⟩
      simp only [hSegPath, Path.coe_mk', ContinuousMap.coe_mk]
      exact Prod.ext (by simp only; field_simp; ring) hw2.symm

variable {D : Drawing J} {m : ℕ} {path : Fin (m + 1) → V} {copies : Fin m → E}

theorem mem_upperCollar_of {i : Fin m} {x y : ℝ} (hx0 : (i : ℝ) / m < x)
    (hx1 : x < ((i : ℝ) + 1) / m) (hy0 : 0 < y) (hy1 : y < gap D copies i x) :
    (x, y) ∈ upperCollar D copies i := ⟨hx0, hx1, hy0, hy1⟩

theorem mem_lowerCollar_of {i : Fin m} {x y : ℝ} (hx0 : (i : ℝ) / m < x)
    (hx1 : x < ((i : ℝ) + 1) / m) (hy0 : -gap D copies i x < y) (hy1 : y < 0) :
    (x, y) ∈ lowerCollar D copies i := ⟨hx0, hx1, hy0, hy1⟩

theorem cast_pred {a : ℕ} (ha : 0 < a) : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by
  rw [Nat.cast_sub (by omega : 1 ≤ a), Nat.cast_one]

theorem disjoint_of_subset_trace {U C : Set (ℝ × ℝ)} (hU : OuterFace D U)
    (hC : C ⊆ drawingTrace D) : Disjoint U C :=
  hU.disjoint.mono_right hC

/-- An edge avoiding a path vertex does not pass through its point. -/
theorem curve_ne_point_of_ne {e : E} {v : V} (hl : J.left e ≠ v) (hr : J.right e ≠ v)
    (t : ArcParameter) : D.curve e t ≠ D.point v := by
  intro heq
  rcases (D.curve_vertex_iff e t v).mp heq with ⟨_, h1⟩ | ⟨_, h1⟩
  · exact hl h1
  · exact hr h1

namespace StraightPath

variable (h : StraightPath D m path copies)
include h

/-- The collars of a path edge reach every neighbourhood of its endpoints. -/
theorem exists_collar_point (i : Fin m) {r : ℝ} (hr : 0 < r) (hrm : r ≤ 1 / m)
    (up : Bool) (right : Bool) :
    ∃ w ∈ (if up then upperCollar D copies i else lowerCollar D copies i),
      w ∈ ball ((if right then ((i : ℝ) + 1) / m else (i : ℝ) / m), (0 : ℝ)) r ∧
      (if up then 0 < w.2 else w.2 < 0) := by
  have hm := h.m_pos_real
  set x : ℝ := if right then ((i : ℝ) + 1) / m - r / 2 else (i : ℝ) / m + r / 2 with hx
  have hr2 : r / 2 < 1 / m := by linarith
  have hx0 : (i : ℝ) / m < x := by
    have h1 : ((i : ℝ) + 1) / m = (i : ℝ) / m + 1 / m := by ring
    cases right <;> simp only [hx, Bool.false_eq_true, if_false, if_true] <;> linarith
  have hx1 : x < ((i : ℝ) + 1) / m := by
    have h1 : ((i : ℝ) + 1) / m = (i : ℝ) / m + 1 / m := by ring
    cases right <;> simp only [hx, Bool.false_eq_true, if_false, if_true] <;> linarith
  have hg := h.gap_pos i hx0 hx1
  set y : ℝ := min (gap D copies i x) r / 2 with hy
  have hy0 : 0 < y := by positivity
  have hyg : y < gap D copies i x := by
    have := min_le_left (gap D copies i x) r
    linarith
  have hyr : y < r := by
    have := min_le_right (gap D copies i x) r
    linarith
  have hball : ∀ z : ℝ, |z| < r →
      (x, z) ∈ ball ((if right then ((i : ℝ) + 1) / m else (i : ℝ) / m), (0 : ℝ)) r := by
    intro z hz
    rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero]
    refine max_lt ?_ hz
    cases right <;> simp only [hx, Bool.false_eq_true, if_false, if_true] <;>
      rw [abs_lt] <;> constructor <;> linarith
  cases up
  · refine ⟨(x, -y), mem_lowerCollar_of hx0 hx1 (by linarith) (by linarith), hball _ ?_, ?_⟩
    · rw [abs_neg, abs_of_pos hy0]
      exact hyr
    · show -y < 0
      linarith
  · exact ⟨(x, y), mem_upperCollar_of hx0 hx1 hy0 hyg, hball _ (by rw [abs_of_pos hy0]; exact hyr),
      hy0⟩

/-- A point of the closed segment between two consecutive path edges lies on the drawing. -/
theorem seg_subset_trace {a : ℕ} (ha0 : 0 < a) (ham : a < m) {w : ℝ × ℝ} (hw2 : w.2 = 0)
    (hw0 : ((a : ℝ) - 1) / m ≤ w.1) (hw1 : w.1 ≤ ((a : ℝ) + 1) / m) : w ∈ drawingTrace D := by
  rcases le_total w.1 ((a : ℝ) / m) with hle | hle
  · obtain ⟨t, ht⟩ := h.mem_range_curve ⟨a - 1, by omega⟩ (x := w.1)
      (by show ((a - 1 : ℕ) : ℝ) / m ≤ w.1; rw [cast_pred ha0]; exact hw0)
      (by show w.1 ≤ (((a - 1 : ℕ) : ℝ) + 1) / m; rw [cast_pred ha0]; simpa using hle)
    exact Or.inr (mem_iUnion.mpr ⟨_, t, ht.trans (Prod.ext rfl hw2.symm)⟩)
  · obtain ⟨t, ht⟩ := h.mem_range_curve ⟨a, ham⟩ (x := w.1) hle hw1
    exact Or.inr (mem_iUnion.mpr ⟨_, t, ht.trans (Prod.ext rfl hw2.symm)⟩)

/-- If the collars on opposite sides of the two path edges at an interior vertex
lie in the unbounded component, the vertex separates its two path neighbours. -/
theorem not_reaches_of_opposite_collars {U : Set (ℝ × ℝ)} (hU : OuterFace D U)
    {a : ℕ} (ha0 : 0 < a) (ham : a < m) (A : Finset E)
    (hA : ∀ e ∈ A, J.left e ≠ path ⟨a, by omega⟩ ∧ J.right e ≠ path ⟨a, by omega⟩)
    (hsides : (upperCollar D copies ⟨a - 1, by omega⟩ ⊆ U ∧ lowerCollar D copies ⟨a, ham⟩ ⊆ U) ∨
      (lowerCollar D copies ⟨a - 1, by omega⟩ ⊆ U ∧ upperCollar D copies ⟨a, ham⟩ ⊆ U)) :
    ¬ J.reaches A (path ⟨a + 1, by omega⟩) (path ⟨a - 1, by omega⟩) := by
  intro hreach
  have hm := h.m_pos_real
  have hne : path ⟨a + 1, by omega⟩ ≠ path ⟨a - 1, by omega⟩ := by
    intro he
    have := congrArg Fin.val (h.injective he)
    simp only at this
    omega
  obtain ⟨Q, hQinj, hQr⟩ := exists_simple_path_on_curves D A hne hreach
  set xl : ℝ := ((a : ℝ) - 1) / m with hxl
  set xa : ℝ := (a : ℝ) / m with hxa
  set xr : ℝ := ((a : ℝ) + 1) / m with hxr
  have hpl : D.point (path ⟨a - 1, by omega⟩) = (xl, 0) := by
    rw [h.point]
    show (((a - 1 : ℕ) : ℝ) / m, (0 : ℝ)) = _
    rw [cast_pred ha0]
  have hpa : D.point (path ⟨a, by omega⟩) = (xa, 0) := by
    rw [h.point]
  have hpr : D.point (path ⟨a + 1, by omega⟩) = (xr, 0) := by
    rw [h.point]
    push_cast
    rfl
  have hlr : xl ≤ xr := by
    rw [hxl, hxr, div_le_div_iff_of_pos_right hm]
    linarith
  have hla : xl < xa := by
    rw [hxl, hxa, div_lt_div_iff_of_pos_right hm]
    linarith
  have har : xa < xr := by
    rw [hxa, hxr, div_lt_div_iff_of_pos_right hm]
    linarith
  have hxl1 : xa - xl = 1 / m := by rw [hxl, hxa]; field_simp; ring
  have hxr1 : xr - xa = 1 / m := by rw [hxr, hxa]; field_simp; ring
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha0
  have hxl0 : 0 ≤ xl := div_nonneg (by linarith) hm.le
  have hxr1' : xr ≤ 1 := by
    rw [hxr, div_le_one hm]
    have : (a : ℝ) + 1 ≤ m := by exact_mod_cast ham
    exact this
  let seg : Path (D.point (path ⟨a + 1, by omega⟩)) (D.point (path ⟨a - 1, by omega⟩)) :=
    ((hSegPath xl xr).symm).cast hpr hpl
  have hseg : range seg = range (hSegPath xl xr) := by
    change range ((hSegPath xl xr).symm) = _
    rw [Path.symm_range]
  have hseginj : Function.Injective seg := by
    intro s t hst
    have := hSegPath_injective (ne_of_lt (lt_of_lt_of_le hla har.le)) hst
    exact unitInterval.symm_involutive.injective this
  -- points of the drawing avoiding the middle vertex
  have hQva : ∀ t, Q t ≠ (xa, 0) := by
    intro t ht
    obtain ⟨e, heA, s, hs⟩ := hQr ⟨t, rfl⟩
    exact curve_ne_point_of_ne (hA e heA).1 (hA e heA).2 s (hs.trans (ht.trans hpa.symm))
  have hmeet : range seg ∩ range Q = {D.point (path ⟨a + 1, by omega⟩),
      D.point (path ⟨a - 1, by omega⟩)} := by
    apply Subset.antisymm
    · rintro z ⟨hzs, hzQ⟩
      rw [hseg, mem_range_hSegPath hlr] at hzs
      obtain ⟨hz2, hz0, hz1⟩ := hzs
      obtain ⟨e, heA, t, ht⟩ := hQr hzQ
      by_cases hep : e ∈ range copies
      · obtain ⟨j, rfl⟩ := hep
        obtain ⟨hj0, hj1⟩ := h.curve_fst j t
        rw [ht] at hj0 hj1
        have hjne1 : (j : ℕ) ≠ a - 1 := by
          intro hj
          have hsucc : j.succ = (⟨a, by omega⟩ : Fin (m + 1)) :=
            Fin.ext (by simp only [Fin.val_succ]; omega)
          rcases h.ends j with ⟨_, hr⟩ | ⟨_, hl⟩
          · exact (hA _ heA).2 (hr.trans (by rw [hsucc]))
          · exact (hA _ heA).1 (hl.trans (by rw [hsucc]))
        have hjne2 : (j : ℕ) ≠ a := by
          intro hj
          have hcs : j.castSucc = (⟨a, by omega⟩ : Fin (m + 1)) :=
            Fin.ext (by simp only [Fin.val_castSucc]; omega)
          rcases h.ends j with ⟨hl, _⟩ | ⟨hr, _⟩
          · exact (hA _ heA).1 (hl.trans (by rw [hcs]))
          · exact (hA _ heA).2 (hr.trans (by rw [hcs]))
        rcases lt_or_gt_of_ne hjne2 with hj | hj
        · have hjle : (j : ℝ) + 1 ≤ (a : ℝ) - 1 := by
            have : (j : ℕ) + 1 ≤ a - 1 := by omega
            have := (Nat.cast_le (α := ℝ)).mpr this
            push_cast at this
            rw [cast_pred ha0] at this
            exact this
          have : z.1 ≤ xl := by
            refine le_trans hj1 ?_
            rw [hxl, div_le_div_iff_of_pos_right hm]
            exact hjle
          right
          rw [hpl]
          exact Prod.ext (le_antisymm this hz0) hz2
        · have hjge : (a : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hj
          have : xr ≤ z.1 := by
            refine le_trans ?_ hj0
            rw [hxr, div_le_div_iff_of_pos_right hm]
            exact hjge
          left
          rw [hpr]
          exact Prod.ext (le_antisymm hz1 this) hz2
      · have hzseg : D.curve e t ∈ unitSeg := by
          rw [ht]
          exact ⟨hz2, le_trans hxl0 hz0, le_trans hz1 hxr1'⟩
        obtain ⟨-, j, hj⟩ := h.nonpath_curve_on_unitSeg hep hzseg
        have hz : z = D.point (path j) := ht.symm.trans hj
        have hjx : z.1 = (j : ℝ) / m := by rw [hz, h.point_fst]
        have hja : (j : ℕ) ≠ a := by
          intro hja
          have hjeq : j = ⟨a, by omega⟩ := Fin.ext hja
          rw [hjeq] at hj
          exact curve_ne_point_of_ne (hA e heA).1 (hA e heA).2 t hj
        have hj0 : (a : ℝ) - 1 ≤ (j : ℝ) := by
          have := hz0
          rw [hjx, hxl, div_le_div_iff_of_pos_right hm] at this
          exact this
        have hj1 : (j : ℝ) ≤ (a : ℝ) + 1 := by
          have := hz1
          rw [hjx, hxr, div_le_div_iff_of_pos_right hm] at this
          exact this
        have hj0' : a - 1 ≤ (j : ℕ) := by
          have : ((a - 1 : ℕ) : ℝ) ≤ (j : ℝ) := by rw [cast_pred ha0]; exact hj0
          exact_mod_cast this
        have hj1' : (j : ℕ) ≤ a + 1 := by exact_mod_cast hj1
        rcases (show (j : ℕ) = a - 1 ∨ (j : ℕ) = a + 1 by omega) with hjv | hjv
        · right
          rw [hz, show j = ⟨a - 1, by omega⟩ from Fin.ext hjv]
          rfl
        · left
          rw [hz, show j = ⟨a + 1, by omega⟩ from Fin.ext hjv]
    · rintro z (rfl | hz)
      · exact ⟨seg.source_mem_range, Q.source_mem_range⟩
      · rw [mem_singleton_iff] at hz
        subst hz
        exact ⟨seg.target_mem_range, Q.target_mem_range⟩
  have hJ := isJordanCurve_of_two_paths seg Q hseginj hQinj hmeet
  have hCtrace : range seg ∪ range Q ⊆ drawingTrace D := by
    rintro w (hw | hw)
    · rw [hseg, mem_range_hSegPath hlr] at hw
      exact h.seg_subset_trace ha0 ham hw.1 hw.2.1 hw.2.2
    · obtain ⟨e, -, t, ht⟩ := hQr hw
      exact Or.inr (mem_iUnion.mpr ⟨e, t, ht⟩)
  have hvaQ : (xa, (0 : ℝ)) ∉ range Q := fun ⟨t, ht⟩ => hQva t ht
  have hd : 0 < infDist (xa, (0 : ℝ)) (range Q) :=
    ((isCompact_range Q.continuous).isClosed.notMem_iff_infDist_pos
      ⟨_, Q.source_mem_range⟩).mp hvaQ
  set r := min (1 / (m : ℝ)) (infDist (xa, (0 : ℝ)) (range Q)) with hr
  have hrpos : 0 < r := lt_min (by positivity) hd
  have hr1 : r ≤ 1 / m := min_le_left _ _
  have hr2 : r ≤ infDist (xa, (0 : ℝ)) (range Q) := min_le_right _ _
  have hloc : ∀ w ∈ ball (xa, (0 : ℝ)) r, w ∈ range seg ∪ range Q ↔ w.2 = (xa, (0 : ℝ)).2 := by
    intro w hw
    have hw' : max (dist w.1 xa) (dist w.2 0) < r := by
      have := mem_ball.mp hw
      rwa [Prod.dist_eq] at this
    have hw1 : |w.1 - xa| < r := by
      have := lt_of_le_of_lt (le_max_left _ _) hw'
      rwa [Real.dist_eq] at this
    constructor
    · rintro (hws | hwQ)
      · rw [hseg, mem_range_hSegPath hlr] at hws
        exact hws.1
      · exfalso
        have h1 : infDist (xa, (0 : ℝ)) (range Q) ≤ dist (xa, (0 : ℝ)) w :=
          infDist_le_dist_of_mem hwQ
        rw [dist_comm] at h1
        linarith [mem_ball.mp hw]
    · intro hw2
      left
      rw [hseg, mem_range_hSegPath hlr]
      refine ⟨hw2, ?_, ?_⟩
      · linarith [(abs_lt.mp hw1).1]
      · linarith [(abs_lt.mp hw1).2]
  have hUC : Disjoint U (range seg ∪ range Q) := disjoint_of_subset_trace hU hCtrace
  have hcl : ((((⟨a - 1, by omega⟩ : Fin m) : ℕ) : ℝ) + 1) / m = xa := by
    show (((a - 1 : ℕ) : ℝ) + 1) / m = _
    rw [cast_pred ha0, sub_add_cancel]
  have hcr : (((⟨a, ham⟩ : Fin m) : ℕ) : ℝ) / m = xa := rfl
  rcases hsides with ⟨hup, hdown⟩ | ⟨hdown, hup⟩
  · obtain ⟨w₁, hw₁, hw₁b, hw₁s⟩ :=
      h.exists_collar_point ⟨a - 1, by omega⟩ hrpos hr1 true true
    obtain ⟨w₂, hw₂, hw₂b, hw₂s⟩ :=
      h.exists_collar_point ⟨a, ham⟩ hrpos hr1 false false
    simp only [if_true, Bool.false_eq_true, if_false] at hw₁ hw₁b hw₁s hw₂ hw₂b hw₂s
    rw [hcl] at hw₁b
    rw [hcr] at hw₂b
    exact not_preconnected_meets_upper_lower hJ hrpos hloc hU.preconnected hUC
      ⟨w₁, hup hw₁, hw₁b, hw₁s⟩ ⟨w₂, hdown hw₂, hw₂b, hw₂s⟩
  · obtain ⟨w₁, hw₁, hw₁b, hw₁s⟩ :=
      h.exists_collar_point ⟨a, ham⟩ hrpos hr1 true false
    obtain ⟨w₂, hw₂, hw₂b, hw₂s⟩ :=
      h.exists_collar_point ⟨a - 1, by omega⟩ hrpos hr1 false true
    simp only [if_true, Bool.false_eq_true, if_false] at hw₁ hw₁b hw₁s hw₂ hw₂b hw₂s
    rw [hcr] at hw₁b
    rw [hcl] at hw₂b
    exact not_preconnected_meets_upper_lower hJ hrpos hloc hU.preconnected hUC
      ⟨w₁, hup hw₁, hw₁b, hw₁s⟩ ⟨w₂, hdown hw₂, hw₂b, hw₂s⟩

end StraightPath

end
end FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing
