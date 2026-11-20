import FiniteAvalanches.Support.Plane.OuterRedrawing.LocalSides
import FiniteAvalanches.Electrical.Geometry.OrientedDrawing

/-!
# Drawings with a straight boundary path

A simple path of a finite plane drawing is straight when its `i`-th vertex is
the point `(i / m, 0)` and its `i`-th edge runs along the horizontal segment
between consecutive vertices. Every other edge meets the unit segment only at
path vertices, at an endpoint of its parameter interval.

Above and below the interior of each path edge lies an open collar avoiding the
whole drawing. Each collar lies in a complementary component of the drawing or
misses it, and a component accumulating along the edge contains one of the two
collars. Near an interior path vertex, every other edge leaves the vertex on one
side of the horizontal line.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing

open Set Metric Bornology
open FiniteAvalanches.Electrical.Source (drawingTrace)

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- A simple path of a drawing lying on the horizontal unit segment, with its
`i`-th vertex at `(i / m, 0)`. -/
structure StraightPath (D : Drawing J) (m : ℕ) (path : Fin (m + 1) → V)
    (copies : Fin m → E) : Prop where
  pos : 0 < m
  injective : Function.Injective path
  ends : ∀ i, (J.left (copies i) = path i.castSucc ∧ J.right (copies i) = path i.succ) ∨
    (J.right (copies i) = path i.castSucc ∧ J.left (copies i) = path i.succ)
  point : ∀ i : Fin (m + 1), D.point (path i) = ((i : ℝ) / m, 0)
  curve_snd : ∀ (i : Fin m) t, (D.curve (copies i) t).2 = 0
  curve_fst : ∀ (i : Fin m) t, (i : ℝ) / m ≤ (D.curve (copies i) t).1 ∧
    (D.curve (copies i) t).1 ≤ ((i : ℝ) + 1) / m

/-- A complementary component of a drawing: preconnected, maximal, avoiding the
drawing, and unbounded. -/
structure OuterFace (D : Drawing J) (U : Set (ℝ × ℝ)) : Prop where
  preconnected : IsPreconnected U
  disjoint : Disjoint U (drawingTrace D)
  unbounded : ¬ IsBounded U
  maximal : ∀ K : Set (ℝ × ℝ), IsPreconnected K → Disjoint K (drawingTrace D) →
    (K ∩ U).Nonempty → K ⊆ U

variable {D : Drawing J} {m : ℕ} {path : Fin (m + 1) → V} {copies : Fin m → E}

/-- The initial parameter of a curve. -/
abbrev zeroParam : ArcParameter := ⟨0, by constructor <;> norm_num⟩

/-- The final parameter of a curve. -/
abbrev oneParam : ArcParameter := ⟨1, by constructor <;> norm_num⟩

/-- The horizontal unit segment. -/
def unitSeg : Set (ℝ × ℝ) := {z | z.2 = 0 ∧ 0 ≤ z.1 ∧ z.1 ≤ 1}

/-- Every point of the unit interval lies in one of the `m` closed subintervals. -/
theorem exists_index_of_mem_Icc {m : ℕ} (hm : 0 < m) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∃ i : Fin m, (i : ℝ) / m ≤ x ∧ x ≤ ((i : ℝ) + 1) / m := by
  have hmr : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  let k := min (⌊x * m⌋₊) (m - 1)
  have hk : k < m := lt_of_le_of_lt (min_le_right _ _) (by omega)
  refine ⟨⟨k, hk⟩, ?_, ?_⟩
  · change (k : ℝ) / m ≤ x
    rw [div_le_iff₀ hmr]
    calc (k : ℝ) ≤ ⌊x * m⌋₊ := by exact_mod_cast min_le_left _ _
      _ ≤ x * m := Nat.floor_le (mul_nonneg hx0 hmr.le)
  · change x ≤ ((k : ℝ) + 1) / m
    rw [le_div_iff₀ hmr]
    rcases le_total (⌊x * m⌋₊) (m - 1) with hle | hle
    · have hkeq : k = ⌊x * m⌋₊ := min_eq_left hle
      rw [hkeq]
      exact (Nat.lt_floor_add_one (x * m)).le
    · have hkeq : k = m - 1 := min_eq_right hle
      rw [hkeq]
      have : ((m - 1 : ℕ) : ℝ) + 1 = m := by
        rw [Nat.cast_sub (by omega : 1 ≤ m)]
        ring
      rw [this]
      nlinarith

/-- The part of the drawing other than one path edge. -/
def otherTrace (i : Fin m) : Set (ℝ × ℝ) :=
  range D.point ∪ ⋃ e ∈ ({copies i}ᶜ : Set E), range (D.curve e)

theorem isCompact_otherTrace (i : Fin m) : IsCompact (otherTrace (D := D) (copies := copies) i) :=
  (Set.finite_range D.point).isCompact.union
    ((Set.toFinite _).isCompact_biUnion fun e _ => isCompact_range (D.continuous e))

namespace StraightPath

variable (h : StraightPath D m path copies)
include h

theorem m_pos_real : (0 : ℝ) < m := Nat.cast_pos.mpr h.pos

theorem point_fst (j : Fin (m + 1)) : (D.point (path j)).1 = (j : ℝ) / m := by
  rw [h.point]

theorem point_castSucc_fst (i : Fin m) : (D.point (path i.castSucc)).1 = (i : ℝ) / m := by
  rw [h.point_fst]
  simp

theorem point_succ_fst (i : Fin m) : (D.point (path i.succ)).1 = ((i : ℝ) + 1) / m := by
  rw [h.point_fst]
  simp

/-- A path edge covers its horizontal segment. -/
theorem mem_range_curve (i : Fin m) {x : ℝ} (hx0 : (i : ℝ) / m ≤ x)
    (hx1 : x ≤ ((i : ℝ) + 1) / m) : (x, (0 : ℝ)) ∈ range (D.curve (copies i)) := by
  have hc : Continuous fun t => (D.curve (copies i) t).1 :=
    continuous_fst.comp (D.continuous (copies i))
  have hpre : IsPreconnected (range fun t => (D.curve (copies i) t).1) :=
    isPreconnected_range hc
  have hmem : x ∈ range fun t => (D.curve (copies i) t).1 := by
    rcases h.ends i with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · have h0 : (D.curve (copies i) zeroParam).1 = (i : ℝ) / m := by
        rw [D.start, hl, h.point_castSucc_fst]
      have h1 : (D.curve (copies i) oneParam).1 = ((i : ℝ) + 1) / m := by
        rw [D.finish, hr, h.point_succ_fst]
      exact hpre.Icc_subset ⟨zeroParam, h0⟩ ⟨oneParam, h1⟩ ⟨hx0, hx1⟩
    · have h0 : (D.curve (copies i) zeroParam).1 = ((i : ℝ) + 1) / m := by
        rw [D.start, hl, h.point_succ_fst]
      have h1 : (D.curve (copies i) oneParam).1 = (i : ℝ) / m := by
        rw [D.finish, hr, h.point_castSucc_fst]
      exact hpre.Icc_subset ⟨oneParam, h1⟩ ⟨zeroParam, h0⟩ ⟨hx0, hx1⟩
  obtain ⟨t, ht⟩ := hmem
  exact ⟨t, Prod.ext ht (h.curve_snd i t)⟩

/-- A path edge lies on the unit segment. -/
theorem curve_mem_unitSeg (i : Fin m) (t : ArcParameter) : D.curve (copies i) t ∈ unitSeg := by
  have hm := h.m_pos_real
  have hi : (i : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
  obtain ⟨h0, h1⟩ := h.curve_fst i t
  refine ⟨h.curve_snd i t, le_trans (by positivity) h0, le_trans h1 ?_⟩
  rw [div_le_one hm]
  exact hi

/-- An endpoint of a path edge is a path vertex. -/
theorem endpoint_of_param (i : Fin m) {s : ArcParameter} (hs : s.val = 0 ∨ s.val = 1) :
    ∃ j, D.curve (copies i) s = D.point (path j) := by
  rcases hs with hs | hs
  · have : s = zeroParam := Subtype.ext hs
    subst this
    rcases h.ends i with ⟨hl, _⟩ | ⟨_, hl⟩
    · exact ⟨_, by rw [D.start, hl]⟩
    · exact ⟨_, by rw [D.start, hl]⟩
  · have : s = oneParam := Subtype.ext hs
    subst this
    rcases h.ends i with ⟨_, hr⟩ | ⟨hr, _⟩
    · exact ⟨_, by rw [D.finish, hr]⟩
    · exact ⟨_, by rw [D.finish, hr]⟩

/-- Every other edge meets the unit segment only at path vertices and only at the
ends of its parameter interval. -/
theorem nonpath_curve_on_unitSeg {e : E} (he : e ∉ range copies) {t : ArcParameter}
    (ht : D.curve e t ∈ unitSeg) :
    (t.val = 0 ∨ t.val = 1) ∧ ∃ j, D.curve e t = D.point (path j) := by
  obtain ⟨hy, hx0, hx1⟩ := ht
  obtain ⟨i, hi0, hi1⟩ := exists_index_of_mem_Icc h.pos hx0 hx1
  obtain ⟨s, hs⟩ := h.mem_range_curve i hi0 hi1
  have hst : D.curve e t = D.curve (copies i) s := by
    rw [hs]
    exact Prod.ext rfl hy
  have hne : e ≠ copies i := fun heq => he ⟨i, heq.symm⟩
  obtain ⟨ht', hs'⟩ := D.intersects e (copies i) hne t s hst
  obtain ⟨j, hj⟩ := h.endpoint_of_param i hs'
  exact ⟨ht', j, hst.trans hj⟩

/-- A vertex outside the path is not on the unit segment. -/
theorem nonpath_point_not_mem_unitSeg {v : V} (hv : v ∉ range path) :
    D.point v ∉ unitSeg := by
  rintro ⟨hy, hx0, hx1⟩
  obtain ⟨i, hi0, hi1⟩ := exists_index_of_mem_Icc h.pos hx0 hx1
  obtain ⟨s, hs⟩ := h.mem_range_curve i hi0 hi1
  have hsv : D.curve (copies i) s = D.point v := by
    rw [hs]
    exact Prod.ext rfl hy.symm
  rcases (D.curve_vertex_iff (copies i) s v).mp hsv with ⟨_, hl⟩ | ⟨_, hr⟩
  · rcases h.ends i with ⟨hl', _⟩ | ⟨_, hl'⟩
    · exact hv ⟨_, (hl.symm.trans hl').symm⟩
    · exact hv ⟨_, (hl.symm.trans hl').symm⟩
  · rcases h.ends i with ⟨_, hr'⟩ | ⟨hr', _⟩
    · exact hv ⟨_, (hr.symm.trans hr').symm⟩
    · exact hv ⟨_, (hr.symm.trans hr').symm⟩

/-- A point strictly between consecutive path vertices is not a vertex position. -/
theorem not_vertex_between (i : Fin m) {x : ℝ} (hx0 : (i : ℝ) / m < x)
    (hx1 : x < ((i : ℝ) + 1) / m) (v : V) : D.point v ≠ (x, 0) := by
  intro hv
  by_cases hvp : v ∈ range path
  · obtain ⟨j, rfl⟩ := hvp
    have hj : x = (j : ℝ) / m := by
      have := h.point_fst j
      rw [hv] at this
      exact this
    have hm := h.m_pos_real
    rw [hj, div_lt_div_iff_of_pos_right hm] at hx0
    rw [hj, div_lt_div_iff_of_pos_right hm] at hx1
    have h1 : (i : ℕ) < (j : ℕ) := by exact_mod_cast hx0
    have h2 : (j : ℕ) < (i : ℕ) + 1 := by exact_mod_cast hx1
    omega
  · apply h.nonpath_point_not_mem_unitSeg hvp
    have hm := h.m_pos_real
    have hi : (i : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
    rw [hv]
    refine ⟨rfl, le_trans (by positivity) hx0.le, le_trans hx1.le ?_⟩
    rw [div_le_one hm]
    exact hi

/-- Points strictly inside a path edge avoid the rest of the drawing. -/
theorem not_mem_otherTrace (i : Fin m) {x : ℝ} (hx0 : (i : ℝ) / m < x)
    (hx1 : x < ((i : ℝ) + 1) / m) : (x, (0 : ℝ)) ∉ otherTrace (D := D) (copies := copies) i := by
  rintro (⟨v, hv⟩ | hz)
  · exact h.not_vertex_between i hx0 hx1 v hv
  · simp only [mem_iUnion, mem_compl_iff, mem_singleton_iff] at hz
    obtain ⟨e, he, t, ht⟩ := hz
    by_cases hep : e ∈ range copies
    · obtain ⟨j, rfl⟩ := hep
      have hji : j ≠ i := fun hji => he (by rw [hji])
      obtain ⟨hj0, hj1⟩ := h.curve_fst j t
      rw [ht] at hj0 hj1
      have hm := h.m_pos_real
      have h1 : (j : ℝ) < (i : ℝ) + 1 := by
        have := lt_of_le_of_lt hj0 hx1
        rwa [div_lt_div_iff_of_pos_right hm] at this
      have h2 : (i : ℝ) < (j : ℝ) + 1 := by
        have := lt_of_lt_of_le hx0 hj1
        rwa [div_lt_div_iff_of_pos_right hm] at this
      have h1' : (j : ℕ) < (i : ℕ) + 1 := by exact_mod_cast h1
      have h2' : (i : ℕ) < (j : ℕ) + 1 := by exact_mod_cast h2
      exact hji (Fin.ext (by omega))
    · have hseg : D.curve e t ∈ unitSeg := by
        have hm := h.m_pos_real
        have hi : (i : ℝ) + 1 ≤ m := by exact_mod_cast i.isLt
        rw [ht]
        refine ⟨rfl, le_trans (by positivity) hx0.le, le_trans hx1.le ?_⟩
        rw [div_le_one hm]
        exact hi
      obtain ⟨-, j, hj⟩ := h.nonpath_curve_on_unitSeg hep hseg
      exact h.not_vertex_between i hx0 hx1 (path j) (hj.symm.trans ht)

end StraightPath

/-- Distance from a point of the horizontal axis to the drawing other than one path edge. -/
def gap (D : Drawing J) (copies : Fin m → E) (i : Fin m) (x : ℝ) : ℝ :=
  infDist (x, (0 : ℝ)) (otherTrace (D := D) (copies := copies) i)

theorem continuous_gap (D : Drawing J) (copies : Fin m → E) (i : Fin m) :
    Continuous (gap D copies i) :=
  (continuous_infDist_pt _).comp (continuous_id.prodMk continuous_const)

/-- The open collar above the interior of a path edge. -/
def upperCollar (D : Drawing J) (copies : Fin m → E) (i : Fin m) : Set (ℝ × ℝ) :=
  {w | (i : ℝ) / m < w.1 ∧ w.1 < ((i : ℝ) + 1) / m ∧ 0 < w.2 ∧ w.2 < gap D copies i w.1}

/-- The open collar below the interior of a path edge. -/
def lowerCollar (D : Drawing J) (copies : Fin m → E) (i : Fin m) : Set (ℝ × ℝ) :=
  {w | (i : ℝ) / m < w.1 ∧ w.1 < ((i : ℝ) + 1) / m ∧ -gap D copies i w.1 < w.2 ∧ w.2 < 0}

namespace StraightPath

variable (h : StraightPath D m path copies)
include h

theorem gap_pos (i : Fin m) {x : ℝ} (hx0 : (i : ℝ) / m < x) (hx1 : x < ((i : ℝ) + 1) / m) :
    0 < gap D copies i x :=
  (isCompact_otherTrace (D := D) (copies := copies) i).isClosed.notMem_iff_infDist_pos
    ⟨D.point (path 0), Or.inl ⟨_, rfl⟩⟩ |>.mp (h.not_mem_otherTrace i hx0 hx1)

/-- The upper collar of a path edge is preconnected. -/
theorem isPreconnected_upperCollar (i : Fin m) : IsPreconnected (upperCollar D copies i) := by
  let f : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, p.2 * gap D copies i p.1)
  have hf : Continuous f :=
    continuous_fst.prodMk (continuous_snd.mul ((continuous_gap D copies i).comp continuous_fst))
  have himage : f '' (Ioo ((i : ℝ) / m) (((i : ℝ) + 1) / m) ×ˢ Ioo 0 1) =
      upperCollar D copies i := by
    ext w
    constructor
    · rintro ⟨p, ⟨⟨hp0, hp1⟩, ⟨ht0, ht1⟩⟩, rfl⟩
      have hg := h.gap_pos i hp0 hp1
      exact ⟨hp0, hp1, mul_pos ht0 hg, by nlinarith⟩
    · rintro ⟨hw0, hw1, hw2, hw3⟩
      have hg := h.gap_pos i hw0 hw1
      refine ⟨(w.1, w.2 / gap D copies i w.1), ⟨⟨hw0, hw1⟩, ⟨div_pos hw2 hg, ?_⟩⟩, ?_⟩
      · rw [div_lt_one hg]
        exact hw3
      · simp only [f]
        rw [div_mul_cancel₀ _ hg.ne']
  rw [← himage]
  exact ((isPreconnected_Ioo.prod isPreconnected_Ioo)).image f hf.continuousOn

/-- The lower collar of a path edge is preconnected. -/
theorem isPreconnected_lowerCollar (i : Fin m) : IsPreconnected (lowerCollar D copies i) := by
  let f : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, -(p.2 * gap D copies i p.1))
  have hf : Continuous f :=
    continuous_fst.prodMk
      ((continuous_snd.mul ((continuous_gap D copies i).comp continuous_fst)).neg)
  have himage : f '' (Ioo ((i : ℝ) / m) (((i : ℝ) + 1) / m) ×ˢ Ioo 0 1) =
      lowerCollar D copies i := by
    ext w
    constructor
    · rintro ⟨p, ⟨⟨hp0, hp1⟩, ⟨ht0, ht1⟩⟩, rfl⟩
      have hg := h.gap_pos i hp0 hp1
      exact ⟨hp0, hp1, by nlinarith, by nlinarith [mul_pos ht0 hg]⟩
    · rintro ⟨hw0, hw1, hw2, hw3⟩
      have hg := h.gap_pos i hw0 hw1
      refine ⟨(w.1, -w.2 / gap D copies i w.1), ⟨⟨hw0, hw1⟩, ⟨div_pos (by linarith) hg, ?_⟩⟩, ?_⟩
      · rw [div_lt_one hg]
        linarith
      · simp only [f]
        rw [div_mul_cancel₀ _ hg.ne', neg_neg]
  rw [← himage]
  exact ((isPreconnected_Ioo.prod isPreconnected_Ioo)).image f hf.continuousOn

/-- A point of the drawing off the horizontal axis lies at least `gap` away from
the axis point below or above it. -/
theorem gap_le_of_mem_trace (i : Fin m) {w : ℝ × ℝ} (hw : w ∈ drawingTrace D)
    (hw2 : w.2 ≠ 0) : gap D copies i w.1 ≤ |w.2| := by
  have hmem : w ∈ otherTrace (D := D) (copies := copies) i := by
    rcases hw with hv | hc
    · exact Or.inl hv
    · simp only [mem_iUnion] at hc
      obtain ⟨e, t, ht⟩ := hc
      by_cases he : e = copies i
      · subst he
        exact absurd (ht ▸ h.curve_snd i t) hw2
      · exact Or.inr (mem_biUnion (by simpa using he) ⟨t, ht⟩)
  calc gap D copies i w.1 ≤ dist (w.1, (0 : ℝ)) w := infDist_le_dist_of_mem hmem
    _ = |w.2| := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq, zero_sub, abs_neg, max_eq_right (abs_nonneg _)]

theorem disjoint_upperCollar (i : Fin m) : Disjoint (upperCollar D copies i) (drawingTrace D) := by
  rw [Set.disjoint_left]
  rintro w ⟨-, -, hw2, hw3⟩ hw
  have := h.gap_le_of_mem_trace i hw hw2.ne'
  rw [abs_of_pos hw2] at this
  linarith

theorem disjoint_lowerCollar (i : Fin m) : Disjoint (lowerCollar D copies i) (drawingTrace D) := by
  rw [Set.disjoint_left]
  rintro w ⟨-, -, hw2, hw3⟩ hw
  have := h.gap_le_of_mem_trace i hw hw3.ne
  rw [abs_of_neg hw3] at this
  linarith

/-- A complementary component accumulating along a path edge contains one of
its two collars. -/
theorem upper_or_lower_of_closure {U : Set (ℝ × ℝ)} (hU : OuterFace D U) (i : Fin m)
    (hfront : ∀ t, D.curve (copies i) t ∈ closure U) :
    upperCollar D copies i ⊆ U ∨ lowerCollar D copies i ⊆ U := by
  have hm := h.m_pos_real
  set x₀ : ℝ := ((i : ℝ) + 1 / 2) / m with hx₀
  have hx₀0 : (i : ℝ) / m < x₀ := by
    rw [hx₀, div_lt_div_iff_of_pos_right hm]
    linarith
  have hx₀1 : x₀ < ((i : ℝ) + 1) / m := by
    rw [hx₀, div_lt_div_iff_of_pos_right hm]
    linarith
  obtain ⟨t₀, ht₀⟩ := h.mem_range_curve i hx₀0.le hx₀1.le
  have hz₀ : (x₀, (0 : ℝ)) ∈ closure U := ht₀ ▸ hfront t₀
  set g₀ := gap D copies i x₀
  have hg₀ : 0 < g₀ := h.gap_pos i hx₀0 hx₀1
  set ε : ℝ := min g₀ (1 / (4 * m)) / 2 with hε
  have hεpos : 0 < ε := by positivity
  have hεg : ε ≤ g₀ / 2 := by
    rw [hε]
    have := min_le_left g₀ (1 / (4 * m))
    linarith
  have hεm : ε ≤ 1 / (8 * m) := by
    rw [hε]
    have := min_le_right g₀ (1 / (4 * m))
    have h8 : 1 / (4 * (m : ℝ)) / 2 = 1 / (8 * m) := by field_simp; ring
    linarith
  obtain ⟨u, hu, hdist⟩ := Metric.mem_closure_iff.mp hz₀ ε hεpos
  have hdist' : max (dist x₀ u.1) (dist (0 : ℝ) u.2) < ε := by
    have := hdist
    rw [Prod.dist_eq] at this
    exact this
  have hu1 : |u.1 - x₀| < ε := by
    have h1 := lt_of_le_of_lt (le_max_left _ _) hdist'
    rwa [Real.dist_eq, abs_sub_comm] at h1
  have hu2 : |u.2| < ε := by
    have h1 := lt_of_le_of_lt (le_max_right _ _) hdist'
    rwa [Real.dist_eq, zero_sub, abs_neg] at h1
  have hu1' : (i : ℝ) / m < u.1 ∧ u.1 < ((i : ℝ) + 1) / m := by
    have h4 : x₀ - (i : ℝ) / m = 1 / (2 * m) := by rw [hx₀]; field_simp; ring
    have h5 : ((i : ℝ) + 1) / m - x₀ = 1 / (2 * m) := by rw [hx₀]; field_simp; ring
    have h6 : 1 / (8 * (m : ℝ)) < 1 / (2 * m) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      linarith
    constructor <;> linarith [(abs_lt.mp hu1).1, (abs_lt.mp hu1).2]
  have hgu : ε < gap D copies i u.1 := by
    have hlip := infDist_le_infDist_add_dist (x := (x₀, (0 : ℝ))) (y := (u.1, (0 : ℝ)))
      (s := otherTrace (D := D) (copies := copies) i)
    have hd : dist (x₀, (0 : ℝ)) (u.1, (0 : ℝ)) = |u.1 - x₀| := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq, abs_sub_comm, max_eq_left (abs_nonneg _)]
    change g₀ ≤ gap D copies i u.1 + _ at hlip
    rw [hd] at hlip
    linarith
  have hu2ne : u.2 ≠ 0 := by
    intro hu20
    obtain ⟨t, ht⟩ := h.mem_range_curve i hu1'.1.le hu1'.2.le
    have hut : u = D.curve (copies i) t := by
      rw [ht]
      exact Prod.ext rfl hu20
    exact hU.disjoint.ne_of_mem hu (Or.inr (mem_iUnion.mpr ⟨copies i, t, hut.symm⟩)) rfl
  rcases lt_or_gt_of_ne hu2ne with hneg | hpos
  · right
    refine hU.maximal _ (h.isPreconnected_lowerCollar i) (h.disjoint_lowerCollar i) ⟨u, ?_, hu⟩
    refine ⟨hu1'.1, hu1'.2, ?_, hneg⟩
    have := (abs_lt.mp hu2).1
    linarith
  · left
    refine hU.maximal _ (h.isPreconnected_upperCollar i) (h.disjoint_upperCollar i) ⟨u, ?_, hu⟩
    refine ⟨hu1'.1, hu1'.2, hpos, ?_⟩
    have := (abs_lt.mp hu2).2
    linarith

end StraightPath

/-- A curve leaving a point of the horizontal line, and not returning to the
line near that point at interior parameters, starts on one side of the line. -/
theorem sign_near_zero {γ : ArcParameter → ℝ × ℝ} (hγ : Continuous γ) {c δ : ℝ}
    (hδ : 0 < δ) (h0 : γ zeroParam = (c, 0))
    (hoff : ∀ t : ArcParameter, 0 < t.val → t.val < 1 → (γ t).2 = 0 → δ ≤ |(γ t).1 - c|) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ 1 ∧ ((∀ t : ArcParameter, 0 < t.val → t.val < τ → 0 < (γ t).2) ∨
      (∀ t : ArcParameter, 0 < t.val → t.val < τ → (γ t).2 < 0)) := by
  obtain ⟨τ₀, hτ₀, hcont⟩ := Metric.continuous_iff.mp hγ zeroParam δ hδ
  set τ := min τ₀ 1 with hτ
  have hτpos : 0 < τ := lt_min hτ₀ one_pos
  have hne : ∀ t : ArcParameter, 0 < t.val → t.val < τ → (γ t).2 ≠ 0 := by
    intro t ht0 htτ hzero
    have hd : dist t zeroParam < τ₀ := by
      rw [Subtype.dist_eq, Real.dist_eq]
      simp only [sub_zero, abs_of_pos ht0]
      exact lt_of_lt_of_le htτ (min_le_left _ _)
    have h1 := hcont t hd
    rw [h0, Prod.dist_eq] at h1
    have h1' : max (dist (γ t).1 c) (dist (γ t).2 0) < δ := h1
    have h2 := hoff t ht0 (lt_of_lt_of_le htτ (min_le_right _ _)) hzero
    have h3 := lt_of_le_of_lt (le_max_left _ _) h1'
    rw [Real.dist_eq] at h3
    linarith
  let f : ℝ → ℝ := fun x => (γ (Set.projIcc 0 1 zero_le_one x)).2
  have hf : Continuous f := continuous_snd.comp (hγ.comp continuous_projIcc)
  have hfval : ∀ t : ArcParameter, f t.val = (γ t).2 := by
    intro t
    simp only [f, Set.projIcc_val]
  refine ⟨τ, hτpos, min_le_right _ _, ?_⟩
  by_cases hex : ∃ t : ArcParameter, 0 < t.val ∧ t.val < τ ∧ 0 < (γ t).2
  · left
    obtain ⟨t₁, ht₁0, ht₁τ, ht₁⟩ := hex
    intro t ht0 htτ
    by_contra hneg
    have hlt : (γ t).2 < 0 := lt_of_le_of_ne (not_lt.mp hneg) (hne t ht0 htτ)
    have hivt := intermediate_value_uIcc (a := t₁.val) (b := t.val) hf.continuousOn
    have h0mem : (0 : ℝ) ∈ uIcc (f t₁.val) (f t.val) := by
      rw [hfval, hfval]
      exact mem_uIcc.mpr (Or.inr ⟨hlt.le, ht₁.le⟩)
    obtain ⟨s, hs, hfs⟩ := hivt h0mem
    have hs0 : 0 < s := by
      rcases mem_uIcc.mp hs with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
    have hsτ : s < τ := by
      rcases mem_uIcc.mp hs with ⟨_, h2⟩ | ⟨_, h2⟩ <;> linarith
    have hs1 : s ≤ 1 := le_trans hsτ.le (min_le_right _ _)
    exact hne ⟨s, hs0.le, hs1⟩ hs0 hsτ (by rw [← hfval]; exact hfs)
  · right
    intro t ht0 htτ
    push Not at hex
    exact lt_of_le_of_ne (hex t ht0 htτ) (hne t ht0 htτ)

end
end FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing
