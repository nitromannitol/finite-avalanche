import FiniteAvalanches.Support.Plane.OuterRedrawing.PartialDrawing

/-!
# Square realizations of a boundary path

A square realization of a selection draws it in the closed square `[-1, 1]²`
with a stretch `p, …, q` of the boundary path along the top edge, its vertices
equally spaced from the top left corner to the top right corner, and with no
other contact with the boundary of the square. At each path vertex it keeps a
free cusp: an embedded triangle inside the square with its apex at the vertex,
meeting the drawing only at the apex. Distinct cusps are disjoint.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing

open Set Metric

noncomputable section

variable {V E : Type} {J : CopiedGraph V E}

/-- The standard cusp: the triangle with apex at the origin. -/
def cuspTri : Set (ℝ × ℝ) := {w | 0 ≤ w.1 ∧ w.1 ≤ 1 ∧ |w.2| ≤ w.1}

/-- The horizontal position of the `i`-th vertex of the stretch `p, …, q` on the top edge. -/
def topPos (p q : ℕ) (i : ℕ) : ℝ := -1 + 2 * ((i : ℝ) - p) / ((q : ℝ) - p)

theorem topPos_left (p q : ℕ) : topPos p q p = -1 := by
  simp [topPos]

theorem topPos_right {p q : ℕ} (hpq : p < q) : topPos p q q = 1 := by
  have : ((q : ℝ) - p) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hpq.ne')
  simp only [topPos]
  field_simp
  ring

theorem topPos_mono {p q : ℕ} (hpq : p < q) {i j : ℕ} (hij : i ≤ j) :
    topPos p q i ≤ topPos p q j := by
  have hqp : (0 : ℝ) < (q : ℝ) - p := sub_pos.mpr (by exact_mod_cast hpq)
  simp only [topPos]
  have : ((i : ℝ) - p) ≤ (j : ℝ) - p := by
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    linarith
  have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left this (by norm_num : (0:ℝ) ≤ 2))
    hqp.le
  linarith

/-- A drawing of a selection in the square with a stretch of the path on its top edge. -/
structure SquareRealization (J : CopiedGraph V E) (S : Set V) (T : Set E) {m : ℕ}
    (path : Fin (m + 1) → V) (copies : Fin m → E) (p q : ℕ) extends PartialDrawing J S T where
  trace_sub : toPartialDrawing.trace ⊆ closedBall 0 1
  path_point : ∀ i : Fin (m + 1), p ≤ (i : ℕ) → (i : ℕ) ≤ q →
    point (path i) = (topPos p q i, 1)
  path_curve : ∀ i : Fin m, p ≤ (i : ℕ) → (i : ℕ) < q → ∀ t,
    (curve (copies i) t).2 = 1 ∧ topPos p q i ≤ (curve (copies i) t).1 ∧
      (curve (copies i) t).1 ≤ topPos p q ((i : ℕ) + 1)
  boundary : ∀ z ∈ toPartialDrawing.trace, z ∉ ball 0 1 → z.2 = 1
  cusp : Fin (m + 1) → ℝ × ℝ → ℝ × ℝ
  cusp_cont : ∀ i : Fin (m + 1), p ≤ (i : ℕ) → (i : ℕ) ≤ q → ContinuousOn (cusp i) cuspTri
  cusp_inj : ∀ i : Fin (m + 1), p ≤ (i : ℕ) → (i : ℕ) ≤ q → InjOn (cusp i) cuspTri
  cusp_tip : ∀ i : Fin (m + 1), p ≤ (i : ℕ) → (i : ℕ) ≤ q → cusp i 0 = point (path i)
  cusp_ball : ∀ i : Fin (m + 1), p ≤ (i : ℕ) → (i : ℕ) ≤ q → ∀ w ∈ cuspTri, w ≠ 0 →
    cusp i w ∈ ball 0 1
  cusp_free : ∀ i : Fin (m + 1), p ≤ (i : ℕ) → (i : ℕ) ≤ q → ∀ w ∈ cuspTri, w ≠ 0 →
    cusp i w ∉ toPartialDrawing.trace
  cusp_disj : ∀ i j : Fin (m + 1), p ≤ (i : ℕ) → (i : ℕ) ≤ q → p ≤ (j : ℕ) → (j : ℕ) ≤ q →
    i ≠ j → ∀ w ∈ cuspTri, ∀ w' ∈ cuspTri, cusp i w ≠ cusp j w'

theorem mem_closedBall_iff' {w : ℝ × ℝ} : w ∈ closedBall (0 : ℝ × ℝ) 1 ↔ |w.1| ≤ 1 ∧ |w.2| ≤ 1 := by
  rw [mem_closedBall, dist_zero_right, Prod.norm_def, max_le_iff, Real.norm_eq_abs,
    Real.norm_eq_abs]

theorem mem_ball_iff' {w : ℝ × ℝ} : w ∈ ball (0 : ℝ × ℝ) 1 ↔ |w.1| < 1 ∧ |w.2| < 1 := by
  rw [mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff, Real.norm_eq_abs, Real.norm_eq_abs]

/-- The affine squeeze of the square onto the vertical strip `[-1 + 2a, -1 + 2b] × [-1, 1]`. -/
def squeeze (a b : ℝ) (w : ℝ × ℝ) : ℝ × ℝ := (-1 + 2 * a + (b - a) * (w.1 + 1), w.2)

theorem continuous_squeeze (a b : ℝ) : Continuous (squeeze a b) := by
  unfold squeeze
  fun_prop

theorem squeeze_injective {a b : ℝ} (hab : a < b) : Function.Injective (squeeze a b) := by
  intro w w' h
  simp only [squeeze, Prod.mk.injEq] at h
  have h1 : (b - a) * (w.1 + 1) = (b - a) * (w'.1 + 1) := by linarith [h.1]
  have h2 := mul_left_cancel₀ (sub_ne_zero.mpr hab.ne') h1
  exact Prod.ext (by linarith) h.2

theorem squeeze_mem_closedBall {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) {w : ℝ × ℝ}
    (hw : w ∈ closedBall (0 : ℝ × ℝ) 1) : squeeze a b w ∈ closedBall (0 : ℝ × ℝ) 1 := by
  rw [mem_closedBall_iff'] at hw ⊢
  obtain ⟨h1, h2⟩ := hw
  rw [abs_le] at h1
  refine ⟨?_, h2⟩
  simp only [squeeze]
  rw [abs_le]
  constructor <;> nlinarith

theorem squeeze_mem_ball {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) {w : ℝ × ℝ}
    (hw : w ∈ ball (0 : ℝ × ℝ) 1) : squeeze a b w ∈ ball (0 : ℝ × ℝ) 1 := by
  rw [mem_ball_iff'] at hw ⊢
  obtain ⟨h1, h2⟩ := hw
  rw [abs_lt] at h1
  refine ⟨?_, h2⟩
  simp only [squeeze]
  rw [abs_lt]
  constructor <;> nlinarith

theorem squeeze_fst_le {a b : ℝ} (hab : a < b) {w : ℝ × ℝ} (hw : w.1 ≤ 1) :
    (squeeze a b w).1 ≤ -1 + 2 * b := by
  simp only [squeeze]
  nlinarith

theorem squeeze_fst_lt {a b : ℝ} (hab : a < b) {w : ℝ × ℝ} (hw : w.1 < 1) :
    (squeeze a b w).1 < -1 + 2 * b := by
  simp only [squeeze]
  nlinarith

theorem squeeze_fst_ge {a b : ℝ} (hab : a < b) {w : ℝ × ℝ} (hw : -1 ≤ w.1) :
    -1 + 2 * a ≤ (squeeze a b w).1 := by
  simp only [squeeze]
  nlinarith

theorem squeeze_fst_gt {a b : ℝ} (hab : a < b) {w : ℝ × ℝ} (hw : -1 < w.1) :
    -1 + 2 * a < (squeeze a b w).1 := by
  simp only [squeeze]
  nlinarith

/-- Squeezing positions of a sub-stretch onto the positions of the whole stretch. -/
theorem squeeze_topPos {p q : ℕ} (hpq : p < q) {r s : ℕ} (hrs : r < s) (i : ℕ) :
    -1 + 2 * (((r : ℝ) - p) / ((q : ℝ) - p)) +
        (((s : ℝ) - p) / ((q : ℝ) - p) - ((r : ℝ) - p) / ((q : ℝ) - p)) * (topPos r s i + 1) =
      topPos p q i := by
  have hqp : ((q : ℝ) - p) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : q ≠ p))
  have hsr : ((s : ℝ) - r) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (by omega : s ≠ r))
  simp only [topPos]
  field_simp
  ring

end
end FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing
