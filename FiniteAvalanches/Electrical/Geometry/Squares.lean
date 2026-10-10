module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic.Linarith

/-! Area packing for literal finite families of closed axis-aligned squares. -/

@[expose] public section

namespace FiniteAvalanches.Electrical.Geometry

open Set MeasureTheory
open scoped BigOperators Classical

/-- A closed square specified by its lower-left corner and nonnegative side. -/
structure Square where
  x : ℝ
  y : ℝ
  side : ℝ
  side_nonneg : 0 ≤ side

/-- The full closed carrier; a zero-side square is a point. -/
def Square.carrier (Q : Square) : Set (ℝ × ℝ) :=
  Icc Q.x (Q.x + Q.side) ×ˢ Icc Q.y (Q.y + Q.side)

/-- The open interior used for area disjointness. -/
def Square.openCarrier (Q : Square) : Set (ℝ × ℝ) :=
  Ioo Q.x (Q.x + Q.side) ×ˢ Ioo Q.y (Q.y + Q.side)

/-- A literal closed rectangle. -/
def rectangle (lx ux ly uy : ℝ) : Set (ℝ × ℝ) := Icc lx ux ×ˢ Icc ly uy

theorem Square.openCarrier_subset_carrier (Q : Square) : Q.openCarrier ⊆ Q.carrier :=
  Set.prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self

theorem Square.measurableSet_openCarrier (Q : Square) : MeasurableSet Q.openCarrier :=
  measurableSet_Ioo.prod measurableSet_Ioo

theorem Square.volume_openCarrier (Q : Square) :
    volume Q.openCarrier = ENNReal.ofReal (Q.side ^ 2) := by
  rw [Square.openCarrier, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo,
    Real.volume_Ioo]
  simp only [add_sub_cancel_left]
  rw [← ENNReal.ofReal_mul Q.side_nonneg]
  congr 1
  ring

theorem Square.area_openCarrier (Q : Square) : volume.real Q.openCarrier = Q.side ^ 2 := by
  rw [measureReal_def, Q.volume_openCarrier, ENNReal.toReal_ofReal (sq_nonneg _)]

theorem volume_rectangle (lx ux ly uy : ℝ) :
    volume (rectangle lx ux ly uy) =
      ENNReal.ofReal (ux - lx) * ENNReal.ofReal (uy - ly) := by
  rw [rectangle, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]

theorem area_rectangle (lx ux ly uy : ℝ) (hx : lx ≤ ux) (hy : ly ≤ uy) :
    volume.real (rectangle lx ux ly uy) = (ux - lx) * (uy - ly) := by
  rw [measureReal_def, volume_rectangle, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hx), ENNReal.toReal_ofReal (sub_nonneg.mpr hy)]

/-- The area bound is derived from actual disjoint open interiors and containment. -/
theorem sum_sq_side_le_area {I : Type*} (s : Finset I) (Q : I → Square)
    (hd : Set.PairwiseDisjoint (↑s) (fun i => (Q i).openCarrier))
    (lx ux ly uy : ℝ) (hx : lx ≤ ux) (hy : ly ≤ uy)
    (hQ : ∀ i ∈ s, (Q i).carrier ⊆ rectangle lx ux ly uy) :
    (∑ i ∈ s, (Q i).side ^ 2) ≤ (ux - lx) * (uy - ly) := by
  have hU : (⋃ i ∈ s, (Q i).openCarrier) ⊆ rectangle lx ux ly uy := by
    intro z hz
    obtain ⟨i, hi, hz⟩ := Set.mem_iUnion₂.mp hz
    exact hQ i hi ((Q i).openCarrier_subset_carrier hz)
  have hm : volume (rectangle lx ux ly uy) ≠ ⊤ := by
    rw [volume_rectangle]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have h := measureReal_mono hU hm
  rw [measureReal_biUnion_finset hd (fun i _ => (Q i).measurableSet_openCarrier)
    (fun i _ => by rw [(Q i).volume_openCarrier]; exact ENNReal.ofReal_ne_top),
    area_rectangle lx ux ly uy hx hy] at h
  simpa only [Square.area_openCarrier] using h

/-- A convenient scale equivalent to side plus distance from the split point. -/
def Square.scale (Q : Square) (epsilon y0 : ℝ) : ℝ :=
  max epsilon (max Q.side (max |Q.x| |Q.y - y0|))

theorem Square.scale_bounds (Q : Square) (epsilon y0 : ℝ) :
    epsilon ≤ Q.scale epsilon y0 ∧ Q.side ≤ Q.scale epsilon y0 ∧
    |Q.x| ≤ Q.scale epsilon y0 ∧ |Q.y-y0| ≤ Q.scale epsilon y0 := by
  unfold Square.scale
  exact ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)),
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

theorem Square.carrier_subset_box_of_scale_le (Q : Square) (epsilon y0 rho : ℝ)
    (hr : Q.scale epsilon y0 ≤ 2 * rho) :
    Q.carrier ⊆ rectangle (-4*rho) (4*rho) (y0-4*rho) (y0+4*rho) := by
  intro z hz
  obtain ⟨hx, hy⟩ := hz
  obtain ⟨_, hs, hqx, hqy⟩ := Q.scale_bounds epsilon y0
  have hx' := abs_le.mp (hqx.trans hr)
  have hy' := abs_le.mp (hqy.trans hr)
  have hs' := hs.trans hr
  have hn : 0 ≤ rho := by linarith [Q.side_nonneg]
  exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩,
    ⟨by linarith [hy.1], by linarith [hy.2]⟩⟩

/-- The three rectangle comparisons prove the local area bound, including the thin-strip case. -/
theorem sum_sq_side_le_local_area {I : Type*} (s : Finset I) (Q : I → Square)
    (hd : Set.PairwiseDisjoint (↑s) (fun i => (Q i).openCarrier))
    (M y0 rho : ℝ) (hM : 0 ≤ M) (hr : 0 ≤ rho)
    (hQ : ∀ i ∈ s, (Q i).carrier ⊆ rectangle 0 1 0 M)
    (hbox : ∀ i ∈ s, (Q i).carrier ⊆
      rectangle (-4*rho) (4*rho) (y0-4*rho) (y0+4*rho)) :
    (∑ i ∈ s, (Q i).side ^ 2) ≤ min (64*rho^2) (8*min 1 M*rho) := by
  have hb := sum_sq_side_le_area s Q hd (-4*rho) (4*rho)
    (y0-4*rho) (y0+4*rho) (by linarith) (by linarith) hbox
  have hv := sum_sq_side_le_area s Q hd (-4*rho) (4*rho) 0 M
    (by linarith) hM (fun i hi z hz => ⟨(hbox i hi hz).1, (hQ i hi hz).2⟩)
  have hh := sum_sq_side_le_area s Q hd 0 1 (y0-4*rho) (y0+4*rho)
    (by norm_num) (by linarith) (fun i hi z hz => ⟨(hQ i hi hz).1, (hbox i hi hz).2⟩)
  apply le_min
  · nlinarith only [hb]
  · by_cases h : M ≤ 1
    · rw [min_eq_right h]; nlinarith only [hv]
    · rw [min_eq_left (le_of_not_ge h)]; nlinarith only [hh]

end FiniteAvalanches.Electrical.Geometry
