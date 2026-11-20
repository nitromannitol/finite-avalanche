import FiniteAvalanches.Support.Plane.OuterRedrawing.BaseCollar
import FiniteAvalanches.Support.Plane.OuterRedrawing.SquareRealization

/-!
# Square realization of a stretch attached from below

Let every selected off-path edge leave the interior vertices of a stretch from
below. The stretch and the upper boundary of its free collar form a Jordan curve,
and a plane homeomorphism carries it onto the boundary of the square, the stretch
onto the top edge with equally spaced vertices. The selected drawing off the
stretch lies in the unbounded region, so after the inversion in the boundary of
the square it lies in the open square. Small curved triangles in the collars
below the path edges, with apexes at the path vertices, become the free cusps.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing

open Set Metric Bornology Schoenflies unitInterval
open FiniteAvalanches.Electrical.Source (drawingTrace)
open scoped Classical

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}
variable {D : Drawing J} {m : ℕ} {path : Fin (m + 1) → V} {copies : Fin m → E}

/-- The collar distance below a path edge, capped at one. -/
def cuspHeight (D : Drawing J) (copies : Fin m → E) (j : Fin m) (x : ℝ) : ℝ :=
  min (gap D copies j x) 1

/-- A curved triangle below a path edge, with apex `(x₀, 0)` and opening in the
horizontal direction `κ`. -/
def baseCusp (D : Drawing J) (copies : Fin m → E) (j : Fin m) (x₀ κ : ℝ) (w : ℝ × ℝ) :
    ℝ × ℝ :=
  (x₀ + κ * w.1, -(cuspHeight D copies j (x₀ + κ * w.1) * (3 * w.1 + w.2)) / 8)

theorem continuous_baseCusp (D : Drawing J) (copies : Fin m → E) (j : Fin m) (x₀ κ : ℝ) :
    Continuous (baseCusp D copies j x₀ κ) := by
  have hg := continuous_gap D copies j
  have hc : Continuous (cuspHeight D copies j) := hg.min continuous_const
  unfold baseCusp
  exact Continuous.prodMk (by fun_prop)
    (((hc.comp (by fun_prop)).mul (by fun_prop)).neg.div_const 8)

theorem baseCusp_zero (D : Drawing J) (copies : Fin m → E) (j : Fin m) (x₀ κ : ℝ) :
    baseCusp D copies j x₀ κ 0 = (x₀, 0) := by
  simp [baseCusp]

theorem cuspTri_fst_pos {w : ℝ × ℝ} (hw : w ∈ cuspTri) (hw0 : w ≠ 0) : 0 < w.1 := by
  obtain ⟨h0, -, h2⟩ := hw
  rcases eq_or_lt_of_le h0 with h | h
  · exfalso
    apply hw0
    have : w.2 = 0 := abs_nonpos_iff.mp (h ▸ h2)
    exact Prod.ext h.symm this
  · exact h

theorem baseCusp_fst (D : Drawing J) (copies : Fin m → E) (j : Fin m) (x₀ κ : ℝ) (w : ℝ × ℝ) :
    (baseCusp D copies j x₀ κ w).1 = x₀ + κ * w.1 := rfl

namespace StraightPath

variable (h : StraightPath D m path copies)
include h

theorem baseCusp_mem_lowerCollar (j : Fin m) {x₀ κ : ℝ}
    (hint : ∀ u : ℝ, 0 < u → u ≤ 1 → (j : ℝ) / m < x₀ + κ * u ∧ x₀ + κ * u < ((j : ℝ) + 1) / m)
    {w : ℝ × ℝ} (hw : w ∈ cuspTri) (hw0 : w ≠ 0) :
    baseCusp D copies j x₀ κ w ∈ lowerCollar D copies j := by
  have hu := cuspTri_fst_pos hw hw0
  obtain ⟨-, hu1, hv⟩ := hw
  obtain ⟨hx0, hx1⟩ := hint w.1 hu hu1
  have hg := h.gap_pos j hx0 hx1
  have hc0 : 0 < cuspHeight D copies j (x₀ + κ * w.1) := lt_min hg one_pos
  have hcg : cuspHeight D copies j (x₀ + κ * w.1) ≤ gap D copies j (x₀ + κ * w.1) :=
    min_le_left _ _
  rw [abs_le] at hv
  refine ⟨hx0, hx1, ?_, ?_⟩
  · change -gap D copies j (x₀ + κ * w.1) <
      -(cuspHeight D copies j (x₀ + κ * w.1) * (3 * w.1 + w.2)) / 8
    have : cuspHeight D copies j (x₀ + κ * w.1) * (3 * w.1 + w.2) ≤
        gap D copies j (x₀ + κ * w.1) * 4 := by
      have h1 : 3 * w.1 + w.2 ≤ 4 := by linarith
      calc cuspHeight D copies j (x₀ + κ * w.1) * (3 * w.1 + w.2)
          ≤ cuspHeight D copies j (x₀ + κ * w.1) * 4 :=
            mul_le_mul_of_nonneg_left h1 hc0.le
        _ ≤ gap D copies j (x₀ + κ * w.1) * 4 := by linarith
    linarith
  · change -(cuspHeight D copies j (x₀ + κ * w.1) * (3 * w.1 + w.2)) / 8 < 0
    have : 0 < cuspHeight D copies j (x₀ + κ * w.1) * (3 * w.1 + w.2) :=
      mul_pos hc0 (by linarith)
    linarith

theorem injOn_baseCusp (j : Fin m) {x₀ κ : ℝ} (hκ : κ ≠ 0)
    (hint : ∀ u : ℝ, 0 < u → u ≤ 1 → (j : ℝ) / m < x₀ + κ * u ∧ x₀ + κ * u < ((j : ℝ) + 1) / m) :
    InjOn (baseCusp D copies j x₀ κ) cuspTri := by
  intro w hw w' hw' heq
  obtain ⟨h1, h2⟩ := Prod.mk.inj heq
  have hu : w.1 = w'.1 := mul_left_cancel₀ hκ (by linarith)
  by_cases hw0 : w = 0
  · rw [hw0] at hu ⊢
    have : w'.1 = 0 := hu.symm
    have hv : w'.2 = 0 := abs_nonpos_iff.mp (this ▸ hw'.2.2)
    exact (Prod.ext this hv).symm
  · have hupos := cuspTri_fst_pos hw hw0
    obtain ⟨hx0, hx1⟩ := hint w.1 hupos hw.2.1
    have hc0 : 0 < cuspHeight D copies j (x₀ + κ * w.1) := lt_min (h.gap_pos j hx0 hx1) one_pos
    rw [← hu] at h2
    have h3 : cuspHeight D copies j (x₀ + κ * w.1) * (3 * w.1 + w.2) =
        cuspHeight D copies j (x₀ + κ * w.1) * (3 * w.1 + w'.2) := by linarith
    have h4 := mul_left_cancel₀ hc0.ne' h3
    exact Prod.ext hu (by linarith)

end StraightPath

/-- The position on the top edge of a point of the stretch. -/
theorem stretch_topPos {m p q : ℕ} (hm : (0 : ℝ) < m) (hpq : p < q) (x : ℝ) :
    -1 + 2 * ((x / m - (p : ℝ) / m) / ((q : ℝ) / m - (p : ℝ) / m)) =
      -1 + 2 * (x - p) / ((q : ℝ) - p) := by
  have hqp : ((q : ℝ) - p) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hpq.ne')
  field_simp

theorem stretch_mono {a b : ℝ} (hab : a < b) {x y : ℝ} (hxy : x ≤ y) :
    -1 + 2 * ((x - a) / (b - a)) ≤ -1 + 2 * ((y - a) / (b - a)) := by
  have := div_le_div_of_nonneg_right (sub_le_sub_right hxy a) (sub_pos.mpr hab).le
  linarith

namespace StraightPath

variable (h : StraightPath D m path copies)
include h

/-- A stretch whose off-path edges leave its interior vertices from below has a
square realization. -/
theorem exists_squareRealization_of_endsBelow (S : Set V) (T : Finset E) {p q : ℕ}
    (hpq : p < q) (hqm : q ≤ m) (hbelow : EndsBelow D path copies T p q) :
    Nonempty (SquareRealization J S T path copies p q) := by
  have hm := h.m_pos_real
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (p : ℝ) / m := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (q : ℝ) / m := ⟨_, rfl⟩
  have hab : a < b := by
    rw [ha, hb]
    exact div_lt_div_of_pos_right (by exact_mod_cast hpq) hm
  have hpos : ∀ x, a < x → x < b → 0 < collarHeight D S T a b x := by
    intro x hx0 hx1
    rw [ha] at hx0 ⊢
    rw [hb] at hx1 ⊢
    exact h.collarHeight_pos S T hqm hbelow hx0 hx1
  obtain ⟨F, hFb, -, hFout⟩ := ArcPair.exists_homeomorph (arcPair_collar D S T hab hpos)
    arcPair_square
  let Ψ : ℝ × ℝ → ℝ × ℝ := squareInversion ∘ F
  let onStretch : ℝ × ℝ → Prop := fun z => z.2 = 0 ∧ a ≤ z.1 ∧ z.1 ≤ b
  have hFst : ∀ z, onStretch z → (z.1 - a) / (b - a) ∈ I ∧
      F z = topEdge ((z.1 - a) / (b - a)) := by
    rintro z ⟨h2, h0, h1⟩
    have hs : (z.1 - a) / (b - a) ∈ I :=
      ⟨div_nonneg (by linarith) (by linarith), (div_le_one (by linarith)).mpr (by linarith)⟩
    have hz : collarBase a b ((z.1 - a) / (b - a)) = z := by
      simp only [collarBase, lerp]
      rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hab.ne'), add_sub_cancel]
      exact Prod.ext rfl h2.symm
    refine ⟨hs, ?_⟩
    have := hFb _ hs
    rwa [hz] at this
  have hFst1 : ∀ z, onStretch z → ‖F z‖ = 1 := by
    intro z hz
    obtain ⟨hs, he⟩ := hFst z hz
    rw [he]
    exact norm_eq_one_of_mem_squareBoundary (Or.inl ⟨_, hs, rfl⟩)
  have hst : ∀ z, onStretch z → Ψ z = (-1 + 2 * ((z.1 - a) / (b - a)), 1) := by
    intro z hz
    change squareInversion (F z) = _
    rw [squareInversion_of_norm_eq_one (hFst1 z hz), (hFst z hz).2]
    rfl
  have hfar : ∀ z : ℝ × ℝ, (z.2 < 0 ∨ (z.2 = 0 ∧ (z.1 < a ∨ b < z.1)) ∨
      (0 < z.2 ∧ collarHeight D S T a b z.1 < z.2)) → 1 < ‖F z‖ :=
    fun z hz => one_lt_norm_of_mem_outside (hFout z (mem_outside_collar D S T hab hpos hz))
  let good : ℝ × ℝ → Prop := fun z => onStretch z ∨ 1 < ‖F z‖
  have hgood_trace : ∀ z ∈ (Drawing.toPartial D S T).trace, good z := by
    intro z hz
    rcases lt_trichotomy z.2 0 with h2 | h2 | h2
    · exact Or.inr (hfar z (Or.inl h2))
    · by_cases hza : a ≤ z.1 ∧ z.1 ≤ b
      · exact Or.inl ⟨h2, hza⟩
      · rw [not_and_or, not_le, not_le] at hza
        exact Or.inr (hfar z (Or.inr (Or.inl ⟨h2, hza⟩)))
    · exact Or.inr (hfar z (Or.inr (Or.inr ⟨h2, collarHeight_lt D S T a b hz h2⟩)))
  have hgood_ne : ∀ z, good z → F z ≠ 0 := by
    rintro z (hz | hz) h0
    · have := hFst1 z hz
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    · rw [h0, norm_zero] at hz
      linarith
  have hΨat : ∀ z, good z → ContinuousAt Ψ z := fun z hz =>
    (continuousAt_squareInversion (hgood_ne z hz)).comp F.continuous.continuousAt
  have hΨinj : Function.Injective Ψ := squareInversion_injective.comp F.injective
  have hΨnorm : ∀ z, 1 < ‖F z‖ → ‖Ψ z‖ < 1 := by
    intro z hz
    change ‖squareInversion (F z)‖ < 1
    rw [norm_squareInversion]
    exact inv_lt_one_of_one_lt₀ hz
  have hcont : ContinuousOn Ψ (Drawing.toPartial D S T).trace :=
    fun z hz => (hΨat z (hgood_trace z hz)).continuousWithinAt
  let P := (Drawing.toPartial D S T).map Ψ hcont hΨinj.injOn
  have hPtr : P.trace = Ψ '' (Drawing.toPartial D S T).trace := PartialDrawing.map_trace _ _ _ _
  have hvert : ∀ i : Fin (m + 1), p ≤ (i : ℕ) → (i : ℕ) ≤ q → onStretch (D.point (path i)) := by
    intro i hi1 hi2
    rw [h.point]
    refine ⟨rfl, ?_, ?_⟩
    · rw [ha]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hi1) hm.le
    · rw [hb]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hi2) hm.le
  have hΨst1 : ∀ z, onStretch z → ‖Ψ z‖ = 1 := by
    intro z hz
    change ‖squareInversion (F z)‖ = 1
    rw [norm_squareInversion, hFst1 z hz, inv_one]
  have hkey : ∀ k : ℕ, topPos p q k = -1 + 2 * (((k : ℝ) / m - a) / (b - a)) := by
    intro k
    rw [ha, hb, stretch_topPos hm hpq]
    rfl
  -- the cusps
  have hq1 : 1 ≤ q := by omega
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / (3 * (m : ℝ)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδ]
    positivity
  have hδm : δ < 1 / m := by
    rw [hδ]
    exact one_div_lt_one_div_of_lt hm (by linarith)
  have hmδ : (m : ℝ) * δ = 1 / 3 := by
    rw [hδ]
    field_simp
  let edgeOf : Fin (m + 1) → Fin m := fun i =>
    if hi : (i : ℕ) < q then ⟨i, by omega⟩ else ⟨q - 1, by omega⟩
  let dirOf : Fin (m + 1) → ℝ := fun i => if (i : ℕ) < q then δ else -δ
  let cuspAt : Fin (m + 1) → ℝ × ℝ → ℝ × ℝ := fun i =>
    baseCusp D copies (edgeOf i) ((i : ℝ) / m) (dirOf i)
  have hdir : ∀ i, dirOf i = δ ∨ dirOf i = -δ := by
    intro i
    by_cases hi : (i : ℕ) < q
    · left
      simp only [dirOf, hi, if_true]
    · right
      simp only [dirOf, hi, if_false]
  have hdir_ne : ∀ i, dirOf i ≠ 0 := by
    intro i
    rcases hdir i with hd | hd <;> rw [hd]
    · exact hδ0.ne'
    · exact neg_ne_zero.mpr hδ0.ne'
  have hhint : ∀ i : Fin (m + 1), (i : ℕ) ≤ q → ∀ u : ℝ, 0 < u → u ≤ 1 →
      ((edgeOf i : ℕ) : ℝ) / m < (i : ℝ) / m + dirOf i * u ∧
        (i : ℝ) / m + dirOf i * u < (((edgeOf i : ℕ) : ℝ) + 1) / m := by
    intro i hi2 u hu0 hu1
    have hδu : dirOf i * u ≤ δ ∧ -δ ≤ dirOf i * u := by
      rcases hdir i with hd | hd <;> rw [hd] <;> constructor <;> nlinarith
    by_cases hiq : (i : ℕ) < q
    · have he : ((edgeOf i : ℕ) : ℝ) = (i : ℝ) := by simp only [edgeOf, hiq, dif_pos]
      have hd : dirOf i = δ := by simp only [dirOf, hiq, if_true]
      rw [he, hd, add_div]
      constructor <;> nlinarith
    · have hiq' : (i : ℕ) = q := by omega
      have he : ((edgeOf i : ℕ) : ℝ) = (i : ℝ) - 1 := by
        simp only [edgeOf, hiq, dif_neg, not_false_eq_true]
        rw [hiq', Nat.cast_sub hq1, Nat.cast_one]
      have hd : dirOf i = -δ := by simp only [dirOf, hiq, if_false]
      rw [he, hd, sub_add_cancel, sub_div]
      constructor <;> nlinarith
  have hcusp_zero : ∀ i : Fin (m + 1), cuspAt i 0 = D.point (path i) := by
    intro i
    rw [h.point]
    exact baseCusp_zero D copies _ _ _
  have hcusp_lower : ∀ i : Fin (m + 1), (i : ℕ) ≤ q → ∀ w ∈ cuspTri, w ≠ 0 →
      cuspAt i w ∈ lowerCollar D copies (edgeOf i) :=
    fun i hi2 w hw hw0 => h.baseCusp_mem_lowerCollar (edgeOf i) (hhint i hi2) hw hw0
  have hcusp_good : ∀ i : Fin (m + 1), p ≤ (i : ℕ) → (i : ℕ) ≤ q → ∀ w ∈ cuspTri,
      good (cuspAt i w) := by
    intro i hi1 hi2 w hw
    by_cases hw0 : w = 0
    · left
      rw [hw0, hcusp_zero]
      exact hvert i hi1 hi2
    · exact Or.inr (hfar _ (Or.inl (hcusp_lower i hi2 w hw hw0).2.2.2))
  have hcusp_x : ∀ i : Fin (m + 1), ∀ w ∈ cuspTri,
      (i : ℝ) - 1 / 3 ≤ m * (cuspAt i w).1 ∧ m * (cuspAt i w).1 ≤ (i : ℝ) + 1 / 3 := by
    intro i w hw
    obtain ⟨h0, h1, -⟩ := hw
    rw [baseCusp_fst]
    have hmi : (m : ℝ) * ((i : ℝ) / m) = i := by field_simp
    have hm2 : (m : ℝ) * ((i : ℝ) / m + dirOf i * w.1) = i + (m * dirOf i) * w.1 := by
      rw [mul_add, hmi]
      ring
    rw [hm2]
    rcases hdir i with hd | hd <;> rw [hd]
    · rw [hmδ]
      constructor <;> nlinarith
    · rw [mul_neg, hmδ]
      constructor <;> nlinarith
  refine ⟨{ P with
    trace_sub := ?_
    path_point := ?_
    path_curve := ?_
    boundary := ?_
    cusp := fun i => Ψ ∘ cuspAt i
    cusp_cont := ?_
    cusp_inj := ?_
    cusp_tip := ?_
    cusp_ball := ?_
    cusp_free := ?_
    cusp_disj := ?_ }⟩
  · intro z hz
    have hz' : z ∈ Ψ '' (Drawing.toPartial D S T).trace := hPtr ▸ hz
    obtain ⟨w, hw, rfl⟩ := hz'
    rw [mem_closedBall, dist_zero_right]
    rcases hgood_trace w hw with hs | hf
    · exact (hΨst1 w hs).le
    · exact (hΨnorm w hf).le
  · intro i hi1 hi2
    change Ψ (D.point (path i)) = _
    rw [hst _ (hvert i hi1 hi2), hkey, h.point]
  · intro i hi1 hi2 t
    have hon : onStretch (D.curve (copies i) t) := by
      obtain ⟨hx0, hx1⟩ := h.curve_fst i t
      refine ⟨h.curve_snd i t, ?_, ?_⟩
      · rw [ha]
        exact le_trans (div_le_div_of_nonneg_right (by exact_mod_cast hi1) hm.le) hx0
      · rw [hb]
        refine le_trans hx1 (div_le_div_of_nonneg_right ?_ hm.le)
        have : (i : ℕ) + 1 ≤ q := hi2
        exact_mod_cast this
    change (Ψ (D.curve (copies i) t)).2 = 1 ∧ topPos p q i ≤ (Ψ (D.curve (copies i) t)).1 ∧
      (Ψ (D.curve (copies i) t)).1 ≤ topPos p q ((i : ℕ) + 1)
    rw [hst _ hon, hkey, hkey]
    obtain ⟨hx0, hx1⟩ := h.curve_fst i t
    refine ⟨rfl, stretch_mono hab hx0, ?_⟩
    have := stretch_mono hab (a := a) hx1
    push_cast
    exact this
  · intro z hz hzb
    have hz' : z ∈ Ψ '' (Drawing.toPartial D S T).trace := hPtr ▸ hz
    obtain ⟨w, hw, rfl⟩ := hz'
    rcases hgood_trace w hw with hs | hf
    · rw [hst w hs]
    · exfalso
      apply hzb
      rw [mem_ball, dist_zero_right]
      exact hΨnorm w hf
  · intro i hi1 hi2 w hw
    exact (hΨat _ (hcusp_good i hi1 hi2 w hw)).comp_continuousWithinAt
      (continuous_baseCusp D copies _ _ _).continuousWithinAt
  · intro i hi1 hi2
    exact hΨinj.comp_injOn (h.injOn_baseCusp _ (hdir_ne i) (hhint i hi2))
  · intro i hi1 hi2
    change Ψ (cuspAt i 0) = Ψ (D.point (path i))
    rw [hcusp_zero]
  · intro i hi1 hi2 w hw hw0
    change Ψ (cuspAt i w) ∈ ball 0 1
    rw [mem_ball, dist_zero_right]
    exact hΨnorm _ (hfar _ (Or.inl (hcusp_lower i hi2 w hw hw0).2.2.2))
  · intro i hi1 hi2 w hw hw0 hz
    have hz' : Ψ (cuspAt i w) ∈ Ψ '' (Drawing.toPartial D S T).trace := hPtr ▸ hz
    obtain ⟨z, hzX, hze⟩ := hz'
    rw [hΨinj hze] at hzX
    exact (h.disjoint_lowerCollar (edgeOf i)).ne_of_mem (hcusp_lower i hi2 w hw hw0)
      (trace_toPartial_subset D S T hzX) rfl
  · intro i j hi1 hi2 hj1 hj2 hij w hw w' hw' heq
    have he : (m : ℝ) * (cuspAt i w).1 = (m : ℝ) * (cuspAt j w').1 :=
      congrArg (fun z => (m : ℝ) * z.1) (hΨinj heq)
    obtain ⟨hi3, hi4⟩ := hcusp_x i w hw
    obtain ⟨hj3, hj4⟩ := hcusp_x j w' hw'
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
      linarith
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast hlt
      linarith

end StraightPath

/-- The reflection in the horizontal axis. -/
def reflectY (z : ℝ × ℝ) : ℝ × ℝ := (z.1, -z.2)

theorem reflectY_injective : Function.Injective reflectY := by
  intro z w hzw
  simp only [reflectY, Prod.mk.injEq, neg_inj] at hzw
  exact Prod.ext hzw.1 hzw.2

theorem continuous_reflectY : Continuous reflectY := by
  unfold reflectY
  fun_prop

/-- The mirror image of a drawing in the horizontal axis. -/
def Drawing.reflect (D : Drawing J) : Drawing J where
  point v := reflectY (D.point v)
  point_injective := reflectY_injective.comp D.point_injective
  curve e t := reflectY (D.curve e t)
  continuous e := continuous_reflectY.comp (D.continuous e)
  injective e := reflectY_injective.comp_injOn (D.injective e)
  start e := congrArg reflectY (D.start e)
  finish e := congrArg reflectY (D.finish e)
  avoids e t h0 h1 v hv := D.avoids e t h0 h1 v (reflectY_injective hv)
  intersects e f hef s t hst := D.intersects e f hef s t (reflectY_injective hst)

namespace StraightPath

variable (h : StraightPath D m path copies)
include h

theorem reflect : StraightPath (Drawing.reflect D) m path copies where
  pos := h.pos
  injective := h.injective
  ends := h.ends
  point i := by
    change reflectY (D.point (path i)) = _
    rw [h.point]
    simp [reflectY]
  curve_snd i t := by
    change -(D.curve (copies i) t).2 = 0
    rw [h.curve_snd, neg_zero]
  curve_fst i t := h.curve_fst i t

/-- A stretch whose off-path edges leave its interior vertices from above has a
square realization. -/
theorem exists_squareRealization_of_endsAbove (S : Set V) (T : Finset E) {p q : ℕ}
    (hpq : p < q) (hqm : q ≤ m) (habove : EndsAbove D path copies T p q) :
    Nonempty (SquareRealization J S T path copies p q) := by
  refine h.reflect.exists_squareRealization_of_endsBelow S T hpq hqm ?_
  intro e he hne a hpa haq ham
  obtain ⟨h1, h2⟩ := habove e he hne a hpa haq ham
  refine ⟨fun hl => ?_, fun hr => ?_⟩
  · obtain ⟨τ, hτ, hs⟩ := h1 hl
    exact ⟨τ, hτ, fun t ht0 ht1 => neg_neg_of_pos (hs t ht0 ht1)⟩
  · obtain ⟨τ, hτ, hs⟩ := h2 hr
    exact ⟨τ, hτ, fun t ht0 ht1 => neg_neg_of_pos (hs t ht0 ht1)⟩

/-- A stretch selection whose interior vertices carry no selected loop and do not
separate the selection has a square realization. -/
theorem exists_squareRealization_base {U : Set (ℝ × ℝ)} (hU : OuterFace D U)
    (hfront : ∀ i t, D.curve (copies i) t ∈ closure U) (S : Set V) (T : Finset E) {p q : ℕ}
    (hpq : p < q) (hqm : q ≤ m) (hcop : ∀ i : Fin m, p ≤ (i : ℕ) → (i : ℕ) < q → copies i ∈ T)
    (hnoloop : ∀ a : ℕ, p < a → ∀ haq : a < q, ∀ e ∈ T,
      ¬ (J.left e = path ⟨a, by omega⟩ ∧ J.right e = path ⟨a, by omega⟩))
    (hconn : ∀ a : ℕ, ∀ hpa : p < a, ∀ haq : a < q, ∀ e ∈ T, ∀ x, (x = J.left e ∨ x = J.right e) →
      x ≠ path ⟨a, by omega⟩ →
        J.reaches (avoiding J T (path ⟨a, by omega⟩)) x (path ⟨a - 1, by omega⟩)) :
    Nonempty (SquareRealization J S T path copies p q) := by
  rcases h.ends_one_side hU hfront T hqm hcop hnoloop hconn with habove | hbelow
  · exact h.exists_squareRealization_of_endsAbove S T hpq hqm habove
  · exact h.exists_squareRealization_of_endsBelow S T hpq hqm hbelow

end StraightPath

end
end FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing
