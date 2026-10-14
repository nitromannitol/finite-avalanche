import FiniteAvalanches.Electrical.Physical.UnscaledPhysicalSquareSum

/-! Incoming Step 4: oscillation on the original copied squares, without dilation. -/

set_option autoImplicit false
open Set MeasureTheory
open scoped BigOperators Classical
open FiniteAvalanches.Electrical.Geometry
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Physical.Unscaled

namespace FiniteAvalanches.Electrical.Physical.Undilated

/-- Dilation by one preserves the complete square, including a point square. -/
theorem square_dilate_one (Q : Square) : Q.dilate 1 (by norm_num) = Q := by
  cases Q
  simp [Square.dilate]

/-- Nonnegativity follows directly from the actual pairwise-difference supremum. -/
theorem square_angularOsc_nonneg (Q : Square) (epsilon y0 : ℝ) (he : 0 < epsilon) :
    0 ≤ Q.angularOsc epsilon y0 1 (by norm_num) he := by
  obtain ⟨z, hz⟩ := (Q.dilate 1 (by norm_num)).carrier_nonempty
  have h := abs_sub_le_oscillation (F := angular epsilon y0) hz hz
    ⟨1, fun u _ v _ => angular_sub_le_one epsilon y0 he u v⟩
  simpa only [Square.angularOsc, sub_self, abs_zero] using h

/-- The source two-side estimate holds at every point of the original closed square. -/
theorem square_angularOsc_le_two (Q : Square) (epsilon y0 : ℝ) (he : 0 < epsilon)
    (z : ℝ × ℝ) (hz : z ∈ Q.carrier) :
    Q.angularOsc epsilon y0 1 (by norm_num) he ≤
      2 * Q.side / max epsilon (radialDistance y0 z) := by
  let r := max epsilon (radialDistance y0 z)
  have hr : 0 < r := lt_of_lt_of_le he (le_max_left _ _)
  have hs := Q.side_nonneg
  apply oscillation_le
  intro u hu v hv
  rw [square_dilate_one] at hu hv
  by_cases hfar : 2 * Q.side ≤ radialDistance y0 z
  · let Du := max epsilon (radialDistance y0 u)
    have hDu : 0 < Du := lt_of_lt_of_le he (le_max_left _ _)
    have hrDu : r ≤ 2 * Du := by
      by_cases hz1 : radialDistance y0 z ≤ epsilon
      · have hre : r = epsilon := max_eq_left hz1
        have hu1 : epsilon ≤ Du := le_max_left _ _
        rw [hre]
        linarith only [hu1, he]
      · have hre : r = radialDistance y0 z := max_eq_right (le_of_not_ge hz1)
        have hdist := (radialDistance_sub_le y0 z u).trans
          (pointDist_le_of_mem_square Q z u hz hu)
        have huD : radialDistance y0 u ≤ Du := le_max_right _ _
        have hcorner : r ≤ Du + Q.side := by
          rw [hre]
          linarith only [(abs_le.mp hdist).2, huD]
        have hlarge : 2 * Q.side ≤ r := hfar.trans (le_max_right _ _)
        linarith only [hcorner, hlarge]
    have hdiam := pointDist_le_of_mem_square Q u v hu hv
    calc
      |angular epsilon y0 u - angular epsilon y0 v| ≤ pointDist u v / Du :=
        angular_sub_le epsilon y0 he u v
      _ ≤ Q.side / Du := div_le_div_of_nonneg_right hdiam hDu.le
      _ ≤ 2 * Q.side / r := (div_le_div_iff₀ hDu hr).mpr (by
        calc
          Q.side * r ≤ Q.side * (2 * Du) := mul_le_mul_of_nonneg_left hrDu hs
          _ = 2 * Q.side * Du := by ring)
  · by_cases hedom : radialDistance y0 z ≤ epsilon
    · have hdenom : epsilon ≤ max epsilon (radialDistance y0 u) := le_max_left _ _
      have hDu : 0 < max epsilon (radialDistance y0 u) := he.trans_le hdenom
      have hdiam := pointDist_le_of_mem_square Q u v hu hv
      rw [max_eq_left hedom]
      calc
        |angular epsilon y0 u - angular epsilon y0 v| ≤
            pointDist u v / max epsilon (radialDistance y0 u) :=
          angular_sub_le epsilon y0 he u v
        _ ≤ Q.side / max epsilon (radialDistance y0 u) :=
          div_le_div_of_nonneg_right hdiam hDu.le
        _ ≤ Q.side / epsilon := div_le_div_of_nonneg_left hs he hdenom
        _ ≤ 2 * Q.side / epsilon :=
          div_le_div_of_nonneg_right (by linarith only [hs]) he.le
    · have hre : r = radialDistance y0 z := max_eq_right (le_of_not_ge hedom)
      have hsmall : r ≤ 2 * Q.side := by rw [hre]; exact le_of_lt (lt_of_not_ge hfar)
      exact (angular_sub_le_one epsilon y0 he u v).trans
        ((le_div_iff₀ hr).mpr (by simpa only [one_mul] using hsmall))

/-- The side-zero branch is settled before any area cancellation. -/
theorem square_angularOsc_eq_zero_of_side_eq_zero (Q : Square) (epsilon y0 : ℝ)
    (he : 0 < epsilon) (hs : Q.side = 0) :
    Q.angularOsc epsilon y0 1 (by norm_num) he = 0 := by
  have hz : (Q.x, Q.y) ∈ Q.carrier :=
    ⟨⟨le_rfl, by linarith only [Q.side_nonneg]⟩,
      ⟨le_rfl, by linarith only [Q.side_nonneg]⟩⟩
  have hb := square_angularOsc_le_two Q epsilon y0 he (Q.x, Q.y) hz
  rw [hs, mul_zero, zero_div] at hb
  exact le_antisymm hb (square_angularOsc_nonneg Q epsilon y0 he)

/-- Average the squared bound over this same square's open carrier: factor four. -/
theorem square_angularOsc_sq_le_four_integral (Q : Square) (epsilon y0 : ℝ)
    (he : 0 < epsilon)
    (hQ : Q.carrier ⊆ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) :
    (Q.angularOsc epsilon y0 1 (by norm_num) he) ^ 2 ≤
      4 * (∫ z : ℝ × ℝ in Q.openCarrier,
        1 / (max epsilon (max |z.1| |z.2 - y0|)) ^ 2 ∂volume) := by
  by_cases hs : Q.side = 0
  · rw [square_angularOsc_eq_zero_of_side_eq_zero Q epsilon y0 he hs, zero_pow (by decide)]
    exact mul_nonneg (by norm_num)
      (setIntegral_nonneg Q.measurableSet_openCarrier (fun _ _ => by positivity))
  · have hspos : 0 < Q.side := lt_of_le_of_ne Q.side_nonneg (Ne.symm hs)
    have harea : 0 < Q.side ^ 2 := sq_pos_of_pos hspos
    have hK := (integrableOn_strip_kernel epsilon y0 he).mono_set
      (Q.openCarrier_subset_carrier.trans hQ)
    have hconst : IntegrableOn (fun _z : ℝ × ℝ =>
        (Q.angularOsc epsilon y0 1 (by norm_num) he) ^ 2) Q.openCarrier volume :=
      integrableOn_const (by rw [Q.volume_openCarrier]; exact ENNReal.ofReal_ne_top)
    have hb0 := square_angularOsc_nonneg Q epsilon y0 he
    have hpoint : ∀ z ∈ Q.openCarrier,
        (Q.angularOsc epsilon y0 1 (by norm_num) he) ^ 2 ≤
          (4 * Q.side ^ 2) * (1 / (max epsilon (max |z.1| |z.2 - y0|)) ^ 2) := by
      intro z hz
      have hb := square_angularOsc_le_two Q epsilon y0 he z
        (Q.openCarrier_subset_carrier hz)
      calc
        _ ≤ (2 * Q.side / max epsilon (radialDistance y0 z)) ^ 2 := by
          simpa only [pow_two] using mul_self_le_mul_self hb0 hb
        _ = _ := by unfold radialDistance; ring
    have hint := setIntegral_mono_on hconst (hK.const_mul (4 * Q.side ^ 2))
      Q.measurableSet_openCarrier hpoint
    rw [setIntegral_const, smul_eq_mul, Q.area_openCarrier, integral_const_mul] at hint
    apply (mul_le_mul_iff_right₀ harea).mp
    calc
      _ = Q.side ^ 2 * (Q.angularOsc epsilon y0 1 (by norm_num) he) ^ 2 := by ring
      _ ≤ (4 * Q.side ^ 2) * (∫ z : ℝ × ℝ in Q.openCarrier,
          1 / (max epsilon (max |z.1| |z.2 - y0|)) ^ 2 ∂volume) := hint
      _ = _ := by ring

/-- Disjoint original interiors in the unit strip give the incoming sum sixteen. -/
theorem angular_square_sum_le_sixteen {I : Type*} (s : Finset I) (Q : I → Square)
    (hd : Set.PairwiseDisjoint (↑s) (fun i => (Q i).openCarrier))
    (epsilon y0 : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1)
    (hQ : ∀ i ∈ s, (Q i).carrier ⊆ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) :
    (∑ i ∈ s, ((Q i).angularOsc epsilon y0 1 (by norm_num) he) ^ 2) ≤
      16 * (1 + Real.log (1 / epsilon)) := by
  have hstrip := integrableOn_strip_kernel epsilon y0 he
  have hK : ∀ i ∈ s, IntegrableOn
      (fun z : ℝ × ℝ => 1 / (max epsilon (max |z.1| |z.2 - y0|)) ^ 2)
      (Q i).openCarrier volume :=
    fun i hi => hstrip.mono_set ((Q i).openCarrier_subset_carrier.trans (hQ i hi))
  have hU : (⋃ i ∈ s, (Q i).openCarrier) ⊆ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) := by
    intro z hz
    obtain ⟨i, hi, hz⟩ := Set.mem_iUnion₂.mp hz
    exact hQ i hi ((Q i).openCarrier_subset_carrier hz)
  have hmono := setIntegral_mono_set hstrip
    (Filter.Eventually.of_forall (fun _z => by positivity))
    (Filter.Eventually.of_forall hU)
  calc
    _ ≤ ∑ i ∈ s, 4 * (∫ z : ℝ × ℝ in (Q i).openCarrier,
        1 / (max epsilon (max |z.1| |z.2 - y0|)) ^ 2 ∂volume) :=
      Finset.sum_le_sum (fun i hi =>
        square_angularOsc_sq_le_four_integral (Q i) epsilon y0 he (hQ i hi))
    _ = 4 * (∫ z : ℝ × ℝ in ⋃ i ∈ s, (Q i).openCarrier,
        1 / (max epsilon (max |z.1| |z.2 - y0|)) ^ 2 ∂volume) := by
      rw [integral_biUnion_finset s (fun i _ => (Q i).measurableSet_openCarrier) hd hK,
        Finset.mul_sum]
    _ ≤ 4 * (∫ z : ℝ × ℝ in Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ),
        1 / (max epsilon (max |z.1| |z.2 - y0|)) ^ 2 ∂volume) :=
      mul_le_mul_of_nonneg_left hmono (by norm_num)
    _ = 16 * (1 + Real.log (1 / epsilon)) := by
      rw [integral_strip_kernel epsilon y0 he he1]
      ring

/-- Packing and strip containment are produced on the unchanged physical copy carrier. -/
theorem physical_angular_square_sum_le_sixteen {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V) (hne : alpha ≠ beta)
    (A : Source.OuterArc D alpha beta) (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A (Source.voltage J alpha beta hc) psi)
    (epsilon y0 : ℝ) (he : 0 < epsilon) (he1 : epsilon ≤ 1) :
    (∑ e : E, ((physicalSquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).angularOsc
      epsilon y0 1 (by norm_num) he) ^ 2) ≤ 16 * (1 + Real.log (1 / epsilon)) := by
  let Q := physicalSquare J D alpha beta A (Source.voltage J alpha beta hc) psi
  have hcarrier := physicalSquare_carrier J D alpha beta A (Source.voltage J alpha beta hc) psi hpsi
  have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset E)) (fun e => (Q e).openCarrier) := by
    intro e _ f _ hef
    change Disjoint (Q e).openCarrier (Q f).openCarrier
    rw [← Plane.Square.interior_carrier, ← Plane.Square.interior_carrier, hcarrier e, hcarrier f]
    exact ((PhysicalTiling.physical_stream_tiling J D hc alpha beta hne A).2 psi hpsi).2.1 e f hef
  have hQ : ∀ e ∈ (Finset.univ : Finset E),
      (Q e).carrier ⊆ Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ) := by
    intro e _ z hz
    rw [hcarrier e] at hz
    have hrect := PhysicalTiling.physical_edgeSquare_subset_rectangle J D hc alpha beta hne A psi hpsi e hz
    exact ⟨hrect.1, mem_univ z.2⟩
  exact angular_square_sum_le_sixteen Finset.univ Q hd epsilon y0 he he1 hQ

/-- The selected original physical copy supplies the literal half-current cutoff. -/
theorem physical_copy_cutoff_square_sum_le_sixteen {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V) (hne : alpha ≠ beta)
    (A : Source.OuterArc D alpha beta) (psi : A.embedding.Face → ℝ)
    (hpsi : Source.stream_spec D alpha beta A (Source.voltage J alpha beta hc) psi)
    (j : E) (hpj : 0 < |Source.voltage J alpha beta hc (J.left j) -
      Source.voltage J alpha beta hc (J.right j)|) (y0 : ℝ) :
    let p := |Source.voltage J alpha beta hc (J.left j) - Source.voltage J alpha beta hc (J.right j)|
    (∑ e : E, ((physicalSquare J D alpha beta A (Source.voltage J alpha beta hc) psi e).angularOsc
      (p / 2) y0 1 (by norm_num) (by positivity)) ^ 2) ≤
        16 * (1 + Real.log (2 / p)) := by
  intro p
  obtain ⟨hpa, hpb, hh⟩ := Source.voltage_spec J alpha beta hne hc
  have hv := Plane.voltage_range J.left J.right alpha beta hc (Source.voltage J alpha beta hc) hpa hpb hh
  have hp1 : p ≤ 1 := abs_le.mpr
    ⟨by linarith only [(hv (J.left j)).1, (hv (J.right j)).2],
      by linarith only [(hv (J.left j)).2, (hv (J.right j)).1]⟩
  have he : 0 < p / 2 := by positivity
  have he1 : p / 2 ≤ 1 := by linarith only [hp1]
  have hrecip : 1 / (p / 2) = 2 / p := by ring
  simpa only [hrecip] using physical_angular_square_sum_le_sixteen J D hc alpha beta hne A psi hpsi
    (p / 2) y0 he he1

end FiniteAvalanches.Electrical.Physical.Undilated
