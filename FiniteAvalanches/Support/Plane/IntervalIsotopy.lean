import FiniteAvalanches.Electrical.Geometry.OrientedDrawing
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Convex.Basic

/-!
# Isotopies of the interval

Increasing homeomorphisms of the unit interval are joined to the identity by
linear interpolation. Compactness gives joint continuity of the inverse family.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- A continuous family of equivalences of a compact Hausdorff space, indexed by
another compact Hausdorff space, has a jointly continuous inverse family. -/
theorem continuous_inverse_family_of_compact
    {T X : Type*} [TopologicalSpace T] [CompactSpace T] [T2Space T]
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (e : T → X ≃ X) (he : Continuous (fun p : T × X => e p.1 p.2)) :
    Continuous (fun p : T × X => (e p.1).symm p.2) := by
  let E : T × X ≃ T × X := {
    toFun p := (p.1, e p.1 p.2)
    invFun p := (p.1, (e p.1).symm p.2)
    left_inv p := by simp
    right_inv p := by simp }
  have hE : Continuous E := continuous_fst.prodMk he
  exact continuous_snd.comp hE.continuous_symm_of_equiv_compact_to_t2

/-- Linear interpolation between the identity and an increasing interval map. -/
noncomputable def intervalInterpolation (f : unitInterval → unitInterval)
    (t x : unitInterval) : unitInterval :=
  ⟨(1 - (t : ℝ)) * (x : ℝ) + (t : ℝ) * (f x : ℝ), by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) x.property.1)
        (mul_nonneg t.property.1 (f x).property.1)
    · have hx := x.property.2
      have hf := (f x).property.2
      have h₁ := mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr hx)
      have h₂ := mul_nonneg t.property.1 (sub_nonneg.mpr hf)
      nlinarith⟩

/-- Linear interpolation is jointly continuous when the endpoint map is. -/
theorem continuous_intervalInterpolation {f : unitInterval → unitInterval}
    (hf : Continuous f) : Continuous (fun p : unitInterval × unitInterval =>
      intervalInterpolation f p.1 p.2) := by
  apply Continuous.subtype_mk
  change Continuous (fun p : unitInterval × unitInterval =>
    (1 - (p.1 : ℝ)) * (p.2 : ℝ) + (p.1 : ℝ) * (f p.2 : ℝ))
  fun_prop

/-- Interpolating an increasing homeomorphism gives strictly increasing maps. -/
theorem intervalInterpolation_strictMono (f : unitInterval ≃ₜ unitInterval)
    (hf : StrictMono f) (t : unitInterval) : StrictMono (intervalInterpolation f t) := by
  intro x y hxy
  change (1 - (t : ℝ)) * (x : ℝ) + (t : ℝ) * (f x : ℝ) <
    (1 - (t : ℝ)) * (y : ℝ) + (t : ℝ) * (f y : ℝ)
  have hxy' : (x : ℝ) < y := hxy
  have hfy : (f x : ℝ) < f y := hf hxy
  have h₁ := mul_nonneg (sub_nonneg.mpr t.property.2) (le_of_lt (sub_pos.mpr hxy'))
  have h₂ := mul_nonneg t.property.1 (le_of_lt (sub_pos.mpr hfy))
  by_cases ht : (t : ℝ) = 1
  · rw [ht]; simp only [sub_self, zero_mul, one_mul, zero_add]; exact hfy
  · have h₃ := mul_pos (sub_pos.mpr (lt_of_le_of_ne t.property.2 ht)) (sub_pos.mpr hxy')
    nlinarith

/-- An increasing interval homeomorphism admits an isotopy through increasing
bijections whose forward and inverse maps are jointly continuous. -/
theorem exists_interval_isotopy (f : unitInterval ≃ₜ unitInterval)
    (hf : StrictMono f) :
    ∃ e : unitInterval → unitInterval ≃ unitInterval,
      (∀ t x, e t x = intervalInterpolation f t x) ∧
      Continuous (fun p : unitInterval × unitInterval => e p.1 p.2) ∧
      Continuous (fun p : unitInterval × unitInterval => (e p.1).symm p.2) ∧
      (∀ x, e 0 x = x) ∧ (∀ x, e 1 x = f x) := by
  have hf0 : f 0 = 0 := by
    obtain ⟨x, hx⟩ := f.surjective 0
    have h : f 0 ≤ f x := hf.monotone (show 0 ≤ x from x.property.1)
    rw [hx] at h
    exact le_antisymm h (f 0).property.1
  have hf1 : f 1 = 1 := by
    obtain ⟨x, hx⟩ := f.surjective 1
    have h : f x ≤ f 1 := hf.monotone (show x ≤ 1 from x.property.2)
    rw [hx] at h
    exact le_antisymm (f 1).property.2 h
  have hcont (t : unitInterval) : Continuous (intervalInterpolation f t) := by
    have h := continuous_intervalInterpolation f.continuous
    exact h.comp (continuous_const.prodMk continuous_id)
  have h0 (t : unitInterval) : intervalInterpolation f t 0 = 0 := by
    apply Subtype.ext
    simp [intervalInterpolation, hf0]
  have h1 (t : unitInterval) : intervalInterpolation f t 1 = 1 := by
    apply Subtype.ext
    simp [intervalInterpolation, hf1]
  have hbij (t : unitInterval) : Function.Bijective (intervalInterpolation f t) := by
    refine ⟨(intervalInterpolation_strictMono f hf t).injective, ?_⟩
    intro y
    have h := intermediate_value_Icc (show (0 : unitInterval) ≤ 1 by norm_num)
      (hcont t).continuousOn
    have hy : y ∈ Icc (intervalInterpolation f t 0) (intervalInterpolation f t 1) := by
      rw [h0, h1]
      exact ⟨y.property.1, y.property.2⟩
    obtain ⟨x, _, hx⟩ := h hy
    exact ⟨x, hx⟩
  let e : unitInterval → unitInterval ≃ unitInterval :=
    fun t => Equiv.ofBijective (intervalInterpolation f t) (hbij t)
  have he : Continuous (fun p : unitInterval × unitInterval => e p.1 p.2) :=
    continuous_intervalInterpolation f.continuous
  refine ⟨e, fun _ _ => rfl, he, continuous_inverse_family_of_compact e he, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    simp [e, intervalInterpolation]
  · intro x
    apply Subtype.ext
    simp [e, intervalInterpolation]

end FiniteAvalanches.Electrical.StatementGeometry
