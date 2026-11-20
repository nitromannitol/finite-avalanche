import FiniteAvalanches.Support.Plane.JordanRounding
import FiniteAvalanches.Support.Plane.ArcClosingPath
import FiniteAvalanches.Support.Plane.DiskReflection
import FiniteAvalanches.Support.Plane.DilationIsotopy
import FiniteAvalanches.Support.Plane.ChartOrientation
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Oriented straightening of plane arcs

A plane homeomorphism carrying one closed round disk onto another agrees near
the centre of the first disk with an oriented chart, possibly followed by a
reflection. Applied to a parameter-preserving straightening of a simple arc,
corrected by the rounding homeomorphism of the image of a large circle, this
gives an oriented chart sending the arc parameter `t` to `(t, 0)`.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set Metric Filter
open scoped Topology
open FiniteAvalanches.Electrical.Source

noncomputable section

/-- Composition of oriented charts, the first one applied first. -/
def orientedChartComp (c d : OrientedChart) : OrientedChart where
  map := c.map.trans d.map
  isotopy t := (c.isotopy t).trans (d.isotopy t)
  continuous := d.continuous.comp (continuous_fst.prodMk c.continuous)
  inverse_continuous := c.inverse_continuous.comp
    (continuous_fst.prodMk d.inverse_continuous)
  start := by rw [c.start, d.start]; rfl
  finish := by rw [c.finish, d.finish]

/-- Conjugation of an oriented chart by a plane homeomorphism. -/
def orientedChartConj (c : OrientedChart) (f : Plane ≃ₜ Plane) : OrientedChart where
  map := f.symm.trans (c.map.trans f)
  isotopy t := f.symm.trans ((c.isotopy t).trans f)
  continuous := f.continuous.comp
    (c.continuous.comp (continuous_fst.prodMk (f.symm.continuous.comp continuous_snd)))
  inverse_continuous := f.continuous.comp
    (c.inverse_continuous.comp (continuous_fst.prodMk (f.symm.continuous.comp continuous_snd)))
  start := by
    rw [c.start]
    apply Homeomorph.ext
    intro x
    exact f.apply_symm_apply x
  finish := by rw [c.finish]

private theorem scaling_factor_pos {s : ℝ} (hs : 0 < s) (t : ArcParameter) :
    0 < 1 + (t : ℝ) * (s - 1) := by
  rcases le_or_gt 1 s with h | h
  · nlinarith [mul_nonneg t.2.1 (sub_nonneg.2 h)]
  · nlinarith [mul_nonneg (sub_nonneg.2 t.2.2) (sub_nonneg.2 h.le)]

/-- Multiplication by a positive scalar is isotopic to the identity. -/
def orientedChartOfScaling (s : ℝ) (hs : 0 < s) : OrientedChart where
  map := Homeomorph.smulOfNeZero s hs.ne'
  isotopy t := Homeomorph.smulOfNeZero (1 + (t : ℝ) * (s - 1)) (scaling_factor_pos hs t).ne'
  continuous := by
    change Continuous (fun p : ArcParameter × Plane => (1 + (p.1 : ℝ) * (s - 1)) • p.2)
    fun_prop
  inverse_continuous := by
    simp only [Homeomorph.smulOfNeZero_symm_apply]
    exact ((continuous_const.add ((continuous_subtype_val.comp continuous_fst).mul
      continuous_const)).inv₀ fun p => (scaling_factor_pos hs p.1).ne').smul continuous_snd
  start := by
    apply Homeomorph.ext
    intro x
    simp
  finish := by
    apply Homeomorph.ext
    intro x
    simp

theorem orientedChartOfScaling_map_apply (s : ℝ) (hs : 0 < s) (x : Plane) :
    (orientedChartOfScaling s hs).map x = s • x := rfl

/-- Reflection in product coordinates. -/
theorem planeReflection_apply (p : Plane) : planeReflection p = (p.1, -p.2) := by
  simp [planeReflection, Complex.equivRealProdCLM_symm_apply]

theorem planeReflection_symm_apply (p : Plane) : planeReflection.symm p = (p.1, -p.2) := by
  rw [Homeomorph.symm_apply_eq, planeReflection_apply]
  simp

/-- Translating and scaling the closed disk of radius `ρ` about the origin. -/
theorem image_affine_closedBall (w : ℂ) {s ρ : ℝ} (hs : 0 < s) :
    (fun x : Plane => Complex.equivRealProdCLM w + s • x) ''
        (Complex.equivRealProdCLM '' closedBall (0 : ℂ) ρ) =
      Complex.equivRealProdCLM '' closedBall w (s * ρ) := by
  ext y
  simp only [mem_image, mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨w + s • z, ?_, ?_⟩
    · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
      exact mul_le_mul_of_nonneg_left hz hs.le
    · rw [map_add, map_smul]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨Complex.equivRealProdCLM (s⁻¹ • (z - w)), ⟨s⁻¹ • (z - w), ?_, rfl⟩, ?_⟩
    · rw [norm_smul, ← dist_eq_norm, Real.norm_eq_abs, abs_inv, abs_of_pos hs,
        inv_mul_le_iff₀ hs]
      exact hz
    · rw [← map_smul, ← map_add, smul_smul, mul_inv_cancel₀ hs.ne', one_smul,
        add_sub_cancel]

private theorem complexDisk_mem_nhds_zero' : complexDisk ∈ 𝓝 (0 : Plane) := by
  let U : Set Plane := {x | ‖Complex.equivRealProdCLM.symm x‖ < 2}
  have hU : IsOpen U := isOpen_lt (continuous_norm.comp Complex.equivRealProdCLM.symm.continuous)
    continuous_const
  have h0 : (0 : Plane) ∈ U := by simp [U]
  apply mem_of_superset (hU.mem_nhds h0)
  intro x hx
  exact (mem_complexDisk x).2 (le_of_lt hx)

/-- A plane homeomorphism carrying the closed disk of radius `R` about the origin
onto another closed round disk agrees near the origin with an oriented chart,
possibly followed by a reflection. -/
theorem exists_local_orientedChart_of_disk_image (f : Plane ≃ₜ Plane) {R r : ℝ}
    (hR : 0 < R) (hr : 0 < r) (w : ℂ)
    (hf : f '' (Complex.equivRealProdCLM '' closedBall (0 : ℂ) R) =
      Complex.equivRealProdCLM '' closedBall w r) :
    ∃ d : OrientedChart, f =ᶠ[𝓝 0] d.map ∨ f =ᶠ[𝓝 0] (planeReflection.symm ∘ d.map) := by
  let A₁ := orientedChartOfScaling (R / 2) (by positivity)
  let A₂ := orientedChartComp (orientedChartOfScaling (r / 2) (by positivity))
    (orientedChartOfTranslation (Complex.equivRealProdCLM w))
  have hA₁ : ∀ x, A₁.map x = Complex.equivRealProdCLM 0 + (R / 2) • x := fun x => by
    rw [map_zero, zero_add]
    rfl
  have hA₂ : ∀ x, A₂.map x = Complex.equivRealProdCLM w + (r / 2) • x := fun _ => rfl
  have hA₁img : A₁.map '' complexDisk =
      Complex.equivRealProdCLM '' closedBall (0 : ℂ) R := by
    rw [complexDisk, show (A₁.map : Plane → Plane) = _ from funext hA₁,
      image_affine_closedBall 0 (by positivity : (0 : ℝ) < R / 2)]
    congr 2
    ring
  have hA₂img : A₂.map '' complexDisk = Complex.equivRealProdCLM '' closedBall w r := by
    rw [complexDisk, show (A₂.map : Plane → Plane) = _ from funext hA₂,
      image_affine_closedBall w (by positivity : (0 : ℝ) < r / 2)]
    congr 2
    ring
  let h : Plane ≃ₜ Plane := A₁.map.trans (f.trans A₂.map.symm)
  have hdisk : h '' complexDisk = complexDisk := by
    change (A₂.map.symm ∘ f ∘ A₁.map) '' complexDisk = complexDisk
    rw [image_comp, image_comp, hA₁img, hf, ← hA₂img, ← image_comp,
      Homeomorph.symm_comp_self, image_id]
  have hU : A₁.map '' complexDisk ∈ 𝓝 (0 : Plane) := by
    have := A₁.map.isOpenMap.image_mem_nhds complexDisk_mem_nhds_zero'
    rwa [hA₁, map_zero, zero_add, smul_zero] at this
  have hfA : ∀ x, f (A₁.map x) = A₂.map (h x) := fun x => by
    change f (A₁.map x) = A₂.map (A₂.map.symm (f (A₁.map x)))
    rw [Homeomorph.apply_symm_apply]
  rcases exists_orientedChart_agree_on_complexDisk_or_reflect h hdisk with ⟨d₀, hd₀⟩ | ⟨d₀, hd₀⟩
  · refine ⟨orientedChartComp A₁.symm (orientedChartComp d₀ A₂), Or.inl ?_⟩
    filter_upwards [hU] with y hy
    obtain ⟨x, hx, rfl⟩ := hy
    change f (A₁.map x) = A₂.map (d₀.map (A₁.map.symm (A₁.map x)))
    rw [Homeomorph.symm_apply_apply, hd₀ x hx, hfA]
  · refine ⟨orientedChartConj (orientedChartComp A₁.symm (orientedChartComp d₀ A₂))
      planeReflection, Or.inr ?_⟩
    filter_upwards [hU] with y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hρx : planeReflection.symm x ∈ complexDisk := by
      rw [← planeReflection_image_complexDisk]
      exact ⟨x, hx, by rw [planeReflection_apply, planeReflection_symm_apply]⟩
    have hcomm : A₁.map.symm (planeReflection.symm (A₁.map x)) = planeReflection.symm x := by
      rw [Homeomorph.symm_apply_eq, planeReflection_symm_apply, planeReflection_symm_apply,
        orientedChartOfScaling_map_apply, orientedChartOfScaling_map_apply]
      simp
    change f (A₁.map x) = planeReflection.symm (planeReflection
      (A₂.map (d₀.map (A₁.map.symm (planeReflection.symm (A₁.map x))))))
    rw [Homeomorph.symm_apply_apply, hcomm, hd₀ _ hρx, Homeomorph.apply_symm_apply, hfA]

/-- The reflection fixes the horizontal axis pointwise. -/
private theorem planeReflection_horizontal' (t : ℝ) : planeReflection (t, 0) = (t, 0) := by
  rw [planeReflection_apply]
  simp

/-- A straightening locally agreeing with an oriented chart, possibly after
reflection of the target, has an oriented straightening. -/
theorem exists_orientedChart_straightening_of_local_agreement'
    (gamma : unitInterval → Plane) (f : Plane ≃ₜ Plane)
    (hf : ∀ t, f (gamma t) = (t.val, 0)) (c : OrientedChart) (z : Plane)
    (hlocal : f =ᶠ[𝓝 z] c.map ∨
      f =ᶠ[𝓝 z] (planeReflection.symm ∘ c.map)) :
    ∃ d : OrientedChart, ∀ t, d.map (gamma t) = (t.val, 0) := by
  rcases hlocal with h | h
  · exact ⟨orientedChartOfLocallyEq f c z h, hf⟩
  · have h' : f.trans planeReflection =ᶠ[𝓝 z] c.map := by
      filter_upwards [h] with x hx
      change planeReflection (f x) = c.map x
      rw [hx]
      exact planeReflection.apply_symm_apply (c.map x)
    refine ⟨orientedChartOfLocallyEq (f.trans planeReflection) c z h', ?_⟩
    intro t
    change planeReflection (f (gamma t)) = (t.val, 0)
    rw [hf, planeReflection_horizontal']

/-- The isometric identification of the complex plane with Euclidean coordinates. -/
private def complexEuclidean : ℂ ≃ₜ Schoenflies.Plane :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph

private theorem complexEuclidean_apply (z : ℂ) :
    complexEuclidean z = Schoenflies.Plane.mk z.re z.im := by
  ext i
  fin_cases i <;> simp [complexEuclidean]

private theorem complexEuclidean_symm_image_closedBall (c : Schoenflies.Plane) (ρ : ℝ) :
    complexEuclidean.symm '' closedBall c ρ = closedBall (complexEuclidean.symm c) ρ :=
  Complex.orthonormalBasisOneI.repr.symm.toIsometryEquiv.image_closedBall c ρ

private theorem complexEuclidean_symm_zero : complexEuclidean.symm 0 = 0 :=
  map_zero Complex.orthonormalBasisOneI.repr.symm

private theorem norm_complexEuclidean (z : ℂ) : ‖complexEuclidean z‖ = ‖z‖ :=
  Complex.orthonormalBasisOneI.repr.norm_map z

/-- Every simple plane arc has an oriented chart sending the arc parameter `t`
to the point `(t, 0)`. -/
theorem exists_orientedChart_arc_straightening (gamma : ArcParameter → Plane)
    (hc : Continuous gamma) (hi : Function.Injective gamma) :
    ∃ c : OrientedChart, ∀ t : ArcParameter, c.map (gamma t) = (t.val, 0) := by
  let p : Path (gamma 0) (gamma 1) := ⟨⟨gamma, hc⟩, rfl, rfl⟩
  obtain ⟨F, hF⟩ := exists_plane_homeomorph_straightening p hi
  let Cx : ℂ ≃ₜ Plane := Complex.equivRealProdCLM.toHomeomorph
  obtain ⟨R, hR, hRb⟩ :=
    ((isCompact_range hc).image Cx.symm.continuous).isBounded.exists_pos_norm_lt
  let Ψ : Plane ≃ₜ Schoenflies.Plane := Cx.symm.trans complexEuclidean
  have hΨ : ∀ a b : ℝ, Ψ (a, b) = Schoenflies.Plane.mk a b := fun a b => by
    change complexEuclidean (Complex.equivRealProdCLM.symm (a, b)) = _
    rw [complexEuclidean_apply, Complex.equivRealProdCLM_symm_apply]
    simp
  have hΨsymm : ∀ a b : ℝ, Ψ.symm (Schoenflies.Plane.mk a b) = (a, b) := fun a b => by
    rw [Homeomorph.symm_apply_eq, hΨ]
  let FE : Schoenflies.Plane ≃ₜ Schoenflies.Plane := Ψ.symm.trans (F.trans Ψ)
  have hFE : ∀ x, FE (Ψ x) = Ψ (F x) := fun x => by
    change Ψ (F (Ψ.symm (Ψ x))) = Ψ (F x)
    rw [Homeomorph.symm_apply_apply]
  let K := FE '' sphere (0 : Schoenflies.Plane) R
  have hK : Schoenflies.IsJordanCurve K := isJordanCurve_homeomorph_image FE (isJordanCurve_sphere hR)
  have hσ : ∀ t ∈ unitInterval, Schoenflies.Plane.mk t 0 ∈ Schoenflies.inside K := by
    intro t ht
    have h1 : Ψ (gamma ⟨t, ht⟩) ∈ ball (0 : Schoenflies.Plane) R := by
      rw [mem_ball, dist_zero_right]
      change ‖complexEuclidean (Cx.symm (gamma ⟨t, ht⟩))‖ < R
      rw [norm_complexEuclidean]
      exact hRb _ ⟨_, ⟨⟨t, ht⟩, rfl⟩, rfl⟩
    rw [← inside_sphere hR] at h1
    have h2 := mem_image_of_mem FE h1
    rw [homeomorph_image_inside, hFE] at h2
    have h3 : F (gamma ⟨t, ht⟩) = (t, 0) := hF ⟨t, ht⟩
    rwa [h3, hΨ] at h2
  obtain ⟨Θ, c, r, hr, hΘσ, hΘK⟩ := exists_rounding_homeomorph hK hσ
  let g : Plane ≃ₜ Plane := Ψ.trans ((FE.trans Θ).trans Ψ.symm)
  have hg : ∀ t : unitInterval, g (gamma t) = (t.val, 0) := fun t => by
    change Ψ.symm (Θ (FE (Ψ (gamma t)))) = _
    have h3 : F (gamma t) = (t.val, 0) := hF t
    rw [hFE, h3, hΨ, hΘσ t.val t.property, hΨsymm]
  have hΨball : ∀ (z : Schoenflies.Plane) (ρ : ℝ),
      Ψ.symm '' closedBall z ρ =
        Complex.equivRealProdCLM '' closedBall (complexEuclidean.symm z) ρ := by
    intro z ρ
    change (Cx ∘ complexEuclidean.symm) '' closedBall z ρ = _
    rw [image_comp, complexEuclidean_symm_image_closedBall]
    rfl
  have hFEball : (Θ ∘ FE) '' closedBall (0 : Schoenflies.Plane) R = closedBall c r := by
    have hΘK' : Θ '' (FE '' sphere (0 : Schoenflies.Plane) R) = sphere c r := hΘK
    rw [image_comp, ← ball_union_sphere, image_union, image_union, ← inside_sphere hR,
      homeomorph_image_inside, homeomorph_image_inside, hΘK', inside_sphere hr, ball_union_sphere]
  have hgdisk : g '' (Complex.equivRealProdCLM '' closedBall (0 : ℂ) R) =
      Complex.equivRealProdCLM '' closedBall (complexEuclidean.symm c) r := by
    have h0 : Complex.equivRealProdCLM '' closedBall (0 : ℂ) R =
        Ψ.symm '' closedBall (0 : Schoenflies.Plane) R := by
      rw [hΨball, complexEuclidean_symm_zero]
    rw [h0, ← hΨball, ← hFEball]
    change (Ψ.symm ∘ Θ ∘ FE ∘ Ψ) '' (Ψ.symm '' closedBall 0 R) =
      Ψ.symm '' ((Θ ∘ FE) '' closedBall 0 R)
    rw [image_comp, image_comp, image_comp, ← image_comp Ψ, Homeomorph.self_comp_symm, image_id,
      ← image_comp Θ FE]
  obtain ⟨d, hd⟩ := exists_local_orientedChart_of_disk_image g hR hr _ hgdisk
  exact exists_orientedChart_straightening_of_local_agreement' gamma g hg d 0 hd

end
end FiniteAvalanches.Electrical.StatementGeometry
