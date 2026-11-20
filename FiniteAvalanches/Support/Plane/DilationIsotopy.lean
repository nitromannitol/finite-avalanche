import FiniteAvalanches.Electrical.Geometry.OrientedDrawing
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Dilation isotopies

A homeomorphism that agrees with the identity near the origin admits a
jointly continuous isotopy to the identity by conjugation with dilations.
The inverse isotopy is jointly continuous as well.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Filter
open scoped Topology

noncomputable section
open FiniteAvalanches.Electrical.Source

private def dilationFamily (f : Plane → Plane) (p : ℝ × Plane) : Plane :=
  if p.1 = 0 then p.2 else p.1⁻¹ • f (p.1 • p.2)

private theorem continuous_dilationFamily (f : Plane → Plane) (hf : Continuous f)
    (hloc : f =ᶠ[𝓝 0] id) : Continuous (dilationFamily f) := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p.1 = 0
  · have he : ∀ᶠ q : ℝ × Plane in 𝓝 p, f (q.1 • q.2) = q.1 • q.2 := by
      have hc : Continuous (fun q : ℝ × Plane => q.1 • q.2) := by fun_prop
      have ht : Tendsto (fun q : ℝ × Plane => q.1 • q.2) (𝓝 p) (𝓝 0) := by
        simpa only [hp, zero_smul] using (hc.continuousAt (x := p)).tendsto
      exact ht hloc
    have heq : dilationFamily f =ᶠ[𝓝 p] fun q : ℝ × Plane => q.2 := by
      filter_upwards [he] with q hq
      by_cases hq0 : q.1 = 0
      · simp [dilationFamily, hq0]
      · simp [dilationFamily, hq0, hq, ← mul_smul]
    exact continuous_snd.continuousAt.congr_of_eventuallyEq heq
  · have heq : dilationFamily f =ᶠ[𝓝 p]
        fun q : ℝ × Plane => q.1⁻¹ • f (q.1 • q.2) := by
      filter_upwards [continuous_fst.continuousAt.eventually_ne hp] with q hq
      simp [dilationFamily, hq]
    have hc : ContinuousAt (fun q : ℝ × Plane => q.1⁻¹ • f (q.1 • q.2)) p := by
      fun_prop (disch := assumption)
    exact hc.congr_of_eventuallyEq heq

/-- A plane homeomorphism equal to the identity near the origin is isotopic to
    the identity, with a jointly continuous inverse isotopy. -/
noncomputable def orientedChartOfIdentityNearOrigin (f : Plane ≃ₜ Plane)
    (hf : f =ᶠ[𝓝 0] id) : OrientedChart where
  map := f
  isotopy t := if ht : (t : ℝ) = 0 then Homeomorph.refl Plane else
    ((Homeomorph.smulOfNeZero (t : ℝ) ht).trans f).trans
      (Homeomorph.smulOfNeZero (t : ℝ) ht).symm
  continuous := by
    have h := continuous_dilationFamily f f.continuous hf
    have hc : Continuous (fun p : ArcParameter × Plane => ((p.1 : ℝ), p.2)) := by fun_prop
    convert h.comp hc using 1
    funext p
    by_cases hp : (p.1 : ℝ) = 0
    · simp [dilationFamily, hp]
    · simp [dilationFamily, hp, Homeomorph.smulOfNeZero_symm_apply]
  inverse_continuous := by
    have hfi : f.symm =ᶠ[𝓝 0] id := by
      filter_upwards [hf] with x hx
      change f x = x at hx
      change f.symm x = x
      calc
        f.symm x = f.symm (f x) := congrArg f.symm hx.symm
        _ = x := f.symm_apply_apply x
    have h := continuous_dilationFamily f.symm f.symm.continuous hfi
    have hc : Continuous (fun p : ArcParameter × Plane => ((p.1 : ℝ), p.2)) := by fun_prop
    convert h.comp hc using 1
    funext p
    by_cases hp : (p.1 : ℝ) = 0
    · simp [dilationFamily, hp]
    · simp [dilationFamily, hp, Homeomorph.smulOfNeZero_symm_apply]
  start := by simp
  finish := by
    apply Homeomorph.ext
    intro x
    simp [Homeomorph.smulOfNeZero_symm_apply]


/-- A plane homeomorphism equal to the identity near any point is isotopic to
    the identity, with a jointly continuous inverse isotopy. -/
noncomputable def orientedChartOfIdentityNearPoint (f : Plane ≃ₜ Plane) (z : Plane)
    (hf : f =ᶠ[𝓝 z] id) : OrientedChart := by
  let T : Plane ≃ₜ Plane := Homeomorph.addLeft z
  let g : Plane ≃ₜ Plane := (T.trans f).trans T.symm
  have hg : g =ᶠ[𝓝 0] id := by
    have hT : Filter.Tendsto T (𝓝 0) (𝓝 z) := by
      simpa [T] using T.continuous.continuousAt.tendsto (x := 0)
    filter_upwards [hT hf] with x hx
    change f (T x) = T x at hx
    change T.symm (f (T x)) = x
    rw [hx, T.symm_apply_apply]
  let c := orientedChartOfIdentityNearOrigin g hg
  exact {
    map := f
    isotopy := fun t => (T.symm.trans (c.isotopy t)).trans T
    continuous := T.continuous.comp (c.continuous.comp
      (continuous_fst.prodMk (T.symm.continuous.comp continuous_snd)))
    inverse_continuous := T.continuous.comp (c.inverse_continuous.comp
      (continuous_fst.prodMk (T.symm.continuous.comp continuous_snd)))
    start := by
      rw [c.start]
      apply Homeomorph.ext
      intro x
      change T (T.symm x) = x
      exact T.apply_symm_apply x
    finish := by
      rw [c.finish]
      apply Homeomorph.ext
      intro x
      change T (g (T.symm x)) = f x
      change T (T.symm (f (T (T.symm x)))) = f x
      rw [T.apply_symm_apply, T.apply_symm_apply]
  }

end
end FiniteAvalanches.Electrical.StatementGeometry
