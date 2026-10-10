import FiniteAvalanches.Electrical.Geometry.DrawingBoundaryPath
import FiniteAvalanches.Electrical.Geometry.CirclePathLift

namespace FiniteAvalanches.Electrical.StatementGeometry
open Set unitInterval
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- Literal two-coordinate unit-circle points as Mathlib circle points. -/
def circlePoint (z : ℝ × ℝ) (hz : z ∈ circle) : Circle :=
  ⟨Complex.equivRealProdCLM.symm z, by
    suffices h : ‖Complex.equivRealProdCLM.symm z‖ = 1 by
      simpa [Submonoid.unitSphere] using h
    rw [Complex.norm_def, Complex.normSq_apply]
    change Real.sqrt (z.1 * z.1 + z.2 * z.2) = 1
    rw [← pow_two, ← pow_two, show z.1 ^ 2 + z.2 ^ 2 = 1 from hz]
    norm_num⟩

namespace Drawing

/-- Circle angles follow the actual simple boundary path in one of the two global directions.
No direction, cyclic order, or angular coordinates are supplied as hypotheses. -/
theorem boundary_path_angles (D : Drawing J) (m : ℕ) (hm : 0 < m)
    (p : Fin (m + 1) → V) (hp : Function.Injective p) (copies : Fin m → E)
    (hends : ∀ i, (J.left (copies i) = p i.castSucc ∧ J.right (copies i) = p i.succ) ∨
      (J.right (copies i) = p i.castSucc ∧ J.left (copies i) = p i.succ))
    (hboundary : ∀ i t, D.curve (copies i) t ∈ circle) :
    ∃ θ : Fin (m + 1) → ℝ, (StrictMono θ ∨ StrictAnti θ) ∧
      |θ (Fin.last m) - θ 0| < 2 * Real.pi ∧
      ∀ k, D.point (p k) = (Real.cos (θ k), Real.sin (θ k)) := by
  cases m with
  | zero => omega
  | succ n =>
    obtain ⟨f, hf, τ, hτ, h0, h1, hvisit, hrange⟩ :=
      D.boundary_path_realization n p hp copies hends
    have hb (t : I) : f t ∈ circle := by
      obtain ⟨i, s, hs⟩ := hrange t
      rw [hs]
      exact hboundary i s
    let g : C(I, Circle) := ⟨fun t => circlePoint (f t) (hb t),
      (Complex.equivRealProdCLM.symm.continuous.comp f.continuous).subtype_mk _⟩
    have hg : Function.Injective g := by
      intro s t h
      apply hf
      apply Complex.equivRealProdCLM.symm.injective
      exact congrArg Subtype.val h
    obtain ⟨φ, hφ, hmono, hspan⟩ := simple_circle_path_angles g hg
    refine ⟨fun k => φ (τ k), hmono.imp (fun h => h.comp hτ) (fun h => h.comp_strictMono hτ), ?_, ?_⟩
    · simpa only [h0, h1] using hspan
    · intro k
      have he := congrArg (fun z : Circle => Complex.equivRealProdCLM (z : ℂ)) (hφ (τ k))
      change Complex.equivRealProdCLM (Complex.exp ((φ (τ k) : ℂ) * Complex.I)) = f (τ k) at he
      rw [Complex.exp_mul_I] at he
      have he' : (Real.cos (φ (τ k)), Real.sin (φ (τ k))) = f (τ k) := by
        simpa only [← Complex.ofReal_cos, ← Complex.ofReal_sin,
          Complex.equivRealProdCLM_apply, Complex.add_re, Complex.mul_re,
          Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
          zero_add, mul_one] using he
      exact (hvisit k).symm.trans he'.symm

end Drawing
end
end FiniteAvalanches.Electrical.StatementGeometry
