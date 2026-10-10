import FiniteAvalanches.Electrical.Geometry.BoundaryAngles

namespace FiniteAvalanches.Electrical.StatementGeometry
noncomputable section

/-- Reflection changes the circle orientation while retaining all original graph copies. -/
def reflectPoint (z : ℝ × ℝ) : ℝ × ℝ := (z.1, -z.2)

theorem reflectPoint_injective : Function.Injective reflectPoint := by
  intro x y h
  apply Prod.ext
  · simpa only [reflectPoint] using congrArg Prod.fst h
  · have := congrArg Prod.snd h
    simpa only [reflectPoint, neg_inj] using this

theorem reflectPoint_mem_disk (z : ℝ × ℝ) : reflectPoint z ∈ disk ↔ z ∈ disk := by
  simp [reflectPoint, disk]

theorem reflectPoint_mem_circle (z : ℝ × ℝ) : reflectPoint z ∈ circle ↔ z ∈ circle := by
  simp [reflectPoint, circle]

namespace Drawing
variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- The literal reflected drawing of the same copied graph. -/
def reflect (D : Drawing J) : Drawing J where
  point := fun v => reflectPoint (D.point v)
  point_injective := reflectPoint_injective.comp D.point_injective
  curve := fun e t => reflectPoint (D.curve e t)
  continuous := fun e => (D.continuous e).fst.prodMk (D.continuous e).snd.neg
  injective := fun e _s hs _t ht h => D.injective e hs ht (reflectPoint_injective h)
  start := fun e => congrArg reflectPoint (D.start e)
  finish := fun e => congrArg reflectPoint (D.finish e)
  avoids := fun e t ht0 ht1 v h => D.avoids e t ht0 ht1 v (reflectPoint_injective h)
  intersects := fun e f hef s t h => D.intersects e f hef s t (reflectPoint_injective h)

/-- The actual boundary path has increasing circle coordinates after at most a global reflection. -/
theorem boundary_path_ordered_angles (D : Drawing J) (m : ℕ) (hm : 0 < m)
    (p : Fin (m + 1) → V) (hp : Function.Injective p) (copies : Fin m → E)
    (hends : ∀ i, (J.left (copies i) = p i.castSucc ∧ J.right (copies i) = p i.succ) ∨
      (J.right (copies i) = p i.castSucc ∧ J.left (copies i) = p i.succ))
    (hboundary : ∀ i t, D.curve (copies i) t ∈ circle) :
    ∃ D' : Drawing J, (D' = D ∨ D' = D.reflect) ∧
      ∃ θ : Fin (m + 1) → ℝ, StrictMono θ ∧
        θ (Fin.last m) < θ 0 + 2 * Real.pi ∧
        ∀ k, D'.point (p k) = (Real.cos (θ k), Real.sin (θ k)) := by
  obtain ⟨θ, hθ, hspan, hpoint⟩ := D.boundary_path_angles m hm p hp copies hends hboundary
  rcases hθ with hθ | hθ
  · refine ⟨D, Or.inl rfl, θ, hθ, ?_, hpoint⟩
    have := (abs_lt.mp hspan).2
    linarith
  · refine ⟨D.reflect, Or.inr rfl, fun k => -θ k, ?_, ?_, ?_⟩
    · intro a b hab
      exact neg_lt_neg (hθ hab)
    · have := (abs_lt.mp hspan).1
      dsimp
      linarith
    · intro k
      change reflectPoint (D.point (p k)) = _
      rw [hpoint k]
      simp [reflectPoint]

end Drawing
end
end FiniteAvalanches.Electrical.StatementGeometry
