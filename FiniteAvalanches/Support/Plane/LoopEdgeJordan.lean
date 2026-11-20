import FiniteAvalanches.Support.Plane.JordanLoopExtension
import FiniteAvalanches.Support.Schoenflies.JordanClosed

/-!
# Jordan curves from loop edges

A loop edge of a copied graph is a Jordan curve and separates the plane.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- A loop edge in a drawing is a Jordan curve in Euclidean coordinates. -/
theorem Drawing.loop_isJordanCurve {V E : Type} [Fintype V] [Fintype E]
    {G : CopiedGraph V E} (D : Drawing G) (e : E) (hloop : G.left e = G.right e) :
    Schoenflies.IsJordanCurve (euclideanPlaneHomeomorph '' range (D.curve e)) := by
  let p : Path (D.point (G.left e)) (D.point (G.left e)) :=
    ⟨⟨D.curve e, D.continuous e⟩, D.start e,
      (D.finish e).trans (congrArg D.point hloop.symm)⟩
  let f : ℝ → Schoenflies.Plane := euclideanPlaneHomeomorph ∘ p.extend
  have hf : Schoenflies.IsLoop f := by
    refine ⟨?_, ?_, ?_⟩
    · exact (euclideanPlaneHomeomorph.continuous.comp p.continuous_extend).continuousOn
    · simp only [f, Function.comp_apply, Path.extend_zero, Path.extend_one]
    · intro s hs t ht hst
      have hse : f s = euclideanPlaneHomeomorph (D.curve e ⟨s, ⟨hs.1, hs.2.le⟩⟩) := by
        simp only [f, Function.comp_apply, Path.extend_apply _ ⟨hs.1, hs.2.le⟩]
        rfl
      have hte : f t = euclideanPlaneHomeomorph (D.curve e ⟨t, ⟨ht.1, ht.2.le⟩⟩) := by
        simp only [f, Function.comp_apply, Path.extend_apply _ ⟨ht.1, ht.2.le⟩]
        rfl
      rw [hse, hte] at hst
      have hp := D.injective e hs.2 ht.2 (euclideanPlaneHomeomorph.injective hst)
      exact congrArg Subtype.val hp
  refine ⟨f, hf, ?_⟩
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨D.curve e ⟨t, ht⟩, ⟨⟨t, ht⟩, rfl⟩, ?_⟩
    simp only [f, Function.comp_apply, Path.extend_apply _ ht]
    rfl
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    refine ⟨t.val, t.property, ?_⟩
    simp only [f, Function.comp_apply, Path.extend_apply _ t.property]
    rfl

/-- A loop edge has exactly the two Jordan complement regions. -/
theorem Drawing.loop_isSeparating {V E : Type} [Fintype V] [Fintype E]
    {G : CopiedGraph V E} (D : Drawing G) (e : E) (hloop : G.left e = G.right e) :
    Schoenflies.IsSeparating (euclideanPlaneHomeomorph '' range (D.curve e)) :=
  Schoenflies.jordan_curve_theorem (D.loop_isJordanCurve e hloop)

end FiniteAvalanches.Electrical.StatementGeometry
