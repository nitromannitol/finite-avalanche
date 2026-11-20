import FiniteAvalanches.Support.Plane.JordanLoopExtension
import FiniteAvalanches.Support.Plane.LoopPaths

/-!
# Jordan curves from two arcs

Two injective paths meeting exactly at their endpoints form a Jordan curve.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- Two simple plane paths with only their endpoints in common form a Jordan curve. -/
theorem isJordanCurve_of_two_paths {x y : ℝ × ℝ} (p q : Path x y)
    (hp : Function.Injective p) (hq : Function.Injective q)
    (hmeet : range p ∩ range q = {x, y}) :
    Schoenflies.IsJordanCurve (euclideanPlaneHomeomorph '' (range p ∪ range q)) := by
  let L : Path x x := p.trans q.symm
  have hL : InjOn L {t : unitInterval | (t : ℝ) < 1} :=
    path_trans_symm_injOn_of_inter_eq_endpoints p q hp hq hmeet
  let f : ℝ → Schoenflies.Plane := euclideanPlaneHomeomorph ∘ L.extend
  have hf : Schoenflies.IsLoop f := by
    refine ⟨?_, ?_, ?_⟩
    · exact (euclideanPlaneHomeomorph.continuous.comp L.continuous_extend).continuousOn
    · simp only [f, Function.comp_apply, Path.extend_zero, Path.extend_one]
    · intro s hs t ht hst
      have hse : f s = euclideanPlaneHomeomorph (L ⟨s, ⟨hs.1, hs.2.le⟩⟩) := by
        simp only [f, Function.comp_apply, Path.extend_apply _ ⟨hs.1, hs.2.le⟩]
      have hte : f t = euclideanPlaneHomeomorph (L ⟨t, ⟨ht.1, ht.2.le⟩⟩) := by
        simp only [f, Function.comp_apply, Path.extend_apply _ ⟨ht.1, ht.2.le⟩]
      rw [hse, hte] at hst
      exact congrArg Subtype.val (hL hs.2 ht.2 (euclideanPlaneHomeomorph.injective hst))
  have hrange : range L = range p ∪ range q := by
    rw [show L = p.trans q.symm from rfl, Path.trans_range, Path.symm_range]
  refine ⟨f, hf, ?_⟩
  rw [← hrange]
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨L ⟨t, ht⟩, ⟨⟨t, ht⟩, rfl⟩, by simp [f, Path.extend_apply _ ht]⟩
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨t.val, t.property, by simp [f, Path.extend_apply _ t.property]⟩

end FiniteAvalanches.Electrical.StatementGeometry
