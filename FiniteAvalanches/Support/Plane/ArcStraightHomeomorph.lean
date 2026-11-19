import FiniteAvalanches.Support.Plane.JordanLoopExtension
import FiniteAvalanches.Support.Plane.StraightModel
import FiniteAvalanches.Support.Plane.LoopPaths

/-!
# Straightening a side of a Jordan loop

The relative Jordan–Schönflies theorem sends either of two complementary arcs
of a simple loop to a horizontal interval with its parametrization preserved.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval
open scoped Classical

/-- An injective plane path with a simple closing arc can be straightened by a
homeomorphism of the plane, preserving its parameter. -/
theorem exists_plane_homeomorph_straightening_of_closing_arc
    {x y : ℝ × ℝ} (p q : Path x y) (hp : Function.Injective p)
    (hq : Function.Injective q) (hmeet : range p ∩ range q = {x, y}) :
    ∃ F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), ∀ t : unitInterval, F (p t) = (t.val, 0) := by
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
      have hparam := hL hs.2 ht.2 (euclideanPlaneHomeomorph.injective hst)
      exact congrArg Subtype.val hparam
  obtain ⟨g, hg, hgside⟩ := Schoenflies.exists_loop_with_straight_side
  obtain ⟨F, hF⟩ := hf.exists_plane_homeomorph hg
  let R : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
    euclideanPlaneHomeomorph.trans (F.trans euclideanPlaneHomeomorph.symm)
  refine ⟨R, ?_⟩
  intro t
  have ht : (t.val / 2 : ℝ) ∈ I := ⟨by linarith [t.property.1], by linarith [t.property.2]⟩
  have hmatch := hF (t.val / 2) ht
  have hside := hgside t.val t.property
  have hsource : f (t.val / 2) = euclideanPlaneHomeomorph (p t) := by
    change euclideanPlaneHomeomorph (L.extend (t.val / 2)) = _
    rw [show L.extend (t.val / 2) = p.extend (2 * (t.val / 2)) from
      Path.extend_trans_of_le_half p q.symm (by linarith [t.property.2])]
    have h2 : 2 * (t.val / 2) = t.val := by ring
    rw [h2, Path.extend_apply _ t.property]
  rw [hsource, hside] at hmatch
  change euclideanPlaneHomeomorph.symm (F (euclideanPlaneHomeomorph (p t))) = (t.val, 0)
  rw [hmatch]
  rfl

end FiniteAvalanches.Electrical.StatementGeometry
