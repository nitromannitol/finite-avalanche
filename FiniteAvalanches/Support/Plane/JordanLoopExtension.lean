import FiniteAvalanches.Support.Schoenflies.JordanSchoenflies
import FiniteAvalanches.Electrical.Geometry.DiskDrawing
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Plane extension of parametrized Jordan curves

A correspondence between two Jordan curves that matches their loop parameters
extends to a homeomorphism of the whole plane. The same statement is given in
product coordinates for plane drawings.
-/

namespace Schoenflies

open Set unitInterval

/-- Two parametrized Jordan loops are related by a plane homeomorphism that
preserves their parameters. -/
theorem IsLoop.exists_plane_homeomorph {f g : ℝ → Plane}
    (hf : IsLoop f) (hg : IsLoop g) :
    ∃ F : Plane ≃ₜ Plane, ∀ t ∈ I, F (f t) = g t := by
  obtain ⟨e, he⟩ := hf.exists_homeomorph hg
  have hCf : IsJordanCurve (f '' I) := ⟨f, hf, rfl⟩
  have hCg : IsJordanCurve (g '' I) := ⟨g, hg, rfl⟩
  obtain ⟨F, hF⟩ := jordan_schoenflies_of_homeomorph hCf hCg e
  refine ⟨F, ?_⟩
  intro t ht
  exact (hF ⟨f t, mem_image_of_mem f ht⟩).trans (he t ht)

end Schoenflies

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- The standard coordinate homeomorphism from the drawing plane to Euclidean coordinates. -/
noncomputable def euclideanPlaneHomeomorph : (ℝ × ℝ) ≃ₜ Schoenflies.Plane :=
  ((PiLp.homeomorph 2 (fun _ : Fin 2 => ℝ)).trans (Homeomorph.finTwoArrow : (Fin 2 → ℝ) ≃ₜ ℝ × ℝ)).symm

/-- Parameter-matched Jordan loops in the drawing plane extend to a plane homeomorphism. -/
theorem exists_plane_homeomorph_of_matched_loops
    (f g : ℝ → ℝ × ℝ)
    (hf : Schoenflies.IsLoop (euclideanPlaneHomeomorph ∘ f))
    (hg : Schoenflies.IsLoop (euclideanPlaneHomeomorph ∘ g)) :
    ∃ F : (ℝ × ℝ) ≃ₜ (ℝ × ℝ), ∀ t ∈ I, F (f t) = g t := by
  obtain ⟨F, hF⟩ := hf.exists_plane_homeomorph hg
  refine ⟨euclideanPlaneHomeomorph.trans (F.trans euclideanPlaneHomeomorph.symm), ?_⟩
  intro t ht
  change euclideanPlaneHomeomorph.symm (F (euclideanPlaneHomeomorph (f t))) = g t
  have h := hF t ht
  change F (euclideanPlaneHomeomorph (f t)) = euclideanPlaneHomeomorph (g t) at h
  rw [h, euclideanPlaneHomeomorph.symm_apply_apply]

end FiniteAvalanches.Electrical.StatementGeometry
