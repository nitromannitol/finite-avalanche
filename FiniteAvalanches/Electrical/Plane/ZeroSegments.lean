import FiniteAvalanches.Electrical.Plane.Sides
import FiniteAvalanches.Electrical.Plane.LargestCurrent

/-! Actual current maximizers and collapsed free-vertex segments, with existence before choice. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical
open FiniteAvalanches.Electrical.Geometry

/-- The largest current is attained by an original incident edge copy. -/
theorem exists_incident_max_current {V E : Type*} [Fintype E]
    (a b : E → V) (phi : V → ℝ) (x : V) (hx : (incidenceDarts a b x).Nonempty) :
    ∃ z : Dart E, tail a b z = x ∧ |current a b phi z| = largestCurrent a b phi x hx := by
  have hm : largestCurrent a b phi x hx ∈ (incidenceDarts a b x).image (fun z => |current a b phi z|) :=
    Finset.max'_mem _ _
  obtain ⟨z,hz,hmax⟩ := Finset.mem_image.mp hm
  exact ⟨z,(mem_incidenceDarts a b x z).mp hz,hmax⟩

/-- Zero largest current forces the actual nonempty free-vertex segment to be one point. -/
theorem vertexSegment_zero_current {V E : Type*} [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta) (phi : V → ℝ) (M : ℝ)
    (psi : ArcFace R da db → ℝ)
    (hp : ∀ z, psi (arcLeftFace R da db z)-psi (arcRightFace R da db z) = arcCurrent a b phi M z)
    (x : V) (hx0 : x ≠ alpha) (hx1 : x ≠ beta) (hx : (incidenceDarts a b x).Nonempty)
    (hz : largestCurrent a b phi x hx = 0) :
    vertexSegment R da db phi psi x hx = {(phi x,streamMin R da db psi x hx)} := by
  have hlo := stream_span_nonneg R da db psi x hx
  have hhi := stream_span_le_degree_mul R alpha beta da db ha hb phi M psi hp x hx0 hx1 hx
    (degree a b x) le_rfl
  rw [hz,mul_zero] at hhi
  have heq : streamMax R da db psi x hx = streamMin R da db psi x hx := by linarith only [hlo,hhi]
  ext p
  change (p.1 ∈ Set.Icc (phi x) (phi x) ∧
    p.2 ∈ Set.Icc (streamMin R da db psi x hx) (streamMax R da db psi x hx)) ↔ _
  rw [heq]
  simp only [Set.Icc_self,Set.mem_singleton_iff]
  exact ⟨fun h => Prod.ext h.1 h.2,fun h => ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩⟩

end FiniteAvalanches.Electrical.Plane
