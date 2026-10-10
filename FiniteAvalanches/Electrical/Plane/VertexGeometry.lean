import FiniteAvalanches.Electrical.Plane.Rectangle
import FiniteAvalanches.Electrical.Plane.Sides
import FiniteAvalanches.Electrical.Plane.LargestCurrent

/-! Actual stream existence consumes the closed-square containment and free-vertex segment bounds.
The source plane-to-rotation/Euler bridge and square disjointness/coverage are separate. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical
open FiniteAvalanches.Electrical.Geometry

/-- The source's range, containment and free-vertex geometry follow jointly from the actual constructed stream. -/
theorem existsUnique_vertex_geometry_of_euler {V E : Type*} [Fintype V] [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hc : (supportGraph a b).Preconnected)
    (hface : R.rightFace da = R.rightFace db)
    (heuler : Fintype.card V+Fintype.card R.Face = Fintype.card E+2)
    (d : ℝ) (hdeg : ∀ x, x ≠ alpha → x ≠ beta → degree a b x ≤ d)
    (phi : V → ℝ) (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0) :
    ∃! psi : ArcFace R da db → ℝ,
      ∃ hp : ∀ z, psi (arcLeftFace R da db z)-psi (arcRightFace R da db z) =
          arcCurrent a b phi (energy a b phi) z,
        psi (arcRightFace R da db (.inr false)) = 0 ∧
        (∀ f, 0 ≤ psi f ∧ psi f ≤ energy a b phi) ∧
        (∀ z : Dart E, (incrementSquare R da db phi psi z (hp (.inl z))).carrier ⊆
          rectangle 0 1 0 (energy a b phi)) ∧
        ∀ x, x ≠ alpha → x ≠ beta →
          let hx := incidenceDarts_nonempty a b alpha beta hne hc x
          0 ≤ streamMax R da db psi x hx-streamMin R da db psi x hx ∧
          streamMax R da db psi x hx-streamMin R da db psi x hx ≤ d*largestCurrent a b phi x hx ∧
          ∀ z : Dart E, tail a b z = x ∨ head a b z = x →
            ∀ p ∈ (incrementSquare R da db phi psi z (hp (.inl z))).carrier,
              p.1 = phi x → p ∈ vertexSegment R da db phi psi x hx := by
  obtain ⟨psi,hpsi,hu⟩ := existsUnique_normalized_stream_of_euler
    R alpha beta hne da db ha hb hc hface heuler phi hp0 hp1 hh
  refine ⟨psi,⟨hpsi.1,hpsi.2,?_,?_,?_⟩,?_⟩
  · exact stream_range R alpha beta hne da db ha hb hc phi (energy a b phi)
      (energy_nonneg a b phi) psi hpsi.1 hpsi.2
  · exact incrementSquare_subset_rectangle R alpha beta hne da db ha hb hc phi hp0 hp1 hh psi hpsi.1 hpsi.2
  · intro x hx0 hx1
    let hx := incidenceDarts_nonempty a b alpha beta hne hc x
    exact ⟨stream_span_nonneg R da db psi x hx,
      stream_span_le_degree_mul R alpha beta da db ha hb phi (energy a b phi) psi hpsi.1 x hx0 hx1 hx d (hdeg x hx0 hx1),
      fun z hz => incidentSquare_side_subset R alpha beta da db ha hb phi (energy a b phi) psi hpsi.1 x hx0 hx1 hx z hz⟩
  · intro chi hchi
    obtain ⟨hj,hzero,_⟩ := hchi
    exact hu chi ⟨hj,hzero⟩

end FiniteAvalanches.Electrical.Plane
