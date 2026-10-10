import FiniteAvalanches.Electrical.Plane.ClosedCoverage
import FiniteAvalanches.Electrical.Plane.VertexGeometry

/-! Stream existence consumes the actual copied square tiling and every free-vertex segment assertion.
The geometric plane embedding to rotation/common-face/Euler bridge remains separate. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical
open FiniteAvalanches.Electrical.Geometry

/-- The constructed stream yields actual disjoint interiors, closed rectangle coverage and free-vertex geometry. -/
theorem existsUnique_stream_tiling_of_euler {V E : Type*} [Fintype V] [Fintype E] {a b : E → V}
    (R : EdgeRotation a b) (alpha beta : V) (hne : alpha ≠ beta) (da db : Dart E)
    (ha : tail a b da = alpha) (hb : tail a b db = beta)
    (hc : (supportGraph a b).Preconnected)
    (hface : R.rightFace da = R.rightFace db)
    (heuler : Fintype.card V+Fintype.card R.Face = Fintype.card E+2)
    (d : ℝ) (hdeg : ∀ x, x ≠ alpha → x ≠ beta → degree a b x ≤ d)
    (phi : V → ℝ) (hp0 : phi alpha = 0) (hp1 : phi beta = 1)
    (hh : ∀ x, x ≠ alpha → x ≠ beta → laplacian a b phi x = 0) :
    ∃! psi : ArcFace R da db → ℝ,
      ∃ hp : ∀ z, psi (arcLeftFace R da db z)-psi (arcRightFace R da db z) = arcCurrent a b phi (energy a b phi) z,
        psi (arcRightFace R da db (.inr false)) = 0 ∧
        Set.PairwiseDisjoint (↑(Finset.univ : Finset E))
          (fun e => (incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).openCarrier) ∧
        (⋃ e : E, (incrementSquare R da db phi psi (e,false) (hp (.inl (e,false)))).carrier) =
          rectangle 0 1 0 (energy a b phi) ∧
        ∀ x, x ≠ alpha → x ≠ beta →
          let hx := incidenceDarts_nonempty a b alpha beta hne hc x
          0 ≤ streamMax R da db psi x hx-streamMin R da db psi x hx ∧
          streamMax R da db psi x hx-streamMin R da db psi x hx ≤ d*largestCurrent a b phi x hx ∧
          ∀ z : Dart E, tail a b z = x ∨ head a b z = x →
            ∀ p ∈ (incrementSquare R da db phi psi z (hp (.inl z))).carrier,
              p.1 = phi x → p ∈ vertexSegment R da db phi psi x hx := by
  obtain ⟨psi,⟨hp,h0,_,_,hvertex⟩,_⟩ := existsUnique_vertex_geometry_of_euler
    R alpha beta hne da db ha hb hc hface heuler d hdeg phi hp0 hp1 hh
  refine ⟨psi,⟨hp,h0,?_,?_,hvertex⟩,?_⟩
  · exact square_open_disjoint R alpha beta hne da db ha hb hc phi hp0 hp1 hh (energy a b phi) psi hp
  · exact square_union_eq_rectangle R alpha beta hne da db ha hb hc hface phi hp0 hp1 hh psi hp h0
  · intro chi hchi
    obtain ⟨hcj,hc0,_⟩ := hchi
    exact (existsUnique_normalized_stream_of_euler R alpha beta hne da db ha hb hc hface heuler phi hp0 hp1 hh).unique
      ⟨hcj,hc0⟩ ⟨hp,h0⟩

end FiniteAvalanches.Electrical.Plane
