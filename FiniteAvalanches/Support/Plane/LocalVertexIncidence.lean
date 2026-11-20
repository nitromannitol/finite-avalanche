import FiniteAvalanches.Support.Plane.UnchartedFaces

/-!
# Local face incidence at vertices

A face accumulating at a vertex meets the interior of an edge in every
connected neighborhood containing an edge interior point.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open Source BSST Set
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- In a connected open neighborhood, an incident face meets an edge interior
in its frontier if the neighborhood contains an edge interior point. -/
theorem exists_edge_interior_frontier_in_open (D : Drawing J) (v : V) (F : Face D)
    {U : Set Plane} (hU : IsOpen U) (hconn : IsPreconnected U) (hv : D.point v ∈ U)
    (hF : incident D v F)
    (htrace : ∃ (e : E) (t : ArcParameter), 0 < t.val ∧ t.val < 1 ∧ D.curve e t ∈ U) :
    ∃ (e : E) (t : ArcParameter), 0 < t.val ∧ t.val < 1 ∧
      D.curve e t ∈ U ∧ D.curve e t ∈ frontier (faceRegion D F) := by
  classical
  have hfront : ¬ frontier (faceRegion D F) ∩ U ⊆ range D.point := by
    intro hsub
    let S : Set Plane := U \ range D.point
    have hS : IsPreconnected S := isPreconnected_sdiff_finite hU hconn (finite_range D.point)
    obtain ⟨a, haU, haF⟩ := mem_closure_iff.mp hF U hU hv
    have haS : a ∈ S := ⟨haU, fun h => haF.1 (Or.inl h)⟩
    have hclosure : closure (faceRegion D F) ∩ S ⊆ faceRegion D F := by
      rintro z ⟨hz, hzU, hzv⟩
      by_contra hzF
      apply hzv
      apply hsub
      exact ⟨by rw [frontier, (punctured_faceRegion_isOpen D F).interior_eq]; exact ⟨hz, hzF⟩, hzU⟩
    have hSF : S ⊆ faceRegion D F :=
      hS.subset_of_closure_inter_subset (punctured_faceRegion_isOpen D F) ⟨a, haS, haF⟩ hclosure
    obtain ⟨e, t, ht0, ht1, htU⟩ := htrace
    have htS : D.curve e t ∈ S := by
      refine ⟨htU, ?_⟩
      rintro ⟨w, hw⟩
      exact D.avoids e t ht0 ht1 w hw.symm
    exact (hSF htS).1 (Or.inr (mem_iUnion.mpr ⟨e, t, rfl⟩))
  obtain ⟨z, ⟨hz, hzU⟩, hzv⟩ := not_subset.mp hfront
  have hztrace := frontier_faceRegion_subset_trace D F hz
  rcases hztrace with hzpoint | hzedge
  · exact (hzv hzpoint).elim
  · obtain ⟨e, t, ht⟩ := mem_iUnion.mp hzedge
    have ht0 : 0 < t.val := by
      by_contra h
      have heq : t = 0 := Subtype.ext (le_antisymm (le_of_not_gt h) t.property.1)
      apply hzv
      exact ⟨J.left e, by rw [← ht, heq]; exact (D.start e).symm⟩
    have ht1 : t.val < 1 := by
      by_contra h
      have heq : t = 1 := Subtype.ext (le_antisymm t.property.2 (le_of_not_gt h))
      apply hzv
      exact ⟨J.right e, by rw [← ht, heq]; exact (D.finish e).symm⟩
    exact ⟨e, t, ht0, ht1, ht ▸ hzU, ht ▸ hz⟩

end FiniteAvalanches.Electrical.StatementGeometry
