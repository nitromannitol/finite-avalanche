import FiniteAvalanches.Electrical.Geometry.BSST

open FiniteAvalanches.Electrical
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Source (Plane drawingTrace augmentedGraph voltage mass)
open scoped Classical

namespace FiniteAvalanches.Electrical.BSST

/-- The classical face characterization immediately yields genuine original endpoint incidence. -/
theorem actual_copy_face_consumer {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Drawing J) (F : Face D) (alpha beta : V)
    (A : AuxiliaryArc D F alpha beta)
    (face0 face1 : E ⊕ Unit → Face A.drawing)
    (hfaces : ∀ z, edgeFaces A.drawing z = {face0 z,face1 z}) (e : E) :
    incident A.drawing (J.left e) (face0 (.inl e)) ∧
    incident A.drawing (J.right e) (face0 (.inl e)) ∧
    incident A.drawing (J.left e) (face1 (.inl e)) ∧
    incident A.drawing (J.right e) (face1 (.inl e)) := by
  have h0 : face0 (.inl e) ∈ edgeFaces A.drawing (.inl e) := by
    rw [hfaces (.inl e)]
    exact Set.mem_insert _ _
  have h1 : face1 (.inl e) ∈ edgeFaces A.drawing (.inl e) := by
    rw [hfaces (.inl e)]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hi0 := edgeFaces_endpoints A.drawing (.inl e) (face0 (.inl e)) h0
  have hi1 := edgeFaces_endpoints A.drawing (.inl e) (face1 (.inl e)) h1
  exact ⟨hi0.1,hi0.2,hi1.1,hi1.2⟩

/-- Chart-compatible intrinsic face labels reconstruct the exact source stream equation. -/
theorem source_stream_consumer {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J) (alpha beta : V)
    (A : Source.OuterArc D alpha beta)
    (face0 face1 : E ⊕ Unit → Face A.embedding.drawing)
    (psi : Face A.embedding.drawing → ℝ) (phi : V → ℝ)
    (hcharts : ∀ z (c : Source.EdgeChart A.embedding.drawing z),
      negativeChartFace A.embedding.drawing z c = face0 z ∧
      positiveChartFace A.embedding.drawing z c = face1 z)
    (hcurrent : ∀ e, psi (face1 (.inl e))-psi (face0 (.inl e)) =
      phi (J.left e)-phi (J.right e))
    (h0 : psi (face0 (.inr ())) = 0) (h1 : psi (face1 (.inr ())) = mass J phi) :
    Source.stream_spec D alpha beta A phi psi := by
  have hf0 (z : E ⊕ Unit) : A.embedding.rightFace z = face0 z :=
    (hcharts z (A.embedding.edgeChart z)).1
  have hf1 (z : E ⊕ Unit) : A.embedding.leftFace z = face1 z :=
    (hcharts z (A.embedding.edgeChart z)).2
  refine ⟨?_,?_,?_,?_⟩
  · intro e
    rw [hf1,hf0]
    exact hcurrent e
  · rw [hf1,hf0,h1,h0,sub_zero]
  · rw [hf0]
    exact h0
  · rw [hf1]
    exact h1

end FiniteAvalanches.Electrical.BSST

namespace FiniteAvalanches.Electrical.BSST

/-- The uncharted physical-current characterization is exactly the existing source stream predicate. -/
theorem source_stream_spec_iff {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Source.PlaneEmbedding J) (alpha beta : V)
    (A : Source.OuterArc D alpha beta)
    (face0 face1 : E ⊕ Unit → Face A.embedding.drawing)
    (psi : Face A.embedding.drawing → ℝ) (phi : V → ℝ)
    (hcharts : ∀ z (c : Source.EdgeChart A.embedding.drawing z),
      negativeChartFace A.embedding.drawing z c = face0 z ∧
      positiveChartFace A.embedding.drawing z c = face1 z) :
    Source.stream_spec D alpha beta A phi psi ↔
      (∀ e, psi (face1 (.inl e))-psi (face0 (.inl e)) =
        phi (J.left e)-phi (J.right e)) ∧
      psi (face0 (.inr ())) = 0 ∧ psi (face1 (.inr ())) = mass J phi := by
  have hf0 (z : E ⊕ Unit) : A.embedding.rightFace z = face0 z :=
    (hcharts z (A.embedding.edgeChart z)).1
  have hf1 (z : E ⊕ Unit) : A.embedding.leftFace z = face1 z :=
    (hcharts z (A.embedding.edgeChart z)).2
  constructor
  · rintro ⟨hcurrent,_,h0,h1⟩
    refine ⟨?_,?_,?_⟩
    · intro e
      simpa only [hf0,hf1] using hcurrent e
    · simpa only [hf0] using h0
    · simpa only [hf1] using h1
  · rintro ⟨hcurrent,h0,h1⟩
    exact source_stream_consumer J D alpha beta A face0 face1 psi phi hcharts hcurrent h0 h1

end FiniteAvalanches.Electrical.BSST
