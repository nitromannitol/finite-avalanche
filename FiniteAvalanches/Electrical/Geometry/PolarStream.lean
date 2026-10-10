import FiniteAvalanches.Electrical.Geometry.PolarDual
import FiniteAvalanches.External.BSST

/-! The registered intrinsic construction gives the literal source stream for
EVERY given physical outer arc, with original copied currents and ground. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.Source
open StatementGeometry BSST
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

/-- No stream is selected until its complete existence and uniqueness are proved. -/
theorem existsUnique_polar_stream (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (hc : (supportGraph J.left J.right).Preconnected) (alpha beta : V)
    (hne : alpha ≠ beta) (A : OuterArc D alpha beta) :
    ∃! psi : A.embedding.Face → ℝ,
      stream_spec D alpha beta A (voltage J alpha beta hc) psi := by
  let B := auxiliaryArcOfOuterArc D alpha beta A
  obtain ⟨_,h⟩ := FiniteAvalanches.External.bsst_square_tiling J D.drawing hc alpha beta hne
    A.face A.alpha_incident A.beta_incident A.unbounded
  obtain ⟨face0,face1,_,hcharts,hunique,_⟩ := h B
  have he (z : E ⊕ Unit) :
      A.embedding.rightFace z = face0 z ∧ A.embedding.leftFace z = face1 z :=
    hcharts z (A.embedding.edgeChart z)
  obtain ⟨psi,hpsi,huni⟩ := hunique
  refine ⟨psi,?_,?_⟩
  · exact source_stream_consumer J D alpha beta A face0 face1 psi _ hcharts
      hpsi.1 hpsi.2.1 hpsi.2.2
  · intro chi hchi
    apply huni chi
    refine ⟨?_,?_,?_⟩
    · intro e
      simpa only [← (he (.inl e)).1,← (he (.inl e)).2] using hchi.1 e
    · simpa only [← (he (.inr ())).1] using hchi.2.2.1
    · simpa only [← (he (.inr ())).2] using hchi.2.2.2

/-- In the predetermined physical polar-dual orientation, stream INCREMENTS are
primal currents; dual unit-current gradients therefore have the opposite sign. -/
theorem polar_stream_copy (J : CopiedGraph V E) (D : PlaneEmbedding J)
    (alpha beta : V) (A : OuterArc D alpha beta) (phi : V → ℝ)
    (psi : A.embedding.Face → ℝ) (hpsi : stream_spec D alpha beta A phi psi) (e : E) :
    psi ((polarDual A).right e) - psi ((polarDual A).left e) = phi (J.left e)-phi (J.right e) ∧
      psi (polarGround A) = 0 ∧ psi (polarSource A) = mass J phi :=
  ⟨hpsi.1 e,hpsi.2.2.1,hpsi.2.2.2⟩

end
end FiniteAvalanches.Electrical.Source
