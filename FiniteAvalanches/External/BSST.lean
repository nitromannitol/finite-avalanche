import FiniteAvalanches.Electrical.Geometry.BSSTStream

set_option autoImplicit false
open FiniteAvalanches.Electrical
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.BSST
open FiniteAvalanches.Electrical.Source (Plane drawingTrace augmentedGraph voltage mass)
open scoped Classical
namespace FiniteAvalanches.External

/-- Classical intrinsic stream/square corollary of Brooks–Smith–Stone–Tutte (1940),
§§3.3 and 4.1–4.3, printed pp319–322, on the actual complement faces and original
copied wires. Auxiliary existence, every auxiliary arc, physical given-chart side
compatibility, unique signed-current stream, and original closed-square coverage
are included. No chart or cyclic-order existence, vertex-range bound, split,
logarithmic or moment conclusion is trusted. -/
axiom bsst_square_tiling :
∀ {V E : Type} [Fintype V] [Fintype E]
    (J : CopiedGraph V E) (D : Drawing J)
    (hc : (supportGraph J.left J.right).Preconnected)
    (alpha beta : V) (_hne : alpha ≠ beta)
    (F : Face D) (_ha : incident D alpha F) (_hb : incident D beta F)
    (_houter : ¬Bornology.IsBounded (faceRegion D F)),
    let phi := voltage J alpha beta hc
    let M := mass J phi
    Nonempty (AuxiliaryArc D F alpha beta) ∧
    ∀ A : AuxiliaryArc D F alpha beta,
    ∃ face0 face1 : E ⊕ Unit → Face A.drawing,
      (∀ z, edgeFaces A.drawing z = {face0 z,face1 z}) ∧
      (∀ z (c : Source.EdgeChart A.drawing z),
        negativeChartFace A.drawing z c = face0 z ∧
        positiveChartFace A.drawing z c = face1 z) ∧
      (∃! psi : Face A.drawing → ℝ,
        (∀ e, psi (face1 (.inl e))-psi (face0 (.inl e)) =
          phi (J.left e)-phi (J.right e)) ∧
        psi (face0 (.inr ())) = 0 ∧ psi (face1 (.inr ())) = M) ∧
      ∀ psi : Face A.drawing → ℝ,
        ((∀ e, psi (face1 (.inl e))-psi (face0 (.inl e)) =
          phi (J.left e)-phi (J.right e)) ∧
          psi (face0 (.inr ())) = 0 ∧ psi (face1 (.inr ())) = M) →
        (∀ F, 0 ≤ psi F ∧ psi F ≤ M) ∧
        (∀ e f : E, e ≠ f → Disjoint
          (interior (copiedSquare J phi psi (fun e => face0 (.inl e))
            (fun e => face1 (.inl e)) e))
          (interior (copiedSquare J phi psi (fun e => face0 (.inl e))
            (fun e => face1 (.inl e)) f))) ∧
        (⋃ e : E, copiedSquare J phi psi (fun e => face0 (.inl e))
          (fun e => face1 (.inl e)) e) = Set.Icc 0 1 ×ˢ Set.Icc 0 M

end FiniteAvalanches.External
