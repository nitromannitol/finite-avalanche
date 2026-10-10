import FiniteAvalanches.Electrical.Geometry.BSST

set_option autoImplicit false
open scoped Classical

namespace FiniteAvalanches.External

/-- A spanning tree of a finite connected plane multigraph is complementary to a dual spanning tree. -/
axiom finite_plane_tree_complement : (∀ {V E : Type} [Fintype V] [Fintype E]
    (G : FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph V E)
    (Q : FiniteAvalanches.Electrical.StatementGeometry.Drawing G)
    (charts : ∀ e, FiniteAvalanches.Electrical.Source.EdgeChart Q e),
  (Set.univ : Set V).Nonempty →
  (∀ x y, G.reaches Finset.univ x y) →
  ∀ finiteFaces : Fintype (FiniteAvalanches.Electrical.BSST.Face Q),
    letI : Fintype (FiniteAvalanches.Electrical.BSST.Face Q) := finiteFaces
    ∀ S : Finset E,
      ((Set.univ : Set V).Nonempty ∧ (∀ x y, G.reaches S x y) ∧
        ∀ e ∈ S, ¬G.reaches (S.erase e) (G.left e) (G.right e)) ↔
      ((Set.univ : Set (FiniteAvalanches.Electrical.BSST.Face Q)).Nonempty ∧
        (∀ x y, (⟨fun e => FiniteAvalanches.Electrical.BSST.negativeChartFace Q e (charts e),
          fun e => FiniteAvalanches.Electrical.BSST.positiveChartFace Q e (charts e)⟩ :
          FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
            (FiniteAvalanches.Electrical.BSST.Face Q) E).reaches Sᶜ x y) ∧
        ∀ e ∈ Sᶜ, ¬(⟨fun e => FiniteAvalanches.Electrical.BSST.negativeChartFace Q e (charts e),
          fun e => FiniteAvalanches.Electrical.BSST.positiveChartFace Q e (charts e)⟩ :
          FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
            (FiniteAvalanches.Electrical.BSST.Face Q) E).reaches
          (Sᶜ.erase e)
          (FiniteAvalanches.Electrical.BSST.negativeChartFace Q e (charts e))
          (FiniteAvalanches.Electrical.BSST.positiveChartFace Q e (charts e))) : Prop)

end FiniteAvalanches.External
