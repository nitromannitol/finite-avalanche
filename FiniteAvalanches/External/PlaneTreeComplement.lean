import FiniteAvalanches.Electrical.Geometry.BSST
import FiniteAvalanches.Support.Plane.SelectedSimplePath
import FiniteAvalanches.Support.Plane.TreeComplementReduction

/-! The spanning-tree complement theorem for finite plane multigraphs. -/

set_option autoImplicit false
open scoped Classical

namespace FiniteAvalanches.External

/-- A spanning tree of a finite connected plane multigraph is complementary to a dual spanning tree. -/
theorem finite_plane_tree_complement : (∀ {V E : Type} [Fintype V] [Fintype E]
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
          (FiniteAvalanches.Electrical.BSST.positiveChartFace Q e (charts e))) : Prop) := by
  intro V E _ _ G Q charts hV hG finiteFaces
  apply FiniteAvalanches.Electrical.StatementGeometry.tree_complement_iff_of_edge_path_duality
    G Q charts hV hG finiteFaces
  by_cases hE : Nonempty E
  · letI : Nonempty E := hE
    exact FiniteAvalanches.Electrical.StatementGeometry.edge_path_duality Q charts
  · letI : IsEmpty E := not_nonempty_iff.mp hE
    intro A e
    exact isEmptyElim e

end FiniteAvalanches.External
