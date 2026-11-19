import FiniteAvalanches.Electrical.Geometry.BSST
import LatticeProb.Graph.CopiedGraph.Basic
import FiniteAvalanches.Support.Plane.FinitePointComplement
import Mathlib.Topology.Order.Compact

/-!
# Faces of finite plane graphs

Ported from Lattice-Probability `LatticeProb/Topology/PlaneGraph/TreeComplement.lean` at commit `01bdb9a9`.

The trace of a finite drawing is compact and its complement has a face.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open FiniteAvalanches.Electrical
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] {G : CopiedGraph V E}

/-- The trace of a finite drawing is compact. The proof follows
`FiniteAvalanches.Electrical.Source.tree_drawingTrace_isCompact`. -/
theorem tree_drawingTrace_isCompact (D : Drawing G) : IsCompact (Source.drawingTrace D) :=
  (Set.finite_range D.point).isCompact.union
    (isCompact_iUnion fun e => isCompact_range (D.continuous e))

/-- A finite plane drawing has at least one complementary face. -/
theorem face_nonempty (D : Drawing G) : (Set.univ : Set (BSST.Face D)).Nonempty := by
  have hcompact := (tree_drawingTrace_isCompact D).image continuous_fst
  obtain ⟨b, hb⟩ := hcompact.bddAbove
  have hoff : (b + 1, 0) ∉ Source.drawingTrace D := by
    intro h
    have : b + 1 ≤ b := hb ⟨(b + 1, 0), h, rfl⟩
    linarith
  exact ⟨ConnectedComponents.mk ⟨(b + 1, 0), hoff⟩, Set.mem_univ _⟩

namespace CopiedGraph

variable {W : Type} [Fintype W]

omit [Fintype V] [Fintype E] in
private theorem reaches_symm (J : CopiedGraph V E) {F : Finset E} {x y : V}
    (h : J.reaches F x y) : J.reaches F y x :=
  LatticeProb.Graph.CopiedGraph.reaches_symm ⟨J.left, J.right⟩ h

omit [Fintype V] in
private theorem connected_of_edges (J : CopiedGraph V E) (F : Finset E)
    (hconn : ∀ x y, J.reaches Finset.univ x y)
    (hedges : ∀ e, J.reaches F (J.left e) (J.right e)) :
    ∀ x y, J.reaches F x y := by
  intro x y
  have h := hconn x y
  induction h with
  | refl => exact .refl
  | tail _ h ih =>
    obtain ⟨e, _, hends⟩ := h
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ih.trans (hedges e)
    · exact ih.trans (reaches_symm J (hedges e))

omit [Fintype V] [Fintype W] in
/-- If two connected copied graphs satisfy the edge-path duality relation, their spanning trees
are complementary. -/
theorem spanningTree_compl_iff_of_edge_path_duality
    (J : CopiedGraph V E) (K : CopiedGraph W E)
    (hV : (Set.univ : Set V).Nonempty) (hW : (Set.univ : Set W).Nonempty)
    (hJ : ∀ x y, J.reaches Finset.univ x y)
    (hK : ∀ x y, K.reaches Finset.univ x y)
    (hdual : ∀ (A : Finset E) e, e ∉ A →
      (J.reaches A (J.left e) (J.right e) ↔
        ¬ K.reaches (Aᶜ.erase e) (K.left e) (K.right e))) (S : Finset E) :
    ((Set.univ : Set V).Nonempty ∧ (∀ x y, J.reaches S x y) ∧
      ∀ e ∈ S, ¬ J.reaches (S.erase e) (J.left e) (J.right e)) ↔
    ((Set.univ : Set W).Nonempty ∧ (∀ x y, K.reaches Sᶜ x y) ∧
      ∀ e ∈ Sᶜ, ¬ K.reaches (Sᶜ.erase e) (K.left e) (K.right e)) := by
  constructor
  · rintro ⟨_, hconnect, hforest⟩
    refine ⟨hW, connected_of_edges K Sᶜ hK ?_, ?_⟩
    · intro e
      by_cases he : e ∈ S
      · have hn := hforest e he
        have hd := hdual (S.erase e) e (Finset.notMem_erase e S)
        have h := not_not.mp (mt hd.mpr hn)
        simpa [Finset.erase_eq_of_notMem (show e ∉ Sᶜ by simpa using he)] using h
      · exact .single ⟨e, Finset.mem_compl.mpr he, Or.inl ⟨rfl, rfl⟩⟩
    · intro e he
      exact (hdual S e (Finset.mem_compl.mp he)).mp (hconnect _ _)
  · rintro ⟨_, hconnect, hforest⟩
    refine ⟨hV, connected_of_edges J S hJ ?_, ?_⟩
    · intro e
      by_cases he : e ∈ S
      · exact .single ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
      · exact (hdual S e he).mpr (hforest e (Finset.mem_compl.mpr he))
    · intro e he hpath
      have hd := (hdual (S.erase e) e (Finset.notMem_erase e S)).mp hpath
      apply hd
      have h := hconnect (K.left e) (K.right e)
      simpa [Finset.erase_eq_of_notMem (show e ∉ Sᶜ by simpa using he)] using h

end CopiedGraph

/-- The tree-complement equivalence for an edge-free drawing. -/
theorem tree_complement_iff_of_isEmpty [IsEmpty E] (G : CopiedGraph V E) (D : Drawing G)
    (charts : ∀ e, Source.EdgeChart D e)
    (hV : (Set.univ : Set V).Nonempty) (hG : ∀ x y, G.reaches Finset.univ x y)
    (finiteFaces : Fintype (BSST.Face D)) :
    letI : Fintype (BSST.Face D) := finiteFaces
    ∀ S : Finset E,
      ((Set.univ : Set V).Nonempty ∧ (∀ x y, G.reaches S x y) ∧
        ∀ e ∈ S, ¬G.reaches (S.erase e) (G.left e) (G.right e)) ↔
      ((Set.univ : Set (BSST.Face D)).Nonempty ∧
        (∀ x y, (⟨fun e => BSST.negativeChartFace D e (charts e),
          fun e => BSST.positiveChartFace D e (charts e)⟩ :
          CopiedGraph (BSST.Face D) E).reaches Sᶜ x y) ∧
        ∀ e ∈ Sᶜ, ¬(⟨fun e => BSST.negativeChartFace D e (charts e),
          fun e => BSST.positiveChartFace D e (charts e)⟩ :
          CopiedGraph (BSST.Face D) E).reaches (Sᶜ.erase e)
          (BSST.negativeChartFace D e (charts e))
          (BSST.positiveChartFace D e (charts e))) := by
  intro S
  have htrace : Source.drawingTrace D = Set.range D.point := by
    simp [Source.drawingTrace]
  have hconn : IsConnected {z | z ∉ Source.drawingTrace D} := by
    rw [htrace]
    exact (LatticeProb.PlaneTopology.isPathConnected_compl_range D.point).isConnected
  have : ConnectedSpace {z : Source.Plane // z ∉ Source.drawingTrace D} :=
    isConnected_iff_connectedSpace.mp hconn
  have : Subsingleton (BSST.Face D) := ConnectedComponents.subsingleton
  have hS : S = Finset.univ := Finset.eq_univ_iff_forall.mpr fun e => isEmptyElim e
  constructor
  · intro _
    refine ⟨face_nonempty D, ?_, ?_⟩
    · intro x y
      have hxy : x = y := Subsingleton.elim _ _
      subst y
      exact .refl
    · intro e
      exact isEmptyElim e
  · intro _
    refine ⟨hV, ?_, ?_⟩
    · simpa [hS] using hG
    · intro e
      exact isEmptyElim e

end FiniteAvalanches.Electrical.StatementGeometry
