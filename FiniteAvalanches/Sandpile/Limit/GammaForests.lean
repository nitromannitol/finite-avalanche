import FiniteAvalanches.Sandpile.Recurrence.GammaGraph
import FiniteAvalanches.Wilson.Lattice.SiteRootLimit

/-! The wired graph of a finite volume `Γ` is the root contraction of its ambient box
with roots the sink and the sites outside `Γ`. Spanning trees of the wired graph are
therefore the rooted forests of the box, with the same copies, and their lattice edge
law is `forestLaw Γ`. -/

set_option autoImplicit false

namespace FiniteAvalanches.Sandpile.GammaGraph

open LatticeProb MeasureTheory FiniteAvalanches.Trees FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.Lattice.SiteRoots
open FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient
open scoped Classical

noncomputable section

/-- The ambient box roots for `Γ`. -/
abbrev boxRoots (Γ : Finset Site2) := roots (Γ : Set Site2) (radius Γ)

/-- Vertices of the root quotient of the ambient box. -/
abbrev QVertex (Γ : Finset Site2) :=
  FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient.Vertex (boxRoots Γ)

/-- Copies of the root quotient of the ambient box. -/
abbrev QCopy (Γ : Finset Site2) :=
  FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient.Copy (WiredTrees.graph (radius Γ))
    (boxRoots Γ)

/-- The root quotient of the ambient box. -/
abbrev qgraph (Γ : Finset Site2) : Multigraph (QVertex Γ) (QCopy Γ) :=
  FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient.graph (WiredTrees.graph (radius Γ))
    (boxRoots Γ)

theorem mem_activeVertices_iff (Γ : Finset Site2) (v : FiniteWired.Vertex (radius Γ)) :
    v ∈ activeVertices Γ ↔ v ∉ (boxRoots Γ).val := by
  cases v with
  | none => exact ⟨fun h => (none_not_active Γ h).elim, fun h => (h trivial).elim⟩
  | some a =>
    simp only [activeVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h hr => hr h, fun h => not_not.mp h⟩

/-- Vertices of the wired graph of `Γ` and of the root quotient of its box. -/
def quotVertexEquiv (Γ : Finset Site2) : Vertex Γ ≃ QVertex Γ :=
  Equiv.optionCongr (Equiv.subtypeEquivRight (mem_activeVertices_iff Γ))

theorem quotVertexEquiv_project (Γ : Finset Site2) (v : FiniteWired.Vertex (radius Γ)) :
    quotVertexEquiv Γ (Burning.projectVertex (activeVertices Γ) v) = project (boxRoots Γ) v := by
  by_cases hv : v ∈ activeVertices Γ
  · have hr : v ∉ (boxRoots Γ).val := (mem_activeVertices_iff Γ v).mp hv
    simp only [Burning.projectVertex, dif_pos hv, project, dif_neg hr]
    rfl
  · have hr : v ∈ (boxRoots Γ).val := by
      by_contra h
      exact hv ((mem_activeVertices_iff Γ v).mpr h)
    simp only [Burning.projectVertex, dif_neg hv, project, dif_pos hr]
    rfl

theorem retained_iff (Γ : Finset Site2) (e : FiniteWired.Edge (radius Γ)) :
    Burning.retained (WiredTrees.graph (radius Γ)) (activeVertices Γ) (activeVertices Γ) e ↔
      project (boxRoots Γ) ((WiredTrees.graph (radius Γ)).left e) ≠
        project (boxRoots Γ) ((WiredTrees.graph (radius Γ)).right e) := by
  rw [Ne, contracted_loop_iff]
  have hl := mem_activeVertices_iff Γ ((WiredTrees.graph (radius Γ)).left e)
  have hr := mem_activeVertices_iff Γ ((WiredTrees.graph (radius Γ)).right e)
  unfold Burning.retained
  by_cases ha : (WiredTrees.graph (radius Γ)).left e ∈ activeVertices Γ <;>
    by_cases hb : (WiredTrees.graph (radius Γ)).right e ∈ activeVertices Γ <;>
    simp_all

/-- Copies of the wired graph of `Γ` and of the root quotient of its box. -/
def quotCopyEquiv (Γ : Finset Site2) :
    Copy Γ ≃ QCopy Γ :=
  Equiv.subtypeEquivRight (retained_iff Γ)

@[simp] theorem quotCopyEquiv_val (Γ : Finset Site2) (e : Copy Γ) :
    (quotCopyEquiv Γ e).val = e.val := rfl

theorem quotCopyEquiv_endpoints (Γ : Finset Site2) (e : Copy Γ) :
    ((qgraph Γ).left (quotCopyEquiv Γ e) =
        quotVertexEquiv Γ ((graph Γ).left e) ∧
      (qgraph Γ).right
          (quotCopyEquiv Γ e) =
        quotVertexEquiv Γ ((graph Γ).right e)) ∨
    ((qgraph Γ).left (quotCopyEquiv Γ e) =
        quotVertexEquiv Γ ((graph Γ).right e) ∧
      (qgraph Γ).right
          (quotCopyEquiv Γ e) =
        quotVertexEquiv Γ ((graph Γ).left e)) :=
  Or.inl ⟨(quotVertexEquiv_project Γ _).symm, (quotVertexEquiv_project Γ _).symm⟩

/-- Spanning trees of the wired graph of `Γ` and of the root quotient of its box. -/
def quotTreeEquiv (Γ : Finset Site2) :
    (graph Γ).ComponentTree Set.univ ≃
      (qgraph Γ).ComponentTree
        Set.univ where
  toFun t := ⟨t.val.image (quotCopyEquiv Γ),
    (Multigraph.copiedEquiv_tree_iff _ _ (quotVertexEquiv Γ) (quotCopyEquiv Γ)
      (quotCopyEquiv_endpoints Γ) t.val).mpr t.property⟩
  invFun t := ⟨t.val.image (quotCopyEquiv Γ).symm, by
    apply (Multigraph.copiedEquiv_tree_iff _ _ (quotVertexEquiv Γ) (quotCopyEquiv Γ)
      (quotCopyEquiv_endpoints Γ) _).mp
    simpa only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply,
      Finset.image_id'] using t.property⟩
  left_inv t := by
    apply Subtype.ext
    simp only [Finset.image_image, Function.comp_def, Equiv.symm_apply_apply,
      Finset.image_id']
  right_inv t := by
    apply Subtype.ext
    simp only [Finset.image_image, Function.comp_def, Equiv.apply_symm_apply,
      Finset.image_id']

/-- Spanning trees of the wired graph of `Γ` are the rooted forests of its box. -/
def treeForestEquiv (Γ : Finset Site2) :
    (graph Γ).ComponentTree Set.univ ≃ Forest (Γ : Set Site2) (radius Γ) :=
  (quotTreeEquiv Γ).trans (rootContractionEquiv (WiredTrees.graph (radius Γ)) (boxRoots Γ)).symm

theorem treeForestEquiv_copies (Γ : Finset Site2) (t : (graph Γ).ComponentTree Set.univ) :
    (treeForestEquiv Γ t).val = t.val.image Subtype.val := by
  change (t.val.image (quotCopyEquiv Γ)).image Subtype.val = _
  rw [Finset.image_image]
  rfl

instance spanningTreeNonempty (Γ : Finset Site2) : Nonempty ((graph Γ).ComponentTree Set.univ) :=
  ⟨(treeForestEquiv Γ).symm (Classical.arbitrary _)⟩

/-- The lattice edges with both endpoints in `Γ` of a spanning tree of the wired graph. -/
def gammaField (Γ : Finset Site2) (t : (graph Γ).ComponentTree Set.univ) : EdgeField :=
  forestField (Γ : Set Site2) (t.val.image Subtype.val)

theorem gammaField_eq (Γ : Finset Site2) (t : (graph Γ).ComponentTree Set.univ) :
    gammaField Γ t = forestField (Γ : Set Site2) (treeForestEquiv Γ t).val := by
  rw [treeForestEquiv_copies]
  rfl

/-- The lattice edge law of the uniform spanning tree of the wired graph of `Γ`. -/
theorem map_gammaField_treeLaw (Γ : Finset Site2) :
    Measure.map (gammaField Γ) (graph Γ).treeLaw = forestLaw (Γ : Set Site2) (radius Γ) := by
  have hmap : gammaField Γ =
      (fun F : Forest (Γ : Set Site2) (radius Γ) => forestField (Γ : Set Site2) F.val) ∘
        treeForestEquiv Γ := by
    funext t
    exact gammaField_eq Γ t
  rw [hmap, ← Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  unfold forestLaw Multigraph.treeLaw
  rw [FiniteAvalanches.uniform_measure_map_equiv]

end

end FiniteAvalanches.Sandpile.GammaGraph
