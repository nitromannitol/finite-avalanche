import FiniteAvalanches.Electrical.Reference.Voltage
import FiniteAvalanches.Trees.ForestProjection.GramTransport
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.Plane.SourceLattice.ReferenceMoment
open LatticeProb
open scoped Classical BigOperators
noncomputable section

/-- Relabel vertices only, leaving every original H0 edge ID unchanged. -/
def vertexEnumeration (D : Finset (Site 2)) (P : OneSet D) :
    Vertex D P ≃ Fin (Fintype.card {x : D // x ∉ P.val} + 2) :=
  ((Equiv.sumCongr finTwoEquiv.symm (Fintype.equivFin {x : D // x ∉ P.val})).trans
    finSumFinEquiv).trans (finCongr (Nat.add_comm 2 _))

@[simp] theorem vertexEnumeration_alpha (D : Finset (Site 2)) (P : OneSet D) :
    vertexEnumeration D P (alpha D P) = 0 := by
  apply Fin.ext
  rfl

@[simp] theorem vertexEnumeration_beta (D : Finset (Site 2)) (P : OneSet D) :
    vertexEnumeration D P (beta D P) = 1 := by
  apply Fin.ext
  rfl

/-- The same voltage and positive Laplacian survive copied endpoint relabeling. -/
theorem relabel_laplacian {V W E : Type} [Fintype V] [Fintype W] [Fintype E]
    (G : Trees.Multigraph V E) (ρ : V ≃ W) (f : V → ℝ) (x : V) :
    laplacian (G.relabelVertices ρ).left (G.relabelVertices ρ).right
      (fun y => f (ρ.symm y)) (ρ x) = laplacian G.left G.right f x := by
  simp [laplacian, Trees.Multigraph.relabelVertices]

end
end FiniteAvalanches.Electrical.Plane.SourceLattice.ReferenceMoment
