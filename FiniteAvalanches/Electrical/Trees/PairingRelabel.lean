import FiniteAvalanches.Electrical.Trees.PairingReindex
import FiniteAvalanches.Electrical.Trees.CopiedVertexTransport

/-! Pairing groves and Green kernels are invariant under vertex relabeling. -/

set_option autoImplicit false

namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph

open FiniteAvalanches.Electrical
open scoped Classical

noncomputable section

variable {V W E : Type} [Fintype V] [Fintype W] [Fintype E]

/-- Relabel vertices while retaining every original copied edge. -/
def relabel (J : CopiedGraph V E) (ρ : V ≃ W) : CopiedGraph W E :=
  ⟨ρ ∘ J.left, ρ ∘ J.right⟩

omit [Fintype V] [Fintype W] in
/-- A vertex equivalence preserves connectedness of the supporting graph. -/
theorem relabel_preconnected (J : CopiedGraph V E) (ρ : V ≃ W)
    (hc : (supportGraph J.left J.right).Preconnected) :
    (supportGraph (J.relabel ρ).left (J.relabel ρ).right).Preconnected := by
  apply (J.relabel ρ).supportGraph_preconnected_of_reaches
  intro x y
  have h := J.reaches_univ_of_supportGraph_reachable (hc (ρ.symm x) (ρ.symm y))
  have ht := (J.reaches_vertex_equiv_iff (J.relabel ρ) ρ (fun _ => rfl)
    (fun _ => rfl) Finset.univ (ρ.symm x) (ρ.symm y)).mp h
  simpa only [Equiv.apply_symm_apply] using ht

/-- Relabeling preserves each literal pairing-grove edge subset. -/
def pairingGroveRelabelEquiv (J : CopiedGraph V E) (ρ : V ≃ W) {k : ℕ}
    (a b : Fin k → V) (ha : Function.Injective a) (π : Equiv.Perm (Fin k)) :
    J.PairingGrove a b π ≃ (J.relabel ρ).PairingGrove (ρ ∘ a) (ρ ∘ b) π :=
  (J.pairingGroveEquivRootedMatching a b ha π).trans
    ((J.latticeProbGraph.rootedMatchingRelabelEquiv ρ a b π).trans
      ((J.relabel ρ).pairingGroveEquivRootedMatching (ρ ∘ a) (ρ ∘ b)
        (ρ.injective.comp ha) π).symm)

/-- The grounded Green kernel is carried along by a vertex equivalence. -/
theorem groundedGreen_relabel (J : CopiedGraph V E) (ρ : V ≃ W) (g : V)
    (hc : (supportGraph J.left J.right).Preconnected)
    (hc' : (supportGraph (J.relabel ρ).left (J.relabel ρ).right).Preconnected)
    (u v : V) :
    groundedGreen (J.relabel ρ).left (J.relabel ρ).right (ρ g) hc' (ρ u) (ρ v) =
      groundedGreen J.left J.right g hc u v := by
  let f : W → ℝ := fun z => groundedGreen J.left J.right g hc u (ρ.symm z)
  have hf : f (ρ g) = 0 ∧ ∀ z, z ≠ ρ g →
      laplacian (J.relabel ρ).left (J.relabel ρ).right f z =
        (if z = ρ u then 1 else 0) := by
    constructor
    · simp [f, groundedGreen_ground]
    · intro z hz
      have hz' : ρ.symm z ≠ g := by
        intro h
        exact hz (by simpa using congrArg ρ h)
      have hlap : laplacian (J.relabel ρ).left (J.relabel ρ).right f z =
          laplacian J.left J.right (groundedGreen J.left J.right g hc u) (ρ.symm z) := by
        simp [laplacian, relabel, f, ρ.apply_eq_iff_eq_symm_apply]
      rw [hlap, groundedGreen_laplacian J.left J.right g hc u (ρ.symm z) hz']
      congr 1
      exact propext ρ.symm_apply_eq
  have he := groundedPoisson_eq (J.relabel ρ).left (J.relabel ρ).right
    (ρ g) hc' (fun z => if z = ρ u then 1 else 0) f hf
  have hv := congrFun he (ρ v)
  simpa only [f, Equiv.symm_apply_apply, groundedGreen] using hv.symm

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
