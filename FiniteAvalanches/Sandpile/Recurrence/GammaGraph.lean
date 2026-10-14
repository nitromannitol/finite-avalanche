import FiniteAvalanches.Sandpile.Recurrence.HeldGraphConnectivity
import FiniteAvalanches.Sandpile.Components.WiredTrees
import FiniteAvalanches.Model.WiredTreeExistence
import FiniteAvalanches.Sandpile.Law.FiniteVolume

/-! A finite ambient box is used ONLY to label original copies. The graph is the
literal wiring of the entire arbitrary Gamma, including disconnected/empty sets. -/
namespace FiniteAvalanches.Sandpile.GammaGraph
open LatticeProb FiniteAvalanches.Sandpile
open scoped Classical BigOperators
noncomputable section

def radius (Γ : Finset Site2) : ℕ := Γ.sup (siteRadius 0)

theorem in_radius {Γ : Finset Site2} (x : Γ) : FiniteWired.inBox (radius Γ) x.val :=
  (mem_box_sites _ _).mp ((site_radius_zero_le_iff x.val _).mp
    (Finset.le_sup (f := siteRadius 0) x.property))

def activeVertices (Γ : Finset Site2) : Finset (FiniteWired.Vertex (radius Γ)) :=
  Finset.univ.filter fun v => match v with
    | none => False
    | some a => FiniteWired.site a ∈ Γ

theorem none_not_active (Γ : Finset Site2) : none ∉ activeVertices Γ := by simp [activeVertices]

def activeEquiv (Γ : Finset Site2) : Γ ≃ Burning.InducedVertex (activeVertices Γ) where
  toFun x := ⟨some (FiniteWired.activeOfSite (radius Γ) x.val (in_radius x)), by
    simp only [activeVertices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact x.property⟩
  invFun v := match v with
    | ⟨none, hv⟩ => (none_not_active Γ hv).elim
    | ⟨some a, hv⟩ => ⟨FiniteWired.site a, by simpa only [activeVertices,
        Finset.mem_filter, Finset.mem_univ, true_and] using hv⟩
  left_inv _ := rfl
  right_inv v := by
    rcases v with ⟨_ | a, hv⟩
    · exact (none_not_active Γ hv).elim
    · apply Subtype.ext
      apply congrArg some
      apply FiniteWired.site_injective (radius Γ)
      rfl

abbrev Vertex (Γ : Finset Site2) := Option (Burning.InducedVertex (activeVertices Γ))
abbrev Copy (Γ : Finset Site2) := Burning.HeldEdge (WiredTrees.graph (radius Γ))
  (activeVertices Γ) (activeVertices Γ)

def graph (Γ : Finset Site2) : FiniteAvalanches.Trees.Multigraph (Vertex Γ) (Copy Γ) :=
  Burning.heldGraph (WiredTrees.graph (radius Γ)) none (activeVertices Γ)
    (activeVertices Γ) (none_not_active Γ) (fun _ h => h)

def vertexEquiv (Γ : Finset Site2) : Γ ≃ Burning.SourceVertex (none : Vertex Γ) where
  toFun x := ⟨some (activeEquiv Γ x), by simp⟩
  invFun v := match v with
    | ⟨none, hv⟩ => ((Finset.mem_erase.mp hv).1 rfl).elim
    | ⟨some a, _⟩ => (activeEquiv Γ).symm a
  left_inv x := (activeEquiv Γ).symm_apply_apply x
  right_inv v := by
    rcases v with ⟨_ | a, hv⟩
    · exact ((Finset.mem_erase.mp hv).1 rfl).elim
    · apply Subtype.ext
      exact congrArg some ((activeEquiv Γ).apply_symm_apply a)

theorem graph_connected (Γ : Finset Site2) :
    (FiniteAvalanches.Electrical.supportGraph (graph Γ).left (graph Γ).right).Preconnected := by
  apply Burning.held_all_connected
  intro v
  cases v with
  | none => exact Relation.ReflTransGen.refl
  | some a =>
    exact (WiredTrees.graph (radius Γ)).reaches_mono
      (Finset.subset_univ _) (WiredTrees.row_reaches_sink a)

theorem degree_four {Γ : Finset Site2} (x : Γ) :
    Burning.degree (graph Γ) (vertexEquiv Γ x).val = 4 := by
  change Burning.degree (Burning.heldGraph _ _ _ _ _ _) (some (activeEquiv Γ x)) = 4
  rw [Burning.degree_held_graph, if_pos (activeEquiv Γ x).property]
  exact Components.wired_graph_degree _

end
end FiniteAvalanches.Sandpile.GammaGraph
