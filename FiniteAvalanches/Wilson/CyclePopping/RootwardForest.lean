import FiniteAvalanches.Wilson.CyclePopping.RootDescendants
import FiniteAvalanches.Wilson.CyclePopping.RootedComponents
import FiniteAvalanches.Trees.RootedForests

/-! Rootward arrows select an acyclic set of original copied edges. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open FiniteAvalanches.Trees
open scoped Classical

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E]

/-- The original copies selected by all nonroot vertices. -/
def rootwardCopies (R : Set V) (edge : V → E) : Finset E :=
  (Finset.univ.filter (fun v => v ∉ R)).image edge

/-- When each arrow points along its selected copy and every orbit reaches a root,
the selected copied-edge set is acyclic. Parallel copies are retained. -/
theorem rootwardCopies_is_forest (G : Multigraph V E) (R : Set V) (f : V → V)
    (edge : V → E) (hhit : ∀ v, ∃ n, f^[n] v ∈ R)
    (hend : ∀ v ∉ R, (G.left (edge v) = v ∧ G.right (edge v) = f v) ∨
      (G.right (edge v) = v ∧ G.left (edge v) = f v)) :
    G.is_forest (rootwardCopies R edge) := by
  intro e he
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp he
  have huR : u ∉ R := (Finset.mem_filter.mp hu).2
  let D := rootDescendants R f hhit u
  have hcut : ∀ j ∈ (rootwardCopies R edge).erase (edge u),
      G.left j ∈ D ↔ G.right j ∈ D := by
    intro j hj
    obtain ⟨hju, hj⟩ := Finset.mem_erase.mp hj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hj
    have hvR : v ∉ R := (Finset.mem_filter.mp hv).2
    have hvu : v ≠ u := fun h => hju (congrArg edge h)
    have hiff := mem_rootDescendants_iff_successor R f hhit hvR hvu
    rcases hend v hvR with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · rw [hl, hr]
      exact hiff
    · rw [hl, hr]
      exact hiff.symm
  have hin : u ∈ D := mem_rootDescendants_self R f hhit u
  have hout : f u ∉ D := successor_not_mem_rootDescendants R f hhit huR
  intro hreaches
  have heq := G.reaches_mem_iff hcut hreaches
  rcases hend u huR with ⟨hl, hr⟩ | ⟨hr, hl⟩
  · rw [hl, hr] at heq
    exact hout (heq.mp hin)
  · rw [hl, hr] at heq
    exact hout (heq.mpr hin)

/-- Rootward copies form a rooted forest in the original copied graph. -/
theorem rootwardCopies_is_rooted_forest (G : Multigraph V E) (R : Set V) (f : V → V)
    (edge : V → E) (hhit : ∀ v, ∃ n, f^[n] v ∈ R)
    (hend : ∀ v ∉ R, (G.left (edge v) = v ∧ G.right (edge v) = f v) ∨
      (G.right (edge v) = v ∧ G.left (edge v) = f v)) :
    G.is_rooted_forest R (rootwardCopies R edge) := by
  refine ⟨rootwardCopies_is_forest G R f edge hhit hend, ?_⟩
  apply rootward_components G (rootwardCopies R edge) R f hhit
  · intro v hv
    exact ⟨edge v, Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩, rfl⟩,
      hend v hv⟩
  · intro x y hxy
    obtain ⟨e, he, heq⟩ := hxy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
    have hvR : v ∉ R := (Finset.mem_filter.mp hv).2
    have hadj : rootwardAdj R f (G.left (edge v)) (G.right (edge v)) := by
      rcases hend v hvR with ⟨hl, hr⟩ | ⟨hr, hl⟩
      · rw [hl, hr]
        exact Or.inl ⟨hvR, rfl⟩
      · rw [hl, hr]
        exact Or.inr ⟨hvR, rfl⟩
    rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hadj
    · exact hadj.symm

end
end FiniteAvalanches.Wilson.CyclePopping
