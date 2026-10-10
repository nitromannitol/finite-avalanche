import FiniteAvalanches.Wilson.RootContraction.Trees

/-! Actual rooted copied forests are bijective with trees after simultaneous nonempty root contraction. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)
  (R : CopiedNetwork.Roots (V := V))

theorem rooted_forest_lift_iff_tree (t : Finset (Copy G R)) :
    G.is_rooted_forest R.val (liftCopies G R t) ↔ (graph G R).is_tree Set.univ t := by
  constructor
  · intro h
    simpa only [project_lift_copies] using tree_of_rooted_forest G R h
  · exact rooted_forest_of_tree G R

/-- For unrestricted original subsets the inverse equation also records absence of deleted root-root copies. -/
theorem rooted_forest_iff_tree_and_lift_project (F : Finset E) :
    G.is_rooted_forest R.val F ↔
      (graph G R).is_tree Set.univ (projectCopies G R F) ∧
        liftCopies G R (projectCopies G R F) = F := by
  constructor
  · intro h
    exact ⟨tree_of_rooted_forest G R h, lift_project_forest G R h⟩
  · rintro ⟨ht, he⟩
    rw [← he]
    exact rooted_forest_of_tree G R ht

/-- A copied rooted forest retains its original subset; only the quotient endpoints change. -/
def rootContractionEquiv : G.RootedForest R.val ≃ (graph G R).ComponentTree Set.univ where
  toFun F := ⟨projectCopies G R F.val, tree_of_rooted_forest G R F.property⟩
  invFun t := ⟨liftCopies G R t.val, rooted_forest_of_tree G R t.property⟩
  left_inv F := Subtype.ext (lift_project_forest G R F.property)
  right_inv t := Subtype.ext (project_lift_copies G R t.val)

@[simp] theorem rootContractionEquiv_copies (F : G.RootedForest R.val) :
    (rootContractionEquiv G R F).val = projectCopies G R F.val := rfl

@[simp] theorem rootContractionEquiv_symm_copies (t : (graph G R).ComponentTree Set.univ) :
    ((rootContractionEquiv G R).symm t).val = liftCopies G R t.val := rfl

/-- Original root labels, including mixed colors, are recovered on the original vertex carrier. -/
theorem oneVertices_lift_project (F : G.RootedForest R.val) (C : Set V) :
    G.oneVertices (liftCopies G R (rootContractionEquiv G R F).val) C =
      G.oneVertices F.val C := by
  rw [rootContractionEquiv_copies, lift_project_forest G R F.property]

theorem all_roots_empty_forest (hR : R.val = Set.univ) : G.is_rooted_forest R.val ∅ := by
  rw [hR]
  refine ⟨by simp [Multigraph.is_forest], ?_⟩
  intro x
  refine ⟨x, Set.mem_univ _, .refl, ?_⟩
  intro y _ h
  induction h with
  | refl => rfl
  | tail _ he _ => obtain ⟨e, he, _⟩ := he; simp at he

theorem all_roots_tree_empty (hR : R.val = Set.univ) : (graph G R).is_tree Set.univ ∅ := by
  simpa [projectCopies, all_roots_copy_empty G R hR] using
    tree_of_rooted_forest G R (all_roots_empty_forest G R hR)

theorem all_roots_forests_empty (hR : R.val = Set.univ) (F : G.RootedForest R.val) : F.val = ∅ := by
  exact G.rootedForest_univ_empty ⟨F.val, hR ▸ F.property⟩

theorem all_roots_trees_empty (hR : R.val = Set.univ) (t : (graph G R).ComponentTree Set.univ) :
    t.val = ∅ := by
  letI := all_roots_copy_empty G R hR
  exact Finset.eq_empty_of_isEmpty t.val

end
end FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient
