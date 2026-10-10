import FiniteAvalanches.Trees.Joining

/-! Deterministic component-color comparison for actual rooted copied forests.
The edge inclusions are local coupling inputs, not distributional conclusions. -/
set_option autoImplicit false
namespace FiniteAvalanches.Trees.Multigraph
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)

/-- An actual copied forest: acyclic individual copies and exactly one prescribed
root in every component, including isolated vertices. -/
def is_rooted_forest (R : Set V) (F : Finset E) : Prop :=
  G.is_forest F ∧ ∀ x, ∃ r ∈ R, G.reaches F x r ∧
    ∀ r' ∈ R, G.reaches F x r' → r' = r

abbrev RootedForest (R : Set V) := {F : Finset E // G.is_rooted_forest R F}

/-- Vertices connected by selected copies to `C`. On a rooted forest whose
roots contain `C`, these are precisely the vertices of roots labeled one. -/
def oneVertices (F : Finset E) (C : Set V) : Set V :=
  {v | ∃ r ∈ C, G.reaches F v r}

/-- The shared one roots and literal copied-edge inclusion suffice for this
deterministic step; no stochastic domination is assumed or concluded. -/
theorem oneVertices_subset_of_edges_subset (A A' C : Set V)
    (F : G.RootedForest (A ∪ C)) (F' : G.RootedForest (A' ∪ C)) (hF : F'.val ⊆ F.val) :
    G.oneVertices F'.val C ⊆ G.oneVertices F.val C := by
  rintro v ⟨r, hr, hvr⟩
  exact ⟨r, hr, G.reaches_mono hF hvr⟩

/-- Removing one roots reverses the copied-edge inclusion. The original zero
root in an old zero component stays a root of its containing new component. -/
theorem oneVertices_subset_of_one_roots_removed (A C C' : Set V) (hAC : Disjoint A C)
    (hC : C' ⊆ C) (F : G.RootedForest (A ∪ C)) (F' : G.RootedForest (A ∪ C'))
    (hF : F.val ⊆ F'.val) : G.oneVertices F'.val C' ⊆ G.oneVertices F.val C := by
  rintro v ⟨c, hc, hvc⟩
  obtain ⟨r, hr, hvr, _⟩ := F.property.2 v
  rcases hr with hr | hr
  · obtain ⟨a, _, _, hu⟩ := F'.property.2 v
    have hra : r = a := hu r (Or.inl hr) (G.reaches_mono hF hvr)
    have hca : c = a := hu c (Or.inr hc) hvc
    have hrc : r = c := hra.trans hca.symm
    have hrC : r ∈ C := by rw [hrc]; exact hC hc
    exact False.elim (Set.disjoint_left.mp hAC hr hrC)
  · exact ⟨r, hr, hvr⟩

theorem rootedForest_univ_empty (F : G.RootedForest Set.univ) : F.val = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨r, _, _, hu⟩ := F.property.2 (G.left e)
  have hl : G.left e = r := hu _ (Set.mem_univ _) Relation.ReflTransGen.refl
  have hr : G.right e = r := hu _ (Set.mem_univ _)
    (Relation.ReflTransGen.single ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩)
  exact G.loopless e (hl.trans hr.symm)

/-- Parallel copies remain different: the two-copy circuit violates the actual
acyclicity predicate even though its underlying support graph has one edge. -/
theorem parallel_pair_not_rooted_forest (R : Set V) (e f : E) (hef : e ≠ f)
    (hl : G.left e = G.left f) (hr : G.right e = G.right f) :
    ¬G.is_rooted_forest R ({e, f} : Finset E) := by
  intro h
  apply h.1 e (by simp)
  exact Relation.ReflTransGen.single ⟨f, by simp [hef.symm], Or.inl ⟨hl.symm, hr.symm⟩⟩

end
end FiniteAvalanches.Trees.Multigraph
