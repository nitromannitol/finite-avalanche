import FiniteAvalanches.Trees.RootedPaths

namespace FiniteAvalanches.Trees.RootedPaths

variable {V : Type*} {T : SimpleGraph V} (hT : T.IsTree)

/-- The strict root path from the lowest common ancestor avoids the connecting subtree. -/
theorem commonAncestor_strict_root_path_disjoint [Fintype V] (r : V) (S : Set V)
    (hS : S.Nonempty) :
    Disjoint {z : V | ancestor hT r z (commonAncestor hT r S hS) ∧
      z ≠ commonAncestor hT r S hS} (connectingSubtree hT S) := by
  refine Set.disjoint_left.mpr ?_
  rintro z ⟨hz, hne⟩ hzK
  have hc := commonAncestor_spec hT r S hS
  have hdesc : ancestor hT r (commonAncestor hT r S hS) z :=
    connectingSubtree_subset_descendants hT r S hc.1 hzK
  exact hne (ancestor_antisymm hT hdesc hz).symm

end FiniteAvalanches.Trees.RootedPaths

set_option pp.universes true in
set_option pp.explicit true in
set_option pp.fullNames true in
#check @FiniteAvalanches.Trees.RootedPaths.commonAncestor_strict_root_path_disjoint
#print axioms FiniteAvalanches.Trees.RootedPaths.commonAncestor_strict_root_path_disjoint
