import FiniteAvalanches.Electrical.Trees.SeparatingForestCompletion

/-! The exact component-crossing criterion for completing a two-root forest. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

omit [Fintype V] [Fintype E] in
/-- Completion is a tree exactly when the new copy joins the two actual components. -/
theorem twoRootForest_insert_tree_iff (J : CopiedGraph V E) (u v : V) (hne : u ≠ v)
    (F : J.TwoRootForest u v) (e : E) :
    ((Set.univ : Set V).Nonempty ∧ (∀ x y, J.reaches (insert e F.val) x y) ∧
      ∀ f ∈ insert e F.val, ¬J.reaches ((insert e F.val).erase f) (J.left f) (J.right f)) ↔
      ¬J.reaches F.val (J.left e) (J.right e) := by
  constructor
  · intro ht hends
    have old {x y : V} (h : J.reaches (insert e F.val) x y) : J.reaches F.val x y := by
      induction h with
      | refl => exact .refl
      | tail _ hadj ih =>
        obtain ⟨f, hf, he⟩ := hadj
        rcases Finset.mem_insert.mp hf with rfl | hf
        · rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ih.trans hends
          · exact ih.trans (TwoCopy.reaches_symm J hends)
        · exact ih.tail ⟨f, hf, he⟩
    exact twoRootForest_roots_separated J u v hne F (old (ht.2.1 u v))
  · exact twoRootForest_insert_tree J u v F e

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
