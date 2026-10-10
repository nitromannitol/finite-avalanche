import FiniteAvalanches.Electrical.Reference.CopyTransport

/-! Relabeling vertices leaves every original selectable edge subset unchanged. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open scoped Classical
noncomputable section
variable {V W E : Type}

theorem reaches_vertex_equiv_iff (J : CopiedGraph V E) (K : CopiedGraph W E)
    (rho : V ≃ W) (hl : ∀ e, rho (J.left e) = K.left e)
    (hr : ∀ e, rho (J.right e) = K.right e) (A : Finset E) (x y : V) :
    J.reaches A x y ↔ K.reaches A (rho x) (rho y) := by
  constructor
  · intro h
    exact Relation.ReflTransGen.lift' rho (fun _ _ hadj => by
      obtain ⟨e, he, h | h⟩ := hadj
      · exact .single ⟨e, he, Or.inl ⟨(hl e).symm.trans (congrArg rho h.1),
          (hr e).symm.trans (congrArg rho h.2)⟩⟩
      · exact .single ⟨e, he, Or.inr ⟨(hr e).symm.trans (congrArg rho h.1),
          (hl e).symm.trans (congrArg rho h.2)⟩⟩) _ _ h
  · intro h
    have hl' (e : E) : J.left e = rho.symm (K.left e) := by
      simpa only [Equiv.symm_apply_apply] using congrArg rho.symm (hl e)
    have hr' (e : E) : J.right e = rho.symm (K.right e) := by
      simpa only [Equiv.symm_apply_apply] using congrArg rho.symm (hr e)
    have h' : J.reaches A (rho.symm (rho x)) (rho.symm (rho y)) :=
      Relation.ReflTransGen.lift' rho.symm (fun _ _ hadj => by
        obtain ⟨e, he, h | h⟩ := hadj
        · exact .single ⟨e, he, Or.inl ⟨(hl' e).trans (congrArg rho.symm h.1),
            (hr' e).trans (congrArg rho.symm h.2)⟩⟩
        · exact .single ⟨e, he, Or.inr ⟨(hr' e).trans (congrArg rho.symm h.1),
            (hl' e).trans (congrArg rho.symm h.2)⟩⟩) _ _ h
    simpa only [Equiv.symm_apply_apply] using h'

theorem tree_vertex_equiv_iff (J : CopiedGraph V E) (K : CopiedGraph W E)
    (rho : V ≃ W) (hl : ∀ e, rho (J.left e) = K.left e)
    (hr : ∀ e, rho (J.right e) = K.right e) (A : Finset E) :
    ((Set.univ : Set V).Nonempty ∧ (∀ x y, J.reaches A x y) ∧
      ∀ e ∈ A, ¬J.reaches (A.erase e) (J.left e) (J.right e)) ↔
    ((Set.univ : Set W).Nonempty ∧ (∀ x y, K.reaches A x y) ∧
      ∀ e ∈ A, ¬K.reaches (A.erase e) (K.left e) (K.right e)) := by
  have reach := reaches_vertex_equiv_iff J K rho hl hr
  constructor
  · rintro ⟨⟨x, _⟩, hc, hf⟩
    refine ⟨⟨rho x, Set.mem_univ _⟩, ?_, ?_⟩
    · intro a b
      simpa only [Equiv.apply_symm_apply] using (reach A _ _).mp (hc (rho.symm a) (rho.symm b))
    · intro e he h
      apply hf e he
      apply (reach (A.erase e) _ _).mpr
      rwa [hl, hr]
  · rintro ⟨⟨x, _⟩, hc, hf⟩
    refine ⟨⟨rho.symm x, Set.mem_univ _⟩, fun a b => (reach A a b).mpr (hc _ _), ?_⟩
    intro e he h
    apply hf e he
    have h' := (reach (A.erase e) _ _).mp h
    rwa [hl, hr] at h'

/-- Vertex transport has literal identity maps on edge subsets in both directions. -/
def treeVertexEquiv (J : CopiedGraph V E) (K : CopiedGraph W E) (rho : V ≃ W)
    (hl : ∀ e, rho (J.left e) = K.left e) (hr : ∀ e, rho (J.right e) = K.right e) :
    J.SpanningTree ≃ K.SpanningTree where
  toFun T := ⟨T.val, (tree_vertex_equiv_iff J K rho hl hr T.val).mp T.property⟩
  invFun T := ⟨T.val, (tree_vertex_equiv_iff J K rho hl hr T.val).mpr T.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem treeVertexEquiv_copies (J : CopiedGraph V E) (K : CopiedGraph W E) (rho : V ≃ W)
    (hl : ∀ e, rho (J.left e) = K.left e) (hr : ∀ e, rho (J.right e) = K.right e)
    (T : J.SpanningTree) : (treeVertexEquiv J K rho hl hr T).val = T.val := rfl

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
