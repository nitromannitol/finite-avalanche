import FiniteAvalanches.Electrical.Trees.ForestEdgeDeletion

/-! Exchanging copies inside a rooted component preserves every component and every root. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open scoped Classical
noncomputable section
variable {V E : Type}

                                                                                       
theorem twoRootForest_exchange (J : CopiedGraph V E) (u v : V)
    (F : J.TwoRootForest u v) (e c : E) (he : e ∈ F.val)
    (hc : J.reaches F.val (J.left c) (J.right c))
    (hcut : ¬J.reaches (F.val.erase e) (J.left c) (J.right c)) :
    (∀ a ∈ insert c (F.val.erase e),
      ¬J.reaches ((insert c (F.val.erase e)).erase a) (J.left a) (J.right a)) ∧
      ∀ x, ∃ r ∈ ({u, v} : Set V), J.reaches (insert c (F.val.erase e)) x r ∧
        ∀ r' ∈ ({u, v} : Set V),
          J.reaches (insert c (F.val.erase e)) x r' → r' = r := by
  let A := F.val.erase e
  let H := insert c A
  have lift {x y : V} (h : J.reaches A x y) : J.reaches H x y :=
    TwoCopy.reaches_mono J (Finset.subset_insert _ _) h
  have hedge : J.reaches H (J.left c) (J.right c) :=
    .single ⟨c, Finset.mem_insert_self _ _, Or.inl ⟨rfl, rfl⟩⟩
  have hejoin : J.reaches H (J.left e) (J.right e) := by
    rw [← Finset.insert_erase he, TwoCopy.reaches_insert_iff J] at hc
    rcases hc with h | ⟨hl, hr⟩ | ⟨hr, hl⟩
    · exact (hcut h).elim
    · exact ((TwoCopy.reaches_symm J (lift hl)).trans hedge).trans
        (TwoCopy.reaches_symm J (lift hr))
    · exact ((lift hl).trans (TwoCopy.reaches_symm J hedge)).trans (lift hr)
  have forward {x y : V} (h : J.reaches F.val x y) : J.reaches H x y := by
    induction h with
    | refl => exact .refl
    | tail _ hadj ih =>
      obtain ⟨a, ha, hends⟩ := hadj
      by_cases hae : a = e
      · subst a
        rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ih.trans hejoin
        · exact ih.trans (TwoCopy.reaches_symm J hejoin)
      · exact ih.tail ⟨a, Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨hae, ha⟩), hends⟩
  have backward {x y : V} (h : J.reaches H x y) : J.reaches F.val x y := by
    induction h with
    | refl => exact .refl
    | tail _ hadj ih =>
      obtain ⟨a, ha, hends⟩ := hadj
      rcases Finset.mem_insert.mp ha with rfl | ha
      · rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ih.trans hc
        · exact ih.trans (TwoCopy.reaches_symm J hc)
      · exact ih.tail ⟨a, Finset.mem_of_mem_erase ha, hends⟩
  refine ⟨TwoCopy.forest_insert J ?_ c hcut, ?_⟩
  · intro a ha h
    apply F.property.1 a (Finset.mem_of_mem_erase ha)
    exact TwoCopy.reaches_mono J (by
      intro b hb
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hb).1,
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb)⟩) h
  · intro x
    obtain ⟨r, hr, hx, hu⟩ := F.property.2 x
    exact ⟨r, hr, forward hx, fun r' hr' hx' => hu r' hr' (backward hx')⟩

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
