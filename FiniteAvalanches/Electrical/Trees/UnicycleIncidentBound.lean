import FiniteAvalanches.Electrical.Trees.IncidentPathUniqueness

/-! A tree with one extra copy has at most two removable copies at a prescribed vertex. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open scoped Classical
noncomputable section
variable {V E : Type}

/-- Among the old tree copies, a cycle through the extra copy uses at most one at its endpoint. -/
theorem unicycle_incident_old_unique (J : CopiedGraph V E) (T : J.SpanningTree)
    (p : V) (c : E) (hc : c ∉ T.val) (hcp : J.left c = p ∨ J.right c = p)
    (e f : E) (he : e ∈ T.val) (hf : f ∈ T.val)
    (hep : J.left e = p ∨ J.right e = p) (hfp : J.left f = p ∨ J.right f = p)
    (hte : (Set.univ : Set V).Nonempty ∧
      (∀ x y, J.reaches ((insert c T.val).erase e) x y) ∧
      ∀ a ∈ (insert c T.val).erase e,
        ¬J.reaches (((insert c T.val).erase e).erase a) (J.left a) (J.right a))
    (htf : (Set.univ : Set V).Nonempty ∧
      (∀ x y, J.reaches ((insert c T.val).erase f) x y) ∧
      ∀ a ∈ (insert c T.val).erase f,
        ¬J.reaches (((insert c T.val).erase f).erase a) (J.left a) (J.right a)) : e = f := by
  have hce : c ≠ e := fun h => hc (h.symm ▸ he)
  have hcf : c ≠ f := fun h => hc (h.symm ▸ hf)
  rw [Finset.erase_insert_of_ne hce] at hte
  rw [Finset.erase_insert_of_ne hcf] at htf
  have hecut := (tree_exchange_iff J T e c he hc).mp hte
  have hfcut := (tree_exchange_iff J T f c hf hc).mp htf
  rcases hcp with hcp | hcp
  · rw [hcp] at hecut hfcut
    exact tree_path_incident_unique J T p (J.right c) e f he hep hfp hecut hfcut
  · have hecut' : ¬J.reaches (T.val.erase e) p (J.left c) := by
      intro h
      apply hecut
      rw [hcp]
      exact TwoCopy.reaches_symm J h
    have hfcut' : ¬J.reaches (T.val.erase f) p (J.left c) := by
      intro h
      apply hfcut
      rw [hcp]
      exact TwoCopy.reaches_symm J h
    exact tree_path_incident_unique J T p (J.left c) e f he hep hfp hecut' hfcut'

/-- This bound counts edge IDs, so an extra loop counts once and parallel copies stay distinct. -/
theorem unicycle_incident_card_le_two (J : CopiedGraph V E) (T : J.SpanningTree)
    (p : V) (c : E) (hc : c ∉ T.val) (hcp : J.left c = p ∨ J.right c = p)
    (S : Finset E)
    (hS : ∀ e ∈ S, e ∈ insert c T.val ∧ (J.left e = p ∨ J.right e = p) ∧
      (Set.univ : Set V).Nonempty ∧
      (∀ x y, J.reaches ((insert c T.val).erase e) x y) ∧
      ∀ a ∈ (insert c T.val).erase e,
        ¬J.reaches (((insert c T.val).erase e).erase a) (J.left a) (J.right a)) :
    S.card ≤ 2 := by
  by_cases h : ∃ f ∈ S, f ≠ c
  · obtain ⟨f, hf, hfc⟩ := h
    have hfT : f ∈ T.val := (Finset.mem_insert.mp (hS f hf).1).resolve_left hfc
    have hsub : S ⊆ ({c, f} : Finset E) := by
      intro e he
      by_cases hec : e = c
      · exact Finset.mem_insert.mpr (Or.inl hec)
      · have heT : e ∈ T.val := (Finset.mem_insert.mp (hS e he).1).resolve_left hec
        have hef := unicycle_incident_old_unique J T p c hc hcp e f heT hfT
          (hS e he).2.1 (hS f hf).2.1 (hS e he).2.2 (hS f hf).2.2
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hef))
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · have hsub : S ⊆ ({c} : Finset E) := by
      intro e he
      apply Finset.mem_singleton.mpr
      by_contra hec
      exact h ⟨e, he, hec⟩
    have hcard := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at hcard
    omega

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
