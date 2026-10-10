import FiniteAvalanches.Electrical.Trees.ForestComponents
import FiniteAvalanches.Electrical.Trees.IncidentPathUniqueness

/-! Deletion of a tree copy and the first incident copy of a forest path. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open scoped Classical
noncomputable section
variable {V E : Type}

/-- Acyclicity, coverage by two roots, and separation give the exact rooted predicate. -/
theorem twoRootForest_of_cover (J : CopiedGraph V E) (A : Finset E) (u v : V)
    (ha : ∀ e ∈ A, ¬J.reaches (A.erase e) (J.left e) (J.right e))
    (hc : ∀ x, J.reaches A x u ∨ J.reaches A x v)
    (hs : ¬J.reaches A u v) :
    (∀ e ∈ A, ¬J.reaches (A.erase e) (J.left e) (J.right e)) ∧
      ∀ x, ∃ r ∈ ({u, v} : Set V), J.reaches A x r ∧
        ∀ r' ∈ ({u, v} : Set V), J.reaches A x r' → r' = r := by
  refine ⟨ha, ?_⟩
  intro x
  rcases hc x with hx | hx
  · refine ⟨u, Or.inl rfl, hx, ?_⟩
    intro r hr hxr
    rcases hr with rfl | rfl
    · rfl
    · exact (hs ((TwoCopy.reaches_symm J hx).trans hxr)).elim
  · refine ⟨v, Or.inr rfl, hx, ?_⟩
    intro r hr hxr
    rcases hr with rfl | rfl
    · exact (hs ((TwoCopy.reaches_symm J hxr).trans hx)).elim
    · rfl

/-- Deleting a selected copy leaves the two components rooted at its endpoints. -/
theorem tree_erase_twoRootForest (J : CopiedGraph V E) (T : J.SpanningTree)
    (e : E) (he : e ∈ T.val) :
    (∀ f ∈ T.val.erase e, ¬J.reaches ((T.val.erase e).erase f) (J.left f) (J.right f)) ∧
      ∀ x, ∃ r ∈ ({J.left e, J.right e} : Set V), J.reaches (T.val.erase e) x r ∧
        ∀ r' ∈ ({J.left e, J.right e} : Set V),
          J.reaches (T.val.erase e) x r' → r' = r := by
  apply twoRootForest_of_cover J _ _ _
  · intro f hf h
    apply T.property.2.2 f (Finset.mem_of_mem_erase hf)
    exact TwoCopy.reaches_mono J (by
      intro a ha
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp ha).1,
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha)⟩) h
  · intro x
    have h := T.property.2.1 (J.left e) x
    rw [← Finset.insert_erase he, TwoCopy.reaches_insert_iff J] at h
    rcases h with h | ⟨_, h⟩ | ⟨h, _⟩
    · exact Or.inl (TwoCopy.reaches_symm J h)
    · exact Or.inr (TwoCopy.reaches_symm J h)
    · exact (T.property.2.2 e he h).elim
  · exact T.property.2.2 e he

/-- Two separated vertices can replace the roots of the same two components. -/
theorem twoRootForest_reroot (J : CopiedGraph V E) (a b u v : V)
    (F : J.TwoRootForest a b) (hs : ¬J.reaches F.val u v) :
    (∀ e ∈ F.val, ¬J.reaches (F.val.erase e) (J.left e) (J.right e)) ∧
      ∀ x, ∃ r ∈ ({u, v} : Set V), J.reaches F.val x r ∧
        ∀ r' ∈ ({u, v} : Set V), J.reaches F.val x r' → r' = r := by
  apply twoRootForest_of_cover J F.val u v F.property.1 _ hs
  intro x
  rcases twoRootForest_cover J a b F u with hu | hu <;>
    rcases twoRootForest_cover J a b F v with hv | hv
  · exact (hs (hu.trans (TwoCopy.reaches_symm J hv))).elim
  · exact (twoRootForest_cover J a b F x).imp
      (fun hx => hx.trans (TwoCopy.reaches_symm J hu))
      (fun hx => hx.trans (TwoCopy.reaches_symm J hv))
  · exact (twoRootForest_cover J a b F x).symm.imp
      (fun hx => hx.trans (TwoCopy.reaches_symm J hu))
      (fun hx => hx.trans (TwoCopy.reaches_symm J hv))
  · exact (hs (hu.trans (TwoCopy.reaches_symm J hv))).elim

/-- Every nontrivial forest path has an incident selected copy whose deletion separates it. -/
theorem forest_path_incident_exists (J : CopiedGraph V E) (A : Finset E)
    (ha : ∀ e ∈ A, ¬J.reaches (A.erase e) (J.left e) (J.right e))
    (p q : V) (hne : p ≠ q) (h : J.reaches A p q) :
    ∃ e ∈ A, (J.left e = p ∨ J.right e = p) ∧ ¬J.reaches (A.erase e) p q := by
  have claim : ∀ {q : V}, J.reaches A p q →
      q = p ∨ ∃ e ∈ A, (J.left e = p ∨ J.right e = p) ∧
        ¬J.reaches (A.erase e) p q := by
    intro q h
    induction h with
    | refl => exact Or.inl rfl
    | @tail z y _ hadj ih =>
      obtain ⟨f, hf, hends⟩ := hadj
      by_cases hyp : y = p
      · exact Or.inl hyp
      · apply Or.inr
        rcases ih with rfl | ⟨e, he, hep, hcut⟩
        · refine ⟨f, hf, ?_, ?_⟩
          · exact hends.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
          · intro h
            apply ha f hf
            rcases hends with ⟨hl, hr⟩ | ⟨hr, hl⟩
            · exact hl ▸ hr ▸ h
            · exact hl ▸ hr ▸ TwoCopy.reaches_symm J h
        · by_cases hfe : f = e
          · subst f
            rcases hep with hep | hep <;> rcases hends with hh | hh
            · exact (hcut (hh.1.symm.trans hep ▸ Relation.ReflTransGen.refl)).elim
            · exact (hyp (hh.2.symm.trans hep)).elim
            · exact (hyp (hh.2.symm.trans hep)).elim
            · exact (hcut (hh.1.symm.trans hep ▸ Relation.ReflTransGen.refl)).elim
          · refine ⟨e, he, hep, ?_⟩
            intro hpy
            have hzy : J.reaches (A.erase e) z y :=
              .single ⟨f, Finset.mem_erase.mpr ⟨hfe, hf⟩, hends⟩
            exact hcut (hpy.trans (TwoCopy.reaches_symm J hzy))
  exact (claim h).resolve_left (Ne.symm hne)

end
end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
