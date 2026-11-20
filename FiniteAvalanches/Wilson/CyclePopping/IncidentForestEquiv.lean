import FiniteAvalanches.Wilson.CyclePopping.IncidentArrows

/-! Orienting finite rooted forests by their original incident copies. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open FiniteAvalanches.Trees
open scoped Classical

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E]
variable (G : Multigraph V E) [∀ v, Nonempty (IncidentCopy G v)]

omit [∀ v, Nonempty (IncidentCopy G v)] in
/-- Every nonroot vertex has an incident forest copy decreasing root distance. -/
theorem exists_forest_rootward_copy (R : Set V) (F : G.RootedForest R)
    (v : V) (hv : v ∉ R) :
    ∃ e : IncidentCopy G v, e.val ∈ F.val ∧
      forestRootRank G R F (incidentCopyHead G v e) < forestRootRank G R F v := by
  obtain ⟨y, ⟨e, he, hend⟩, hy⟩ := forestRootRank_descends G R F hv
  have hi : G.left e = v ∨ G.right e = v := by
    rcases hend with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  let a : IncidentCopy G v := ⟨e, hi⟩
  have ha := incidentCopy_endpoints G v a
  have hy' : incidentCopyHead G v a = y := by
    rcases hend with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases ha with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · exact h4.symm.trans h2
    · have hf : G.left e = G.right e := h1.trans h3.symm
      exact (G.loopless e hf).elim
    · have hf : G.left e = G.right e := h3.trans h1.symm
      exact (G.loopless e hf).elim
    · exact h4.symm.trans h2
  exact ⟨a, he, hy' ▸ hy⟩

/-- Choose a descending copied edge at each nonroot and an arbitrary root copy. -/
def forestIncidentCopy (R : Set V) (F : G.RootedForest R) (v : V) : IncidentCopy G v :=
  if hv : v ∉ R then Classical.choose (exists_forest_rootward_copy G R F v hv)
  else Classical.choice (inferInstance : Nonempty (IncidentCopy G v))

/-- Chosen nonroot copies belong to the forest and decrease the root rank. -/
theorem forestIncidentCopy_spec (R : Set V) (F : G.RootedForest R) (v : V) (hv : v ∉ R) :
    (forestIncidentCopy G R F v).val ∈ F.val ∧
      forestRootRank G R F (incidentCopyHead G v (forestIncidentCopy G R F v)) <
        forestRootRank G R F v := by
  simp only [forestIncidentCopy, dif_pos hv]
  exact Classical.choose_spec (exists_forest_rootward_copy G R F v hv)

/-- Forest copies oriented toward the roots contain no directed root-avoiding cycle. -/
def forestIncidentArrows (R : Set V) (F : G.RootedForest R) : GoodIncidentArrows G R := by
  refine ⟨forestIncidentCopy G R F, ?_⟩
  intro c hc
  obtain ⟨v, hv, hmin⟩ := c.exists_min_image (forestRootRank G R F) hc.nonempty
  have hlt := (forestIncidentCopy_spec G R F v (hc.avoids_roots v hv)).2
  exact (not_lt_of_ge (hmin _ (hc.maps_to v hv))) hlt

/-- Forgetting the rootward orientation recovers the original forest. -/
theorem incidentArrowForest_forestIncidentArrows (R : Set V) (F : G.RootedForest R) :
    incidentArrowForest G R (forestIncidentArrows G R F) = F := by
  apply rootedForest_eq_of_subset G R F
  intro e he
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
  exact (forestIncidentCopy_spec G R F v (Finset.mem_filter.mp hv).2).1

/-- The independent unused instructions at the roots. -/
abbrev IncidentRootCopies (R : Set V) := (v : {v : V // v ∈ R}) → IncidentCopy G v.val

/-- Orient a forest and insert prescribed incident copies at the roots. -/
def forestIncidentArrowsWithRoots (R : Set V) (F : G.RootedForest R)
    (d : IncidentRootCopies G R) : GoodIncidentArrows G R := by
  let a : (v : V) → IncidentCopy G v := fun v =>
    if hv : v ∈ R then d ⟨v, hv⟩ else forestIncidentCopy G R F v
  refine ⟨a, ?_⟩
  intro c hc
  apply (forestIncidentArrows G R F).property c
  apply hc.congr
  intro v hv
  have hnot := hc.avoids_roots v hv
  simp only [a, dif_neg hnot, forestIncidentArrows]

/-- Root instructions do not alter the forest recovered from its orientation. -/
theorem incidentArrowForest_forestIncidentArrowsWithRoots (R : Set V) (F : G.RootedForest R)
    (d : IncidentRootCopies G R) :
    incidentArrowForest G R (forestIncidentArrowsWithRoots G R F d) = F := by
  have he : incidentArrowForest G R (forestIncidentArrowsWithRoots G R F d) =
      incidentArrowForest G R (forestIncidentArrows G R F) := by
    apply incidentArrowForest_eq_of_nonroot_eq G R
    intro v hv
    simp only [forestIncidentArrowsWithRoots, dif_neg hv, forestIncidentArrows]
  exact he.trans (incidentArrowForest_forestIncidentArrows G R F)

/-- Cycle-free incident assignments correspond to rooted forests together
with arbitrary unused root instructions. -/
def incidentArrowForestEquiv (R : Set V) :
    GoodIncidentArrows G R ≃ G.RootedForest R × IncidentRootCopies G R where
  toFun a := (incidentArrowForest G R a, fun r => a.val r.val)
  invFun p := forestIncidentArrowsWithRoots G R p.1 p.2
  left_inv a := by
    apply Subtype.ext
    funext v
    by_cases hv : v ∈ R
    · simp only [forestIncidentArrowsWithRoots, dif_pos hv]
    · have he := incidentArrowForest_eq_imp_nonroot_eq G R
        (forestIncidentArrows G R (incidentArrowForest G R a)) a
        (incidentArrowForest_forestIncidentArrows G R (incidentArrowForest G R a)) hv
      simpa only [forestIncidentArrowsWithRoots, dif_neg hv, forestIncidentArrows] using he
  right_inv p := by
    apply Prod.ext
    · exact incidentArrowForest_forestIncidentArrowsWithRoots G R p.1 p.2
    · funext r
      simp only [forestIncidentArrowsWithRoots, dif_pos r.property]

end
end FiniteAvalanches.Wilson.CyclePopping
