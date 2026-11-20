import FiniteAvalanches.Wilson.CyclePopping.VariableStackLaw
import FiniteAvalanches.Wilson.CyclePopping.RootwardForest
import FiniteAvalanches.Wilson.CyclePopping.RootwardUniqueness
import FiniteAvalanches.Wilson.CyclePopping.ForestRank

/-! Rootward arrow assignments on finite copied-edge graphs. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open FiniteAvalanches.Trees
open scoped Classical

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq E]

/-- A copy incident to a vertex, retaining its original edge identity. -/
def IncidentCopy (G : Multigraph V E) (v : V) :=
  {e : E // G.left e = v ∨ G.right e = v}

instance (G : Multigraph V E) (v : V) : Fintype (IncidentCopy G v) := by
  unfold IncidentCopy
  infer_instance

/-- The other endpoint of an incident copied edge. -/
def incidentCopyHead (G : Multigraph V E) (v : V) (e : IncidentCopy G v) : V :=
  if G.left e.val = v then G.right e.val else G.left e.val

omit [DecidableEq E] in
/-- An incident copy joins its source to the associated head. -/
theorem incidentCopy_endpoints (G : Multigraph V E) (v : V) (e : IncidentCopy G v) :
    (G.left e.val = v ∧ G.right e.val = incidentCopyHead G v e) ∨
      (G.right e.val = v ∧ G.left e.val = incidentCopyHead G v e) := by
  by_cases h : G.left e.val = v
  · exact Or.inl ⟨h, by simp only [incidentCopyHead, if_pos h]⟩
  · exact Or.inr ⟨e.property.resolve_left h, by simp only [incidentCopyHead, if_neg h]⟩

/-- Cycle-free incident-copy assignments, retaining the unused arrows at roots. -/
abbrev GoodIncidentArrows (G : Multigraph V E) (R : Set V) :=
  GoodArrows R (incidentCopyHead G)

/-- The copied edges selected by nonroot vertices of a good assignment. -/
def incidentArrowCopies (G : Multigraph V E) (R : Set V) (a : GoodIncidentArrows G R) : Finset E :=
  rootwardCopies R (fun v => (a.val v).val)

omit [DecidableEq E] in
/-- A cycle-free assignment of incident copies induces an actual rooted forest. -/
theorem incidentArrowCopies_is_rooted_forest (G : Multigraph V E) (R : Set V)
    (a : GoodIncidentArrows G R) : G.is_rooted_forest R (incidentArrowCopies G R a) := by
  apply rootwardCopies_is_rooted_forest G R (fun v => incidentCopyHead G v (a.val v))
    (fun v => (a.val v).val)
  · exact GoodArrows.reaches_root R (incidentCopyHead G) a.val a.property
  · intro v _
    exact incidentCopy_endpoints G v (a.val v)

/-- The rooted copied forest induced by a good incident-arrow assignment. -/
def incidentArrowForest (G : Multigraph V E) (R : Set V) (a : GoodIncidentArrows G R) :
    G.RootedForest R :=
  ⟨incidentArrowCopies G R a, incidentArrowCopies_is_rooted_forest G R a⟩

omit [DecidableEq E] in
/-- Equal incident-arrow forests have identical arrows away from the roots. -/
theorem incidentArrowForest_eq_imp_nonroot_eq (G : Multigraph V E) (R : Set V)
    (a b : GoodIncidentArrows G R) (h : incidentArrowForest G R a = incidentArrowForest G R b)
    {v : V} (hv : v ∉ R) : a.val v = b.val v := by
  have hF : rootwardCopies R (fun v => (a.val v).val) =
      rootwardCopies R (fun v => (b.val v).val) := congrArg Subtype.val h
  have he := rootwardCopies_eq_imp_edge_eq G R
    (fun v => incidentCopyHead G v (a.val v)) (fun v => incidentCopyHead G v (b.val v))
    (fun v => (a.val v).val) (fun v => (b.val v).val)
    (GoodArrows.reaches_root R (incidentCopyHead G) a.val a.property)
    (GoodArrows.reaches_root R (incidentCopyHead G) b.val b.property)
    (fun v _ => incidentCopy_endpoints G v (a.val v))
    (fun v _ => incidentCopy_endpoints G v (b.val v)) hF hv
  exact Subtype.ext he

omit [DecidableEq E] in
/-- Root arrows do not affect the selected copied forest. -/
theorem incidentArrowForest_eq_of_nonroot_eq (G : Multigraph V E) (R : Set V)
    (a b : GoodIncidentArrows G R) (h : ∀ v ∉ R, a.val v = b.val v) :
    incidentArrowForest G R a = incidentArrowForest G R b := by
  apply Subtype.ext
  change rootwardCopies R (fun v => (a.val v).val) = rootwardCopies R (fun v => (b.val v).val)
  ext e
  simp only [rootwardCopies, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨v, hv, he⟩
    exact ⟨v, hv, (congrArg Subtype.val (h v hv)).symm.trans he⟩
  · rintro ⟨v, hv, he⟩
    exact ⟨v, hv, (congrArg Subtype.val (h v hv)).trans he⟩

end
end FiniteAvalanches.Wilson.CyclePopping
