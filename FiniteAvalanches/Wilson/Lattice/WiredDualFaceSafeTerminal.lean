import FiniteAvalanches.Wilson.Lattice.WiredDualFaceSafeIncident
import FiniteAvalanches.Wilson.Lattice.WiredDualFaceBoundaryTermination
import FiniteAvalanches.Wilson.CyclePopping.NestedRootTerminalCopies

/-! Safe face-square prefixes couple origin and boundary terminal forests. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance decEqWiredEdgeDualFaceSafeTerminal (B : ℕ) :
    DecidableEq (FiniteWired.Edge B) := Classical.decEq _

/-- At an interior face, a padded direction instruction has the same successor
as the original incident-copy instruction. -/
theorem wiredDualFace_paddedIncident_successor (B : ℕ)
    (σ : (p : WiredDualFace (B + 1) × ℕ) → IncidentCopy (wiredDualFaceGraph (B + 1)) p.1)
    (v : WiredDualFace (B + 1)) (hin : FiniteWired.inBox B (wiredDualFaceSite v)) (i : ℕ) :
    incidentCopyHead (wiredDualFaceGraph (B + 1)) v (σ (v, i)) =
      wiredDualFaceDirectionHead (B + 1) v
        (padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ) (v, i)) := by
  let x := wiredDualFaceInteriorVertex B v hin
  have hx : FiniteWired.inBox B (FiniteWired.site x) := by
    rw [site_wiredDualFaceInteriorVertex]
    exact hin
  have he : wiredDualFaceInnerVertex (B + 1) x = v :=
    wiredDualFaceInnerVertex_interiorVertex B v hin
  simp only [padWiredDualFaceInteriorStacks, dif_pos hin, wiredDualFaceInteriorDirectionStacks]
  change incidentCopyHead (wiredDualFaceGraph (B + 1)) v (σ (v, i)) =
    wiredDualFaceDirectionHead (B + 1) v
      ((wiredDualFaceInteriorDirectionEquiv B x hx).symm
        (σ (wiredDualFaceInnerVertex (B + 1) x, i)))
  have h := wiredDualFaceDirectionHead_eq_incident B x hx
    ((wiredDualFaceInteriorDirectionEquiv B x hx).symm
      (σ (wiredDualFaceInnerVertex (B + 1) x, i)))
  have hm := congrArg (fun z => incidentCopyHead (wiredDualFaceGraph (B + 1)) z (σ (z, i))) he.symm
  calc
    incidentCopyHead (wiredDualFaceGraph (B + 1)) v (σ (v, i)) = _ := hm
    _ = wiredDualFaceDirectionHead (B + 1) (wiredDualFaceInnerVertex (B + 1) x)
        ((wiredDualFaceInteriorDirectionEquiv B x hx).symm
          (σ (wiredDualFaceInnerVertex (B + 1) x, i))) := by
      simpa only [Equiv.apply_symm_apply] using h
    _ = _ := congrArg (fun z => wiredDualFaceDirectionHead (B + 1) z
      ((wiredDualFaceInteriorDirectionEquiv B x hx).symm
        (σ (wiredDualFaceInnerVertex (B + 1) x, i)))) he

/-- A safe incident history gives a face exploration avoiding the outer boundary. -/
theorem wiredDualFaceSafeIncidentStackEvent_avoids_boundary (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1))) (n : ℕ)
    (σ : (p : WiredDualFace (B + 1) × ℕ) → IncidentCopy (wiredDualFaceGraph (B + 1)) p.1)
    (hσ : σ ∈ wiredDualFaceSafeIncidentStackEvent B x k n) :
    stackExploreAvoidsRoots (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i))
      (wiredDualFaceOuterBoundary B) (wiredDualFaceOriginAndBoundary B) k
        ((List.range n).map fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i))) := by
  let τ := padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ)
  let y := fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i))
  obtain ⟨N, hhit, havoid⟩ := hσ
  have hh := (boundedBranchHistory_hitsBefore_iff (wiredDualFaceDirectionHead (B + 1)) y
    (wiredDualFaceOriginAndBoundary B) k N n τ).mp hhit
  have hs := stackExploreAvoidsRoots_of_boundedBranchHistory (wiredDualFaceDirectionHead (B + 1)) y
    (wiredDualFaceOriginAndBoundary B) (wiredDualFaceOuterBoundary B) k N n τ hh havoid
  apply stackExploreAvoidsRoots_of_matching_successors (wiredDualFaceDirectionHead (B + 1))
    (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => τ (v, i)) (fun v i => σ (v, i))
    (wiredDualFaceOriginAndBoundary B) (wiredDualFaceOuterBoundary B) k _ ?_ hs
  intro v hv i
  have hin : FiniteWired.inBox B (wiredDualFaceSite v) := by
    by_contra hn
    exact hv (Set.mem_union_right _ hn)
  exact (wiredDualFace_paddedIncident_successor B σ v hin i).symm

/-- Safe face explorations agree for the origin and the origin plus boundary. -/
theorem wiredDualFaceSafeIncidentStackEvent_explorations (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1))) (n : ℕ)
    (σ : (p : WiredDualFace (B + 1) × ℕ) → IncidentCopy (wiredDualFaceGraph (B + 1)) p.1)
    (hσ : σ ∈ wiredDualFaceSafeIncidentStackEvent B x k n) :
    ∃ T j, stackExplore (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i))
        {wiredDualFaceOrigin (B + 1)} k
          ((List.range n).map fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i))) = some (T, j) ∧
      stackExplore (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i))
        (wiredDualFaceOriginAndBoundary B) k
          ((List.range n).map fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i))) =
          some (wiredDualFaceOriginAndBoundary B ∪ T, j) ∧ {wiredDualFaceOrigin (B + 1)} ⊆ T := by
  have hSD : wiredDualFaceOriginAndBoundary B ⊆
      {wiredDualFaceOrigin (B + 1)} ∪ wiredDualFaceOuterBoundary B := by
    intro v hv
    rcases hv with h | h
    · left
      apply Set.mem_singleton_iff.mpr
      apply wiredDualFaceSite_injective (B + 1)
      exact h
    · exact Or.inr h
  exact stackExplore_eq_of_avoidsExtraRoots (incidentCopyHead (wiredDualFaceGraph (B + 1)))
    (fun v i => σ (v, i)) {wiredDualFaceOrigin (B + 1)} (wiredDualFaceOriginAndBoundary B)
    (wiredDualFaceOuterBoundary B) k _ (wiredDualFaceOrigin_subset_originAndBoundary B) hSD
    (wiredDualFaceSafeIncidentStackEvent_avoids_boundary B x k n σ hσ)

/-- Safe face prefixes make origin and boundary terminal forests agree on
attached copies with endpoints away from the outer boundary. -/
theorem wiredDualFaceSafe_terminalCopies_agree (B : ℕ) (x : ℕ → Site 2)
    (k t u : Cursor (WiredDualFace (B + 1))) (n : ℕ)
    (σ : (p : WiredDualFace (B + 1) × ℕ) → IncidentCopy (wiredDualFaceGraph (B + 1)) p.1)
    (hσ : σ ∈ wiredDualFaceSafeIncidentStackEvent B x k n)
    (hrun : Relation.ReflTransGen (pop_step {wiredDualFaceOrigin (B + 1)}
      (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i))) k t)
    (ht : terminal {wiredDualFaceOrigin (B + 1)} (incidentCopyHead (wiredDualFaceGraph (B + 1)))
      (fun v i => σ (v, i)) t)
    (hsrun : Relation.ReflTransGen (pop_step (wiredDualFaceOriginAndBoundary B)
      (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i))) k u)
    (hu : terminal (wiredDualFaceOriginAndBoundary B) (incidentCopyHead (wiredDualFaceGraph (B + 1)))
      (fun v i => σ (v, i)) u) :
    ∃ T : Set (WiredDualFace (B + 1)),
      (∀ i < n, wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)) ∈ T) ∧
      ∀ e : FiniteWired.Edge (B + 1), (wiredDualFaceGraph (B + 1)).left e ∈ T →
        (wiredDualFaceGraph (B + 1)).right e ∈ T →
        (wiredDualFaceGraph (B + 1)).left e ∉ wiredDualFaceOuterBoundary B →
        (wiredDualFaceGraph (B + 1)).right e ∉ wiredDualFaceOuterBoundary B →
        (e ∈ incidentArrowCopies (wiredDualFaceGraph (B + 1)) {wiredDualFaceOrigin (B + 1)}
            ⟨fun v => σ (v, t v), ht⟩ ↔
          e ∈ incidentArrowCopies (wiredDualFaceGraph (B + 1)) (wiredDualFaceOriginAndBoundary B)
            ⟨fun v => σ (v, u v), hu⟩) := by
  obtain ⟨T, j, hsmall, hlarge, _⟩ := wiredDualFaceSafeIncidentStackEvent_explorations B x k n σ hσ
  have hcover := (stackExplore_of_some {wiredDualFaceOrigin (B + 1)}
    (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i)) k
    ((List.range n).map fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i))) T j hsmall).2.1
  refine ⟨T, ?_, ?_⟩
  · intro i hi
    exact hcover _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  · intro e he1 he2 hne1 hne2
    apply terminal_incidentCopy_mem_iff_of_nested_prefix (wiredDualFaceGraph (B + 1))
      {wiredDualFaceOrigin (B + 1)} (wiredDualFaceOriginAndBoundary B)
      (wiredDualFaceOrigin_subset_originAndBoundary B)
      (fun v i => σ (v, i)) k t u _ T j hrun ht hsrun hu hsmall hlarge e he1 he2
    all_goals
      intro hv
      rcases hv with h | h
      · apply Set.mem_singleton_iff.mpr
        apply wiredDualFaceSite_injective (B + 1)
        exact h
      · first | exact (hne1 h).elim | exact (hne2 h).elim

end
end FiniteAvalanches.Wilson.Lattice
