import FiniteAvalanches.Wilson.Lattice.FreeSafeHistoryLaw
import FiniteAvalanches.Wilson.Lattice.HistoryRootCursor
import FiniteAvalanches.Wilson.CyclePopping.AvoidAlphabetCoupling

/-! Safe free-box histories under independent incident-copy stacks. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance decEqInteriorEdgeFreeSafeIncidentLaw (N : ℕ) : DecidableEq (FiniteWired.InteriorEdge N) := Classical.decEq _

/-- Safe direction-stack histories form a measurable event. -/
theorem measurableSet_freeSafeStackHistoryEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1))) (n : ℕ) :
    MeasurableSet (freeSafeStackHistoryEvent B x k n) := by
  have he : freeSafeStackHistoryEvent B x k n = ⋃ N : ℕ,
      {σ | BranchHistory.HitsBefore N n
          (boundedBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
            (freeOriginAndBoundary B) k N σ n) ∧
        BranchHistory.EndsAvoid (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
          (freeOuterBoundary B) n
          (boundedBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
            (freeOriginAndBoundary B) k N σ n)} := by
    ext σ
    simp only [freeSafeStackHistoryEvent, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [he]
  apply MeasurableSet.iUnion
  intro N
  apply measurableSet_of_countable_fibers
    (fun σ => boundedBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
      (freeOriginAndBoundary B) k N σ n)
    (measurableSet_boundedBranchHistory_eq (freeDirectionHead (B + 1))
      (fun i => freeSite (B + 1) (x i)) (freeOriginAndBoundary B) k N n)
    (fun a => BranchHistory.HitsBefore N n a ∧ BranchHistory.EndsAvoid (freeDirectionHead (B + 1))
      (fun i => freeSite (B + 1) (x i)) (freeOuterBoundary B) n a)

/-- A safe history is unchanged by modifying stacks at outer-boundary roots. -/
theorem freeSafeStackHistoryEvent_of_agree_interior (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1)))
    (hk : ∀ v ∈ freeOuterBoundary B, k v = 0) (n : ℕ)
    (σ τ : FiniteWired.Active (B + 1) × ℕ → FiniteWired.Direction)
    (hactive : ∀ v, FiniteWired.inBox B (FiniteWired.site v) → ∀ i, τ (v, i) = σ (v, i))
    (hσ : σ ∈ freeSafeStackHistoryEvent B x k n) : τ ∈ freeSafeStackHistoryEvent B x k n := by
  obtain ⟨N, hhit, havoid⟩ := hσ
  let h := boundedBranchHistory (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i))
    (freeOriginAndBoundary B) k N σ n
  have hh := (boundedBranchHistory_hitsBefore_iff (freeDirectionHead (B + 1))
    (fun i => freeSite (B + 1) (x i)) (freeOriginAndBoundary B) k N n σ).mp hhit
  have hboundary (v : FiniteWired.Active (B + 1)) (hv : v ∈ freeOuterBoundary B) :
      branchHistoryCursor (freeDirectionHead (B + 1)) (fun i => freeSite (B + 1) (x i)) k n h v = 0 := by
    rw [branchHistoryCursor_eq_at_initial_root (freeDirectionHead (B + 1))
      (fun i => freeSite (B + 1) (x i)) (freeOriginAndBoundary B) k N n σ hh v
      (Set.mem_union_right _ hv), hk v hv]
  have hagree : ∀ v i, i < branchHistoryCursor (freeDirectionHead (B + 1))
      (fun i => freeSite (B + 1) (x i)) k n h v → τ (v, i) = σ (v, i) := by
    intro v i hi
    by_cases hv : FiniteWired.inBox B (FiniteWired.site v)
    · exact hactive v hv i
    · have hv' : v ∈ freeOuterBoundary B := hv
      rw [hboundary v hv'] at hi
      omega
  have he := boundedBranchHistory_stable (freeDirectionHead (B + 1))
    (fun i => freeSite (B + 1) (x i)) (freeOriginAndBoundary B) k N n σ τ hagree
  refine ⟨N, ?_, ?_⟩ <;> rw [he]
  · exact hhit
  · exact havoid

/-- Padding the boundary does not change a safe history. -/
theorem freeSafeStackHistoryEvent_pad_iff (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1)))
    (hk : ∀ v ∈ freeOuterBoundary B, k v = 0) (n : ℕ)
    (σ : FiniteWired.Active (B + 1) × ℕ → FiniteWired.Direction) :
    padFreeInteriorStacks B (freeInteriorProjection B σ) ∈ freeSafeStackHistoryEvent B x k n ↔
      σ ∈ freeSafeStackHistoryEvent B x k n := by
  constructor
  · intro h
    apply freeSafeStackHistoryEvent_of_agree_interior B x k hk n
      (padFreeInteriorStacks B (freeInteriorProjection B σ)) σ ?_ h
    intro v hv i
    simp only [padFreeInteriorStacks, dif_pos hv, freeInteriorProjection]
  · intro h
    apply freeSafeStackHistoryEvent_of_agree_interior B x k hk n σ
      (padFreeInteriorStacks B (freeInteriorProjection B σ)) ?_ h
    intro v hv i
    simp only [padFreeInteriorStacks, dif_pos hv, freeInteriorProjection]

/-- A boundary-insensitive direction event has the same probability under
free incident stacks and ordinary direction stacks. -/
theorem variableStackLaw_freeInterior_event_eq (B : ℕ)
    (E : Set (FiniteWired.Active (B + 1) × ℕ → FiniteWired.Direction)) (hE : MeasurableSet E)
    (hstable : ∀ σ, padFreeInteriorStacks B (freeInteriorProjection B σ) ∈ E ↔ σ ∈ E) :
    variableStackLaw (IncidentCopy (freeBoxGraph (B + 1)))
      {σ | padFreeInteriorStacks B (freeInteriorDirectionStacks B σ) ∈ E} =
      directionStackLaw (FiniteWired.Active (B + 1)) E := by
  let A := (padFreeInteriorStacks B) ⁻¹' E
  have hA : MeasurableSet A := hE.preimage (measurable_padFreeInteriorStacks B)
  have he := congrArg (fun μ : Measure (FreeInterior B × ℕ → FiniteWired.Direction) => μ A)
    (variableStackLaw_map_freeInteriorDirections B)
  rw [Measure.map_apply (by
      apply measurable_pi_iff.mpr
      intro p
      exact (measurable_of_finite (freeInteriorDirectionEquiv B p.1.val p.1.property).symm).comp
        (measurable_pi_apply (p.1.val, p.2))) hA] at he
  have hd := congrArg (fun μ : Measure (FreeInterior B × ℕ → FiniteWired.Direction) => μ A)
    (directionStackLaw_map_freeInteriorProjection B)
  rw [Measure.map_apply (by
      apply measurable_pi_iff.mpr
      intro p
      exact measurable_pi_apply (p.1.val, p.2)) hA] at hd
  have hset : (freeInteriorProjection B) ⁻¹' A = E := by
    ext σ
    exact hstable σ
  rw [hset] at hd
  exact he.trans hd.symm

/-- Free incident stacks whose inner directions give a safe history. -/
def freeSafeIncidentStackEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1))) (n : ℕ) :
    Set ((p : FiniteWired.Active (B + 1) × ℕ) → IncidentCopy (freeBoxGraph (B + 1)) p.1) :=
  {σ | padFreeInteriorStacks B (freeInteriorDirectionStacks B σ) ∈ freeSafeStackHistoryEvent B x k n}

/-- Safe incident-stack history probabilities equal the corresponding row probabilities. -/
theorem freeSafeIncidentStackEvent_measure (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1)))
    (hk : ∀ v ∈ freeOuterBoundary B, k v = 0) (n : ℕ) :
    variableStackLaw (IncidentCopy (freeBoxGraph (B + 1))) (freeSafeIncidentStackEvent B x k n) =
      wilsonRows (freeSafeRowEvent B x k n) := by
  change variableStackLaw (IncidentCopy (freeBoxGraph (B + 1)))
    {σ | padFreeInteriorStacks B (freeInteriorDirectionStacks B σ) ∈ freeSafeStackHistoryEvent B x k n} = _
  rw [variableStackLaw_freeInterior_event_eq B (freeSafeStackHistoryEvent B x k n)
    (measurableSet_freeSafeStackHistoryEvent B x k n) (freeSafeStackHistoryEvent_pad_iff B x k hk n)]
  exact freeSafeStackHistoryEvent_measure B x k n

/-- Safe incident stacks give an actual exploration avoiding the outer boundary. -/
theorem freeSafeIncidentStackEvent_avoids_boundary (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1))) (n : ℕ)
    (σ : (p : FiniteWired.Active (B + 1) × ℕ) → IncidentCopy (freeBoxGraph (B + 1)) p.1)
    (hσ : σ ∈ freeSafeIncidentStackEvent B x k n) :
    stackExploreAvoidsRoots (incidentCopyHead (freeBoxGraph (B + 1))) (fun v i => σ (v, i))
      (freeOuterBoundary B) (freeOriginAndBoundary B) k
        ((List.range n).map fun i => freeSite (B + 1) (x i)) := by
  let τ := padFreeInteriorStacks B (freeInteriorDirectionStacks B σ)
  obtain ⟨N, hhit, havoid⟩ := hσ
  have hh := (boundedBranchHistory_hitsBefore_iff (freeDirectionHead (B + 1))
    (fun i => freeSite (B + 1) (x i)) (freeOriginAndBoundary B) k N n τ).mp hhit
  have hs := stackExploreAvoidsRoots_of_boundedBranchHistory (freeDirectionHead (B + 1))
    (fun i => freeSite (B + 1) (x i)) (freeOriginAndBoundary B) (freeOuterBoundary B)
    k N n τ hh havoid
  apply stackExploreAvoidsRoots_of_matching_successors (freeDirectionHead (B + 1))
    (incidentCopyHead (freeBoxGraph (B + 1))) (fun v i => τ (v, i)) (fun v i => σ (v, i))
    (freeOriginAndBoundary B) (freeOuterBoundary B) k _ ?_ hs
  intro v hv i
  have hin : FiniteWired.inBox B (FiniteWired.site v) := by
    by_contra hn
    exact hv (Set.mem_union_right _ hn)
  simp only [τ, padFreeInteriorStacks, dif_pos hin, freeInteriorDirectionStacks]
  have h := freeInteriorDirection_head_eq B v hin ((freeInteriorDirectionEquiv B v hin).symm (σ (v, i)))
  simpa only [Equiv.apply_symm_apply] using h.symm

/-- Safe free incident-stack exploration probabilities tend to one. -/
theorem freeSafeIncidentStackEvent_tendsto_one (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Active (B + 1)))
    (hk : ∀ B v, v ∈ freeOuterBoundary B → kb B v = 0) (n : ℕ) :
    Tendsto (fun B => variableStackLaw (IncidentCopy (freeBoxGraph (B + 1)))
      (freeSafeIncidentStackEvent B x (kb B) n)) atTop (nhds 1) := by
  have he : (fun B => variableStackLaw (IncidentCopy (freeBoxGraph (B + 1)))
      (freeSafeIncidentStackEvent B x (kb B) n)) =
      fun B => wilsonRows (freeSafeRowEvent B x (kb B) n) := by
    funext B
    exact freeSafeIncidentStackEvent_measure B x (kb B) (hk B) n
  rw [he]
  exact freeSafeRowEvent_tendsto_one x ka kb n

end
end FiniteAvalanches.Wilson.Lattice
