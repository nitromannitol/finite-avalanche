import FiniteAvalanches.Wilson.Lattice.WiredDualFaceSafeRow
import FiniteAvalanches.Wilson.Lattice.WiredDualFaceStoppedExploration
import FiniteAvalanches.Wilson.Lattice.FreeSafeIncidentLaw

/-! Safe face-square histories under independent incident-copy stacks. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Face direction-stack histories that complete without ending on the boundary. -/
def wiredDualFaceSafeStackHistoryEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1))) (n : ℕ) :
    Set (WiredDualFace (B + 1) × ℕ → FiniteWired.Direction) :=
  {σ | ∃ N, BranchHistory.HitsBefore N n
      (boundedBranchHistory (wiredDualFaceDirectionHead (B + 1))
        (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
        (wiredDualFaceOriginAndBoundary B) k N σ n) ∧
    BranchHistory.EndsAvoid (wiredDualFaceDirectionHead (B + 1))
      (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
      (wiredDualFaceOuterBoundary B) n
      (boundedBranchHistory (wiredDualFaceDirectionHead (B + 1))
        (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
        (wiredDualFaceOriginAndBoundary B) k N σ n)}

/-- Safe face direction-stack histories are measurable. -/
theorem measurableSet_wiredDualFaceSafeStackHistoryEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1))) (n : ℕ) :
    MeasurableSet (wiredDualFaceSafeStackHistoryEvent B x k n) := by
  let y := fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i))
  have he : wiredDualFaceSafeStackHistoryEvent B x k n = ⋃ N : ℕ,
      {σ | BranchHistory.HitsBefore N n
          (boundedBranchHistory (wiredDualFaceDirectionHead (B + 1)) y
            (wiredDualFaceOriginAndBoundary B) k N σ n) ∧
        BranchHistory.EndsAvoid (wiredDualFaceDirectionHead (B + 1)) y
          (wiredDualFaceOuterBoundary B) n
          (boundedBranchHistory (wiredDualFaceDirectionHead (B + 1)) y
            (wiredDualFaceOriginAndBoundary B) k N σ n)} := by
    ext σ
    simp only [wiredDualFaceSafeStackHistoryEvent, Set.mem_setOf_eq, Set.mem_iUnion, y]
  rw [he]
  apply MeasurableSet.iUnion
  intro N
  apply measurableSet_of_countable_fibers
    (fun σ => boundedBranchHistory (wiredDualFaceDirectionHead (B + 1)) y
      (wiredDualFaceOriginAndBoundary B) k N σ n)
    (measurableSet_boundedBranchHistory_eq (wiredDualFaceDirectionHead (B + 1)) y
      (wiredDualFaceOriginAndBoundary B) k N n)
    (fun a => BranchHistory.HitsBefore N n a ∧
      BranchHistory.EndsAvoid (wiredDualFaceDirectionHead (B + 1)) y (wiredDualFaceOuterBoundary B) n a)

/-- Safe face histories are unchanged by modifying stacks on the boundary roots. -/
theorem wiredDualFaceSafeStackHistoryEvent_of_agree_interior (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1)))
    (hk : ∀ v ∈ wiredDualFaceOuterBoundary B, k v = 0) (n : ℕ)
    (σ τ : WiredDualFace (B + 1) × ℕ → FiniteWired.Direction)
    (hactive : ∀ v, FiniteWired.inBox B (wiredDualFaceSite v) → ∀ i, τ (v, i) = σ (v, i))
    (hσ : σ ∈ wiredDualFaceSafeStackHistoryEvent B x k n) :
    τ ∈ wiredDualFaceSafeStackHistoryEvent B x k n := by
  obtain ⟨N, hhit, havoid⟩ := hσ
  let y := fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i))
  let h := boundedBranchHistory (wiredDualFaceDirectionHead (B + 1)) y
    (wiredDualFaceOriginAndBoundary B) k N σ n
  have hh := (boundedBranchHistory_hitsBefore_iff (wiredDualFaceDirectionHead (B + 1)) y
    (wiredDualFaceOriginAndBoundary B) k N n σ).mp hhit
  have hboundary (v : WiredDualFace (B + 1)) (hv : v ∈ wiredDualFaceOuterBoundary B) :
      branchHistoryCursor (wiredDualFaceDirectionHead (B + 1)) y k n h v = 0 := by
    rw [branchHistoryCursor_eq_at_initial_root (wiredDualFaceDirectionHead (B + 1)) y
      (wiredDualFaceOriginAndBoundary B) k N n σ hh v (Set.mem_union_right _ hv), hk v hv]
  have hagree : ∀ v i, i < branchHistoryCursor (wiredDualFaceDirectionHead (B + 1)) y k n h v →
      τ (v, i) = σ (v, i) := by
    intro v i hi
    by_cases hv : FiniteWired.inBox B (wiredDualFaceSite v)
    · exact hactive v hv i
    · have hv' : v ∈ wiredDualFaceOuterBoundary B := hv
      rw [hboundary v hv'] at hi
      omega
  have he := boundedBranchHistory_stable (wiredDualFaceDirectionHead (B + 1)) y
    (wiredDualFaceOriginAndBoundary B) k N n σ τ hagree
  refine ⟨N, ?_, ?_⟩ <;> rw [he]
  · exact hhit
  · exact havoid

/-- Padding boundary stacks leaves a safe face history unchanged. -/
theorem wiredDualFaceSafeStackHistoryEvent_pad_iff (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1)))
    (hk : ∀ v ∈ wiredDualFaceOuterBoundary B, k v = 0) (n : ℕ)
    (σ : WiredDualFace (B + 1) × ℕ → FiniteWired.Direction) :
    padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorProjection B σ) ∈
        wiredDualFaceSafeStackHistoryEvent B x k n ↔
      σ ∈ wiredDualFaceSafeStackHistoryEvent B x k n := by
  constructor
  · intro h
    apply wiredDualFaceSafeStackHistoryEvent_of_agree_interior B x k hk n
      (padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorProjection B σ)) σ ?_ h
    intro v hv i
    simp only [padWiredDualFaceInteriorStacks, dif_pos hv, wiredDualFaceInteriorProjection,
      wiredDualFaceInnerVertex_interiorVertex]
  · intro h
    apply wiredDualFaceSafeStackHistoryEvent_of_agree_interior B x k hk n σ
      (padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorProjection B σ)) ?_ h
    intro v hv i
    simp only [padWiredDualFaceInteriorStacks, dif_pos hv, wiredDualFaceInteriorProjection,
      wiredDualFaceInnerVertex_interiorVertex]

/-- A boundary-insensitive direction event has the same probability under
face incident stacks and ordinary direction stacks. -/
theorem variableStackLaw_wiredDualFaceInterior_event_eq (B : ℕ)
    (E : Set (WiredDualFace (B + 1) × ℕ → FiniteWired.Direction)) (hE : MeasurableSet E)
    (hstable : ∀ σ, padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorProjection B σ) ∈ E ↔ σ ∈ E) :
    variableStackLaw (IncidentCopy (wiredDualFaceGraph (B + 1)))
      {σ | padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ) ∈ E} =
      directionStackLaw (WiredDualFace (B + 1)) E := by
  let A := (padWiredDualFaceInteriorStacks B) ⁻¹' E
  have hA : MeasurableSet A := hE.preimage (measurable_padWiredDualFaceInteriorStacks B)
  have he := congrArg (fun μ : Measure (FreeInterior B × ℕ → FiniteWired.Direction) => μ A)
    (variableStackLaw_map_wiredDualFaceInteriorDirections B)
  rw [Measure.map_apply (by
      apply measurable_pi_iff.mpr
      intro p
      exact (measurable_of_finite (wiredDualFaceInteriorDirectionEquiv B p.1.val p.1.property).symm).comp
        (measurable_pi_apply (wiredDualFaceInnerVertex (B + 1) p.1.val, p.2))) hA] at he
  have hd := congrArg (fun μ : Measure (FreeInterior B × ℕ → FiniteWired.Direction) => μ A)
    (directionStackLaw_map_wiredDualFaceInteriorProjection B)
  rw [Measure.map_apply (by
      apply measurable_pi_iff.mpr
      intro p
      exact measurable_pi_apply (wiredDualFaceInnerVertex (B + 1) p.1.val, p.2)) hA] at hd
  have hset : (wiredDualFaceInteriorProjection B) ⁻¹' A = E := by
    ext σ
    exact hstable σ
  rw [hset] at hd
  exact he.trans hd.symm

/-- Face incident stacks whose interior directions give a safe history. -/
def wiredDualFaceSafeIncidentStackEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1))) (n : ℕ) :
    Set ((p : WiredDualFace (B + 1) × ℕ) → IncidentCopy (wiredDualFaceGraph (B + 1)) p.1) :=
  {σ | padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ) ∈
    wiredDualFaceSafeStackHistoryEvent B x k n}

/-- Safe face incident-stack probabilities equal the corresponding row probabilities. -/
theorem wiredDualFaceSafeIncidentStackEvent_measure (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1)))
    (hk : ∀ v ∈ wiredDualFaceOuterBoundary B, k v = 0) (n : ℕ) :
    variableStackLaw (IncidentCopy (wiredDualFaceGraph (B + 1)))
      (wiredDualFaceSafeIncidentStackEvent B x k n) =
      wilsonRows (wiredDualFaceSafeRowEvent B x k n) := by
  change variableStackLaw (IncidentCopy (wiredDualFaceGraph (B + 1)))
    {σ | padWiredDualFaceInteriorStacks B (wiredDualFaceInteriorDirectionStacks B σ) ∈
      wiredDualFaceSafeStackHistoryEvent B x k n} = _
  rw [variableStackLaw_wiredDualFaceInterior_event_eq B (wiredDualFaceSafeStackHistoryEvent B x k n)
    (measurableSet_wiredDualFaceSafeStackHistoryEvent B x k n)
    (wiredDualFaceSafeStackHistoryEvent_pad_iff B x k hk n)]
  exact directionStackLaw_completedBranchHistory_eq_wilsonRows (wiredDualFaceDirectionHead (B + 1))
    (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
    (wiredDualFaceOriginAndBoundary B) k n
    (BranchHistory.EndsAvoid (wiredDualFaceDirectionHead (B + 1))
      (fun i => wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (x i)))
      (wiredDualFaceOuterBoundary B) n)

/-- Safe face incident-stack histories have probability tending to one. -/
theorem wiredDualFaceSafeIncidentStackEvent_tendsto_one (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Active (B + 1)))
    (kc : (B : ℕ) → Cursor (WiredDualFace (B + 1)))
    (hk : ∀ B v, v ∈ wiredDualFaceOuterBoundary B → kc B v = 0) (n : ℕ) :
    Tendsto (fun B => variableStackLaw (IncidentCopy (wiredDualFaceGraph (B + 1)))
      (wiredDualFaceSafeIncidentStackEvent B x (kc B) n)) atTop (nhds 1) := by
  have he : (fun B => variableStackLaw (IncidentCopy (wiredDualFaceGraph (B + 1)))
      (wiredDualFaceSafeIncidentStackEvent B x (kc B) n)) =
      fun B => wilsonRows (wiredDualFaceSafeRowEvent B x (kc B) n) := by
    funext B
    exact wiredDualFaceSafeIncidentStackEvent_measure B x (kc B) (hk B) n
  rw [he]
  exact wiredDualFaceSafeRowEvent_tendsto_one x ka kb kc n

end
end FiniteAvalanches.Wilson.Lattice
