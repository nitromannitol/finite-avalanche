import FiniteAvalanches.Wilson.Lattice.HistoryRootCursor
import FiniteAvalanches.Wilson.Lattice.WiredStackExploreCoupling
import FiniteAvalanches.Wilson.CyclePopping.AvoidAlphabetCoupling

/-! High-probability safe origin explorations for wired incident stacks. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Safe stack-history events are measurable. -/
theorem measurableSet_originSafeStackHistoryEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) :
    MeasurableSet (originSafeStackHistoryEvent B x k n) := by
  have he : originSafeStackHistoryEvent B x k n = ⋃ N : ℕ,
      {σ | BranchHistory.HitsBefore N n
          (boundedBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) (wiredOriginAndSink B)
            k N σ n) ∧
        BranchHistory.EndsAvoid (wiredHead B) (fun i => wiredSite B (x i)) {none} n
          (boundedBranchHistory (wiredHead B) (fun i => wiredSite B (x i)) (wiredOriginAndSink B)
            k N σ n)} := by
    ext σ
    simp only [originSafeStackHistoryEvent, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [he]
  apply MeasurableSet.iUnion
  intro N
  apply measurableSet_of_countable_fibers
    (fun σ => boundedBranchHistory (wiredHead B) (fun i => wiredSite B (x i))
      (wiredOriginAndSink B) k N σ n)
    (measurableSet_boundedBranchHistory_eq (wiredHead B) (fun i => wiredSite B (x i))
      (wiredOriginAndSink B) k N n)
    (fun a => BranchHistory.HitsBefore N n a ∧
      BranchHistory.EndsAvoid (wiredHead B) (fun i => wiredSite B (x i)) {none} n a)

/-- With initial sink cursor zero, safe histories depend only on active stacks. -/
theorem originSafeStackHistoryEvent_of_agree_active (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (hk : k none = 0) (n : ℕ)
    (σ τ : FiniteWired.Vertex B × ℕ → FiniteWired.Direction)
    (hactive : ∀ v i, τ (some v, i) = σ (some v, i))
    (hσ : σ ∈ originSafeStackHistoryEvent B x k n) :
    τ ∈ originSafeStackHistoryEvent B x k n := by
  obtain ⟨N, hhit, havoid⟩ := hσ
  let h := boundedBranchHistory (wiredHead B) (fun i => wiredSite B (x i))
    (wiredOriginAndSink B) k N σ n
  have hh := (boundedBranchHistory_hitsBefore_iff (wiredHead B) (fun i => wiredSite B (x i))
    (wiredOriginAndSink B) k N n σ).mp hhit
  have hnone : branchHistoryCursor (wiredHead B) (fun i => wiredSite B (x i)) k n h none = 0 := by
    rw [branchHistoryCursor_eq_at_initial_root (wiredHead B) (fun i => wiredSite B (x i))
      (wiredOriginAndSink B) k N n σ hh none (by simp [wiredOriginAndSink]), hk]
  have hagree : ∀ v i, i < branchHistoryCursor (wiredHead B) (fun i => wiredSite B (x i)) k n h v →
      τ (v, i) = σ (v, i) := by
    intro v i hi
    cases v with
    | none => rw [hnone] at hi; omega
    | some v => exact hactive v i
  have he := boundedBranchHistory_stable (wiredHead B) (fun i => wiredSite B (x i))
    (wiredOriginAndSink B) k N n σ τ hagree
  refine ⟨N, ?_, ?_⟩ <;> rw [he]
  · exact hhit
  · exact havoid

/-- Padding the active stacks does not change the safe-history event. -/
theorem originSafeStackHistoryEvent_pad_iff (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (hk : k none = 0) (n : ℕ)
    (σ : FiniteWired.Vertex B × ℕ → FiniteWired.Direction) :
    padActiveDirectionStacks B (activeDirectionProjection B σ) ∈ originSafeStackHistoryEvent B x k n ↔
      σ ∈ originSafeStackHistoryEvent B x k n := by
  constructor
  · intro h
    apply originSafeStackHistoryEvent_of_agree_active B x k hk n
      (padActiveDirectionStacks B (activeDirectionProjection B σ)) σ ?_ h
    intro v i
    rfl
  · intro h
    apply originSafeStackHistoryEvent_of_agree_active B x k hk n σ
      (padActiveDirectionStacks B (activeDirectionProjection B σ)) ?_ h
    intro v i
    rfl

/-- Incident stacks whose active directions give a successful safe history. -/
def originSafeIncidentStackEvent (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) :
    Set ((p : FiniteWired.Vertex B × ℕ) → IncidentCopy (WiredTrees.graph B) p.1) :=
  {σ | padActiveDirectionStacks B (wiredActiveDirectionStacks B σ) ∈ originSafeStackHistoryEvent B x k n}

/-- The safe-history event has exactly the independent-row probability under
incident-copy stacks. -/
theorem originSafeIncidentStackEvent_measure (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (hk : k none = 0) (n : ℕ) :
    variableStackLaw (IncidentCopy (WiredTrees.graph B)) (originSafeIncidentStackEvent B x k n) =
      wilsonRows (originSafeRowEvent B x k n) := by
  change variableStackLaw (IncidentCopy (WiredTrees.graph B))
    {σ | padActiveDirectionStacks B (wiredActiveDirectionStacks B σ) ∈ originSafeStackHistoryEvent B x k n} = _
  rw [variableStackLaw_active_event_eq B (originSafeStackHistoryEvent B x k n)
    (measurableSet_originSafeStackHistoryEvent B x k n)
    (originSafeStackHistoryEvent_pad_iff B x k hk n)]
  exact originSafeStackHistoryEvent_measure B x k n

/-- A safe incident-stack history gives an actual exploration whose branch
endpoints avoid the wired sink. -/
theorem originSafeIncidentStackEvent_avoids_sink (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ)
    (σ : (p : FiniteWired.Vertex B × ℕ) → IncidentCopy (WiredTrees.graph B) p.1)
    (hσ : σ ∈ originSafeIncidentStackEvent B x k n) :
    stackExploreAvoidsRoots (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i))
      {none} (wiredOriginAndSink B) k ((List.range n).map fun i => wiredSite B (x i)) := by
  let τ := padActiveDirectionStacks B (wiredActiveDirectionStacks B σ)
  obtain ⟨N, hhit, havoid⟩ := hσ
  have hh := (boundedBranchHistory_hitsBefore_iff (wiredHead B) (fun i => wiredSite B (x i))
    (wiredOriginAndSink B) k N n τ).mp hhit
  have hs := stackExploreAvoidsRoots_of_boundedBranchHistory (wiredHead B)
    (fun i => wiredSite B (x i)) (wiredOriginAndSink B) {none} k N n τ hh havoid
  apply stackExploreAvoidsRoots_of_matching_successors (wiredHead B)
    (incidentCopyHead (WiredTrees.graph B)) (fun v i => τ (v, i)) (fun v i => σ (v, i))
    (wiredOriginAndSink B) {none} k _ ?_ hs
  intro v hv i
  cases v with
  | none => exact (hv (by simp [wiredOriginAndSink])).elim
  | some x => exact (incidentCopyHead_eq_wiredHead x (σ (some x, i))).symm

/-- Safe incident-stack exploration probabilities tend to one. -/
theorem originSafeIncidentStackEvent_tendsto_one (x : ℕ → Site 2)
    (ka : Cursor (Site 2)) (kb : (B : ℕ) → Cursor (FiniteWired.Vertex B))
    (hk : ∀ B, kb B none = 0) (n : ℕ) :
    Tendsto (fun B => variableStackLaw (IncidentCopy (WiredTrees.graph B))
      (originSafeIncidentStackEvent B x (kb B) n)) atTop (nhds 1) := by
  have he : (fun B => variableStackLaw (IncidentCopy (WiredTrees.graph B))
      (originSafeIncidentStackEvent B x (kb B) n)) =
      fun B => wilsonRows (originSafeRowEvent B x (kb B) n) := by
    funext B
    exact originSafeIncidentStackEvent_measure B x (kb B) (hk B) n
  rw [he]
  exact originSafeRowEvent_tendsto_one x ka kb n

end
end FiniteAvalanches.Wilson.Lattice
