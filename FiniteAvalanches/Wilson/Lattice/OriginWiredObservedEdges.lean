import FiniteAvalanches.Wilson.Lattice.OriginWiredCouplingEvent
import FiniteAvalanches.Wilson.Lattice.WiredObservationGeometry

/-! Agreement of queried interior copies in finite wired forest couplings. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- On a safe prefix, the two terminal forests agree on each interior copy
whose endpoints are among the queried sites. -/
theorem originSafe_terminalCopies_agree_of_queried (B : ℕ) (x : ℕ → Site 2)
    (k t u : Cursor (FiniteWired.Vertex B)) (n : ℕ)
    (σ : (p : FiniteWired.Vertex B × ℕ) → IncidentCopy (WiredTrees.graph B) p.1)
    (hσ : σ ∈ originSafeIncidentStackEvent B x k n)
    (hrun : Relation.ReflTransGen (pop_step (wiredOriginRoot B)
      (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i))) k t)
    (ht : terminal (wiredOriginRoot B) (incidentCopyHead (WiredTrees.graph B))
      (fun v i => σ (v, i)) t)
    (hsrun : Relation.ReflTransGen (pop_step (wiredOriginAndSink B)
      (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i))) k u)
    (hu : terminal (wiredOriginAndSink B) (incidentCopyHead (WiredTrees.graph B))
      (fun v i => σ (v, i)) u)
    (e : FiniteWired.InteriorEdge B)
    (hl : ∃ i < n, x i = FiniteWired.site e.val.1)
    (hr : ∃ i < n, x i = FiniteWired.site e.val.2) :
    Sum.inl e ∈ incidentArrowCopies (WiredTrees.graph B) (wiredOriginRoot B)
        ⟨fun v => σ (v, t v), ht⟩ ↔
      Sum.inl e ∈ incidentArrowCopies (WiredTrees.graph B) (wiredOriginAndSink B)
        ⟨fun v => σ (v, u v), hu⟩ := by
  obtain ⟨T, hcover, hagree⟩ := originSafe_terminalCopies_agree B x k t u n σ
    hσ hrun ht hsrun hu
  obtain ⟨i, hi, hix⟩ := hl
  obtain ⟨j, hj, hjx⟩ := hr
  have hsite (v : FiniteWired.Active B) : wiredSite B (FiniteWired.site v) = some v := by
    simpa only [wiredVertexSite] using wiredSite_wiredVertexSite B (some v)
  have hleft : some e.val.1 ∈ T := by
    have h := hcover i hi
    rw [hix] at h
    simpa only [hsite] using h
  have hright : some e.val.2 ∈ T := by
    have h := hcover j hj
    rw [hjx] at h
    simpa only [hsite] using h
  apply hagree (Sum.inl e)
  · exact hleft
  · exact hright
  · simp [WiredTrees.graph, FiniteWired.endpoints, Multigraph.ofEndpoints]
  · simp [WiredTrees.graph, FiniteWired.endpoints, Multigraph.ofEndpoints]

/-- On a safe prefix, the two terminal forests give the same indicator for
each lattice edge whose endpoints have been queried. -/
theorem originSafe_terminalEdge_agree_of_queried (B : ℕ) (x : ℕ → Site 2)
    (k t u : Cursor (FiniteWired.Vertex B)) (n : ℕ)
    (σ : (p : FiniteWired.Vertex B × ℕ) → IncidentCopy (WiredTrees.graph B) p.1)
    (hσ : σ ∈ originSafeIncidentStackEvent B x k n)
    (hrun : Relation.ReflTransGen (pop_step (wiredOriginRoot B)
      (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i))) k t)
    (ht : terminal (wiredOriginRoot B) (incidentCopyHead (WiredTrees.graph B))
      (fun v i => σ (v, i)) t)
    (hsrun : Relation.ReflTransGen (pop_step (wiredOriginAndSink B)
      (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i))) k u)
    (hu : terminal (wiredOriginAndSink B) (incidentCopyHead (WiredTrees.graph B))
      (fun v i => σ (v, i)) u)
    (e : LatticeEdge) (hq : ∀ z ∈ e.val, ∃ i < n, x i = z) :
    (∃ i : FiniteWired.InteriorEdge B,
      Sum.inl i ∈ incidentArrowCopies (WiredTrees.graph B) (wiredOriginRoot B)
        ⟨fun v => σ (v, t v), ht⟩ ∧ interiorEdge i = e) ↔
    (∃ i : FiniteWired.InteriorEdge B,
      Sum.inl i ∈ incidentArrowCopies (WiredTrees.graph B) (wiredOriginAndSink B)
        ⟨fun v => σ (v, u v), hu⟩ ∧ interiorEdge i = e) := by
  have hcopy (i : FiniteWired.InteriorEdge B) (hi : interiorEdge i = e) :=
    originSafe_terminalCopies_agree_of_queried B x k t u n σ hσ hrun ht hsrun hu i
      (hq _ (hi ▸ (interiorEdge_endpoint_mem i).1))
      (hq _ (hi ▸ (interiorEdge_endpoint_mem i).2))
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨i, (hcopy i he).mp hi, he⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨i, (hcopy i he).mpr hi, he⟩

/-- On the coupling event, terminal continuations agree simultaneously on
every edge in a finite observation whose endpoints have been queried. -/
theorem originWiredCouplingEvent_edges_agree (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) (E : Finset LatticeEdge)
    (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z)
    (σ : (p : FiniteWired.Vertex B × ℕ) → IncidentCopy (WiredTrees.graph B) p.1)
    (hσ : σ ∈ originWiredCouplingEvent B x k n) :
    ∃ t u,
      ∃ ht : terminal (wiredOriginRoot B) (incidentCopyHead (WiredTrees.graph B))
        (fun v i => σ (v, i)) t,
      ∃ hu : terminal (wiredOriginAndSink B) (incidentCopyHead (WiredTrees.graph B))
        (fun v i => σ (v, i)) u,
      Relation.ReflTransGen (pop_step (wiredOriginRoot B)
        (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i))) k t ∧
      Relation.ReflTransGen (pop_step (wiredOriginAndSink B)
        (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i))) k u ∧
      ∀ e ∈ E,
        (∃ i : FiniteWired.InteriorEdge B,
          Sum.inl i ∈ incidentArrowCopies (WiredTrees.graph B) (wiredOriginRoot B)
            ⟨fun v => σ (v, t v), ht⟩ ∧ interiorEdge i = e) ↔
        (∃ i : FiniteWired.InteriorEdge B,
          Sum.inl i ∈ incidentArrowCopies (WiredTrees.graph B) (wiredOriginAndSink B)
            ⟨fun v => σ (v, u v), hu⟩ ∧ interiorEdge i = e) := by
  obtain ⟨⟨hsafe, t, htRun, ht⟩, u, huRun, hu⟩ := hσ
  refine ⟨t, u, ht, hu, htRun, huRun, ?_⟩
  intro e he
  exact originSafe_terminalEdge_agree_of_queried B x k t u n σ hsafe htRun ht huRun hu e
    (hE e he)

end
end FiniteAvalanches.Wilson.Lattice
