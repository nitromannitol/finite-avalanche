import FiniteAvalanches.Wilson.Lattice.FreeCouplingEvent
import FiniteAvalanches.Wilson.Lattice.WiredObservationGeometry

/-! Coupled terminal free forests agree on queried lattice edges. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance decEqInteriorEdgeFreeObservedEdges (N : ℕ) :
    DecidableEq (FiniteWired.InteriorEdge N) := Classical.decEq _

/-- Projecting an active site back into its own free box recovers the vertex. -/
theorem freeSite_site (B : ℕ) (v : FiniteWired.Active B) :
    freeSite B (FiniteWired.site v) = v := by
  apply FiniteWired.site_injective B
  exact site_freeSite_of_inBox B _ (fun i => (v i).property)

/-- Coupled free terminal forests agree on finite lattice observations whose
endpoints are both queried and inside the inner box. -/
theorem freeCouplingEvent_edges_agree (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Active (B + 1))) (n : ℕ) (E : Finset LatticeEdge)
    (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z)
    (hbox : ∀ e ∈ E, ∀ z ∈ e.val, FiniteWired.inBox B z)
    (σ : (q : FiniteWired.Active (B + 1) × ℕ) → IncidentCopy (freeBoxGraph (B + 1)) q.1)
    (hσ : σ ∈ freeCouplingEvent B x k n) :
    ∃ t u,
      ∃ ht : terminal (freeOriginRoot B) (incidentCopyHead (freeBoxGraph (B + 1)))
        (fun v i => σ (v, i)) t,
      ∃ hu : terminal (freeOriginAndBoundary B) (incidentCopyHead (freeBoxGraph (B + 1)))
        (fun v i => σ (v, i)) u,
      Relation.ReflTransGen (pop_step (freeOriginRoot B)
        (incidentCopyHead (freeBoxGraph (B + 1))) (fun v i => σ (v, i))) k t ∧
      Relation.ReflTransGen (pop_step (freeOriginAndBoundary B)
        (incidentCopyHead (freeBoxGraph (B + 1))) (fun v i => σ (v, i))) k u ∧
      ∀ e ∈ E,
        (∃ i : FiniteWired.InteriorEdge (B + 1),
          i ∈ incidentArrowCopies (freeBoxGraph (B + 1)) (freeOriginRoot B)
            ⟨fun v => σ (v, t v), ht⟩ ∧ interiorEdge i = e) ↔
        (∃ i : FiniteWired.InteriorEdge (B + 1),
          i ∈ incidentArrowCopies (freeBoxGraph (B + 1)) (freeOriginAndBoundary B)
            ⟨fun v => σ (v, u v), hu⟩ ∧ interiorEdge i = e) := by
  obtain ⟨T, t, u, ht, hu, htRun, huRun, hcover, hagree⟩ :=
    freeCouplingEvent_agreement B x k n σ hσ
  refine ⟨t, u, ht, hu, htRun, huRun, ?_⟩
  intro e he
  have hcopy (i : FiniteWired.InteriorEdge (B + 1)) (hi : interiorEdge i = e) :
      i ∈ incidentArrowCopies (freeBoxGraph (B + 1)) (freeOriginRoot B)
          ⟨fun v => σ (v, t v), ht⟩ ↔
        i ∈ incidentArrowCopies (freeBoxGraph (B + 1)) (freeOriginAndBoundary B)
          ⟨fun v => σ (v, u v), hu⟩ := by
    have hlmem : FiniteWired.site i.val.1 ∈ e.val := hi ▸ (interiorEdge_endpoint_mem i).1
    have hrmem : FiniteWired.site i.val.2 ∈ e.val := hi ▸ (interiorEdge_endpoint_mem i).2
    obtain ⟨l, hl, hlx⟩ := hE e he _ hlmem
    obtain ⟨r, hr, hrx⟩ := hE e he _ hrmem
    have hleft : i.val.1 ∈ T := by
      have hh := hcover l hl
      rw [hlx, freeSite_site] at hh
      exact hh
    have hright : i.val.2 ∈ T := by
      have hh := hcover r hr
      rw [hrx, freeSite_site] at hh
      exact hh
    apply hagree i hleft hright
    · change ¬¬FiniteWired.inBox B (FiniteWired.site i.val.1)
      exact not_not.mpr (hbox e he _ hlmem)
    · change ¬¬FiniteWired.inBox B (FiniteWired.site i.val.2)
      exact not_not.mpr (hbox e he _ hrmem)
  constructor
  · rintro ⟨i, hi, heq⟩
    exact ⟨i, (hcopy i heq).mp hi, heq⟩
  · rintro ⟨i, hi, heq⟩
    exact ⟨i, (hcopy i heq).mpr hi, heq⟩

end
end FiniteAvalanches.Wilson.Lattice
