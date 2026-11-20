import FiniteAvalanches.Wilson.Lattice.WiredDualFaceCouplingEvent

/-! Coupled face terminal forests agree on queried lattice edges. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees FiniteAvalanches.Trees.Lattice
open FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance decEqWiredEdgeDualFaceObservedEdges (B : ℕ) :
    DecidableEq (FiniteWired.Edge B) := Classical.decEq _

/-- An inner face label projected into the centered box and included again recovers that face. -/
theorem wiredDualFaceInnerVertex_freeSite (B : ℕ) (v : WiredDualFace (B + 1))
    (hv : FiniteWired.inBox (B + 1) (wiredDualFaceSite v)) :
    wiredDualFaceInnerVertex (B + 1) (freeSite (B + 1) (wiredDualFaceSite v)) = v := by
  apply wiredDualFaceSite_injective (B + 1)
  exact site_freeSite_of_inBox (B + 1) (wiredDualFaceSite v) hv

/-- Coupled face terminal forests agree on queried lattice edges in the inner box. -/
theorem wiredDualFaceCouplingEvent_edges_agree (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1))) (n : ℕ) (E : Finset LatticeEdge)
    (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z)
    (hbox : ∀ e ∈ E, ∀ z ∈ e.val, FiniteWired.inBox B z)
    (σ : (q : WiredDualFace (B + 1) × ℕ) → IncidentCopy (wiredDualFaceGraph (B + 1)) q.1)
    (hσ : σ ∈ wiredDualFaceCouplingEvent B x k n) :
    ∃ t u,
      ∃ ht : terminal {wiredDualFaceOrigin (B + 1)} (incidentCopyHead (wiredDualFaceGraph (B + 1)))
        (fun v i => σ (v, i)) t,
      ∃ hu : terminal (wiredDualFaceOriginAndBoundary B) (incidentCopyHead (wiredDualFaceGraph (B + 1)))
        (fun v i => σ (v, i)) u,
      Relation.ReflTransGen (pop_step {wiredDualFaceOrigin (B + 1)}
        (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i))) k t ∧
      Relation.ReflTransGen (pop_step (wiredDualFaceOriginAndBoundary B)
        (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i))) k u ∧
      ∀ e ∈ E,
        (∃ q : FiniteWired.Edge (B + 1),
          q ∈ incidentArrowCopies (wiredDualFaceGraph (B + 1)) {wiredDualFaceOrigin (B + 1)}
            ⟨fun v => σ (v, t v), ht⟩ ∧ wiredCopyDualEdge q = e) ↔
        (∃ q : FiniteWired.Edge (B + 1),
          q ∈ incidentArrowCopies (wiredDualFaceGraph (B + 1)) (wiredDualFaceOriginAndBoundary B)
            ⟨fun v => σ (v, u v), hu⟩ ∧ wiredCopyDualEdge q = e) := by
  obtain ⟨T, t, u, ht, hu, htRun, huRun, hcover, hagree⟩ :=
    wiredDualFaceCouplingEvent_agreement B x k n σ hσ
  refine ⟨t, u, ht, hu, htRun, huRun, ?_⟩
  intro e he
  have hcopy (q : FiniteWired.Edge (B + 1)) (hq : wiredCopyDualEdge q = e) :
      q ∈ incidentArrowCopies (wiredDualFaceGraph (B + 1)) {wiredDualFaceOrigin (B + 1)}
          ⟨fun v => σ (v, t v), ht⟩ ↔
        q ∈ incidentArrowCopies (wiredDualFaceGraph (B + 1)) (wiredDualFaceOriginAndBoundary B)
          ⟨fun v => σ (v, u v), hu⟩ := by
    have hpair := wiredDualFaceGraph_edge (B + 1) q
    have hlmem : wiredDualFaceSite ((wiredDualFaceGraph (B + 1)).left q) ∈ e.val := by
      rw [← hq, ← hpair]
      exact Sym2.mem_iff.mpr (Or.inl rfl)
    have hrmem : wiredDualFaceSite ((wiredDualFaceGraph (B + 1)).right q) ∈ e.val := by
      rw [← hq, ← hpair]
      exact Sym2.mem_iff.mpr (Or.inr rfl)
    obtain ⟨l, hl, hlx⟩ := hE e he _ hlmem
    obtain ⟨r, hr, hrx⟩ := hE e he _ hrmem
    have hinleft : FiniteWired.inBox (B + 1)
        (wiredDualFaceSite ((wiredDualFaceGraph (B + 1)).left q)) := by
      intro d
      have hh := hbox e he _ hlmem d
      constructor <;> omega
    have hinright : FiniteWired.inBox (B + 1)
        (wiredDualFaceSite ((wiredDualFaceGraph (B + 1)).right q)) := by
      intro d
      have hh := hbox e he _ hrmem d
      constructor <;> omega
    have hleft : (wiredDualFaceGraph (B + 1)).left q ∈ T := by
      have hh := hcover l hl
      rw [hlx, wiredDualFaceInnerVertex_freeSite B _ hinleft] at hh
      exact hh
    have hright : (wiredDualFaceGraph (B + 1)).right q ∈ T := by
      have hh := hcover r hr
      rw [hrx, wiredDualFaceInnerVertex_freeSite B _ hinright] at hh
      exact hh
    apply hagree q hleft hright
    · change ¬¬FiniteWired.inBox B (wiredDualFaceSite ((wiredDualFaceGraph (B + 1)).left q))
      exact not_not.mpr (hbox e he _ hlmem)
    · change ¬¬FiniteWired.inBox B (wiredDualFaceSite ((wiredDualFaceGraph (B + 1)).right q))
      exact not_not.mpr (hbox e he _ hrmem)
  constructor
  · rintro ⟨q, hq, heq⟩
    exact ⟨q, (hcopy q heq).mp hq, heq⟩
  · rintro ⟨q, hq, heq⟩
    exact ⟨q, (hcopy q heq).mpr hq, heq⟩

end
end FiniteAvalanches.Wilson.Lattice
