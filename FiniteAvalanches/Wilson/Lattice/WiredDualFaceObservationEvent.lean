import FiniteAvalanches.Wilson.Lattice.WiredDualFaceObservedEdges

/-! Finite edge observations of terminal face-square cycle-popping forests. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

local instance decEqWiredEdgeDualFaceObservationEvent (N : ℕ) :
    DecidableEq (FiniteWired.Edge N) := Classical.decEq _

/-- The lattice edge field induced by a terminal incident-arrow assignment. -/
def wiredDualFaceIncidentArrowEdgeField (B : ℕ) (R : Set (WiredDualFace (B + 1)))
    (a : GoodIncidentArrows (wiredDualFaceGraph (B + 1)) R) : EdgeField :=
  fun e => decide (∃ i : FiniteWired.Edge (B + 1),
    i ∈ incidentArrowCopies (wiredDualFaceGraph (B + 1)) R a ∧ wiredCopyDualEdge i = e)

/-- A stack observation specified by finitely many terminal edge indicators. -/
def wiredDualFaceIncidentStackEdgeEvent (B : ℕ) (R : Set (WiredDualFace (B + 1)))
    (k : Cursor (WiredDualFace (B + 1))) (E : Finset LatticeEdge) (p : LatticeEdge → Bool) :
    Set ((q : WiredDualFace (B + 1) × ℕ) → IncidentCopy (wiredDualFaceGraph (B + 1)) q.1) :=
  {σ | ∃ a : GoodIncidentArrows (wiredDualFaceGraph (B + 1)) R,
    (∀ e ∈ E, wiredDualFaceIncidentArrowEdgeField B R a e = p e) ∧
    σ ∈ terminalOutputEvent R (incidentCopyHead (wiredDualFaceGraph (B + 1))) k
      (fun v i σ => σ (v, i)) a}

/-- A terminal edge observation is measurable in the incident stacks. -/
theorem measurableSet_wiredDualFaceIncidentStackEdgeEvent (B : ℕ) (R : Set (WiredDualFace (B + 1)))
    (k : Cursor (WiredDualFace (B + 1))) (E : Finset LatticeEdge) (p : LatticeEdge → Bool) :
    MeasurableSet (wiredDualFaceIncidentStackEdgeEvent B R k E p) := by
  have he : wiredDualFaceIncidentStackEdgeEvent B R k E p =
      ⋃ a : {a : GoodIncidentArrows (wiredDualFaceGraph (B + 1)) R //
        ∀ e ∈ E, wiredDualFaceIncidentArrowEdgeField B R a e = p e},
        terminalOutputEvent R (incidentCopyHead (wiredDualFaceGraph (B + 1))) k
          (fun v i σ => σ (v, i)) a.val := by
    ext σ
    simp only [wiredDualFaceIncidentStackEdgeEvent, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨a, ha, hσ⟩
      exact ⟨⟨a, ha⟩, hσ⟩
    · rintro ⟨⟨a, ha⟩, hσ⟩
      exact ⟨a, ha, hσ⟩
  rw [he]
  apply MeasurableSet.iUnion
  intro a
  exact measurableSet_terminalOutputEvent R (incidentCopyHead (wiredDualFaceGraph (B + 1))) k
    (fun v i (σ : (q : WiredDualFace (B + 1) × ℕ) → IncidentCopy (wiredDualFaceGraph (B + 1)) q.1) =>
      σ (v, i)) (fun v i => measurable_pi_apply (v, i)) a.val

/-- Any terminal continuation determines every finite edge observation. -/
theorem wiredDualFaceIncidentStackEdgeEvent_iff_terminal (B : ℕ) (R : Set (WiredDualFace (B + 1)))
    (k t : Cursor (WiredDualFace (B + 1))) (E : Finset LatticeEdge) (p : LatticeEdge → Bool)
    (σ : (q : WiredDualFace (B + 1) × ℕ) → IncidentCopy (wiredDualFaceGraph (B + 1)) q.1)
    (hrun : Relation.ReflTransGen (pop_step R (incidentCopyHead (wiredDualFaceGraph (B + 1)))
      (fun v i => σ (v, i))) k t)
    (ht : terminal R (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i)) t) :
    σ ∈ wiredDualFaceIncidentStackEdgeEvent B R k E p ↔
      ∀ e ∈ E, wiredDualFaceIncidentArrowEdgeField B R ⟨fun v => σ (v, t v), ht⟩ e = p e := by
  constructor
  · rintro ⟨a, ha, l, hl, htop⟩
    have hlt : terminal R (incidentCopyHead (wiredDualFaceGraph (B + 1))) (fun v i => σ (v, i)) l :=
      terminal_of_top_eq R (incidentCopyHead (wiredDualFaceGraph (B + 1))) _ l a.val a.property htop
    have hle : l = t := terminal_cursor_eq R (incidentCopyHead (wiredDualFaceGraph (B + 1)))
      (fun v i => σ (v, i)) hl hrun hlt ht
    have haeq : a = ⟨fun v => σ (v, t v), ht⟩ := by
      apply Subtype.ext
      funext v
      have hv : σ (v, l v) = a.val v := htop v
      rw [hle] at hv
      exact hv.symm
    simpa only [haeq] using ha
  · intro h
    refine ⟨⟨fun v => σ (v, t v), ht⟩, h, t, hrun, ?_⟩
    intro v
    rfl

/-- Safe coupled terminal observations give the same finite edge pattern. -/
theorem wiredDualFaceCouplingEvent_edgeEvent_iff (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (WiredDualFace (B + 1))) (n : ℕ) (E : Finset LatticeEdge)
    (p : LatticeEdge → Bool) (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z)
    (hbox : ∀ e ∈ E, ∀ z ∈ e.val, FiniteWired.inBox B z)
    (σ : (q : WiredDualFace (B + 1) × ℕ) → IncidentCopy (wiredDualFaceGraph (B + 1)) q.1)
    (hσ : σ ∈ wiredDualFaceCouplingEvent B x k n) :
    σ ∈ wiredDualFaceIncidentStackEdgeEvent B (({wiredDualFaceOrigin (B + 1)} : Set (WiredDualFace (B + 1)))) k E p ↔
      σ ∈ wiredDualFaceIncidentStackEdgeEvent B (wiredDualFaceOriginAndBoundary B) k E p := by
  obtain ⟨t, u, ht, hu, htr, hur, he⟩ := wiredDualFaceCouplingEvent_edges_agree B x k n E hE hbox σ hσ
  rw [wiredDualFaceIncidentStackEdgeEvent_iff_terminal B _ k t E p σ htr ht,
    wiredDualFaceIncidentStackEdgeEvent_iff_terminal B _ k u E p σ hur hu]
  constructor <;> intro h e heE
  · rw [← h e heE]
    exact Bool.decide_congr (he e heE).symm
  · rw [← h e heE]
    exact Bool.decide_congr (he e heE)

end
end FiniteAvalanches.Wilson.Lattice
