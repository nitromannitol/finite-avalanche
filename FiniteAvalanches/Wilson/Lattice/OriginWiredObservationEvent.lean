import FiniteAvalanches.Wilson.Lattice.OriginWiredObservedEdges

/-! Finite edge observations of terminal wired cycle-popping forests. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- The lattice edge field induced by a terminal incident-arrow assignment. -/
def incidentArrowEdgeField (B : ℕ) (R : Set (FiniteWired.Vertex B))
    (a : GoodIncidentArrows (WiredTrees.graph B) R) : EdgeField :=
  fun e => decide (∃ i : FiniteWired.InteriorEdge B,
    Sum.inl i ∈ incidentArrowCopies (WiredTrees.graph B) R a ∧ interiorEdge i = e)

/-- A stack observation specified by finitely many terminal edge indicators. -/
def incidentStackEdgeEvent (B : ℕ) (R : Set (FiniteWired.Vertex B))
    (k : Cursor (FiniteWired.Vertex B)) (E : Finset LatticeEdge) (p : LatticeEdge → Bool) :
    Set ((q : FiniteWired.Vertex B × ℕ) → IncidentCopy (WiredTrees.graph B) q.1) :=
  {σ | ∃ a : GoodIncidentArrows (WiredTrees.graph B) R,
    (∀ e ∈ E, incidentArrowEdgeField B R a e = p e) ∧
    σ ∈ terminalOutputEvent R (incidentCopyHead (WiredTrees.graph B)) k
      (fun v i σ => σ (v, i)) a}

/-- A terminal edge observation is measurable in the incident stacks. -/
theorem measurableSet_incidentStackEdgeEvent (B : ℕ) (R : Set (FiniteWired.Vertex B))
    (k : Cursor (FiniteWired.Vertex B)) (E : Finset LatticeEdge) (p : LatticeEdge → Bool) :
    MeasurableSet (incidentStackEdgeEvent B R k E p) := by
  have he : incidentStackEdgeEvent B R k E p =
      ⋃ a : {a : GoodIncidentArrows (WiredTrees.graph B) R //
        ∀ e ∈ E, incidentArrowEdgeField B R a e = p e},
        terminalOutputEvent R (incidentCopyHead (WiredTrees.graph B)) k
          (fun v i σ => σ (v, i)) a.val := by
    ext σ
    simp only [incidentStackEdgeEvent, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨a, ha, hσ⟩
      exact ⟨⟨a, ha⟩, hσ⟩
    · rintro ⟨⟨a, ha⟩, hσ⟩
      exact ⟨a, ha, hσ⟩
  rw [he]
  apply MeasurableSet.iUnion
  intro a
  exact measurableSet_terminalOutputEvent R (incidentCopyHead (WiredTrees.graph B)) k
    (fun v i (σ : (q : FiniteWired.Vertex B × ℕ) → IncidentCopy (WiredTrees.graph B) q.1) =>
      σ (v, i)) (fun v i => measurable_pi_apply (v, i)) a.val

/-- Any terminal continuation determines every finite edge observation. -/
theorem incidentStackEdgeEvent_iff_terminal (B : ℕ) (R : Set (FiniteWired.Vertex B))
    (k t : Cursor (FiniteWired.Vertex B)) (E : Finset LatticeEdge) (p : LatticeEdge → Bool)
    (σ : (q : FiniteWired.Vertex B × ℕ) → IncidentCopy (WiredTrees.graph B) q.1)
    (hrun : Relation.ReflTransGen (pop_step R (incidentCopyHead (WiredTrees.graph B))
      (fun v i => σ (v, i))) k t)
    (ht : terminal R (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i)) t) :
    σ ∈ incidentStackEdgeEvent B R k E p ↔
      ∀ e ∈ E, incidentArrowEdgeField B R ⟨fun v => σ (v, t v), ht⟩ e = p e := by
  constructor
  · rintro ⟨a, ha, l, hl, htop⟩
    have hlt : terminal R (incidentCopyHead (WiredTrees.graph B)) (fun v i => σ (v, i)) l :=
      terminal_of_top_eq R (incidentCopyHead (WiredTrees.graph B)) _ l a.val a.property htop
    have hle : l = t := terminal_cursor_eq R (incidentCopyHead (WiredTrees.graph B))
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
theorem originWiredCouplingEvent_edgeEvent_iff (B : ℕ) (x : ℕ → Site 2)
    (k : Cursor (FiniteWired.Vertex B)) (n : ℕ) (E : Finset LatticeEdge)
    (p : LatticeEdge → Bool) (hE : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z)
    (σ : (q : FiniteWired.Vertex B × ℕ) → IncidentCopy (WiredTrees.graph B) q.1)
    (hσ : σ ∈ originWiredCouplingEvent B x k n) :
    σ ∈ incidentStackEdgeEvent B (wiredOriginRoot B) k E p ↔
      σ ∈ incidentStackEdgeEvent B (wiredOriginAndSink B) k E p := by
  obtain ⟨t, u, ht, hu, htr, hur, he⟩ := originWiredCouplingEvent_edges_agree B x k n E hE σ hσ
  rw [incidentStackEdgeEvent_iff_terminal B _ k t E p σ htr ht,
    incidentStackEdgeEvent_iff_terminal B _ k u E p σ hur hu]
  constructor <;> intro h e heE
  · rw [← h e heE]
    exact Bool.decide_congr (he e heE).symm
  · rw [← h e heE]
    exact Bool.decide_congr (he e heE)

end
end FiniteAvalanches.Wilson.Lattice
