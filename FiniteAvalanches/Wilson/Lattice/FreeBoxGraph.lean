import FiniteAvalanches.Wilson.Lattice.WiredSingleRootCyclePopping
import FiniteAvalanches.Needle.ConnectedSet

/-! The free square-box copied graph and its lattice adjacency. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical ENNReal

noncomputable section

local instance (N : ℕ) : DecidableEq (FiniteWired.InteriorEdge N) := Classical.decEq _

/-- The free box keeps precisely the interior original edge copies. -/
def freeBoxGraph (N : ℕ) : Multigraph (FiniteWired.Active N) (FiniteWired.InteriorEdge N) :=
  Multigraph.ofEndpoints (fun e => e.val) (by
    intro e h
    have h' : (FiniteWired.endpoints (.inl e)).1 = (FiniteWired.endpoints (.inl e)).2 := by
      simpa [FiniteWired.endpoints] using congrArg some h
    exact FiniteWired.endpoints_ne (.inl e) h')

/-- Free-box adjacency is the induced square-lattice adjacency. -/
theorem freeBoxGraph_adjacent_iff (N : ℕ) (x y : FiniteWired.Active N) :
    (freeBoxGraph N).adjacent Finset.univ x y ↔
      (lattice 2).Adj (FiniteWired.site x) (FiniteWired.site y) := by
  constructor
  · rintro ⟨e, _, ⟨hl, hr⟩ | ⟨hr, hl⟩⟩
    · obtain ⟨i, hi⟩ := e.property
      change e.val.1 = x at hl
      change e.val.2 = y at hr
      exact ⟨i, Or.inl (by simpa only [hl, hr] using hi)⟩
    · obtain ⟨i, hi⟩ := e.property
      change e.val.2 = x at hr
      change e.val.1 = y at hl
      exact ⟨i, Or.inr (by simpa only [hl, hr] using hi)⟩
  · rintro ⟨i, hi | hi⟩
    · exact ⟨⟨(x, y), i, hi⟩, Finset.mem_univ _, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨⟨(y, x), i, hi⟩, Finset.mem_univ _, Or.inr ⟨rfl, rfl⟩⟩

/-- The lattice sites represented by the active vertices of a box. -/
def freeBoxSites (N : ℕ) : Finset (Site 2) :=
  Finset.univ.image (FiniteWired.site : FiniteWired.Active N → Site 2)

/-- Membership in the finite set of sites is exactly box membership. -/
theorem mem_freeBoxSites (N : ℕ) (z : Site 2) :
    z ∈ freeBoxSites N ↔ FiniteWired.inBox N z := by
  constructor
  · intro hz
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    exact fun i => (x i).property
  · intro hz
    exact Finset.mem_image.mpr ⟨FiniteWired.activeOfSite N z hz, Finset.mem_univ _, rfl⟩

/-- A finite lattice path inside the box lifts to the free copied graph. -/
theorem freeBoxGraph_reaches_of_lattice_steps (N : ℕ) (x y : FiniteWired.Active N)
    (h : Relation.ReflTransGen (FiniteAvalanches.Needle.stepIn (freeBoxSites N))
      (FiniteWired.site x) (FiniteWired.site y)) :
    (freeBoxGraph N).reaches Finset.univ x y := by
  have hgen : ∀ a b : Site 2,
      Relation.ReflTransGen (FiniteAvalanches.Needle.stepIn (freeBoxSites N)) a b →
      ∀ (ha : FiniteWired.inBox N a) (hb : FiniteWired.inBox N b),
        (freeBoxGraph N).reaches Finset.univ
          (FiniteWired.activeOfSite N a ha) (FiniteWired.activeOfSite N b hb) := by
    intro a b hab
    induction hab with
    | refl =>
      intro ha hb
      have he : FiniteWired.activeOfSite N a ha = FiniteWired.activeOfSite N a hb := by
        apply FiniteWired.site_injective N
        rfl
      rw [he]
      exact .refl
    | @tail b c hab hbc ih =>
      intro ha hc
      have hb : FiniteWired.inBox N b := (mem_freeBoxSites N b).mp hbc.1
      have hs : (freeBoxGraph N).adjacent Finset.univ
          (FiniteWired.activeOfSite N b hb) (FiniteWired.activeOfSite N c hc) := by
        apply (freeBoxGraph_adjacent_iff N _ _).mpr
        exact hbc.2.2
      exact (ih ha hb).trans (Relation.ReflTransGen.single hs)
  have hx : FiniteWired.inBox N (FiniteWired.site x) := fun i => (x i).property
  have hy : FiniteWired.inBox N (FiniteWired.site y) := fun i => (y i).property
  have hh := hgen _ _ h hx hy
  have heq (z : FiniteWired.Active N) (hz : FiniteWired.inBox N (FiniteWired.site z)) :
      FiniteWired.activeOfSite N (FiniteWired.site z) hz = z :=
    FiniteWired.site_injective N rfl
  simpa only [heq] using hh

/-- Every two active vertices in the free box are connected by its original copies. -/
theorem freeBoxGraph_connected (N : ℕ) (x y : FiniteWired.Active N) :
    (freeBoxGraph N).reaches Finset.univ x y := by
  have hB : ∀ z : Site 2, FiniteAvalanches.Needle.radius z ≤ (N : ℤ) →
      z ∈ freeBoxSites N := by
    intro z hz
    apply (mem_freeBoxSites N z).mpr
    exact (FiniteWired.inBox_iff N z).mpr ((FiniteAvalanches.Needle.mem_box_iff z N).mpr hz)
  have hx : FiniteAvalanches.Needle.radius (FiniteWired.site x) ≤ (N : ℤ) := by
    apply (FiniteAvalanches.Needle.mem_box_iff _ N).mp
    exact (FiniteWired.inBox_iff N _).mp (fun i => (x i).property)
  have hy : FiniteAvalanches.Needle.radius (FiniteWired.site y) ≤ (N : ℤ) := by
    apply (FiniteAvalanches.Needle.mem_box_iff _ N).mp
    exact (FiniteWired.inBox_iff N _).mp (fun i => (y i).property)
  apply freeBoxGraph_reaches_of_lattice_steps
  exact (FiniteAvalanches.Needle.box_reaches_zero N (freeBoxSites N) hB _ hx).trans
    (FiniteAvalanches.Needle.reflTransGen_reverse
      (fun {_ _} h => ⟨h.2.1, h.1, h.2.2.symm⟩)
      (FiniteAvalanches.Needle.box_reaches_zero N (freeBoxSites N) hB _ hy))

/-- Every vertex in a positive-radius free box has an incident interior copy. -/
instance freeBoxIncidentCopyNonempty (N : ℕ) (x : FiniteWired.Active (N + 1)) :
    Nonempty (IncidentCopy (freeBoxGraph (N + 1)) x) := by
  let a : FiniteWired.Active (N + 1) := wiredOrigin (N + 1)
  let b : FiniteWired.Active (N + 1) := fun i =>
    if h : i = 0 then ⟨1, by constructor <;> omega⟩ else ⟨0, by constructor <;> omega⟩
  have hab : a ≠ b := by
    intro h
    have h0 := congrArg (fun z : FiniteWired.Active (N + 1) => (z 0).val) h
    simp [a, b, wiredOrigin] at h0
  by_cases hx : x = a
  · subst x
    exact incidentCopy_nonempty_of_reaches_ne _ Finset.univ hab (freeBoxGraph_connected _ a b)
  · exact incidentCopy_nonempty_of_reaches_ne _ Finset.univ hx (freeBoxGraph_connected _ x a)

/-- Cycle popping with an arbitrary root samples the free-box spanning trees uniformly. -/
theorem variableStackLaw_freeBoxSpanningTreeEvent_eq (N : ℕ)
    (r : FiniteWired.Active (N + 1)) (k : Cursor (FiniteWired.Active (N + 1)))
    (S : Set (freeBoxGraph (N + 1)).SpanningTree) :
    variableStackLaw (IncidentCopy (freeBoxGraph (N + 1)))
      {σ | ∃ a : GoodIncidentArrows (freeBoxGraph (N + 1)) {r},
        S (singletonRootedForestEquiv (freeBoxGraph (N + 1)) r
          (incidentArrowForest (freeBoxGraph (N + 1)) {r} a)) ∧
        σ ∈ terminalOutputEvent {r} (incidentCopyHead (freeBoxGraph (N + 1))) k
          (fun v i σ => σ (v, i)) a} =
      (Nat.card S : ℝ≥0∞) / (Fintype.card (freeBoxGraph (N + 1)).SpanningTree : ℝ≥0∞) :=
  variableStackLaw_spanningTreeEvent_eq _ _ _ _

end
end FiniteAvalanches.Wilson.Lattice
