import FiniteAvalanches.Trees.Lattice.CommonRawPast
import FiniteAvalanches.Trees.Lattice.InfinitePastPattern
import FiniteAvalanches.Trees.Lattice.InfiniteLawProperties

/-! Incoming cd552a5 main.tex177–179: the common raw finite union, its exact
finite coordinate observation, and the genuine finite/infinite past probability limit. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Trees.Lattice.CurrentPastCylinder
open LatticeProb FiniteAvalanches.Sandpile MeasureTheory Filter TreeMeasurability11
open CurrentOriginalField CurrentCommonRawPast
open scoped Classical ENNReal
noncomputable section

/-- Literal original F/H/e union, with both-endpoint support and every absent bit. -/
def rawPastEvent (x : Site 2) (W : Finset (Site 2)) : Set EdgeField :=
  {ω | ∃ F : Finset (Site 2), F ⊆ W ∧ x ∈ F ∧ ∃ H : Finset LatticeEdge,
    ((toGraph (fun f : LatticeEdge => decide (f ∈ H))).induce (F : Set (Site 2))).IsTree ∧
    (∀ f ∈ H, ∃ u ∈ F, ∃ v ∈ F, f.val = s(u, v)) ∧
    ∃ e : LatticeEdge, ∃ y : Site 2, e.val = s(x, y) ∧ y ∉ F ∧
      ∀ f ∈ incidentCoordinates F, ω f = decide (f ∈ insert e H)}

/-- Only a genuine finite active vertex can witness the actual sink-rooted past. -/
def finitePastEvent (x : Site 2) (W : Finset (Site 2)) (N : ℕ) :
    Set (WiredTrees.graph N).SpanningTree :=
  {t | ∃ a : FiniteWired.Active N, FiniteWired.site a = x ∧
    (WiredTrees.graph N).past t none (some a) (by simp) ⊆ activeLift N (W : Set (Site 2))}

/-- The infinite event requires actual tree and one-end proofs, never a fake past. -/
def infinitePastEvent (x : Site 2) (W : Finset (Site 2)) : Set EdgeField :=
  {ω | ∃ hT : IsTree ω, ∃ hE : OneEnded ω, vertexPast ω hT hE x ⊆ (W : Set (Site 2))}

theorem incident_coordinates_mono (F W : Finset (Site 2)) (hFW : F ⊆ W) :
    incidentCoordinates F ⊆ incidentCoordinates W := by
  intro f hf
  obtain ⟨u, hu, hf⟩ := Finset.mem_biUnion.mp hf
  exact Finset.mem_biUnion.mpr ⟨u, hFW hu, hf⟩

/-- Both support endpoints force every inside edge into the SAME finite family. -/
theorem supported_edges_incident_window (F W : Finset (Site 2)) (hFW : F ⊆ W)
    (H : Finset LatticeEdge) (hs : ∀ f ∈ H, ∃ u ∈ F, ∃ v ∈ F, f.val = s(u, v)) :
    H ⊆ incidentCoordinates W := by
  intro f hf
  obtain ⟨u, hu, v, _hv, hp⟩ := hs f hf
  exact raw_edge_incident W f u v (hFW hu) hp

/-- A genuine finite union over original F, H and outgoing e; y remains the
outside endpoint of that SAME e. No disjointness of candidates is asserted. -/
theorem rawPastEvent_eq_finite_union (x : Site 2) (W : Finset (Site 2)) :
    rawPastEvent x W = ⋃ F ∈ W.powerset,
      ⋃ H ∈ (incidentCoordinates W).powerset, ⋃ e ∈ incidentCoordinates W,
      {ω : EdgeField | x ∈ F ∧
        ((toGraph (fun f : LatticeEdge => decide (f ∈ H))).induce (F : Set (Site 2))).IsTree ∧
        (∀ f ∈ H, ∃ u ∈ F, ∃ v ∈ F, f.val = s(u, v)) ∧
        ∃ y : Site 2, e.val = s(x, y) ∧ y ∉ F ∧
          ∀ f ∈ incidentCoordinates F, ω f = decide (f ∈ insert e H)} := by
  ext ω
  simp only [rawPastEvent, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨F, hFW, hx, H, ht, hs, e, y, hp, hy, hb⟩
    exact ⟨F, Finset.mem_powerset.mpr hFW, H,
      Finset.mem_powerset.mpr (supported_edges_incident_window F W hFW H hs),
      e, raw_edge_incident W e x y (hFW hx) hp, hx, ht, hs, y, hp, hy, hb⟩
  · rintro ⟨F, hF, H, _hH, e, _he, hx, ht, hs, y, hp, hy, hb⟩
    exact ⟨F, Finset.mem_powerset.mp hF, hx, H, ht, hs, e, y, hp, hy, hb⟩

/-- Equality of every original window coordinate preserves the SAME full pattern. -/
theorem rawPastEvent_congr (x : Site 2) (W : Finset (Site 2)) (ω η : EdgeField)
    (hobs : ∀ f ∈ incidentCoordinates W, ω f = η f) :
    ω ∈ rawPastEvent x W ↔ η ∈ rawPastEvent x W := by
  have transfer (ω η : EdgeField) (hobs : ∀ f ∈ incidentCoordinates W, ω f = η f)
      (h : ω ∈ rawPastEvent x W) : η ∈ rawPastEvent x W := by
    obtain ⟨F, hFW, hx, H, ht, hs, e, y, hp, hy, hb⟩ := h
    refine ⟨F, hFW, hx, H, ht, hs, e, y, hp, hy, ?_⟩
    intro f hf
    rw [← hobs f (incident_coordinates_mono F W hFW hf)]
    exact hb f hf
  exact ⟨transfer ω η hobs, transfer η ω (fun f hf => (hobs f hf).symm)⟩

/-- Full Boolean observations realized by the literal candidate union. -/
def admissibleAssignments (x : Site 2) (W : Finset (Site 2)) :
    Finset ((incidentCoordinates W) → Bool) :=
  Finset.univ.filter fun p => ∃ ω ∈ rawPastEvent x W, (incidentCoordinates W).restrict ω = p

/-- Each partial F pattern is a union of complete B patterns, preserving all other bits. -/
theorem rawPastEvent_eq_full_cylinders (x : Site 2) (W : Finset (Site 2)) :
    rawPastEvent x W = ⋃ p ∈ admissibleAssignments x W, cylinder (incidentCoordinates W) p := by
  ext ω
  constructor
  · intro hω
    exact Set.mem_iUnion.mpr ⟨(incidentCoordinates W).restrict ω,
      Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ω, hω, rfl⟩, rfl⟩⟩
  · intro hω
    obtain ⟨p, hinner⟩ := Set.mem_iUnion.mp hω
    obtain ⟨hp, hωp⟩ := Set.mem_iUnion.mp hinner
    obtain ⟨η, hη, hηp⟩ := (Finset.mem_filter.mp hp).2
    apply (rawPastEvent_congr x W η ω ?_).mp hη
    intro f hf
    exact congrFun (hηp.trans hωp.symm) ⟨f, hf⟩

/-- Complete B cylinders, unlike raw tree candidates, are pairwise disjoint. -/
theorem full_cylinders_disjoint (B : Finset LatticeEdge) (p q : B → Bool) (hne : p ≠ q) :
    Disjoint (cylinder B p) (cylinder B q) := by
  apply Set.disjoint_left.mpr
  intro ω hp hq
  exact hne (hp.symm.trans hq)

theorem isClopen_rawPastEvent (x : Site 2) (W : Finset (Site 2)) :
    IsClopen (rawPastEvent x W) := by
  rw [rawPastEvent_eq_full_cylinders]
  exact isClopen_biUnion_finset (fun p _ => isClopen_cylinder (incidentCoordinates W) p)

theorem measurable_rawPastEvent (x : Site 2) (W : Finset (Site 2)) :
    MeasurableSet (rawPastEvent x W) := (isClopen_rawPastEvent x W).isClosed.measurableSet

/-- Genuine finite past equals the common raw event, including unbuffered exits. -/
theorem finitePastEvent_iff_original_raw (N : ℕ) (x : Site 2) (hx : FiniteWired.inBox N x)
    (W : Finset (Site 2)) (hW : ∀ y ∈ W, FiniteWired.inBox N y)
    (t : (WiredTrees.graph N).SpanningTree) :
    t ∈ finitePastEvent x W N ↔ originalWiredField t ∈ rawPastEvent x W := by
  have hd := past_subset_iff_exists_common_raw_tree N t x hx W hW
  constructor
  · rintro ⟨a, ha, hp⟩
    have he : a = FiniteWired.activeOfSite N x hx := FiniteWired.site_injective N ha
    subst a
    exact hd.mp hp
  · intro h
    exact ⟨FiniteWired.activeOfSite N x hx, rfl, hd.mpr h⟩

/-- Exact infinity dictionary on its actual tree/end carrier. -/
theorem infinitePastEvent_iff_raw (x : Site 2) (W : Finset (Site 2)) (ω : EdgeField)
    (hT : IsTree ω) (hE : OneEnded ω) :
    ω ∈ infinitePastEvent x W ↔ ω ∈ rawPastEvent x W := by
  constructor
  · rintro ⟨hT', hE', hp⟩
    exact (CurrentInfinitePastPattern.past_subset_iff_exists_raw_tree ⟨ω, hT', hE'⟩ x W).mp hp
  · intro hp
    exact ⟨hT, hE, (CurrentInfinitePastPattern.past_subset_iff_exists_raw_tree ⟨ω, hT, hE⟩ x W).mpr hp⟩

theorem infinitePastEvent_ae_raw (x : Site 2) (W : Finset (Site 2)) :
    ∀ᵐ ω ∂(squareLatticeUST : Measure EdgeField),
      ω ∈ infinitePastEvent x W ↔ ω ∈ rawPastEvent x W := by
  filter_upwards [squareLatticeUST_ae_tree_oneEnded] with ω hω
  exact infinitePastEvent_iff_raw x W ω hω.1 hω.2

/-- Raw finite-coordinate union probabilities converge by weak convergence and empty frontier. -/
theorem rawPastEvent_probability_tendsto (x : Site 2) (W : Finset (Site 2)) :
    Tendsto (fun N : ℕ => (finiteProbability N : Measure EdgeField) (rawPastEvent x W))
      atTop (nhds ((squareLatticeUST : Measure EdgeField) (rawPastEvent x W))) := by
  exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    squareLatticeUST_tendsto (E := rawPastEvent x W)
    (by rw [(isClopen_rawPastEvent x W).frontier_eq]; exact measure_empty)

/-- One source threshold supplies real vertices and every original coordinate agreement. -/
theorem eventually_finitePastEvent_law_eq (x : Site 2) (W : Finset (Site 2)) :
    ∀ᶠ N : ℕ in atTop,
      WiredTrees.law N (finitePastEvent x W N) = (finiteProbability N : Measure EdgeField) (rawPastEvent x W) := by
  filter_upwards [eventually_ge_atTop (max (siteRadius 0 x) (W.sup (siteRadius 0))),
    eventually_finite_field_agreement (incidentCoordinates W)] with N hN hagree
  have hx : FiniteWired.inBox N x := (mem_box_sites N x).mp
    ((site_radius_zero_le_iff x N).mp ((le_max_left _ _).trans hN))
  have hW : ∀ y ∈ W, FiniteWired.inBox N y := by
    intro y hy
    exact (mem_box_sites N y).mp ((site_radius_zero_le_iff y N).mp
      ((Finset.le_sup (f := siteRadius 0) hy).trans ((le_max_right _ _).trans hN)))
  change _ = finiteLaw N (rawPastEvent x W)
  rw [finiteLaw_apply N _ (measurable_rawPastEvent x W)]
  congr 1
  ext t
  exact (finitePastEvent_iff_original_raw N x hx W hW t).trans
    (rawPastEvent_congr x W (originalWiredField t) (wiredField t) (hagree t))

/-- Incoming pre:past-limit by its current common finite-union and weak-convergence route. -/
theorem past_probability_tendsto (x : Site 2) (W : Finset (Site 2)) :
    Tendsto (fun N : ℕ => WiredTrees.law N (finitePastEvent x W N)) atTop
      (nhds ((squareLatticeUST : Measure EdgeField) (infinitePastEvent x W))) := by
  have he : (squareLatticeUST : Measure EdgeField) (infinitePastEvent x W) =
      (squareLatticeUST : Measure EdgeField) (rawPastEvent x W) := by
    apply measure_congr
    filter_upwards [infinitePastEvent_ae_raw x W] with ω hω
    exact propext hω
  rw [he]
  exact (rawPastEvent_probability_tendsto x W).congr'
    (Filter.EventuallyEq.symm (eventually_finitePastEvent_law_eq x W))

end
end FiniteAvalanches.Trees.Lattice.CurrentPastCylinder

set_option pp.fullNames true
#print FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.rawPastEvent
#print axioms FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.rawPastEvent
#print FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.finitePastEvent
#print axioms FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.finitePastEvent
#print FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.infinitePastEvent
#print axioms FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.infinitePastEvent
#print FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.incident_coordinates_mono
#print axioms FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.incident_coordinates_mono
#print FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.supported_edges_incident_window
#print axioms FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.supported_edges_incident_window
#print FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.rawPastEvent_eq_finite_union
#print axioms FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.rawPastEvent_eq_finite_union
#print FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.rawPastEvent_congr
#print axioms FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.rawPastEvent_congr
#print FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.admissibleAssignments
#print axioms FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.admissibleAssignments
#print FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.rawPastEvent_eq_full_cylinders
#print axioms FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.rawPastEvent_eq_full_cylinders
#print FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.full_cylinders_disjoint
#print axioms FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.full_cylinders_disjoint
#print FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.isClopen_rawPastEvent
#print axioms FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.isClopen_rawPastEvent
#print FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.measurable_rawPastEvent
#print axioms FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.measurable_rawPastEvent
#print FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.finitePastEvent_iff_original_raw
#print axioms FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.finitePastEvent_iff_original_raw
#print FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.infinitePastEvent_iff_raw
#print axioms FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.infinitePastEvent_iff_raw
#print FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.infinitePastEvent_ae_raw
#print axioms FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.infinitePastEvent_ae_raw
#print FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.rawPastEvent_probability_tendsto
#print axioms FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.rawPastEvent_probability_tendsto
#print FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.eventually_finitePastEvent_law_eq
#print axioms FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.eventually_finitePastEvent_law_eq
#print FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.past_probability_tendsto
#print axioms FiniteAvalanches.Trees.Lattice.CurrentPastCylinder.past_probability_tendsto
