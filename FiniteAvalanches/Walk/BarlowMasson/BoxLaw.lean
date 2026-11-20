import FiniteAvalanches.Walk.BarlowMasson.BoxContraction
import FiniteAvalanches.Wilson.Lattice.WiredCylinderLaw
import FiniteAvalanches.Wilson.Lattice.WiredJointCylinders
import FiniteAvalanches.Wilson.Lattice.WiredObservationGeometry
import FiniteAvalanches.Wilson.Lattice.SamplerEvents

/-!
# The wired box law as a lattice Wilson sampler

The uniform spanning tree of the wired box of size `N`, observed on edges with both endpoints in
the box, has the law of the lattice Wilson sampler whose roots are the sites outside the box:
each queried site runs a simple random walk until it hits the exterior of the box or an earlier
branch, and adds the loop erasure of this walk.

## Proof

Take the root pair `sinkRoots N`, with no root inside the box and every exterior site a root.
Its rooted forests in the box of size `N` are the spanning trees of the wired box rooted at the
sink. By `WiredBoxCopies.ExteriorRoots.finiteForestEquiv` its rooted forests in every larger box
have the same law on the edges of the box of size `N`. These laws converge to the unique law with
the finite joint distributions of the lattice sampler (`finiteForestProbability_tendsto_of_cylinderLaw`).

## Main statements

* `sinkRoots`: the exterior of the box as a root pair.
* `finiteLaw_cylinder_eq_sampler`: the wired box law of an edge cylinder inside the box is the
  probability of the corresponding sampler event.
-/

set_option autoImplicit false

namespace FiniteAvalanches.Walk.BarlowMasson

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Wilson.Lattice.WiredBoxCopies
open scoped Classical ENNReal

noncomputable section

/-- The edge field of a rooted forest of a larger box agrees with that of the corresponding
forest of the smaller box on every edge with both endpoints in the smaller box. -/
theorem finiteEdgeField_finiteForestEquiv {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (hext : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero ∪ R.one) (F : FiniteForest R N)
    (e : LatticeEdge) (he : ∀ z ∈ e.val, FiniteWired.inBox N z) :
    finiteEdgeField R M (ExteriorRoots.finiteForestEquiv hNM R hext F) e =
      finiteEdgeField R N F e := by
  obtain ⟨i, rfl⟩ := exists_interiorEdge_of_inBox N e he
  obtain ⟨j, hj⟩ : ∃ j, copyInLarger hNM (Sum.inl i) = Sum.inl j := ⟨_, rfl⟩
  have hji : interiorEdge j = interiorEdge i := by
    have h := copyInLarger_original hNM (Sum.inl i)
    rw [hj] at h
    exact h
  rw [finiteEdgeField_internal_eq R N F i, ← hji, finiteEdgeField_internal_eq,
    ExteriorRoots.finiteForestEquiv_copies]
  apply Bool.decide_congr
  rw [← hj, Finset.mem_image]
  constructor
  · rintro ⟨f, hf, hfe⟩
    rwa [← copyInLarger_injective hNM hfe]
  · intro h
    exact ⟨_, h, rfl⟩

/-- The law of a joint edge observation inside the smaller box is the same in every larger box. -/
theorem finiteForestLaw_window_eq {N M : ℕ} (hNM : N ≤ M) (R : RootPair)
    (hext : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero ∪ R.one) (E : Finset LatticeEdge)
    (hE : ∀ e ∈ E, ∀ z ∈ e.val, FiniteWired.inBox N z) (pe : LatticeEdge → Bool)
    (pc : Site 2 → Bool) :
    finiteForestLaw R N (jointEvent E ∅ pe pc) = finiteForestLaw R M (jointEvent E ∅ pe pc) := by
  have hm : MeasurableSet (jointEvent E ∅ pe pc) :=
    (isClopen_jointEvent E ∅ pe pc).isClosed.measurableSet
  have hevent (F : FiniteForest R N) :
      finiteForestField R N F ∈ jointEvent E ∅ pe pc ↔
        finiteForestField R M (ExteriorRoots.finiteForestEquiv hNM R hext F) ∈
          jointEvent E ∅ pe pc := by
    simp only [jointEvent, Set.mem_setOf_eq, Finset.notMem_empty, IsEmpty.forall_iff,
      implies_true, and_true, finiteForestField]
    constructor
    · intro h e heE
      rw [finiteEdgeField_finiteForestEquiv hNM R hext F e (hE e heE)]
      exact h e heE
    · intro h e heE
      rw [← finiteEdgeField_finiteForestEquiv hNM R hext F e (hE e heE)]
      exact h e heE
  have hcount := Nat.card_congr ((ExteriorRoots.finiteForestEquiv hNM R hext).subtypeEquiv
    (p := fun F => finiteForestField R N F ∈ jointEvent E ∅ pe pc)
    (q := fun F => finiteForestField R M F ∈ jointEvent E ∅ pe pc) hevent)
  rw [finiteForestLaw_count R N _ hm, finiteForestLaw_count R M _ hm,
    ExteriorRoots.finiteForestCount_eq hNM R hext]
  congr 2

/-- A wired box whose exterior consists of roots has, on its own edges, the finite joint
distributions of the lattice Wilson sampler. -/
theorem finiteForestLaw_window_eq_sampler (R : RootPair) (N : ℕ)
    (hext : ∀ x, ¬FiniteWired.inBox N x → x ∈ R.zero ∪ R.one) (x : ℕ → Site 2) (n : ℕ)
    (E : Finset LatticeEdge) (hE : ∀ e ∈ E, ∀ z ∈ e.val, FiniteWired.inBox N z)
    (hq : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z) (pe : LatticeEdge → Bool) :
    finiteForestLaw R N (jointEvent E ∅ pe (fun _ => false)) =
      wilsonRows (samplerEvent R ((List.range n).map x) E ∅ pe (fun _ => false)) := by
  obtain ⟨ν, hν, -⟩ := existsUnique_wilsonCylinderLaw R
  have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (finiteForestProbability_tendsto_of_cylinderLaw R ν hν)
    (E := jointEvent E ∅ pe (fun _ => false))
    (by simp [(isClopen_jointEvent E ∅ pe (fun _ => false)).frontier_eq])
  have hconst : Tendsto (fun M => (finiteForestProbability R M : Measure ForestField)
      (jointEvent E ∅ pe (fun _ => false))) atTop
      (nhds (finiteForestLaw R N (jointEvent E ∅ pe (fun _ => false)))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with M hM
    exact finiteForestLaw_window_eq hM R hext E hE pe _
  rw [tendsto_nhds_unique hconst ht]
  exact hν x n E ∅ pe _ hq (by simp)

/-- The exterior of the box of size `N` as a root pair: the site `(N + 1, N + 1)` is the zero
root and every other exterior site is a one root. -/
def sinkRoots (N : ℕ) : RootPair where
  zero := {fun _ => (N : ℤ) + 1}
  one := {z | ¬FiniteWired.inBox N z ∧ z ≠ fun _ => (N : ℤ) + 1}
  disjoint := by
    rw [Set.disjoint_left]
    rintro z hz ⟨-, hne⟩
    exact hne hz
  zero_nonempty := Set.singleton_nonempty _
  one_nonempty := by
    refine ⟨fun _ => -((N : ℤ) + 1), ?_, ?_⟩
    · intro h
      have := (h 0).1
      simp only at this
      omega
    · intro h
      have : -((N : ℤ) + 1) = (N : ℤ) + 1 := congrFun h 0
      omega

theorem sinkRoots_ext (N : ℕ) (x : Site 2) (hx : ¬FiniteWired.inBox N x) :
    x ∈ (sinkRoots N).zero ∪ (sinkRoots N).one := by
  by_cases h : x = fun _ => (N : ℤ) + 1
  · exact Or.inl h
  · exact Or.inr ⟨hx, h⟩

theorem not_mem_sinkRoots (N : ℕ) (x : Site 2) (hx : FiniteWired.inBox N x) :
    x ∉ (sinkRoots N).zero ∪ (sinkRoots N).one := by
  rintro (h | ⟨h, -⟩)
  · have h' : x = fun _ => (N : ℤ) + 1 := h
    have := (hx 0).2
    rw [h'] at this
    simp only at this
    omega
  · exact h hx

theorem wiredRoots_sinkRoots (N : ℕ) : (wiredRoots (sinkRoots N) N).val = {none} := by
  ext v
  cases v with
  | none => simp only [Set.mem_singleton_iff, iff_true]; exact Or.inr trivial
  | some x =>
    simp only [Set.mem_singleton_iff, reduceCtorEq, iff_false]
    exact not_mem_sinkRoots N (FiniteWired.site x) (fun i => (x i).property)

/-- The rooted forests of the box for `sinkRoots` are its spanning trees. -/
def sinkForestEquiv (N : ℕ) : FiniteForest (sinkRoots N) N ≃ (WiredTrees.graph N).SpanningTree :=
  (Equiv.subtypeEquivRight (fun F => by rw [wiredRoots_sinkRoots])).trans
    (FiniteAvalanches.Wilson.CyclePopping.singletonRootedForestEquiv (WiredTrees.graph N) none)

theorem finiteEdgeField_sinkRoots (N : ℕ) (F : FiniteForest (sinkRoots N) N) :
    finiteEdgeField (sinkRoots N) N F = wiredField (sinkForestEquiv N F) := rfl

/-- **The wired box law as a sampler.** An edge cylinder inside the box has the probability of
the corresponding event of the lattice sampler rooted at the exterior of the box. -/
theorem finiteLaw_cylinder_eq_sampler (N : ℕ) (x : ℕ → Site 2) (n : ℕ)
    (E : Finset LatticeEdge) (hE : ∀ e ∈ E, ∀ z ∈ e.val, FiniteWired.inBox N z)
    (hq : ∀ e ∈ E, ∀ z ∈ e.val, ∃ i < n, x i = z) (p : E → Bool) :
    finiteLaw N (Lattice.cylinder E p) =
      wilsonRows (samplerEvent (sinkRoots N) ((List.range n).map x) E ∅
        (fun e => if h : e ∈ E then p ⟨e, h⟩ else false) (fun _ => false)) := by
  let pe : LatticeEdge → Bool := fun e => if h : e ∈ E then p ⟨e, h⟩ else false
  rw [← finiteForestLaw_window_eq_sampler (sinkRoots N) N (sinkRoots_ext N) x n E hE hq pe]
  have hm : MeasurableSet (jointEvent E ∅ pe (fun _ => false)) :=
    (isClopen_jointEvent E ∅ pe (fun _ => false)).isClosed.measurableSet
  have hevent (F : FiniteForest (sinkRoots N) N) :
      finiteForestField (sinkRoots N) N F ∈ jointEvent E ∅ pe (fun _ => false) ↔
        wiredField (sinkForestEquiv N F) ∈ Lattice.cylinder E p := by
    simp only [jointEvent, Set.mem_setOf_eq, Finset.notMem_empty, IsEmpty.forall_iff,
      implies_true, and_true, finiteForestField, Lattice.cylinder, finiteEdgeField_sinkRoots]
    constructor
    · intro h
      funext e
      simpa [pe, e.property] using h e.val e.property
    · intro h e he
      have := congrFun h ⟨e, he⟩
      simpa [pe, he] using this
  have hcount := Nat.card_congr ((sinkForestEquiv N).subtypeEquiv
    (p := fun F => finiteForestField (sinkRoots N) N F ∈ jointEvent E ∅ pe (fun _ => false))
    (q := fun t => wiredField t ∈ Lattice.cylinder E p) hevent)
  rw [finiteForestLaw_count _ N _ hm, finiteLaw_original_count N _ (measurableSet_cylinder E p)]
  have hc : finiteForestCount (sinkRoots N) N = WiredTrees.treeCount N := by
    rw [finiteForestCount, Nat.card_congr (sinkForestEquiv N), WiredTrees.treeCount,
      Nat.card_eq_fintype_card]
  rw [hc]
  congr 2
  exact hcount.symm

end

end FiniteAvalanches.Walk.BarlowMasson
