import FiniteAvalanches.Trees.RootedPaths
import FiniteAvalanches.Trees.ConnectorTree
import FiniteAvalanches.Sandpile.SourceCounting.CountingPaths
import FiniteAvalanches.Trees.Lattice.ObservationRootSites

/-! Lattice geometry of the actual finite marked span on the nonsink event. -/
namespace FiniteAvalanches.ConditioningConsumer
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Sandpile.Components
open FiniteAvalanches.Sandpile.SourceCounting
open scoped Classical
noncomputable section

private theorem lattice_adj_of_wired_adj {N : ℕ} {s : Finset (FiniteWired.Edge N)}
    {x y : FiniteWired.Active N}
    (h : ((graph N).toSimple s).Adj (some x) (some y)) :
    (lattice 2).Adj (FiniteWired.site x) (FiniteWired.site y) := by
  obtain ⟨e, _, he⟩ := h
  cases e with
  | inl e =>
    obtain ⟨i, hi⟩ := e.property
    rcases he with he | he
    · change some e.val.1 = some x ∧ some e.val.2 = some y at he
      have hx := Option.some.inj he.1
      have hy := Option.some.inj he.2
      subst x; subst y
      exact ⟨i, Or.inl hi⟩
    · change some e.val.2 = some x ∧ some e.val.1 = some y at he
      have hx := Option.some.inj he.1
      have hy := Option.some.inj he.2
      subst x; subst y
      exact ⟨i, Or.inr hi⟩
  | inr e =>
    change (some e.val.1 = some x ∧ none = some y) ∨
      (none = some x ∧ some e.val.1 = some y) at he
    rcases he with he | he
    · cases he.2
    · cases he.1

/-- Connectivity is transported from the actual tree span after deriving that
every span vertex is active. No lattice paths or connectedness are assumed. -/
theorem observed_span_lattice_connected (N : ℕ) (S : Set (FiniteWired.Vertex N))
    (hS : S.Nonempty) (t : (graph N).SpanningTree)
    (hne : (graph N).ancestorOf t none S hS ≠ none) :
    ((lattice 2).induce (activeSites N ((graph N).span t S) : Set Site2)).Connected := by
  have hsink := sink_not_mem_observed_span N S hS t hne
  let active (v : (graph N).span t S) : FiniteWired.Active N :=
    v.val.get (Option.isSome_iff_ne_none.mpr (fun he => hsink (he ▸ v.property)))
  have hactive (v : (graph N).span t S) : some (active v) = v.val := Option.some_get _
  let φ : ((graph N).toSimple t.val).induce ((graph N).span t S) →g
      (lattice 2).induce (activeSites N ((graph N).span t S) : Set Site2) := {
    toFun := fun v => ⟨FiniteWired.site (active v),
      (site_mem_activeSites N _ (active v)).mpr (by rw [hactive]; exact v.property)⟩
    map_rel' := by
      intro x y h
      change ((graph N).toSimple t.val).Adj x.val y.val at h
      change (lattice 2).Adj (FiniteWired.site (active x)) (FiniteWired.site (active y))
      rw [← hactive x, ← hactive y] at h
      exact lattice_adj_of_wired_adj h }
  apply SimpleGraph.Connected.map φ
  · intro z
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp z.property
    have haK := (Finset.mem_filter.mp ha).2
    refine ⟨⟨some a, haK⟩, ?_⟩
    apply Subtype.ext
    have hv : active ⟨some a, haK⟩ = a := Option.some.inj (hactive ⟨some a, haK⟩)
    change FiniteWired.site (active ⟨some a, haK⟩) = z.val
    rw [hv]
    exact he
  · exact RootedPaths.connectingSubtree_connected
      ((graph N).toSimple_isTree t.property) S hS

/-- The literal lattice site of the common ancestor belongs to the marked span. -/
theorem observed_ancestor_site_mem (N : ℕ) (S : Set (FiniteWired.Vertex N))
    (hS : S.Nonempty) (t : (graph N).SpanningTree)
    (hne : (graph N).ancestorOf t none S hS ≠ none) :
    FiniteWired.site (((graph N).ancestorOf t none S hS).get
      (Option.isSome_iff_ne_none.mpr hne)) ∈ activeSites N ((graph N).span t S) := by
  apply (site_mem_activeSites N _ _).mpr
  rw [Option.some_get]
  exact RootedPaths.commonAncestor_mem_connectingSubtree
    ((graph N).toSimple_isTree t.property) none S hS

/-- Every supplied active mark lies in its actual tree span. -/
theorem markedSites_subset_observed_span {N : ℕ}
    (marks : Finset (FiniteWired.Active N)) (t : (graph N).SpanningTree) :
    markedSites marks ⊆ activeSites N ((graph N).span t (markedVertices marks)) := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
  apply (site_mem_activeSites N _ a).mpr
  exact RootedPaths.subset_connectingSubtree ((graph N).toSimple_isTree t.property)
    (markedVertices marks) ⟨a, ha, rfl⟩

/-- The source's two distinguished marks are exactly distance `r` apart in the
integer lattice supremum metric. -/
theorem siteRadius_zero_axisSite (r : ℕ) : siteRadius 0 (axisSite r) = r := by
  apply Nat.le_antisymm
  · apply (siteRadius_le_iff _ _ _).mpr
    intro i
    fin_cases i <;> simp [axisSite]
  · have h := Finset.le_sup (s := (Finset.univ : Finset (Fin 2)))
      (f := fun i => ((axisSite r) i - (0 : Site2) i).natAbs) (Finset.mem_univ 0)
    change ((r : ℤ) - 0).natAbs ≤ siteRadius 0 (axisSite r) at h
    simpa only [sub_zero, Int.natAbs_natCast] using h

/-- The literal source marks force the infinity-diameter lower bound. -/
theorem sourceMarks_le_sup_diameter (r : ℕ) (K : Finset Site2)
    (hmarks : sourceMarks r ⊆ K) :
    r ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) := by
  have h0 : (0 : Site2) ∈ K := hmarks (by simp [sourceMarks])
  have hr : axisSite r ∈ K := hmarks (Finset.mem_insert_self _ _)
  calc
    r = siteRadius 0 (axisSite r) := (siteRadius_zero_axisSite r).symm
    _ ≤ K.sup (fun y => siteRadius 0 y) := Finset.le_sup hr
    _ ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) :=
      Finset.le_sup (f := fun x => K.sup (fun y => siteRadius x y)) h0

/-- All finite-observation geometry for the six actual source marks, with only
the source scales, literal spanning tree, and nonsink ancestor event as inputs. -/
theorem source_marks_observed_span_geometry {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (t : (graph N).SpanningTree)
    (hne : (graph N).ancestorOf t none (markedVertices (activeMarks N r))
      (marked_vertices_nonempty _ (source_mem_activeMarks N r)) ≠ none) :
    let S := markedVertices (activeMarks N r)
    let hS := marked_vertices_nonempty _ (source_mem_activeMarks N r)
    let Ksites := activeSites N ((graph N).span t S)
    none ∉ (graph N).span t S ∧
    ((lattice 2).induce (Ksites : Set Site2)).Connected ∧
    FiniteWired.site (((graph N).ancestorOf t none S hS).get
      (Option.isSome_iff_ne_none.mpr hne)) ∈ Ksites ∧
    sourceMarks r ⊆ Ksites ∧ (0 : Site2) ∈ Ksites ∧ axisSite r ∈ Ksites ∧
    r ≤ Ksites.sup (fun x => Ksites.sup (fun y => siteRadius x y)) ∧
    (observationRootPair N S hS t hne).zero = (Ksites : Set Site2) := by
  dsimp only
  have hm : sourceMarks r ⊆
      activeSites N ((graph N).span t (markedVertices (activeMarks N r))) := by
    rw [← markedSites_activeMarks hr hrN]
    exact markedSites_subset_observed_span _ t
  refine ⟨sink_not_mem_observed_span N _ _ t hne,
    observed_span_lattice_connected N _ _ t hne,
    observed_ancestor_site_mem N _ _ t hne, hm, ?_, ?_,
    sourceMarks_le_sup_diameter r _ hm, observationRootPair_zero_eq_activeSites N _ _ t hne⟩
  · exact hm (by simp [sourceMarks])
  · exact hm (Finset.mem_insert_self _ _)

end
end FiniteAvalanches.ConditioningConsumer
