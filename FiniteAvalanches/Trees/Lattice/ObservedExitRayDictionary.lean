import FiniteAvalanches.Wilson.Lattice.FiniteTreeExitRay
import FiniteAvalanches.Trees.Lattice.ObservationRootSites

/-! Literal dictionaries between the finite-tree escaping ray and the roots
of the copied finite observation. -/
namespace FiniteAvalanches.ConditioningConsumer
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Trees.RootedPaths
open scoped Classical
noncomputable section

/-- Both finite site sets are the sites of the active vertices in the same span. -/
theorem connectingSites_eq_activeSites {N : ℕ} (t : (graph N).SpanningTree)
    (S : Set (FiniteWired.Vertex N)) :
    FiniteExitRay.connectingSites t S = (activeSites N ((graph N).span t S) : Set Site2) := by
  ext x
  constructor
  · rintro ⟨b, rfl, hb⟩
    exact (site_mem_activeSites N _ b).mpr hb
  · intro hx
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hx
    exact ⟨b, he.symm, (Finset.mem_filter.mp hb).2⟩

/-- The ordered tail retains every path vertex except its initial ancestor. -/
theorem active_mem_orderedAncestorTail_iff {N : ℕ} (t : (graph N).SpanningTree)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty) (a b : FiniteWired.Active N)
    (ha : (graph N).ancestorOf t none S hS = some a) :
    some b ∈ (graph N).orderedAncestorTail t none S hS ↔
      b ≠ a ∧ some b ∈ (path ((graph N).toSimple_isTree t.property) (some a) none).support := by
  unfold Multigraph.orderedAncestorTail
  rw [ha]
  let p := path ((graph N).toSimple_isTree t.property) (some a) none
  change some b ∈ p.support.tail ↔ b ≠ a ∧ some b ∈ p.support
  have hnodup : (some a :: p.support.tail).Nodup := by
    rw [p.cons_tail_support]
    exact (path_isPath ((graph N).toSimple_isTree t.property) (some a) none).support_nodup
  have hnot : some a ∉ p.support.tail := (List.nodup_cons.mp hnodup).1
  constructor
  · intro hb
    refine ⟨fun h => hnot (h ▸ hb), ?_⟩
    rw [← p.cons_tail_support]
    exact List.mem_cons_of_mem _ hb
  · rintro ⟨hba, hb⟩
    rw [← p.cons_tail_support, List.mem_cons] at hb
    exact hb.resolve_left (fun h => hba (Option.some.inj h))

/-- The finite-tree Gamma is exactly the current observation's one roots,
including the entire exterior and the whole strict interior path tail. -/
theorem observedGamma_eq_observationRootPair_one {N : ℕ} (t : (graph N).SpanningTree)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (hne : (graph N).ancestorOf t none S hS ≠ none) (a : FiniteWired.Active N)
    (ha : (graph N).ancestorOf t none S hS = some a) :
    FiniteExitRay.observedGamma t a = (observationRootPair N S hS t hne).one := by
  rw [observationRootPair_one_eq_exterior_union_tail]
  unfold FiniteExitRay.observedGamma
  apply congrArg (fun A : Set Site2 => {x | ¬FiniteWired.inBox N x} ∪ A)
  ext x
  constructor
  · rintro ⟨b, rfl, hba, hbp⟩
    refine ⟨fun i => (b i).property, ?_⟩
    rw [wiredSite_active]
    exact (active_mem_orderedAncestorTail_iff t S hS a b ha).mpr ⟨hba, hbp⟩
  · rintro ⟨hx, htail⟩
    let b := FiniteWired.activeOfSite N x hx
    have hb : FiniteWired.site b = x := FiniteWired.site_activeOfSite N x hx
    have hwire : wiredSite N x = some b := by
      rw [← hb, wiredSite_active]
    rw [hwire] at htail
    obtain ⟨hba, hbp⟩ := (active_mem_orderedAncestorTail_iff t S hS a b ha).mp htail
    exact ⟨b, hb.symm, hba, hbp⟩

/-- The actual common ancestor has an adjacent escaping ray inside its exact
observation roots, retaining the original final exit copy and straight tail. -/
theorem observationRootPair_escaping_ray {N : ℕ} (t : (graph N).SpanningTree)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (hne : (graph N).ancestorOf t none S hS ≠ none) :
    ∃ (a : FiniteWired.Active N) (γ : SimpleRay),
      (graph N).ancestorOf t none S hS = some a ∧
      FiniteWired.site a ∈ activeSites N ((graph N).span t S) ∧
      (lattice 2).Adj (FiniteWired.site a) (γ.vertex 0) ∧
      γ.vertices ⊆ (observationRootPair N S hS t hne).one ∧
      Disjoint (activeSites N ((graph N).span t S) : Set Site2) γ.vertices ∧
      ∃ e : FiniteWired.ExitEdge N,
        Sum.inr e ∈ (graph N).rootPathCopies t (some a) none ∧
        ∃ m : ℕ, ∀ n, γ.vertex (m + n) = FiniteExitRay.outwardVertex e.val.1 e.val.2 (n + 1) := by
  obtain ⟨a, γ, ha, haK, hadj, hΓ, hdisj, hexit⟩ :=
    FiniteExitRay.common_ancestor_escaping_ray t S hS hne
  rw [connectingSites_eq_activeSites] at haK hdisj
  rw [observedGamma_eq_observationRootPair_one t S hS hne a ha] at hΓ
  exact ⟨a, γ, ha, haK, hadj, hΓ, hdisj.symm, hexit⟩

end
end FiniteAvalanches.ConditioningConsumer
