import FiniteAvalanches.Sandpile.SourceCounting.ObservedSpanGeometry
import FiniteAvalanches.Trees.Lattice.ObservedExitRayDictionary
import FiniteAvalanches.Wilson.Lattice.RevealedGeometry.CofiniteComponent

/-! Connectivity of the entire exterior and strict observed tree-path tail. -/
namespace FiniteAvalanches.ConditioningConsumer
open LatticeProb FiniteAvalanches.Trees FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.WiredTrees FiniteAvalanches.Sandpile.Components
open FiniteAvalanches.Sandpile.SourceCounting FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Trees.RootedPaths
open scoped Classical
noncomputable section

private theorem exterior_reachable {N : ℕ} (Γ : Set Site2)
    (hout : ∀ x, ¬FiniteWired.inBox N x → x ∈ Γ)
    (x y : Site2) (hx : ¬FiniteWired.inBox N x) (hy : ¬FiniteWired.inBox N y) :
    ((lattice 2).induce Γ).Reachable ⟨x, hout x hx⟩ ⟨y, hout y hy⟩ := by
  let f : (lattice 2).induce (box 2 N)ᶜ →g (lattice 2).induce Γ := {
    toFun := fun z => ⟨z.val, hout z.val (fun hz =>
      z.property ((FiniteWired.inBox_iff N z.val).mp hz))⟩
    map_rel' := fun h => h }
  exact ((JointExterior.exterior_connected N).preconnected
    ⟨x, fun h => hx ((FiniteWired.inBox_iff N x).mpr h)⟩
    ⟨y, fun h => hy ((FiniteWired.inBox_iff N y).mpr h)⟩).map f

private theorem walk_reachable_exterior {N : ℕ} {F : Finset (FiniteWired.Edge N)}
    {u v : FiniteWired.Vertex N} (p : ((graph N).toSimple F).Walk u v)
    (hv : v = none) (Γ : Set Site2)
    (hout : ∀ x, ¬FiniteWired.inBox N x → x ∈ Γ)
    (hs : ∀ b : FiniteWired.Active N, some b ∈ p.support → FiniteWired.site b ∈ Γ)
    (a : FiniteWired.Active N) (hu : u = some a)
    (z : Site2) (hz : ¬FiniteWired.inBox N z) :
    ((lattice 2).induce Γ).Reachable
      ⟨FiniteWired.site a, hs a (hu ▸ p.start_mem_support)⟩ ⟨z, hout z hz⟩ := by
  induction p generalizing a with
  | nil => exact (Option.some_ne_none a (hu.symm.trans hv)).elim
  | @cons u v w h p ih =>
    subst u
    subst w
    cases v with
    | none =>
      obtain ⟨e, _, hea⟩ := FiniteExitRay.copied_exit h
      have heout := FiniteExitRay.outwardVertex_outside e (by norm_num : 0 < 1)
      have heΓ := hout _ heout
      have hadj : (lattice 2).Adj (FiniteWired.site a)
          (FiniteExitRay.outwardVertex e.val.1 e.val.2 1) := by
        rw [← hea, ← FiniteExitRay.outwardVertex_zero e.val.1 e.val.2]
        exact FiniteExitRay.outwardVertex_adjacent e.val.1 e.val.2 0
      exact (SimpleGraph.Adj.reachable (show ((lattice 2).induce Γ).Adj
        ⟨FiniteWired.site a, hs a List.mem_cons_self⟩
        ⟨FiniteExitRay.outwardVertex e.val.1 e.val.2 1, heΓ⟩ from hadj)).trans
          (exterior_reachable Γ hout _ z heout hz)
    | some b =>
      have hs' (c : FiniteWired.Active N) (hc : some c ∈ p.support) :
          FiniteWired.site c ∈ Γ := hs c (List.mem_cons_of_mem _ hc)
      have hreach := ih rfl hs' b rfl
      exact (SimpleGraph.Adj.reachable (show ((lattice 2).induce Γ).Adj
        ⟨FiniteWired.site a, hs a List.mem_cons_self⟩
        ⟨FiniteWired.site b, hs' b p.start_mem_support⟩ from
          FiniteExitRay.copied_internal_adjacent h)).trans hreach

/-- The full original Gamma, with every exterior site and every strict path
vertex, is connected. No selected ray or component replaces it. -/
theorem observedGamma_connected {N : ℕ} (t : (graph N).SpanningTree)
    (a : FiniteWired.Active N) :
    ((lattice 2).induce (FiniteExitRay.observedGamma t a)).Connected := by
  let Γ := FiniteExitRay.observedGamma t a
  have hout (x : Site2) (hx : ¬FiniteWired.inBox N x) : x ∈ Γ := Or.inl hx
  obtain ⟨z, hz⟩ := (JointExterior.exterior_connected N).nonempty
  have hzout : ¬FiniteWired.inBox N z := fun h =>
    hz ((FiniteWired.inBox_iff N z).mp h)
  have hr (x : Site2) (hx : x ∈ Γ) :
      ((lattice 2).induce Γ).Reachable ⟨x, hx⟩ ⟨z, hout z hzout⟩ := by
    rcases hx with hx | ⟨b, rfl, hba, hbp⟩
    · exact exterior_reachable Γ hout x z hx hzout
    · let p := path ((graph N).toSimple_isTree t.property) (some a) none
      have hp : p.IsPath := path_isPath _ _ _
      have hnon : ¬p.Nil := fun hn => Option.some_ne_none a hn.eq
      have haout : some a ∉ p.support.tail := by
        have hnodup : (some a :: p.support.tail).Nodup := by
          rw [p.cons_tail_support]
          exact hp.support_nodup
        exact (List.nodup_cons.mp hnodup).1
      have hb : some b ∈ p.tail.support := by
        rw [p.support_tail_of_not_nil hnon]
        change some b ∈ p.support at hbp
        rw [← p.cons_tail_support, List.mem_cons] at hbp
        exact hbp.resolve_left (fun he => hba (Option.some.inj he))
      have hq (c : FiniteWired.Active N) (hc : some c ∈ p.tail.support) :
          FiniteWired.site c ∈ Γ := by
        rw [p.support_tail_of_not_nil hnon] at hc
        refine Or.inr ⟨c, rfl, fun he => haout (he ▸ hc), ?_⟩
        rw [← p.cons_tail_support]
        exact List.mem_cons_of_mem _ hc
      exact walk_reachable_exterior (p.tail.dropUntil (some b) hb) rfl Γ hout
        (fun c hc => hq c (p.tail.support_dropUntil_subset_support hb hc)) b rfl z hzout
  exact { preconnected := fun x y => (hr x.val x.property).trans (hr y.val y.property).symm
          nonempty := ⟨⟨z, hout z hzout⟩⟩ }

/-- The actual observed one roots form the entire connected cofinite Gamma_N. -/
theorem observationRootPair_one_connected_cofinite (N : ℕ)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty) (t : (graph N).SpanningTree)
    (hne : (graph N).ancestorOf t none S hS ≠ none) :
    ((lattice 2).induce (observationRootPair N S hS t hne).one).Connected ∧
      (observationRootPair N S hS t hne).oneᶜ.Finite := by
  let a := ((graph N).ancestorOf t none S hS).get (Option.isSome_iff_ne_none.mpr hne)
  have ha : (graph N).ancestorOf t none S hS = some a := (Option.some_get _).symm
  constructor
  · rw [← observedGamma_eq_observationRootPair_one t S hS hne a ha]
    exact observedGamma_connected t a
  · apply (JointCofiniteComponent.box_finite N).subset
    intro x hx
    apply (FiniteWired.inBox_iff N x).mp
    by_contra hn
    exact hx (observationRootPair_exterior_one N S hS t hne hn)

/-- Every forest antecedent is produced from the actual six-mark observation. -/
theorem source_marks_observed_cofinite_geometry {N r : ℕ}
    (hr : 2 ≤ r) (hrN : r ≤ N) (t : (graph N).SpanningTree)
    (hne : (graph N).ancestorOf t none (markedVertices (activeMarks N r))
      (marked_vertices_nonempty _ (source_mem_activeMarks N r)) ≠ none) :
    let S := markedVertices (activeMarks N r)
    let hS := marked_vertices_nonempty _ (source_mem_activeMarks N r)
    let K := activeSites N ((graph N).span t S)
    let Q := observationRootPair N S hS t hne
    ((lattice 2).induce (K : Set Site2)).Connected ∧
      ((lattice 2).induce Q.one).Connected ∧ Q.oneᶜ.Finite ∧
      Disjoint (K : Set Site2) Q.one ∧
      (∃ k ∈ K, ∃ y ∈ Q.one, (lattice 2).Adj k y) ∧
      Q.zero = (K : Set Site2) ∧
      r ≤ K.sup (fun x => K.sup (fun y => siteRadius x y)) := by
  dsimp only
  obtain ⟨_, hK, _, _, _, _, hdiam, hzero⟩ :=
    source_marks_observed_span_geometry hr hrN t hne
  obtain ⟨hΓ, hfin⟩ := observationRootPair_one_connected_cofinite N _ _ t hne
  obtain ⟨a, γ, _, haK, hadj, hγ, _, _⟩ := observationRootPair_escaping_ray t _ _ hne
  have hdisj := (observationRootPair N _ _ t hne).disjoint
  rw [hzero] at hdisj
  exact ⟨hK, hΓ, hfin, hdisj,
    ⟨FiniteWired.site a, haK, γ.vertex 0, hγ ⟨0, rfl⟩, hadj⟩, hzero, hdiam⟩

end
end FiniteAvalanches.ConditioningConsumer
