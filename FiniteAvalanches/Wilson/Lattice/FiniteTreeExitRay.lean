import FiniteAvalanches.Wilson.Lattice.FiniteExitRay

/-! The finite source's actual common ancestor, connecting subtree and Gamma_N. -/
open scoped Classical
namespace FiniteAvalanches.Wilson.Lattice.FiniteExitRay
open LatticeProb FiniteAvalanches.Sandpile
open FiniteAvalanches.Trees.RootedPaths
noncomputable section

def removeFirst (γ : SimpleRay) : SimpleRay where
  vertex n := γ.vertex (n + 1)
  adjacent n := γ.adjacent (n + 1)
  injective := fun _ _ h => Nat.add_right_cancel (γ.injective h)

/-- The source's actual minimal connecting lattice subtree. -/
def connectingSites {N : ℕ} (t : (WiredTrees.graph N).SpanningTree)
    (S : Set (FiniteWired.Vertex N)) : Set (Site 2) :=
  {x | ∃ b : FiniteWired.Active N,
    x = FiniteWired.site b ∧ some b ∈ (WiredTrees.graph N).span t S}

/-- Outside B_N together with the actual observed path vertices after the ancestor. -/
def observedGamma {N : ℕ} (t : (WiredTrees.graph N).SpanningTree)
    (a : FiniteWired.Active N) : Set (Site 2) :=
  {x | ¬ FiniteWired.inBox N x} ∪
    {x | ∃ b : FiniteWired.Active N, x = FiniteWired.site b ∧ b ≠ a ∧
      some b ∈ (path ((WiredTrees.graph N).toSimple_isTree t.property) (some a) none).support}

theorem root_path_span_intersection {N : ℕ} (t : (WiredTrees.graph N).SpanningTree)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty) (a : FiniteWired.Active N)
    (ha : (WiredTrees.graph N).ancestorOf t none S hS = some a)
    {b : FiniteWired.Vertex N}
    (hb : b ∈ (path ((WiredTrees.graph N).toSimple_isTree t.property) (some a) none).support)
    (hK : b ∈ (WiredTrees.graph N).span t S) : b = some a := by
  let hT := (WiredTrees.graph N).toSimple_isTree t.property
  have hc := commonAncestor_spec hT none S hS
  change is_common_ancestor hT none S ((WiredTrees.graph N).ancestorOf t none S hS) at hc
  rw [ha] at hc
  have hab : ancestor hT none (some a) b :=
    connectingSubtree_subset_descendants hT none S hc.1 hK
  have hba : ancestor hT none b (some a) := by
    change b ∈ (path hT none (some a)).support
    rw [path_reverse hT none (some a), SimpleGraph.Walk.support_reverse]
    exact List.mem_reverse.mpr hb
  exact (ancestor_antisymm hT hab hba).symm

/-- On the nonsink-ancestor event the actual connecting subtree has no sink. -/
theorem sink_not_mem_span {N : ℕ} (t : (WiredTrees.graph N).SpanningTree)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (hne : (WiredTrees.graph N).ancestorOf t none S hS ≠ none) :
    none ∉ (WiredTrees.graph N).span t S := by
  intro h
  let hT := (WiredTrees.graph N).toSimple_isTree t.property
  have hc := commonAncestor_spec hT none S hS
  have ha := connectingSubtree_subset_descendants hT none S hc.1 h
  exact hne (ancestor_antisymm hT ha (ancestor_root hT none _))

theorem connectingSites_inBox {N : ℕ} (t : (WiredTrees.graph N).SpanningTree)
    (S : Set (FiniteWired.Vertex N)) :
    connectingSites t S ⊆ {x | FiniteWired.inBox N x} := by
  rintro _ ⟨b, rfl, _⟩
  exact fun i => (b i).property

/-- The entire actual observed color-one root set is disjoint from K. -/
theorem observedGamma_disjoint_connectingSites {N : ℕ}
    (t : (WiredTrees.graph N).SpanningTree) (S : Set (FiniteWired.Vertex N))
    (hS : S.Nonempty) (a : FiniteWired.Active N)
    (ha : (WiredTrees.graph N).ancestorOf t none S hS = some a) :
    Disjoint (observedGamma t a) (connectingSites t S) := by
  apply Set.disjoint_left.mpr
  rintro x (hout | ⟨b, hb, hba, hbp⟩) hK
  · exact hout (connectingSites_inBox t S hK)
  · obtain ⟨c, hc, hcK⟩ := hK
    have hbc : b = c := FiniteWired.site_injective N (hb.symm.trans hc)
    have he := root_path_span_intersection t S hS a ha hbp (hbc.symm ▸ hcK)
    exact hba (Option.some.inj he)

/-- Actual source construction: no arbitrary ray, path-order or avoidance premise.
The tail comes from the unique tree path and its original final sink-exit copy. -/
theorem common_ancestor_escaping_ray {N : ℕ} (t : (WiredTrees.graph N).SpanningTree)
    (S : Set (FiniteWired.Vertex N)) (hS : S.Nonempty)
    (hne : (WiredTrees.graph N).ancestorOf t none S hS ≠ none) :
    ∃ (a : FiniteWired.Active N) (γ : SimpleRay),
      (WiredTrees.graph N).ancestorOf t none S hS = some a ∧
      FiniteWired.site a ∈ connectingSites t S ∧
      (lattice 2).Adj (FiniteWired.site a) (γ.vertex 0) ∧
      γ.vertices ⊆ observedGamma t a ∧
      Disjoint γ.vertices (connectingSites t S) ∧
      ∃ e : FiniteWired.ExitEdge N,
        Sum.inr e ∈ (WiredTrees.graph N).rootPathCopies t (some a) none ∧
        ∃ m : ℕ, ∀ n, γ.vertex (m + n) = outwardVertex e.val.1 e.val.2 (n + 1) := by
  cases ha : (WiredTrees.graph N).ancestorOf t none S hS with
  | none => exact (hne ha).elim
  | some a =>
    let p := path ((WiredTrees.graph N).toSimple_isTree t.property) (some a) none
    obtain ⟨δ, hstart, hinside, e, heF, hepath, m, htail⟩ :=
      walk_extension p (path_isPath _ _ _) rfl a rfl
    have hfree (n : ℕ) : δ.vertex (n + 1) ≠ FiniteWired.site a := by
      intro h
      have hn := δ.injective (h.trans hstart.symm)
      omega
    refine ⟨a, removeFirst δ, rfl, ?_, ?_, ?_, ?_, e, ?_, m, ?_⟩
    · refine ⟨a, rfl, ?_⟩
      have hc := commonAncestor_mem_connectingSubtree
        ((WiredTrees.graph N).toSimple_isTree t.property) none S hS
      change (WiredTrees.graph N).ancestorOf t none S hS ∈
        (WiredTrees.graph N).span t S at hc
      exact ha ▸ hc
    · change (lattice 2).Adj (FiniteWired.site a) (δ.vertex (0 + 1))
      rw [← hstart]
      exact δ.adjacent 0
    · rintro x ⟨n, rfl⟩
      by_cases hx : FiniteWired.inBox N (δ.vertex (n + 1))
      · obtain ⟨b, hb, hbp⟩ := hinside (n + 1) hx
        exact Or.inr ⟨b, hb, fun h => hfree n (hb.trans (congrArg FiniteWired.site h)), hbp⟩
      · exact Or.inl hx
    · apply Set.disjoint_left.mpr
      rintro x ⟨n, rfl⟩ ⟨b, hb, hbK⟩
      have hx : FiniteWired.inBox N (δ.vertex (n + 1)) := by
        rw [show δ.vertex (n + 1) = FiniteWired.site b from hb]
        exact fun i => (b i).property
      obtain ⟨c, hc, hcp⟩ := hinside (n + 1) hx
      have hcb : c = b := FiniteWired.site_injective N (hc.symm.trans hb)
      have hca := root_path_span_intersection t S hS a ha hcp (hcb.symm ▸ hbK)
      exact hfree n (hc.trans (congrArg FiniteWired.site (Option.some.inj hca)))
    · apply ((WiredTrees.graph N).mem_rootPathCopies t (some a) none (Sum.inr e)).mpr
      exact ⟨heF, ((WiredTrees.graph N).separates_iff_mem_path
        t (Sum.inr e) heF (some a) none).mpr hepath⟩
    · intro n
      change δ.vertex (m + n + 1) = _
      simpa only [Nat.add_assoc] using htail (n + 1)

end
end FiniteAvalanches.Wilson.Lattice.FiniteExitRay
