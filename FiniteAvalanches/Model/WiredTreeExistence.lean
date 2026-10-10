import FiniteAvalanches.Model.WiredTrees
import FiniteAvalanches.Model.WiredLaplacian

/-! A literal spanning tree: every row follows its positive first-coordinate copies to the sink. -/
open scoped Classical
namespace FiniteAvalanches.Sandpile.WiredTrees
open FiniteAvalanches.Trees
open FiniteAvalanches.Sandpile

noncomputable def rowEdge {N : ℕ} (x : FiniteWired.Active N) : FiniteWired.Edge N :=
  FiniteWired.directionEdge x (0, true)

noncomputable def rowEdges (N : ℕ) : Finset (FiniteWired.Edge N) :=
  Finset.univ.image rowEdge

theorem shifted_in_box_iff {N : ℕ} (x : FiniteWired.Active N) :
    FiniteWired.inBox N (FiniteWired.site x + LatticeProb.unit 0) ↔ (x 0).val < N := by
  obtain ⟨h0l, h0r⟩ := (x 0).property
  obtain ⟨h1l, h1r⟩ := (x 1).property
  simp only [FiniteWired.inBox, Fin.forall_fin_two, Pi.add_apply, FiniteWired.site,
    LatticeProb.unit, Pi.single_apply, ite_true]
  norm_num
  omega

theorem row_edge_endpoints {N : ℕ} (x : FiniteWired.Active N) :
    FiniteWired.endpoints (rowEdge x) =
      if h : FiniteWired.inBox N (FiniteWired.site x + LatticeProb.unit 0) then
        (some x, some (FiniteWired.activeOfSite N (FiniteWired.site x + LatticeProb.unit 0) h))
      else (some x, none) := by
  by_cases h : FiniteWired.inBox N (FiniteWired.site x + LatticeProb.unit 0)
  · simp [rowEdge, FiniteWired.directionEdge, h, FiniteWired.endpoints]
  · simp [rowEdge, FiniteWired.directionEdge, h, FiniteWired.endpoints]

theorem row_edge_left {N : ℕ} (x : FiniteWired.Active N) :
    (graph N).left (rowEdge x) = some x := by
  change (FiniteWired.endpoints (rowEdge x)).1 = some x
  rw [row_edge_endpoints]
  split <;> rfl

theorem row_edge_mem {N : ℕ} (x : FiniteWired.Active N) : rowEdge x ∈ rowEdges N :=
  Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

private theorem active_eq_of_coordinates {N : ℕ} {x y : FiniteWired.Active N}
    (h0 : (y 0).val = (x 0).val) (h1 : (y 1).val = (x 1).val) : y = x := by
  funext i
  fin_cases i
  · exact Subtype.ext h0
  · exact Subtype.ext h1

/-- The vertices separated from the sink by deletion of the outgoing copy at x. -/
def prefixRow {N : ℕ} (x : FiniteWired.Active N) : Set (FiniteWired.Vertex N) :=
  {v | match v with
    | none => False
    | some y => (y 1).val = (x 1).val ∧ (y 0).val ≤ (x 0).val}

theorem row_edge_right_not_mem {N : ℕ} (x : FiniteWired.Active N) :
    (graph N).right (rowEdge x) ∉ prefixRow x := by
  change (FiniteWired.endpoints (rowEdge x)).2 ∉ prefixRow x
  rw [row_edge_endpoints]
  split
  · simp only [prefixRow, Set.mem_setOf_eq, FiniteWired.activeOfSite, FiniteWired.site,
      Pi.add_apply, LatticeProb.unit, Pi.single_apply]
    norm_num
  · simp [prefixRow]

theorem other_row_edge_same_side {N : ℕ} (x y : FiniteWired.Active N) (hne : y ≠ x) :
    (graph N).left (rowEdge y) ∈ prefixRow x ↔
      (graph N).right (rowEdge y) ∈ prefixRow x := by
  have hn : ¬ ((y 1).val = (x 1).val ∧ (y 0).val = (x 0).val) :=
    fun h => hne (active_eq_of_coordinates h.2 h.1)
  change (FiniteWired.endpoints (rowEdge y)).1 ∈ prefixRow x ↔
    (FiniteWired.endpoints (rowEdge y)).2 ∈ prefixRow x
  rw [row_edge_endpoints]
  split
  · simp only [prefixRow, Set.mem_setOf_eq, FiniteWired.activeOfSite, FiniteWired.site,
      Pi.add_apply, LatticeProb.unit, Pi.single_apply]
    norm_num
    intro hrow
    change (y 0).val ≤ (x 0).val ↔ (y 0).val < (x 0).val
    have hneq := fun h => hn ⟨hrow, h⟩
    omega
  · rename_i hy
    have hb : (y 0).val = N := by
      have h := (shifted_in_box_iff y).not.mp hy
      have hle := (y 0).property.2
      omega
    have hx := (x 0).property.2
    simp only [prefixRow, Set.mem_setOf_eq, iff_false]
    rintro ⟨hrow, hle⟩
    exact hn ⟨hrow, by omega⟩

theorem row_edges_is_forest (N : ℕ) : (graph N).is_forest (rowEdges N) := by
  intro e he hreach
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp he
  have hside : ∀ f ∈ (rowEdges N).erase (rowEdge x),
      (graph N).left f ∈ prefixRow x ↔ (graph N).right f ∈ prefixRow x := by
    intro f hf
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hf)
    apply other_row_edge_same_side x y
    intro h
    apply (Finset.mem_erase.mp hf).1
    rw [h]
  have hsame := (graph N).reaches_mem_iff hside hreach
  have hl : (graph N).left (rowEdge x) ∈ prefixRow x := by
    rw [row_edge_left]
    exact ⟨rfl, le_rfl⟩
  exact row_edge_right_not_mem x (hsame.mp hl)

theorem row_reaches_sink {N : ℕ} (x : FiniteWired.Active N) :
    (graph N).reaches (rowEdges N) (some x) none := by
  have hall (d : ℕ) : ∀ x : FiniteWired.Active N,
      ((N : ℤ) - (x 0).val).toNat = d →
        (graph N).reaches (rowEdges N) (some x) none := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro x hd
      by_cases hx : FiniteWired.inBox N (FiniteWired.site x + LatticeProb.unit 0)
      · let y := FiniteWired.activeOfSite N (FiniteWired.site x + LatticeProb.unit 0) hx
        have hy : (y 0).val = (x 0).val + 1 := by simp [y, FiniteWired.activeOfSite, FiniteWired.site, LatticeProb.unit]
        have hlt : ((N : ℤ) - (y 0).val).toNat < d := by
          have h := (shifted_in_box_iff x).mp hx
          rw [hy]
          omega
        have hstep : (graph N).adjacent (rowEdges N) (some x) (some y) := by
          refine ⟨rowEdge x, row_edge_mem x, Or.inl ⟨row_edge_left x, ?_⟩⟩
          change (FiniteWired.endpoints (rowEdge x)).2 = some y
          rw [row_edge_endpoints, dif_pos hx]
        exact (Relation.ReflTransGen.single hstep).trans (ih _ hlt y rfl)
      · apply Relation.ReflTransGen.single
        refine ⟨rowEdge x, row_edge_mem x, Or.inl ⟨row_edge_left x, ?_⟩⟩
        change (FiniteWired.endpoints (rowEdge x)).2 = none
        rw [row_edge_endpoints, dif_neg hx]
  exact hall _ x rfl

theorem row_edges_is_tree (N : ℕ) : (graph N).is_tree Set.univ (rowEdges N) := by
  have hr (v : FiniteWired.Vertex N) : (graph N).reaches (rowEdges N) v none := by
    cases v with
    | none => exact .refl
    | some x => exact row_reaches_sink x
  exact ⟨⟨none, Set.mem_univ _⟩, (fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩),
    (fun x _ y _ => (hr x).trans ((graph N).reaches_symm (hr y))), row_edges_is_forest N⟩

/-- A genuine ordinary copied-edge spanning tree, also in the radius-zero box. -/
noncomputable def rowTree (N : ℕ) : (graph N).SpanningTree := ⟨rowEdges N, row_edges_is_tree N⟩

instance spanningTreeNonempty (N : ℕ) : Nonempty (graph N).SpanningTree := ⟨rowTree N⟩

end FiniteAvalanches.Sandpile.WiredTrees
