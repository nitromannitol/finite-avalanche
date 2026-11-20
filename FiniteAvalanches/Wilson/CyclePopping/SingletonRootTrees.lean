import FiniteAvalanches.Wilson.CyclePopping.IncidentForestLaw
import FiniteAvalanches.Trees.Ancestors

/-! A single rooted component is an ordinary spanning tree. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open FiniteAvalanches.Trees MeasureTheory
open scoped Classical ENNReal

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E]

/-- A copied forest rooted at one vertex is exactly a copied spanning tree. -/
theorem rootedForest_singleton_iff_tree (G : Multigraph V E) (r : V) (F : Finset E) :
    G.is_rooted_forest {r} F ↔ G.is_tree Set.univ F := by
  constructor
  · intro h
    refine ⟨⟨r, Set.mem_univ r⟩, ?_, ?_, h.1⟩
    · intro e he
      exact ⟨Set.mem_univ _, Set.mem_univ _⟩
    · intro x _ y _
      obtain ⟨rx, hrx, hxr, _⟩ := h.2 x
      obtain ⟨ry, hry, hyr, _⟩ := h.2 y
      have hx : rx = r := Set.mem_singleton_iff.mp hrx
      have hy : ry = r := Set.mem_singleton_iff.mp hry
      rw [hx] at hxr
      rw [hy] at hyr
      exact hxr.trans (G.reaches_symm hyr)
  · intro h
    refine ⟨h.2.2.2, ?_⟩
    intro x
    refine ⟨r, Set.mem_singleton r, h.2.2.1 x (Set.mem_univ x) r (Set.mem_univ r), ?_⟩
    intro r' hr' _
    exact Set.mem_singleton_iff.mp hr'

/-- The singleton-rooted forest carrier and the spanning-tree carrier agree
on their original copied-edge sets. -/
def singletonRootedForestEquiv (G : Multigraph V E) (r : V) :
    G.RootedForest {r} ≃ G.SpanningTree where
  toFun F := ⟨F.val, (rootedForest_singleton_iff_tree G r F.val).mp F.property⟩
  invFun T := ⟨T.val, (rootedForest_singleton_iff_tree G r T.val).mpr T.property⟩
  left_inv F := by apply Subtype.ext; rfl
  right_inv T := by apply Subtype.ext; rfl

/-- With one prescribed root, cycle popping samples the original-copy spanning
tree law, allowing arbitrary vertex degrees and parallel edge copies. -/
theorem variableStackLaw_spanningTreeEvent_eq [DecidableEq V] (G : Multigraph V E)
    [∀ v, Nonempty (IncidentCopy G v)] (r : V) (k : Cursor V) (S : Set G.SpanningTree) :
    variableStackLaw (IncidentCopy G)
      {σ | ∃ a : GoodIncidentArrows G {r},
        singletonRootedForestEquiv G r (incidentArrowForest G {r} a) ∈ S ∧
        σ ∈ terminalOutputEvent {r} (incidentCopyHead G) k (fun v i σ => σ (v, i)) a} =
      (Nat.card S : ℝ≥0∞) / (Fintype.card G.SpanningTree : ℝ≥0∞) := by
  let e := singletonRootedForestEquiv G r
  have hcard : Nat.card (e ⁻¹' S) = Nat.card S :=
    Nat.card_preimage_of_injective e.injective (by rw [e.surjective.range_eq]; exact Set.subset_univ S)
  have htotal : Fintype.card (G.RootedForest {r}) = Fintype.card G.SpanningTree :=
    Fintype.card_congr e
  have h := variableStackLaw_incidentForestEvent_eq G {r} k (e ⁻¹' S)
  simpa only [Set.mem_preimage, hcard, htotal] using h

end
end FiniteAvalanches.Wilson.CyclePopping
