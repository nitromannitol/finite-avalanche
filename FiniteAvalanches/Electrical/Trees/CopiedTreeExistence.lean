import FiniteAvalanches.Electrical.Geometry.CopiedGraphConnectivity
import Mathlib.Data.Finset.Max

/-! Spanning trees of the full original copied graph, including loops and parallel IDs. -/
namespace FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
open scoped Classical

/-- A connected nonempty copied graph has a tree on its full original carrier. -/
theorem nonempty_spanningTree_of_reaches {V E : Type} [Fintype V] [Fintype E]
    [Nonempty V] (J : CopiedGraph V E)
    (hconn : ∀ x y : V, J.reaches Finset.univ x y) : Nonempty J.SpanningTree := by
  let candidates : Finset (Finset E) :=
    Finset.univ.filter (fun F => ∀ x y : V, J.reaches F x y)
  have inhabited : candidates.Nonempty :=
    ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hconn⟩⟩
  obtain ⟨F, hF, hminimal⟩ := candidates.exists_min_image Finset.card inhabited
  have connected : ∀ x y : V, J.reaches F x y := (Finset.mem_filter.mp hF).2
  refine ⟨⟨F, Set.univ_nonempty, connected, ?_⟩⟩
  intro e he hcycle
  have smaller : F.erase e ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun x y =>
      J.reaches_erase_of_alternative e hcycle (connected x y)⟩
  exact (Nat.not_le_of_lt (Finset.card_erase_lt_of_mem he))
    (hminimal (F.erase e) smaller)

end FiniteAvalanches.Electrical.StatementGeometry.CopiedGraph
