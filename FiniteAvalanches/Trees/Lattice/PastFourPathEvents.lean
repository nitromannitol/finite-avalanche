import FiniteAvalanches.Trees.Lattice.PastEscapeGeometry
import FiniteAvalanches.Trees.Lattice.InfiniteLawProperties

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice.PastTail
open LatticeProb SimpleGraph MeasureTheory FiniteAvalanches.Trees.Lattice
open scoped Classical
noncomputable section

/-- The four original incident edges at a source, named by direction and sign. -/
def incidentBase (v : Site 2) (j : Fin 2 × Bool) : Site 2 × Fin 2 :=
  (if j.2 then v - unit j.1 else v, j.1)

/-- An unconditional fixed adjacent dual-path escape event. -/
def adjacentDualEscape (v : Site 2) (j : Fin 2 × Bool) (k : ℝ) : Set EdgeField :=
  let d := dualBaseInv (incidentBase v j)
  {ω | dualField ω ∈ BarlowMasson.treePathLeavesEuclidean (d.1 + unit d.2) d.1 k}

theorem measurableSet_adjacentDualEscape (v : Site 2) (j : Fin 2 × Bool) (k : ℝ) :
    MeasurableSet (adjacentDualEscape v j k) :=
  (BarlowMasson.measurableSet_treePathLeavesEuclidean _ _ _).preimage measurable_dualField

theorem outgoingEdge_one_of_four (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (v : Site 2) :
    ∃ j : Fin 2 × Bool, incidentBase v j = edgeEquiv.symm (outgoingEdge ω hT hOne v) := by
  let p := edgeEquiv.symm (outgoingEdge ω hT hOne v)
  have hp : baseEdge p = outgoingEdge ω hT hOne v := edgeEquiv.apply_symm_apply _
  have he := congrArg Subtype.val hp
  change s(p.1, p.1 + unit p.2) = s(v, towardEnd ω hT hOne v) at he
  rcases Sym2.eq_iff.mp he with ⟨hleft, _⟩ | ⟨_, hright⟩
  · refine ⟨(p.2, false), Prod.ext ?_ rfl⟩
    exact hleft.symm
  · refine ⟨(p.2, true), Prod.ext ?_ rfl⟩
    change v - unit p.2 = p.1
    rw [← hright, add_sub_cancel_right]

/-- Pointwise inclusion on the actual common primal/dual tree domain; the union
has exactly the four fixed incident edges and imposes no outgoing-edge condition. -/
theorem pastEscapesSup_mem_four_paths (ω : EdgeField) (hT : IsTree ω)
    (hOne : OneEnded ω) (hDual : IsTree (dualField ω)) (v : Site 2)
    (m : ℝ) (hm : 2 ≤ m) (hEscape : ω ∈ pastEscapesSup v m) :
    ω ∈ ⋃ j : Fin 2 × Bool, adjacentDualEscape v j (m / 2) := by
  obtain ⟨j, hj⟩ := outgoingEdge_one_of_four ω hT hOne v
  have h := vertexPast_escape_dual_selected_path ω hT hOne hDual v m hm
    ((mem_pastEscapesSup_iff ω hT hOne v m).mp hEscape)
  apply Set.mem_iUnion.mpr
  refine ⟨j, ?_⟩
  change dualField ω ∈ BarlowMasson.treePathLeavesEuclidean
    ((dualBaseInv (incidentBase v j)).1 + unit (dualBaseInv (incidentBase v j)).2)
    (dualBaseInv (incidentBase v j)).1 (m / 2)
  rw [hj]
  exact h

/-- One genuine UST witness precedes all sources and all real radii. -/
theorem squareLatticeUST_ae_four_path_reduction :
    ∀ᵐ ω ∂(squareLatticeUST : Measure EdgeField),
      ∃ _hT : IsTree ω, ∃ _hOne : OneEnded ω, ∃ _hDual : IsTree (dualField ω),
      ∀ v : Site 2, ∀ m : ℝ, 2 ≤ m → ω ∈ pastEscapesSup v m →
        ω ∈ ⋃ j : Fin 2 × Bool, adjacentDualEscape v j (m / 2) := by
  have hTree : ∀ᵐ ω ∂(squareLatticeUST : Measure EdgeField), IsTree ω :=
    squareLatticeUST_ae_tree_oneEnded.mono fun _ h => h.1
  have hMap : ∀ᵐ ω ∂((squareLatticeUST : Measure EdgeField).map dualField), IsTree ω := by
    rw [squareLatticeUST_dual_law]
    exact hTree
  have hDual : ∀ᵐ ω ∂(squareLatticeUST : Measure EdgeField), IsTree (dualField ω) :=
    (ae_map_iff measurable_dualField.aemeasurable BarlowMasson.measurableSet_isTree).mp hMap
  filter_upwards [squareLatticeUST_ae_tree_oneEnded, hDual] with ω hω hd
  exact ⟨hω.1, hω.2, hd, fun v m hm hEscape =>
    pastEscapesSup_mem_four_paths ω hω.1 hω.2 hd v m hm hEscape⟩

end
end FiniteAvalanches.Trees.Lattice.PastTail
