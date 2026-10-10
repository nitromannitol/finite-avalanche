import FiniteAvalanches.Electrical.ChordSplit.IdentifiedResponse
import FiniteAvalanches.Electrical.Reference.Voltage

/-! Applications on the actual punctured lattice copy carrier. -/
namespace ElectricalFollowup.Canonical
open FiniteAvalanches.Electrical FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.ChordSplit FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.Plane.SourceLattice LatticeProb
open scoped Classical
noncomputable section

/-- The canonical copied-geometry packaging of the unchanged lattice endpoints. -/
def latticeCopiedGraph (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :
    CopiedGraph (Vertex D P) (Copy D P marked) := ⟨copyA D P marked,copyB D P marked⟩

@[simp] theorem latticeCopiedGraph_left (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (e : Copy D P marked) :
    (latticeCopiedGraph D P marked).left e = copyA D P marked e := rfl

@[simp] theorem latticeCopiedGraph_right (D : Finset (Site 2)) (P : OneSet D)
    (marked : MarkedCopy D P) (e : Copy D P marked) :
    (latticeCopiedGraph D P marked).right e = copyB D P marked e := rfl

/-- The energy identity retains exactly the actual original lattice copy carrier. -/
theorem actual_identified_energy_eq_total_response
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) (side : Copy D P marked → Bool) :
    let J := latticeCopiedGraph D P marked
    let hc := (Repair8.graph_connected D P hD marked).preconnected
    let hbeta : beta D P ≠ alpha D P := by intro h; cases h
    energy (groundedSplitGraph J (alpha D P) (beta D P) side).left
      (groundedSplitGraph J (alpha D P) (beta D P) side).right
      (identifiedVoltage J (alpha D P) (beta D P) side hc) =
    responseEntry (splitGraph J (alpha D P) side).left (splitGraph J (alpha D P) side).right
      (splitTerminals (alpha D P) (beta D P) hbeta)
      (split_terminal_reachable J.left J.right (alpha D P) (beta D P) hbeta side hc) 1 1 := by
  exact identified_energy_eq_total_response (latticeCopiedGraph D P marked)
    (alpha D P) (beta D P) (by intro h; cases h) side
    (Repair8.graph_connected D P hD marked).preconnected

/-- Both literal contraction diagrams hold for every actual retained original ID. -/
theorem actual_original_copy_contractions
    (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P)
    (side : Copy D P marked → Bool) (e : Copy D P marked) :
    let J := latticeCopiedGraph D P marked
    let hbeta : beta D P ≠ alpha D P := by intro h; cases h
    let H := splitWithRadial J (alpha D P) (beta D P) hbeta side
    collapse (alpha D P) (H.left (.inl (.inl e))) = J.left e ∧
    collapse (alpha D P) (H.right (.inl (.inl e))) = J.right e ∧
    groundMap (alpha D P) (beta D P) (H.left (.inl (.inl e))) =
      (groundedSplitGraph J (alpha D P) (beta D P) side).left e ∧
    groundMap (alpha D P) (beta D P) (H.right (.inl (.inl e))) =
      (groundedSplitGraph J (alpha D P) (beta D P) side).right e := by
  let J := latticeCopiedGraph D P marked
  have hbeta : beta D P ≠ alpha D P := by intro h; cases h
  have hrad := contract_radial_recovers_augmented J (alpha D P) (beta D P) hbeta side (.inl e)
  have hmarked := contract_marked_is_grounded_split_plus_radial
    J (alpha D P) (beta D P) hbeta side (.inl e)
  exact ⟨hrad.1,hrad.2,hmarked.1,hmarked.2⟩

end
end ElectricalFollowup.Canonical
