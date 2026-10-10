import FiniteAvalanches.Electrical.Reference.NoBridges
import FiniteAvalanches.Sandpile.WiredTermination

set_option autoImplicit false
namespace JointBoundarySize
open LatticeProb FiniteAvalanches.Electrical.Plane.SourceLattice
open FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

theorem exits_card_le_four_card (D : Finset (Site 2)) :
    (latticeExits D).card ≤ 4*D.card := by
  calc
    _ ≤ (domainCopies D).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ (D ×ˢ (Finset.univ : Finset FiniteWired.Direction)).card := Finset.card_image_le
    _ = 4*D.card := by simp only [Finset.card_product, Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; omega

theorem reference_boundary_le_cube (r : ℕ) (hr : 100 ≤ r) (D : Finset (Site 2))
    (hD : (D : Set (Site 2)) ⊆ (boxSites (2*r-1) : Set (Site 2))) :
    (latticeExits D).card-1 ≤ r^3 := by
  have hcard := Finset.card_le_card hD
  rw [card_box_sites] at hcard
  have hsub : 2*(2*r-1)+1 ≤ 4*r := by omega
  have hsq : (2*(2*r-1)+1)^2 ≤ (4*r)^2 := Nat.pow_le_pow_left hsub 2
  have hbound : 4*D.card ≤ r^3 := by
    have hh : 4*(4*r)^2 ≤ r^3 := by nlinarith only [hr]
    exact (Nat.mul_le_mul_left 4 (hcard.trans hsq)).trans hh
  exact (Nat.sub_le _ _).trans ((exits_card_le_four_card D).trans hbound)

end
end JointBoundarySize
