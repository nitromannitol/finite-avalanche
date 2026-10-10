import FiniteAvalanches.Electrical.Reference.Lattice

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.Plane.SourceLattice
open LatticeProb
open FiniteAvalanches.Sandpile.FiniteWired (Direction step)
open scoped Classical
noncomputable section

variable (D : Finset (Site 2)) (P : OneSet D)

/-- The literal marked source edge from a one-site to its specified outside neighbor. -/
def markedBoundary (b : D) (hb : b ∈ P.val) (d : Direction)
    (hout : b.val + step d ∉ D) : MarkedCopy D P :=
  ⟨incidentID b.val d,by
    have hbeta : project D P b.val = beta D P :=
      (project_eq_beta_iff D P b.val).mpr (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
    have halpha : project D P (b.val + step d) = alpha D P :=
      (project_eq_alpha_iff D P _).mpr hout
    rcases d with ⟨i,c⟩
    cases c
    · left
      constructor
      · simpa [incidentID,originalA,step,sub_eq_add_neg] using halpha
      · simpa [incidentID,originalB] using hbeta
    · right
      constructor
      · simpa [incidentID,originalA] using hbeta
      · simpa [incidentID,originalB,step] using halpha⟩

@[simp] theorem markedBoundary_ID (b : D) (hb : b ∈ P.val) (d : Direction)
    (hout : b.val + step d ∉ D) :
    (markedBoundary D P b hb d hout).val = incidentID b.val d := rfl

theorem markedBoundary_deleted (b : D) (hb : b ∈ P.val) (d : Direction)
    (hout : b.val + step d ∉ D) :
    incidentID b.val d ∉ retainedCopies D P (markedBoundary D P b hb d hout) := by
  simp [mem_retainedCopies,markedBoundary_ID]

/-- The exact source boundary marking consumes the proved copied free-degree bridge. -/
theorem source_boundary_free_degree (b : D) (hb : b ∈ P.val) (d : Direction)
    (hout : b.val + step d ∉ D) (x : {x : D // x ∉ P.val}) :
    Geometry.degree (copyA D P (markedBoundary D P b hb d hout))
      (copyB D P (markedBoundary D P b hb d hout)) (.inr x) = 4 :=
  free_degree D P (markedBoundary D P b hb d hout) x

end
end FiniteAvalanches.Electrical.Plane.SourceLattice
