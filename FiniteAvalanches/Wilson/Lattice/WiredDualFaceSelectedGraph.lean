import FiniteAvalanches.Wilson.Lattice.WiredLimitDualDetourBox

/-! The selected dual lattice graph restricted to the finite face square. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

local instance decEqWiredEdgeDualFaceSelectedGraph (B : ℕ) :
    DecidableEq (FiniteWired.Edge B) := Classical.decEq _

/-- Original copies whose crossing dual lattice edge is selected. -/
def wiredDualFaceSelectedCopies (B : ℕ) (ω : EdgeField) : Finset (FiniteWired.Edge B) :=
  Finset.univ.filter (fun q => dualField ω (wiredCopyDualEdge q) = true)

/-- Selected face-copy adjacency is exactly selected dual lattice adjacency
between the corresponding face labels. -/
theorem wiredDualFaceSelectedCopies_adjacent_iff (B : ℕ) (ω : EdgeField)
    (v w : WiredDualFace B) :
    (wiredDualFaceGraph B).adjacent (wiredDualFaceSelectedCopies B ω) v w ↔
      (toGraph (dualField ω)).Adj (wiredDualFaceSite v) (wiredDualFaceSite w) := by
  constructor
  · rintro ⟨q, hq, hends⟩
    have hval : dualField ω (wiredCopyDualEdge q) = true := (Finset.mem_filter.mp hq).2
    have hmem := (edge_mem_toGraph_iff (dualField ω) (wiredCopyDualEdge q)).mpr hval
    change s(wiredDualFaceSite v, wiredDualFaceSite w) ∈ (toGraph (dualField ω)).edgeSet
    rw [← wiredDualFaceGraph_edge] at hmem
    rcases hends with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · simpa only [hl, hr] using hmem
    · simpa only [hl, hr, Sym2.eq_swap] using hmem
  · intro hadj
    have hlattice : (lattice 2).Adj (wiredDualFaceSite v) (wiredDualFaceSite w) :=
      toGraph_le_lattice (dualField ω) hadj
    obtain ⟨q, _, hends⟩ := (wiredDualFaceGraph_adjacent_iff B v w).mpr hlattice
    let e : LatticeEdge := ⟨s(wiredDualFaceSite v, wiredDualFaceSite w), hlattice⟩
    have he : wiredCopyDualEdge q = e := by
      apply Subtype.ext
      rw [← wiredDualFaceGraph_edge]
      change s(wiredDualFaceSite ((wiredDualFaceGraph B).left q),
        wiredDualFaceSite ((wiredDualFaceGraph B).right q)) =
          s(wiredDualFaceSite v, wiredDualFaceSite w)
      rcases hends with ⟨hl, hr⟩ | ⟨hr, hl⟩
      · simpa only [hl, hr]
      · simpa only [hl, hr] using (Sym2.eq_swap :
          s(wiredDualFaceSite w, wiredDualFaceSite v) = s(wiredDualFaceSite v, wiredDualFaceSite w))
    have hval : dualField ω (wiredCopyDualEdge q) = true := by
      rw [he]
      exact (edge_mem_toGraph_iff (dualField ω) e).mp hadj
    exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hval⟩, hends⟩

end
end FiniteAvalanches.Wilson.Lattice
