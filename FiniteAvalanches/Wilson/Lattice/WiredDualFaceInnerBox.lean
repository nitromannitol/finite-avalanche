import FiniteAvalanches.Wilson.Lattice.WiredDualFaceConnected
import FiniteAvalanches.Wilson.Lattice.FreeBoxGraph

/-! The centered free box as a subgraph of the shifted dual face square. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- Every site in the centered wired box lies in the shifted face square. -/
theorem inDualFaceBox_of_inBox (B : ℕ) (z : Site 2) (hz : FiniteWired.inBox B z) :
    inDualFaceBox B z := by
  intro i
  have h := hz i
  omega

/-- Include a centered-box vertex into the shifted dual face square. -/
def wiredDualFaceInnerVertex (B : ℕ) (v : FiniteWired.Active B) : WiredDualFace B :=
  wiredDualFaceOfSite B (FiniteWired.site v)
    (inDualFaceBox_of_inBox B (FiniteWired.site v) (fun i => (v i).property))

/-- Inclusion of centered-box vertices preserves the lattice label. -/
theorem wiredDualFaceSite_innerVertex (B : ℕ) (v : FiniteWired.Active B) :
    wiredDualFaceSite (wiredDualFaceInnerVertex B v) = FiniteWired.site v := rfl

/-- The centered-box vertex inclusion is injective. -/
theorem wiredDualFaceInnerVertex_injective (B : ℕ) :
    Function.Injective (wiredDualFaceInnerVertex B) := by
  intro v w h
  apply FiniteWired.site_injective B
  exact congrArg wiredDualFaceSite h

/-- The edge of the face square with the same lattice label as a centered-box edge. -/
def wiredDualFaceInnerCopy (B : ℕ) (e : FiniteWired.InteriorEdge B) : FiniteWired.Edge B :=
  (wiredCopyDualFaceEdgeEquiv B).symm ⟨interiorEdge e, by
    intro z hz
    have hz' : z = FiniteWired.site e.val.1 ∨ z = FiniteWired.site e.val.2 := by
      simpa only [interiorEdge, Sym2.mem_iff] using hz
    rcases hz' with rfl | rfl
    · exact inDualFaceBox_of_inBox B _ (fun i => (e.val.1 i).property)
    · exact inDualFaceBox_of_inBox B _ (fun i => (e.val.2 i).property)⟩

/-- The included copy has the same underlying lattice edge. -/
theorem wiredCopyDualEdge_innerCopy (B : ℕ) (e : FiniteWired.InteriorEdge B) :
    wiredCopyDualEdge (wiredDualFaceInnerCopy B e) = interiorEdge e := by
  exact congrArg Subtype.val ((wiredCopyDualFaceEdgeEquiv B).apply_symm_apply _)

/-- Distinct centered-box edge copies remain distinct in the face square. -/
theorem wiredDualFaceInnerCopy_injective (B : ℕ) :
    Function.Injective (wiredDualFaceInnerCopy B) := by
  intro e f h
  apply interiorEdge_injective B
  rw [← wiredCopyDualEdge_innerCopy B e, ← wiredCopyDualEdge_innerCopy B f, h]

/-- The included edge has exactly the included endpoints, up to orientation. -/
theorem wiredDualFaceInnerCopy_endpoints (B : ℕ) (e : FiniteWired.InteriorEdge B) :
    s((wiredDualFaceGraph B).left (wiredDualFaceInnerCopy B e),
      (wiredDualFaceGraph B).right (wiredDualFaceInnerCopy B e)) =
    s(wiredDualFaceInnerVertex B ((freeBoxGraph B).left e),
      wiredDualFaceInnerVertex B ((freeBoxGraph B).right e)) := by
  apply Sym2.map.injective (wiredDualFaceSite_injective B)
  rw [Sym2.map_mk, wiredDualFaceGraph_edge, wiredCopyDualEdge_innerCopy, Sym2.map_mk]
  rfl

/-- A face-square copy lies in the centered induced subgraph precisely when
it comes from a centered-box edge copy. -/
theorem wiredDualFaceInnerCopy_range_iff (B : ℕ) (q : FiniteWired.Edge B) :
    (∃ e : FiniteWired.InteriorEdge B, wiredDualFaceInnerCopy B e = q) ↔
      ∀ z ∈ (wiredCopyDualEdge q).val, FiniteWired.inBox B z := by
  constructor
  · rintro ⟨e, rfl⟩ z hz
    rw [wiredCopyDualEdge_innerCopy] at hz
    have hz' : z = FiniteWired.site e.val.1 ∨ z = FiniteWired.site e.val.2 := by
      simpa only [interiorEdge, Sym2.mem_iff] using hz
    rcases hz' with rfl | rfl
    · exact fun i => (e.val.1 i).property
    · exact fun i => (e.val.2 i).property
  · intro hq
    obtain ⟨e, he⟩ := exists_interiorEdge_of_inBox B (wiredCopyDualEdge q) hq
    refine ⟨e, wiredCopyDualEdge_injective B ?_⟩
    rw [wiredCopyDualEdge_innerCopy, he]

end
end FiniteAvalanches.Wilson.Lattice
