import FiniteAvalanches.Wilson.Lattice.WiredLimitDualDetours
import FiniteAvalanches.Wilson.Lattice.WiredDualFaceEdges
import FiniteAvalanches.Wilson.Lattice.LatticeBranchHorizon

/-! Finite dual detours fit into a sufficiently large wired-box face graph. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees.Lattice
open scoped Classical

noncomputable section

/-- A finite dual lattice walk and its endpoint edge are represented by copies
in every sufficiently large wired-box face graph. -/
theorem dualWalk_eventually_has_face_copies (u v : Site 2) (d : LatticeEdge)
    (hpair : d.val = s(u, v)) (p : (lattice 2).Walk u v) :
    ∀ᶠ B : ℕ in atTop,
      (∃ q : FiniteWired.Edge B, wiredCopyDualEdge q = d) ∧
      ∀ f : LatticeEdge, f.val ∈ p.edges →
        ∃ q : FiniteWired.Edge B, wiredCopyDualEdge q = f := by
  have hsites : ∀ᶠ B : ℕ in atTop, ∀ z : {z // z ∈ p.support}, FiniteWired.inBox B z.val :=
    eventually_all.mpr (fun z => eventually_finiteWired_inBox z.val)
  filter_upwards [hsites] with B hB
  have hsupport : ∀ z ∈ p.support, inDualFaceBox B z := by
    intro z hz
    exact inDualFaceBox_of_inBox B z (hB ⟨z, hz⟩)
  constructor
  · apply (dualFaceEdge_iff_wiredCopy B d).mp
    intro z hz
    rw [hpair] at hz
    rcases Sym2.mem_iff.mp hz with hz | hz
    · subst z
      exact hsupport u p.start_mem_support
    · subst z
      exact hsupport v p.end_mem_support
  · intro f hf
    apply (dualFaceEdge_iff_wiredCopy B f).mp
    intro z hz
    exact hsupport z (SimpleGraph.Walk.mem_support_of_mem_edges hf hz)

/-- Every finite selected dual detour and the crossed dual edge have original
face copies in all sufficiently large wired boxes. -/
theorem dualDetour_eventually_has_face_copies (ω : EdgeField) (d : LatticeEdge)
    (p : (toGraph (dualField ω)).Walk d.val.out.1 d.val.out.2) :
    ∀ᶠ B : ℕ in atTop,
      (∃ q : FiniteWired.Edge B, wiredCopyDualEdge q = d) ∧
      ∀ f : LatticeEdge, f.val ∈ p.edges →
        ∃ q : FiniteWired.Edge B, wiredCopyDualEdge q = f := by
  let q := p.mapLe (toGraph_le_lattice (dualField ω))
  have h := dualWalk_eventually_has_face_copies d.val.out.1 d.val.out.2 d d.val.out_eq.symm q
  filter_upwards [h] with B hB
  refine ⟨hB.1, ?_⟩
  intro f hf
  apply hB.2 f
  simpa only [q, SimpleGraph.Walk.edges_mapLe_eq_edges] using hf

end
end FiniteAvalanches.Wilson.Lattice
