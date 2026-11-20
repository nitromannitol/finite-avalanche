import FiniteAvalanches.Wilson.Lattice.WiredCylinderRootColors
import FiniteAvalanches.Wilson.Lattice.WiredObservationGeometry

/-! Colors agree across every selected edge of a finite wired forest. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- Vertices connected in a wired forest have the same component color. -/
theorem finiteColors_eq_of_reaches (R : RootPair) (B : ℕ) (F : FiniteForest R B)
    (v w : FiniteWired.Vertex B) (h : (WiredTrees.graph B).reaches F.val v w) :
    finiteColors R B F v = finiteColors R B F w := by
  apply Bool.eq_iff_iff.mpr
  simp only [finiteColors, decide_eq_true_eq]
  constructor
  · rintro ⟨r, hr, hvr⟩
    exact ⟨r, hr, ((WiredTrees.graph B).reaches_symm h).trans hvr⟩
  · rintro ⟨r, hr, hwr⟩
    exact ⟨r, hr, h.trans hwr⟩

/-- The endpoint colors agree whenever a lattice edge is selected by a finite
wired forest field. -/
theorem finiteForestField_edge_colors_eq (R : RootPair) (B : ℕ) (F : FiniteForest R B)
    (x y : Site 2) (hxy : (lattice 2).Adj x y)
    (he : finiteEdgeField R B F ⟨s(x, y), hxy⟩ = true) :
    finiteColors R B F (wiredSite B x) = finiteColors R B F (wiredSite B y) := by
  simp only [finiteEdgeField, decide_eq_true_eq] at he
  obtain ⟨i, hi, heq⟩ := he
  have hp := Sym2.eq_iff.mp (congrArg Subtype.val heq)
  have hreach : (WiredTrees.graph B).reaches F.val (some i.val.1) (some i.val.2) :=
    Relation.ReflTransGen.single ((wiredInterior_adjacent_iff B F.val i).mpr hi)
  have hc := finiteColors_eq_of_reaches R B F _ _ hreach
  have hsite (v : FiniteWired.Active B) : wiredSite B (FiniteWired.site v) = some v := by
    simpa only [wiredVertexSite] using wiredSite_wiredVertexSite B (some v)
  change finiteColors R B F (wiredSite B x) = finiteColors R B F (wiredSite B y)
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2, hsite, hsite]
    exact hc
  · rw [← h2, ← h1, hsite, hsite]
    exact hc.symm

end
end FiniteAvalanches.Wilson.Lattice
