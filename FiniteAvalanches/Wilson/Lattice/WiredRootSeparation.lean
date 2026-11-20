import FiniteAvalanches.Wilson.Lattice.WiredRootedColorReduction

/-! Root separation in the ambient projections of finite wired forests. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- A selected ambient edge gives a connection in the copied wired forest. -/
theorem finiteForest_reaches_of_adj (R : RootPair) (B : ℕ) (F : FiniteForest R B)
    {x y : Site 2} (h : (toGraph (finiteEdgeField R B F)).Adj x y) :
    (WiredTrees.graph B).reaches F.val (wiredSite B x) (wiredSite B y) := by
  obtain ⟨hxy, he⟩ := h
  simp only [finiteEdgeField, decide_eq_true_eq] at he
  obtain ⟨i, hi, heq⟩ := he
  have hp := Sym2.eq_iff.mp (congrArg Subtype.val heq)
  have hreach : (WiredTrees.graph B).reaches F.val (some i.val.1) (some i.val.2) :=
    Relation.ReflTransGen.single ((wiredInterior_adjacent_iff B F.val i).mpr hi)
  have hsite (v : FiniteWired.Active B) : wiredSite B (FiniteWired.site v) = some v := by
    simpa only [wiredVertexSite] using wiredSite_wiredVertexSite B (some v)
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2, hsite, hsite]
    exact hreach
  · rw [← h2, ← h1, hsite, hsite]
    exact (WiredTrees.graph B).reaches_symm hreach

/-- Ambient reachability gives reachability of the wired site images. -/
theorem finiteForest_reaches_of_reachable (R : RootPair) (B : ℕ) (F : FiniteForest R B)
    {x y : Site 2} (h : (toGraph (finiteEdgeField R B F)).Reachable x y) :
    (WiredTrees.graph B).reaches F.val (wiredSite B x) (wiredSite B y) := by
  have hp := ((toGraph (finiteEdgeField R B F)).reachable_iff_reflTransGen x y).mp h
  clear h
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | tail hp he ih => exact ih.trans (finiteForest_reaches_of_adj R B F he)

/-- Distinct original roots inside the box cannot be connected by selected
ambient edges. -/
theorem finiteForest_roots_not_reachable (R : RootPair) (B : ℕ) (F : FiniteForest R B)
    {r s : Site 2} (hr : r ∈ R.zero ∪ R.one) (hs : s ∈ R.zero ∪ R.one)
    (hbr : FiniteWired.inBox B r) (hbs : FiniteWired.inBox B s) (hne : r ≠ s) :
    ¬(toGraph (finiteEdgeField R B F)).Reachable r s := by
  intro h
  have hw : (WiredTrees.graph B).reaches F.val (wiredSite B r) (wiredSite B s) :=
    finiteForest_reaches_of_reachable R B F h
  have hwr : wiredSite B r ∈ (wiredRoots R B).val := by
    rw [wiredSite, dif_pos hbr]
    change FiniteWired.site (FiniteWired.activeOfSite B r hbr) ∈ R.zero ∪ R.one
    simpa only [FiniteWired.site_activeOfSite] using hr
  have hws : wiredSite B s ∈ (wiredRoots R B).val := by
    rw [wiredSite, dif_pos hbs]
    change FiniteWired.site (FiniteWired.activeOfSite B s hbs) ∈ R.zero ∪ R.one
    simpa only [FiniteWired.site_activeOfSite] using hs
  obtain ⟨u, _, _, hu⟩ := F.property.2 (wiredSite B r)
  have heq : wiredSite B r = wiredSite B s :=
    (hu _ hwr Relation.ReflTransGen.refl).trans (hu _ hws hw).symm
  rw [wiredSite, dif_pos hbr, wiredSite, dif_pos hbs] at heq
  apply hne
  exact congrArg FiniteWired.site (Option.some.inj heq)

end
end FiniteAvalanches.Wilson.Lattice
