import FiniteAvalanches.Wilson.Lattice.WiredRootSeparationLimit

/-! Acyclicity of finite wired forests as ambient lattice fields. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice

open LatticeProb MeasureTheory Filter FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice FiniteAvalanches.Wilson.CyclePopping
open scoped Classical

noncomputable section

/-- A selected ambient edge has both endpoints inside the wired box. -/
theorem finiteEdgeField_adj_inBox (R : RootPair) (B : ℕ) (F : FiniteForest R B)
    {x y : Site 2} (h : (toGraph (finiteEdgeField R B F)).Adj x y) :
    FiniteWired.inBox B x ∧ FiniteWired.inBox B y := by
  obtain ⟨_, he⟩ := h
  simp only [finiteEdgeField, decide_eq_true_eq] at he
  obtain ⟨i, _, heq⟩ := he
  have hp := Sym2.eq_iff.mp (congrArg Subtype.val heq)
  have hi (v : FiniteWired.Active B) : FiniteWired.inBox B (FiniteWired.site v) :=
    fun j => (v j).property
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1 ▸ hi i.val.1, h2 ▸ hi i.val.2⟩
  · exact ⟨h2 ▸ hi i.val.2, h1 ▸ hi i.val.1⟩

/-- Every selected ambient edge maps to an edge of the copied wired forest. -/
theorem finiteForest_adj_of_adj (R : RootPair) (B : ℕ) (F : FiniteForest R B)
    {x y : Site 2} (h : (toGraph (finiteEdgeField R B F)).Adj x y) :
    (WiredTrees.graph B).adjacent F.val (wiredSite B x) (wiredSite B y) := by
  obtain ⟨_, he⟩ := h
  simp only [finiteEdgeField, decide_eq_true_eq] at he
  obtain ⟨i, hi, heq⟩ := he
  have hp := Sym2.eq_iff.mp (congrArg Subtype.val heq)
  have hreach : (WiredTrees.graph B).adjacent F.val (some i.val.1) (some i.val.2) :=
    (wiredInterior_adjacent_iff B F.val i).mpr hi
  have hsite (v : FiniteWired.Active B) : wiredSite B (FiniteWired.site v) = some v := by
    simpa only [wiredVertexSite] using wiredSite_wiredVertexSite B (some v)
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [← h1, ← h2, hsite, hsite]
    exact hreach
  · rw [← h2, ← h1, hsite, hsite]
    exact (WiredTrees.graph B).adjacent_symm hreach

/-- The finite ambient edge field is acyclic, including its isolated exterior. -/
theorem finiteEdgeField_isAcyclic (R : RootPair) (B : ℕ) (F : FiniteForest R B) :
    (toGraph (finiteEdgeField R B F)).IsAcyclic := by
  let G := toGraph (finiteEdgeField R B F)
  let S : Set (Site 2) := {x | FiniteWired.inBox B x}
  let f : G.induce S →g (WiredTrees.graph B).toSimple F.val :=
    { toFun := fun x => wiredSite B x.val
      map_rel' := fun h => finiteForest_adj_of_adj R B F h }
  have hinj : Function.Injective f := by
    intro x y he
    change wiredSite B x.val = wiredSite B y.val at he
    have hx : FiniteWired.inBox B x.val := x.property
    have hy : FiniteWired.inBox B y.val := y.property
    rw [wiredSite, dif_pos hx, wiredSite, dif_pos hy] at he
    apply Subtype.ext
    exact congrArg FiniteWired.site (Option.some.inj he)
  have ha : (G.induce S).IsAcyclic :=
    ((WiredTrees.graph B).toSimple_isAcyclic F.property.1).comap f hinj
  intro x p hp
  have hS : ∀ z ∈ p.support, z ∈ S := by
    intro z hz
    obtain ⟨e, he, hze⟩ := (p.mem_support_iff_exists_mem_edges_of_not_nil hp.not_nil).mp hz
    have heG := p.edges_subset_edgeSet he
    induction e using Sym2.inductionOn with
    | _ a b =>
      have hab : G.Adj a b := heG
      have hbox := finiteEdgeField_adj_inBox R B F hab
      rcases Sym2.mem_iff.mp hze with rfl | rfl
      · exact hbox.1
      · exact hbox.2
  let q := p.induce S hS
  have hq : q.IsCycle := by
    apply SimpleGraph.Walk.IsCycle.of_map (f := (SimpleGraph.Embedding.induce S).toHom)
    change ((p.induce S hS).map (SimpleGraph.Embedding.induce S).toHom).IsCycle
    rw [SimpleGraph.Walk.map_induce]
    exact hp
  exact ha q hq

end
end FiniteAvalanches.Wilson.Lattice
