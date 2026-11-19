import FiniteAvalanches.Trees.RootedForests

/-! Root-distance ranks and minimality for finite copied rooted forests. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open FiniteAvalanches.Trees
open scoped Classical

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E]

/-- A copied-edge walk of a specified length from a vertex to the roots. -/
def rootWalk (G : Multigraph V E) (F : Finset E) (R : Set V) : V → ℕ → Prop
  | x, 0 => x ∈ R
  | x, n + 1 => ∃ y, G.adjacent F x y ∧ rootWalk G F R y n

/-- Any finite copied-edge walk to a root has a finite length. -/
theorem exists_rootWalk (G : Multigraph V E) (F : Finset E) (R : Set V)
    {x r : V} (hr : r ∈ R) (h : G.reaches F x r) : ∃ n, rootWalk G F R x n := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, hr⟩
  | @head x y hxy hyr ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, y, hxy, hn⟩

/-- Every vertex of a rooted forest has a finite walk to a root. -/
theorem rootedForest_has_rootWalk (G : Multigraph V E) (R : Set V)
    (F : G.RootedForest R) (x : V) : ∃ n, rootWalk G F.val R x n := by
  obtain ⟨r, hr, hxr, _⟩ := F.property.2 x
  exact exists_rootWalk G F.val R hr hxr

/-- The shortest copied-edge distance to the root set. -/
def forestRootRank (G : Multigraph V E) (R : Set V) (F : G.RootedForest R) (x : V) : ℕ :=
  Nat.find (rootedForest_has_rootWalk G R F x)

/-- Every nonroot has a forest neighbor of smaller root-distance rank. -/
theorem forestRootRank_descends (G : Multigraph V E) (R : Set V)
    (F : G.RootedForest R) {x : V} (hx : x ∉ R) :
    ∃ y, G.adjacent F.val x y ∧ forestRootRank G R F y < forestRootRank G R F x := by
  have hspec := Nat.find_spec (rootedForest_has_rootWalk G R F x)
  change rootWalk G F.val R x (forestRootRank G R F x) at hspec
  cases hn : forestRootRank G R F x with
  | zero =>
    rw [hn] at hspec
    exact (hx hspec).elim
  | succ n =>
    rw [hn] at hspec
    obtain ⟨y, hxy, hy⟩ := hspec
    refine ⟨y, hxy, ?_⟩
    have hmin := Nat.find_min' (rootedForest_has_rootWalk G R F y) hy
    change forestRootRank G R F y ≤ n at hmin
    omega

/-- A rooted forest has no proper rooted subforest with the same roots. -/
theorem rootedForest_eq_of_subset (G : Multigraph V E) (R : Set V)
    (F H : G.RootedForest R) (hHF : H.val ⊆ F.val) : H = F := by
  apply Subtype.ext
  apply Finset.Subset.antisymm hHF
  intro e he
  by_contra hnot
  obtain ⟨r, hr, hlr, _⟩ := H.property.2 (G.left e)
  obtain ⟨s, hs, hrs, _⟩ := H.property.2 (G.right e)
  have hed : G.reaches F.val (G.left e) (G.right e) :=
    .single ⟨e, he, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨q, _, _, hq⟩ := F.property.2 (G.left e)
  have heq : r = s := (hq r hr (G.reaches_mono hHF hlr)).trans
    (hq s hs (hed.trans (G.reaches_mono hHF hrs))).symm
  have hre : G.reaches H.val (G.left e) (G.right e) :=
    hlr.trans (G.reaches_symm (heq ▸ hrs))
  have hsub : H.val ⊆ F.val.erase e := by
    intro f hf
    exact Finset.mem_erase.mpr ⟨fun h => hnot (h ▸ hf), hHF hf⟩
  exact F.property.1 e he (G.reaches_mono hsub hre)

end
end FiniteAvalanches.Wilson.CyclePopping
