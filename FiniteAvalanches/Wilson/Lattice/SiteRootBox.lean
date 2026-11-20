import FiniteAvalanches.Wilson.Lattice.SiteRootLaw
import FiniteAvalanches.Trees.Lattice.WiredLaw

/-! When the unrooted set is the whole wired box, the rooted forests are the spanning
trees of the wired box, and the lattice edge law is the wired uniform spanning tree law
`finiteLaw` of the box. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.Lattice.SiteRoots

open LatticeProb MeasureTheory FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Trees.Lattice
open scoped Classical ENNReal

noncomputable section

/-- The sites of the box `[-N, N]²`. -/
def boxSet (N : ℕ) : Set (Site 2) := {x | FiniteWired.inBox N x}

theorem roots_boxSet (N : ℕ) : (roots (boxSet N) N).val = {none} := by
  ext v
  cases v with
  | none => simp only [Set.mem_singleton_iff, iff_true]; trivial
  | some x =>
    simp only [Set.mem_singleton_iff, reduceCtorEq, iff_false]
    exact fun h => h (fun i => (x i).property)

theorem isRootedForest_singleton_iff {V E : Type} [Fintype V] [Fintype E]
    (G : Multigraph V E) (r : V) (F : Finset E) :
    G.is_rooted_forest {r} F ↔ G.is_tree Set.univ F := by
  constructor
  · rintro ⟨hf, hr⟩
    have hx : ∀ x, G.reaches F x r := by
      intro x
      obtain ⟨r', hr', hxr, -⟩ := hr x
      rw [Set.mem_singleton_iff] at hr'
      exact hr' ▸ hxr
    exact ⟨⟨r, Set.mem_univ r⟩, fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩,
      fun x _ y _ => (hx x).trans (G.reaches_symm (hx y)), hf⟩
  · rintro ⟨-, -, hc, hf⟩
    exact ⟨hf, fun x => ⟨r, rfl, hc x (Set.mem_univ x) r (Set.mem_univ r),
      fun r' hr' _ => hr'⟩⟩

theorem isRootedForest_boxSet_iff (N : ℕ) (F : Finset (FiniteWired.Edge N)) :
    (WiredTrees.graph N).is_rooted_forest (roots (boxSet N) N).val F ↔
      (WiredTrees.graph N).is_tree Set.univ F := by
  rw [roots_boxSet N]
  exact isRootedForest_singleton_iff _ none F

/-- Rooted forests of the whole box are the spanning trees of the wired box. -/
def boxForestEquiv (N : ℕ) : Forest (boxSet N) N ≃ (WiredTrees.graph N).SpanningTree :=
  Equiv.subtypeEquivRight (isRootedForest_boxSet_iff N)

@[simp] theorem boxForestEquiv_val (N : ℕ) (F : Forest (boxSet N) N) :
    (boxForestEquiv N F).val = F.val := rfl

theorem forestField_boxSet (N : ℕ) (t : (WiredTrees.graph N).SpanningTree) :
    forestField (boxSet N) t.val = wiredField t := by
  funext e
  apply Bool.eq_iff_iff.mpr
  rw [forestField_eq_true, wiredField_eq_true]
  constructor
  · rintro ⟨c, hc, hce, hz⟩
    cases c with
    | inl i => exact ⟨i, hc, hce⟩
    | inr x =>
      exfalso
      apply x.property
      apply hz
      rw [← hce]
      exact Sym2.mem_mk_right _ _
  · rintro ⟨i, hi, hie⟩
    refine ⟨Sum.inl i, hi, hie, ?_⟩
    rw [← hie]
    intro z hz
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    · exact fun j => (i.val.1 j).property
    · exact fun j => (i.val.2 j).property

/-- On the whole box the lattice law is the wired uniform spanning tree law. -/
theorem forestLaw_boxSet (N : ℕ) : forestLaw (boxSet N) N = finiteLaw N := by
  have hmap : (fun F : Forest (boxSet N) N => forestField (boxSet N) F.val) =
      (fun t : (WiredTrees.graph N).SpanningTree => wiredField t) ∘ boxForestEquiv N := by
    funext F
    rw [Function.comp_apply, ← forestField_boxSet N (boxForestEquiv N F), boxForestEquiv_val]
  have hw : Measurable (fun t : (WiredTrees.graph N).SpanningTree => wiredField t) :=
    measurable_of_countable _
  have he : Measurable (boxForestEquiv N) := measurable_of_countable _
  calc forestLaw (boxSet N) N
      = Measure.map ((fun t : (WiredTrees.graph N).SpanningTree => wiredField t) ∘
          boxForestEquiv N) (FiniteAvalanches.uniformMeasure (Forest (boxSet N) N)) := by
        unfold forestLaw
        rw [hmap]
    _ = Measure.map (fun t : (WiredTrees.graph N).SpanningTree => wiredField t)
          (Measure.map (boxForestEquiv N)
            (FiniteAvalanches.uniformMeasure (Forest (boxSet N) N))) :=
        (Measure.map_map hw he).symm
    _ = Measure.map (fun t : (WiredTrees.graph N).SpanningTree => wiredField t)
          (FiniteAvalanches.uniformMeasure (WiredTrees.graph N).SpanningTree) := by
        rw [FiniteAvalanches.uniform_measure_map_equiv]
    _ = finiteLaw N := rfl

end

end FiniteAvalanches.Wilson.Lattice.SiteRoots
