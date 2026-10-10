import FiniteAvalanches.Wilson.Lattice.TranslationGeometry
import LatticeProb.Graph.Zd
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

set_option autoImplicit false
namespace JointExterior
open LatticeProb FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

theorem line_reachable (S : Set (Site 2)) (x : Site 2) (i : Fin 2)
    (hs : ∀ t : ℤ, Function.update x i t ∈ S) (a b : ℤ) :
    ((lattice 2).induce S).Reachable ⟨Function.update x i a, hs a⟩
      ⟨Function.update x i b, hs b⟩ := by
  let f : lattice 1 →g (lattice 2).induce S :=
    { toFun := fun t => ⟨Function.update x i (t 0), hs (t 0)⟩
      map_rel' := by
        intro u v huv
        obtain ⟨j, hj | hj⟩ := Graph.Zd.adj_iff.mp huv
        · apply Graph.Zd.adj_iff.mpr
          refine ⟨i, Or.inl ?_⟩
          funext k
          have he := congrFun hj 0
          have hj0 : j = 0 := Subsingleton.elim _ _
          subst j
          by_cases hk : k = i
          · subst k; simpa [Function.update, unit] using he
          · simp [Function.update, unit, hk]
        · apply Graph.Zd.adj_iff.mpr
          refine ⟨i, Or.inr ?_⟩
          funext k
          have he := congrFun hj 0
          have hj0 : j = 0 := Subsingleton.elim _ _
          subst j
          by_cases hk : k = i
          · subst k; simpa [Function.update, unit] using he
          · simp [Function.update, unit, hk] }
  exact ((Graph.Zd.latticeConnected 1).preconnected (fun _ => a) (fun _ => b)).map f

theorem exterior_connected (N : ℕ) : ((lattice 2).induce (box 2 N)ᶜ).Connected := by
  let a : Site 2 := fun _ => (N : ℤ) + 1
  have ha : a ∈ (box 2 N)ᶜ := by
    intro h; have := h 0; simp only [a, abs_of_nonneg (by omega : 0 ≤ (N : ℤ)+1)] at this; omega
  have hr (x : Site 2) (hx : x ∈ (box 2 N)ᶜ) :
      ((lattice 2).induce (box 2 N)ᶜ).Reachable ⟨x,hx⟩ ⟨a,ha⟩ := by
    have hcoordinate : (N : ℤ) < |x 0| ∨ (N : ℤ) < |x 1| := by
      by_contra hn
      push Not at hn
      apply hx
      intro i
      fin_cases i <;> simp_all
    rcases hcoordinate with h0 | h1
    · have hs (t : ℤ) : Function.update x (1 : Fin 2) t ∈ (box 2 N)ᶜ := by
        intro hb; have := hb 0; simp at this; omega
      have ht := line_reachable _ x 1 hs (x 1) ((N : ℤ)+1)
      have hq (t : ℤ) : Function.update (Function.update x (1 : Fin 2) ((N : ℤ)+1))
          (0 : Fin 2) t ∈ (box 2 N)ᶜ := by
        intro hb; have := hb 1; simp [abs_of_nonneg (by omega : 0 ≤ (N : ℤ)+1)] at this
      have hu := line_reachable _ _ 0 hq (x 0) ((N : ℤ)+1)
      have he : Function.update (Function.update x (1 : Fin 2) ((N : ℤ)+1))
          (0 : Fin 2) ((N : ℤ)+1) = a := by
        funext i; fin_cases i <;> simp [a]
      have he0 : Function.update (Function.update x (1 : Fin 2) ((N : ℤ)+1))
          (0 : Fin 2) (x 0) = Function.update x 1 ((N : ℤ)+1) := by
        funext i; fin_cases i <;> simp
      have hu' : ((lattice 2).induce (box 2 N)ᶜ).Reachable
          ⟨Function.update x 1 ((N : ℤ)+1),hs _⟩ ⟨a,ha⟩ := by
        simpa only [he0,he] using hu
      have ht' : ((lattice 2).induce (box 2 N)ᶜ).Reachable
          ⟨x,hx⟩ ⟨Function.update x 1 ((N : ℤ)+1),hs _⟩ := by
        simpa only [Function.update_eq_self] using ht
      exact ht'.trans hu'
    · have hs (t : ℤ) : Function.update x (0 : Fin 2) t ∈ (box 2 N)ᶜ := by
        intro hb; have := hb 1; simp at this; omega
      have ht := line_reachable _ x 0 hs (x 0) ((N : ℤ)+1)
      have hq (t : ℤ) : Function.update (Function.update x (0 : Fin 2) ((N : ℤ)+1))
          (1 : Fin 2) t ∈ (box 2 N)ᶜ := by
        intro hb; have := hb 0; simp [abs_of_nonneg (by omega : 0 ≤ (N : ℤ)+1)] at this
      have hu := line_reachable _ _ 1 hq (x 1) ((N : ℤ)+1)
      have he : Function.update (Function.update x (0 : Fin 2) ((N : ℤ)+1))
          (1 : Fin 2) ((N : ℤ)+1) = a := by
        funext i; fin_cases i <;> simp [a]
      have he0 : Function.update (Function.update x (0 : Fin 2) ((N : ℤ)+1))
          (1 : Fin 2) (x 1) = Function.update x 0 ((N : ℤ)+1) := by
        funext i; fin_cases i <;> simp
      have hu' : ((lattice 2).induce (box 2 N)ᶜ).Reachable
          ⟨Function.update x 0 ((N : ℤ)+1),hs _⟩ ⟨a,ha⟩ := by
        simpa only [he0,he] using hu
      have ht' : ((lattice 2).induce (box 2 N)ᶜ).Reachable
          ⟨x,hx⟩ ⟨Function.update x 0 ((N : ℤ)+1),hs _⟩ := by
        simpa only [Function.update_eq_self] using ht
      exact ht'.trans hu'
  exact { preconnected := fun x y => (hr x.val x.property).trans (hr y.val y.property).symm
          nonempty := ⟨⟨a,ha⟩⟩ }

/-- Original-site support of the actual induced connected component. -/
def component (U : Set (Site 2)) (b : U) : Set (Site 2) :=
  {x | ∃ hx : x ∈ U, ((lattice 2).induce U).connectedComponentMk ⟨x,hx⟩ =
    ((lattice 2).induce U).connectedComponentMk b}

theorem component_subset (U : Set (Site 2)) (b : U) : component U b ⊆ U :=
  fun _ hx => hx.choose

theorem base_mem_component (U : Set (Site 2)) (b : U) : b.val ∈ component U b :=
  ⟨b.property,rfl⟩

theorem component_connected (U : Set (Site 2)) (b : U) :
    ((lattice 2).induce (component U b)).Connected := by
  let C := ((lattice 2).induce U).connectedComponentMk b
  let f : C.toSimpleGraph →g (lattice 2).induce (component U b) :=
    { toFun := fun x => ⟨x.val.val, x.val.property, x.property⟩
      map_rel' := fun h => h }
  apply C.connected_toSimpleGraph.map f
  rintro ⟨x,hx,hC⟩
  exact ⟨⟨⟨x,hx⟩,hC⟩,rfl⟩

theorem reachable_mem_component (U : Set (Site 2)) (b : U) (x : U)
    (h : ((lattice 2).induce U).Reachable b x) : x.val ∈ component U b :=
  ⟨x.property, Quot.sound h.symm⟩

theorem neighbor_mem_component (U : Set (Site 2)) (b : U) (x y : Site 2)
    (hx : x ∈ component U b) (hy : y ∈ U) (hxy : (lattice 2).Adj x y) :
    y ∈ component U b := by
  obtain ⟨hxU,hxC⟩ := hx
  refine ⟨hy, ?_⟩
  exact (Quot.sound (show ((lattice 2).induce U).Reachable ⟨y,hy⟩ ⟨x,hxU⟩
    from SimpleGraph.Adj.reachable hxy.symm)).trans hxC

end
end JointExterior
