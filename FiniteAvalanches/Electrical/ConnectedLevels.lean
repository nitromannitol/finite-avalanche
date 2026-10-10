import FiniteAvalanches.Electrical.MaximumPrinciple
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-! Connected voltage level sets in a finite network with two terminals. -/
namespace FiniteAvalanches.Electrical
open scoped BigOperators Classical
variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] in
/-- A harmonic local minimum has the same value at each adjacent vertex. -/
theorem eq_of_laplacian_eq_zero_of_neighbor_min (a b : E → V) (f : V → ℝ) (x : V)
    (hh : laplacian a b f x = 0)
    (hm : ∀ y, (supportGraph a b).Adj x y → f x ≤ f y)
    {y : V} (hxy : (supportGraph a b).Adj x y) : f y = f x := by
  have hinc (e : E) :
      (if a e = x then f x - f (b e) else 0) +
        (if b e = x then f x - f (a e) else 0) ≤ 0 := by
    by_cases ha : a e = x
    · by_cases hb : b e = x
      · simp [ha, hb]
      · have h := hm (b e) ⟨Ne.symm hb, e, Or.inl ⟨ha, rfl⟩⟩
        simp only [if_pos ha, if_neg hb, add_zero]
        linarith
    · by_cases hb : b e = x
      · have h := hm (a e) ⟨Ne.symm ha, e, Or.inr ⟨hb, rfl⟩⟩
        simp only [if_neg ha, if_pos hb, zero_add]
        linarith
      · simp [ha, hb]
  have hz := (Finset.sum_eq_zero_iff_of_nonpos (fun e _ => hinc e)).mp hh
  obtain ⟨hne, e, he⟩ := hxy
  have hez := hz e (Finset.mem_univ e)
  rcases he with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · have hb' : b e ≠ x := by rw [hb]; exact Ne.symm hne
    rw [if_pos ha, if_neg hb', add_zero, hb] at hez
    linarith
  · have ha' : a e ≠ x := by rw [ha]; exact Ne.symm hne
    rw [if_neg ha', if_pos hb, zero_add, ha] at hez
    linarith

/-- Every strict sublevel component of a harmonic field meets the boundary. -/
theorem sublevel_component_meets_boundary (a b : E → V) (B : Finset V)
    (hB : ∀ x, ∃ y ∈ B, (supportGraph a b).Reachable x y)
    (f : V → ℝ) (hf : ∀ x, x ∉ B → laplacian a b f x = 0) (t : ℝ)
    (C : ((supportGraph a b).induce {x | f x < t}).ConnectedComponent) :
    ∃ x : {x : V // f x < t}, x.val ∈ B ∧ x ∈ C.supp := by
  classical
  by_contra hn
  have hno : ∀ x : {x : V // f x < t}, x ∈ C.supp → x.val ∉ B := by
    intro x hx hxb
    exact hn ⟨x, hxb, hx⟩
  let S : Finset {x : V // f x < t} := Finset.univ.filter (fun x => x ∈ C.supp)
  have hSne : S.Nonempty := by
    obtain ⟨x, hx⟩ := C.nonempty_supp
    exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
  obtain ⟨z, hzS, hzMin⟩ := Finset.exists_min_image S (fun x => f x.val) hSne
  have hzC : z ∈ C.supp := (Finset.mem_filter.mp hzS).2
  have hmin : ∀ x : {x : V // f x < t}, x ∈ C.supp → f z.val ≤ f x.val := by
    intro x hx
    exact hzMin x (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩)
  have propagate {u v : V} (p : (supportGraph a b).Walk u v) :
      (∃ hu : f u < t, (⟨u, hu⟩ : {x : V // f x < t}) ∈ C.supp ∧ f u = f z.val) →
      ∃ hv : f v < t, (⟨v, hv⟩ : {x : V // f x < t}) ∈ C.supp ∧ f v = f z.val := by
    induction p with
    | nil => exact id
    | @cons u w v huw p ih =>
      rintro ⟨hu, huC, humin⟩
      have huMin : ∀ y, (supportGraph a b).Adj u y → f u ≤ f y := by
        intro y huy
        by_cases hy : f y < t
        · have hyC := C.mem_supp_of_adj_mem_supp huC
            (show ((supportGraph a b).induce {x | f x < t}).Adj ⟨u, hu⟩ ⟨y, hy⟩ from huy)
          rw [humin]
          exact hmin ⟨y, hy⟩ hyC
        · linarith
      have he := eq_of_laplacian_eq_zero_of_neighbor_min a b f u
        (hf u (hno ⟨u, hu⟩ huC)) huMin huw
      have hw : f w < t := by rw [he]; exact hu
      have hwC := C.mem_supp_of_adj_mem_supp huC
        (show ((supportGraph a b).induce {x | f x < t}).Adj ⟨u, hu⟩ ⟨w, hw⟩ from huw)
      exact ih ⟨hw, hwC, he.trans humin⟩
  obtain ⟨y, hyB, ⟨p⟩⟩ := hB z.val
  obtain ⟨hy, hyC, _⟩ := propagate p ⟨z.property, hzC, rfl⟩
  exact hno ⟨y, hy⟩ hyC hyB

/-- With two boundary vertices, a level below the upper boundary is connected. -/
theorem connected_strict_sublevel (a b : E → V)
    (hG : (supportGraph a b).Connected) (f : V → ℝ) (α β : V)
    (hf : ∀ x, x ≠ α → x ≠ β → laplacian a b f x = 0)
    (t : ℝ) (hα : f α < t) (hβ : t ≤ f β) :
    ((supportGraph a b).induce {x | f x < t}).Connected := by
  classical
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨α, hα⟩, ?_⟩
  intro w
  let C := ((supportGraph a b).induce {x | f x < t}).connectedComponentMk w
  have hB : ∀ x, ∃ y ∈ ({α, β} : Finset V), (supportGraph a b).Reachable x y := by
    intro x
    exact ⟨α, by simp, hG x α⟩
  have hfB : ∀ x, x ∉ ({α, β} : Finset V) → laplacian a b f x = 0 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    exact hf x hx.1 hx.2
  obtain ⟨x, hxB, hxC⟩ := sublevel_component_meets_boundary a b {α, β} hB f hfB t C
  have hxα : x.val = α := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxB
    rcases hxB with h | h
    · exact h
    · have hx := x.property
      rw [h] at hx
      linarith
  have he : x = (⟨α, hα⟩ : {x : V // f x < t}) := Subtype.ext hxα
  rw [he] at hxC
  exact C.reachable_of_mem_supp hxC SimpleGraph.ConnectedComponent.connectedComponentMk_mem


/-- With two boundary vertices, a level above the lower boundary is connected. -/
theorem connected_strict_superlevel (a b : E → V)
    (hG : (supportGraph a b).Connected) (f : V → ℝ) (α β : V)
    (hf : ∀ x, x ≠ α → x ≠ β → laplacian a b f x = 0)
    (t : ℝ) (hα : f α ≤ t) (hβ : t < f β) :
    ((supportGraph a b).induce {x | t < f x}).Connected := by
  have hneg : ∀ x, x ≠ β → x ≠ α →
      laplacian a b ((-1 : ℝ) • f) x = 0 := by
    intro x hxβ hxα
    rw [laplacian_smul, hf x hxα hxβ, mul_zero]
  have h := connected_strict_sublevel a b hG ((-1 : ℝ) • f) β α hneg (-t)
    (by simp only [Pi.smul_apply, smul_eq_mul, neg_one_mul]; linarith)
    (by simp only [Pi.smul_apply, smul_eq_mul, neg_one_mul]; linarith)
  change ((supportGraph a b).induce {x | (-1 : ℝ) * f x < -t}).Connected at h
  have hs : {x | (-1 : ℝ) * f x < -t} = {x | t < f x} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor <;> intro hx <;> linarith
  rw [hs] at h
  exact h

/-- The strict level sets of a two-terminal voltage are connected at every interior level. -/
theorem connected_voltage_levels (a b : E → V)
    (hG : (supportGraph a b).Connected) (f : V → ℝ) (α β : V)
    (hf : ∀ x, x ≠ α → x ≠ β → laplacian a b f x = 0)
    (hα : f α = 0) (hβ : f β = 1) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ((supportGraph a b).induce {x | f x < t}).Connected ∧
      ((supportGraph a b).induce {x | t < f x}).Connected := by
  constructor
  · exact connected_strict_sublevel a b hG f α β hf t (by rw [hα]; exact ht0)
      (by rw [hβ]; exact ht1.le)
  · exact connected_strict_superlevel a b hG f α β hf t (by rw [hα]; exact ht0.le)
      (by rw [hβ]; exact ht1)

end FiniteAvalanches.Electrical
