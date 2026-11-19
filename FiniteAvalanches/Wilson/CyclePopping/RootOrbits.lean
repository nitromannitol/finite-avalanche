import FiniteAvalanches.Wilson.CyclePopping.Terminal

/-! The first root reached by each orbit of a terminal arrow configuration. -/

set_option autoImplicit false

namespace FiniteAvalanches.Wilson.CyclePopping

open Function
open scoped Classical

noncomputable section

variable {V : Type*}

/-- The first root visited by an orbit, assuming every orbit hits the root set. -/
def firstRoot (R : Set V) (f : V → V) (h : ∀ v, ∃ n, f^[n] v ∈ R) (v : V) : V :=
  f^[Nat.find (h v)] v

/-- The first visited root belongs to the prescribed root set. -/
theorem firstRoot_mem (R : Set V) (f : V → V) (h : ∀ v, ∃ n, f^[n] v ∈ R)
    (v : V) : firstRoot R f h v ∈ R := Nat.find_spec (h v)

/-- An orbit started at a root has that root as its first root. -/
theorem firstRoot_of_mem (R : Set V) (f : V → V) (h : ∀ v, ∃ n, f^[n] v ∈ R)
    {v : V} (hv : v ∈ R) : firstRoot R f h v = v := by
  have hn : Nat.find (h v) = 0 := Nat.eq_zero_of_le_zero (Nat.find_min' (h v) hv)
  simp only [firstRoot, hn, Function.iterate_zero, id_eq]

/-- Following a nonroot arrow decreases the first-root hitting time by one. -/
theorem firstRootTime_succ (R : Set V) (f : V → V) (h : ∀ v, ∃ n, f^[n] v ∈ R)
    {v : V} (hv : v ∉ R) : Nat.find (h (f v)) + 1 = Nat.find (h v) := by
  let n := Nat.find (h v)
  let m := Nat.find (h (f v))
  have hn : 0 < n := by
    have hn0 : n ≠ 0 := by
      intro he
      have hs := Nat.find_spec (h v)
      change f^[n] v ∈ R at hs
      rw [he, Function.iterate_zero, id_eq] at hs
      exact hv hs
    exact Nat.pos_of_ne_zero hn0
  have hprev : f^[n - 1] (f v) ∈ R := by
    rw [← Function.iterate_succ_apply]
    have he : (n - 1).succ = n := by omega
    rw [he]
    exact Nat.find_spec (h v)
  have hmle : m + 1 ≤ n := by
    have hh := Nat.find_min' (h (f v)) hprev
    change m ≤ n - 1 at hh
    omega
  have hnle : n ≤ m + 1 := by
    by_contra hh
    have hlt : m + 1 < n := Nat.lt_of_not_ge hh
    have hmiss := Nat.find_min (h v) hlt
    apply hmiss
    rw [Function.iterate_succ_apply]
    exact Nat.find_spec (h (f v))
  exact Nat.le_antisymm hmle hnle

/-- At a nonroot, the first visited root is unchanged by following one arrow. -/
theorem firstRoot_succ (R : Set V) (f : V → V) (h : ∀ v, ∃ n, f^[n] v ∈ R)
    {v : V} (hv : v ∉ R) : firstRoot R f h v = firstRoot R f h (f v) := by
  unfold firstRoot
  rw [← firstRootTime_succ R f h hv, Function.iterate_succ_apply]

/-- Before the first root, iteration decreases the first-root time by the number of steps. -/
theorem firstRootTime_iterate (R : Set V) (f : V → V) (h : ∀ v, ∃ n, f^[n] v ∈ R)
    (v : V) (n : ℕ) (hn : n ≤ Nat.find (h v)) :
    Nat.find (h (f^[n] v)) + n = Nat.find (h v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlt : n < Nat.find (h v) := Nat.lt_of_succ_le hn
    have hnot : f^[n] v ∉ R := Nat.find_min (h v) hlt
    have hs := firstRootTime_succ R f h hnot
    have hi := ih (Nat.le_of_lt hlt)
    rw [Function.iterate_succ_apply']
    omega


/-- An undirected edge induced by one nonroot arrow. -/
def rootwardAdj (R : Set V) (f : V → V) (x y : V) : Prop :=
  (x ∉ R ∧ f x = y) ∨ (y ∉ R ∧ f y = x)

/-- Both ends of a nonroot arrow have the same first root. -/
theorem firstRoot_eq_of_rootwardAdj (R : Set V) (f : V → V)
    (h : ∀ v, ∃ n, f^[n] v ∈ R) {x y : V} (hxy : rootwardAdj R f x y) :
    firstRoot R f h x = firstRoot R f h y := by
  rcases hxy with ⟨hx, rfl⟩ | ⟨hy, rfl⟩
  · exact firstRoot_succ R f h hx
  · exact (firstRoot_succ R f h hy).symm

/-- A walk using nonroot arrows connects vertices with the same first root. -/
theorem firstRoot_eq_of_rootwardReach (R : Set V) (f : V → V)
    (h : ∀ v, ∃ n, f^[n] v ∈ R) {x y : V}
    (hxy : Relation.ReflTransGen (rootwardAdj R f) x y) :
    firstRoot R f h x = firstRoot R f h y := by
  induction hxy with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (firstRoot_eq_of_rootwardAdj R f h hstep)

variable [Fintype V]

/-- A cycle-free finite arrow assignment sends every vertex to a root. -/
theorem GoodArrows.reaches_root {A : V → Type*} (R : Set V)
    (head : (v : V) → A v → V) (a : (v : V) → A v)
    (ha : ∀ c : Finset V, ¬ IsCycle R (fun v => head v (a v)) c) :
    ∀ v, ∃ n, (fun v => head v (a v))^[n] v ∈ R := by
  intro v
  by_contra h
  push Not at h
  obtain ⟨c, hc⟩ := exists_cycle_of_orbit_avoids R (fun v => head v (a v)) v h
  exact ha c hc

end
end FiniteAvalanches.Wilson.CyclePopping
