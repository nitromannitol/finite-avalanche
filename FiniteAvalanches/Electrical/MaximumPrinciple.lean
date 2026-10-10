import FiniteAvalanches.Electrical.Dirichlet
import Mathlib.Data.Finset.Max

/-! Maximum principle on the finite edge-copy network. -/

namespace FiniteAvalanches.Electrical

open scoped BigOperators Classical

variable {V E : Type*} [Fintype V] [Fintype E]

omit [Fintype V] in
theorem eq_of_laplacian_eq_zero_of_max (a b : E → V) (f : V → ℝ) (x : V)
    (hh : laplacian a b f x = 0) (hm : ∀ y, f y ≤ f x)
    {y : V} (hxy : (supportGraph a b).Adj x y) : f y = f x := by
  have hn (e : E) : 0 ≤
      (if a e = x then f x - f (b e) else 0) +
      (if b e = x then f x - f (a e) else 0) := by
    split_ifs <;> linarith only [hm (a e), hm (b e)]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => hn e)).mp hh
  obtain ⟨_, e, he⟩ := hxy
  have hez := hz e (Finset.mem_univ e)
  rcases he with ⟨ha, hb⟩ | ⟨hb, ha⟩
  · rw [if_pos ha] at hez
    split_ifs at hez <;> rw [hb] at hez <;> linarith only [hez, hm (a e), hm y]
  · rw [if_pos hb] at hez
    split_ifs at hez <;> rw [ha] at hez <;> linarith only [hez, hm (b e), hm y]

theorem le_of_harmonic (a b : E → V) (B : Finset V)
    (hB : ∀ x, ∃ y ∈ B, (supportGraph a b).Reachable x y)
    (f : V → ℝ) (c : ℝ) (hfB : ∀ x ∈ B, f x ≤ c)
    (hf : ∀ x, x ∉ B → laplacian a b f x = 0) : ∀ x, f x ≤ c := by
  intro x
  by_contra hx
  have hne : (Finset.univ : Finset V).Nonempty := ⟨x, Finset.mem_univ x⟩
  obtain ⟨z, _, hz⟩ := Finset.exists_max_image Finset.univ f hne
  have hm : ∀ y, f y ≤ f z := fun y => hz y (Finset.mem_univ y)
  have hzc : c < f z := lt_of_lt_of_le (lt_of_not_ge hx) (hm x)
  have hprop {u v : V} (hu : f u = f z) (p : (supportGraph a b).Walk u v) :
      f v = f z := by
    induction p with
    | nil => exact hu
    | @cons u w v huw p ih =>
      have huB : u ∉ B := fun huB => (not_le_of_gt hzc) (hu ▸ hfB u huB)
      have huw' := eq_of_laplacian_eq_zero_of_max a b f u (hf u huB)
        (fun y => (hm y).trans_eq hu.symm) huw
      exact ih (huw'.trans hu)
  obtain ⟨y, hy, ⟨p⟩⟩ := hB z
  exact (not_le_of_gt hzc) ((hprop rfl p) ▸ hfB y hy)

theorem harmonicExtension_nonneg (a b : E → V) (B : Finset V)
    (hB : ∀ x, ∃ y ∈ B, (supportGraph a b).Reachable x y)
    (t : V → ℝ) (ht : ∀ x ∈ B, 0 ≤ t x) :
    ∀ x, 0 ≤ harmonicExtension a b B hB t x := by
  have hs := harmonicExtension_spec a b B hB t
  have hneg := le_of_harmonic a b B hB
    ((-1 : ℝ) • harmonicExtension a b B hB t) 0
    (fun x hx => by simp only [Pi.smul_apply, smul_eq_mul, hs.1 x hx]; linarith [ht x hx])
    (fun x hx => by rw [laplacian_smul, hs.2 x hx, mul_zero])
  intro x
  have hx := hneg x
  simp only [Pi.smul_apply, smul_eq_mul, neg_one_mul] at hx
  linarith only [hx]

end FiniteAvalanches.Electrical
