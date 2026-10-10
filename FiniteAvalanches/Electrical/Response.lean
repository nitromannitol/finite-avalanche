import FiniteAvalanches.Electrical.MaximumPrinciple
import Mathlib.Data.Fin.VecNotation

/-! Three-terminal response energy derived from the finite Dirichlet problem. -/

namespace FiniteAvalanches.Electrical

open scoped BigOperators Classical

variable {V E : Type*} [Fintype V] [Fintype E]

/-- The three distinguished terminals, all retained as vertices. -/
noncomputable def terminalSet (r : Fin 3 → V) : Finset V := Finset.univ.image r

omit [Fintype V] in
theorem mem_terminalSet (r : Fin 3 → V) (i : Fin 3) : r i ∈ terminalSet r :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

omit [Fintype V] in
theorem mem_terminalSet_iff (r : Fin 3 → V) (x : V) :
    x ∈ terminalSet r ↔ ∃ i, r i = x := by
  simp only [terminalSet, Finset.mem_image, Finset.mem_univ, true_and]

theorem sum_eq_terminal_sum (r : Fin 3 → V) (hr : Function.Injective r)
    (f : V → ℝ) (hf : ∀ x, x ∉ terminalSet r → f x = 0) :
    (∑ x, f x) = ∑ i, f (r i) := by
  calc
    _ = ∑ x ∈ terminalSet r, f x :=
      (Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => hf x hx)).symm
    _ = _ := Finset.sum_image (fun i _ j _ hij => hr hij)

omit [Fintype V] in
theorem laplacian_sum {I : Type*} (a b : E → V) (s : Finset I)
    (f : I → V → ℝ) (x : V) :
    laplacian a b (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, laplacian a b (f i) x := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, laplacian_const]
  | @insert i s hi ih =>
    have h : (fun y => ∑ j ∈ insert i s, f j y) = f i + (fun y => ∑ j ∈ s, f j y) := by
      funext y; rw [Finset.sum_insert hi]; rfl
    rw [h, laplacian_add, ih, Finset.sum_insert hi]

theorem sum_laplacian_eq_zero (a b : E → V) (f : V → ℝ) :
    (∑ x, laplacian a b f x) = 0 := by
  have h := incidence_sum a b f (fun _ => 1)
  simpa only [one_mul, sub_self, mul_zero, Finset.sum_const_zero] using h

/-- The unique harmonic potential for one unit terminal value and two zeros. -/
noncomputable def responseBasis (a b : E → V) (r : Fin 3 → V)
    (hB : ∀ x, ∃ y ∈ terminalSet r, (supportGraph a b).Reachable x y) (j : Fin 3) : V → ℝ :=
  harmonicExtension a b (terminalSet r) hB (fun x => if x = r j then 1 else 0)

/-- Positive-Laplacian terminal flux, before changing its off-diagonal sign. -/
noncomputable def responseEntry (a b : E → V) (r : Fin 3 → V)
    (hB : ∀ x, ∃ y ∈ terminalSet r, (supportGraph a b).Reachable x y)
    (i j : Fin 3) : ℝ := laplacian a b (responseBasis a b r hB j) (r i)

theorem responseBasis_terminal (a b : E → V) (r : Fin 3 → V)
    (hr : Function.Injective r)
    (hB : ∀ x, ∃ y ∈ terminalSet r, (supportGraph a b).Reachable x y) (i j : Fin 3) :
    responseBasis a b r hB j (r i) = if i = j then 1 else 0 := by
  unfold responseBasis
  rw [(harmonicExtension_spec a b (terminalSet r) hB _).1 _ (mem_terminalSet r i)]
  simp only [hr.eq_iff]

theorem responseBasis_harmonic (a b : E → V) (r : Fin 3 → V)
    (hB : ∀ x, ∃ y ∈ terminalSet r, (supportGraph a b).Reachable x y) (j : Fin 3) :
    ∀ x, x ∉ terminalSet r → laplacian a b (responseBasis a b r hB j) x = 0 :=
  (harmonicExtension_spec a b (terminalSet r) hB _).2

theorem sum_responseEntry_eq_zero (a b : E → V) (r : Fin 3 → V)
    (hr : Function.Injective r)
    (hB : ∀ x, ∃ y ∈ terminalSet r, (supportGraph a b).Reachable x y) (j : Fin 3) :
    (∑ i, responseEntry a b r hB i j) = 0 := by
  unfold responseEntry
  rw [← sum_eq_terminal_sum r hr _ (responseBasis_harmonic a b r hB j)]
  exact sum_laplacian_eq_zero a b _

theorem responseEntry_comm (a b : E → V) (r : Fin 3 → V)
    (hr : Function.Injective r)
    (hB : ∀ x, ∃ y ∈ terminalSet r, (supportGraph a b).Reachable x y) (i j : Fin 3) :
    responseEntry a b r hB i j = responseEntry a b r hB j i := by
  have hi (j i : Fin 3) :
      (∑ x, responseBasis a b r hB i x * laplacian a b (responseBasis a b r hB j) x) =
      responseEntry a b r hB i j := by
    rw [sum_eq_terminal_sum r hr _ (fun x hx => by
      rw [responseBasis_harmonic a b r hB j x hx, mul_zero])]
    simp_rw [responseBasis_terminal a b r hr hB, ite_mul, one_mul, zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, responseEntry]
  rw [← hi j i, ← hi i j, incidence_sum, incidence_sum]
  exact Finset.sum_congr rfl fun e _ => mul_comm _ _

theorem responseEntry_nonpos (a b : E → V) (r : Fin 3 → V)
    (hr : Function.Injective r)
    (hB : ∀ x, ∃ y ∈ terminalSet r, (supportGraph a b).Reachable x y)
    (i j : Fin 3) (hij : i ≠ j) : responseEntry a b r hB i j ≤ 0 := by
  have hn := harmonicExtension_nonneg a b (terminalSet r) hB
    (fun x => if x = r j then 1 else 0) (fun x _ => by split_ifs <;> norm_num)
  change ∀ x, 0 ≤ responseBasis a b r hB j x at hn
  unfold responseEntry laplacian
  rw [responseBasis_terminal a b r hr hB, if_neg hij]
  apply Finset.sum_nonpos
  intro e _
  change (if a e = r i then 0 - responseBasis a b r hB j (b e) else 0) +
    (if b e = r i then 0 - responseBasis a b r hB j (a e) else 0) ≤ 0
  split_ifs <;> linarith only [hn (a e), hn (b e)]

/-- The energy of the proved harmonic extension, as a literal terminal quadratic form. -/
theorem harmonic_extension_energy_eq_response (a b : E → V) (r : Fin 3 → V)
    (hr : Function.Injective r)
    (hB : ∀ x, ∃ y ∈ terminalSet r, (supportGraph a b).Reachable x y) (t : Fin 3 → ℝ) :
    let f : V → ℝ := fun x => ∑ j, t j * responseBasis a b r hB j x
    energy a b f = ∑ i, ∑ j, t i * responseEntry a b r hB i j * t j := by
  intro f
  have hf (i : Fin 3) : f (r i) = t i := by
    simp only [f, responseBasis_terminal a b r hr hB]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hl (x : V) : laplacian a b f x =
      ∑ j, t j * laplacian a b (responseBasis a b r hB j) x := by
    rw [laplacian_sum]
    exact Finset.sum_congr rfl fun j _ => laplacian_smul a b (t j) _ x
  rw [energy_eq_incidence_sum, sum_eq_terminal_sum r hr _ (fun x hx => by
    rw [hl]; simp only [responseBasis_harmonic a b r hB _ x hx, mul_zero,
      Finset.sum_const_zero])]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hf, hl, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by unfold responseEntry; ring

/-- Once-counted response energy with no arbitrary normalization. -/
theorem three_terminal_response_energy (a b : E → V) (r : Fin 3 → V)
    (hr : Function.Injective r)
    (hB : ∀ x, ∃ y ∈ terminalSet r, (supportGraph a b).Reachable x y) (t : Fin 3 → ℝ) :
    energy a b (fun x => ∑ j, t j * responseBasis a b r hB j x) =
      -responseEntry a b r hB 0 1 * (t 0 - t 1) ^ 2 +
      -responseEntry a b r hB 0 2 * (t 0 - t 2) ^ 2 +
      -responseEntry a b r hB 1 2 * (t 1 - t 2) ^ 2 := by
  rw [harmonic_extension_energy_eq_response a b r hr hB]
  have h0 := sum_responseEntry_eq_zero a b r hr hB 0
  have h1 := sum_responseEntry_eq_zero a b r hr hB 1
  have h2 := sum_responseEntry_eq_zero a b r hr hB 2
  simp only [Fin.sum_univ_three] at h0 h1 h2 ⊢
  have h10 := responseEntry_comm a b r hr hB 1 0
  have h20 := responseEntry_comm a b r hr hB 2 0
  have h21 := responseEntry_comm a b r hr hB 2 1
  simp only [h10, h20, h21] at h0 h1 h2 ⊢
  have hd0 : responseEntry a b r hB 0 0 =
      -responseEntry a b r hB 0 1 - responseEntry a b r hB 0 2 := by linarith only [h0]
  have hd1 : responseEntry a b r hB 1 1 =
      -responseEntry a b r hB 0 1 - responseEntry a b r hB 1 2 := by linarith only [h1]
  have hd2 : responseEntry a b r hB 2 2 =
      -responseEntry a b r hB 0 2 - responseEntry a b r hB 1 2 := by linarith only [h2]
  rw [hd0, hd1, hd2]
  ring

theorem response_potential_spec (a b : E → V) (r : Fin 3 → V)
    (hr : Function.Injective r)
    (hB : ∀ x, ∃ y ∈ terminalSet r, (supportGraph a b).Reachable x y) (t : Fin 3 → ℝ) :
    let h : V → ℝ := fun x => ∑ j, t j * responseBasis a b r hB j x
    (∀ i, h (r i) = t i) ∧ (∀ x, x ∉ terminalSet r → laplacian a b h x = 0) := by
  intro h
  constructor
  · intro i
    simp only [h, responseBasis_terminal a b r hr hB]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · intro x hx
    rw [laplacian_sum]
    apply Finset.sum_eq_zero
    intro j _
    change laplacian a b (t j • responseBasis a b r hB j) x = 0
    rw [laplacian_smul a b (t j), responseBasis_harmonic a b r hB j x hx, mul_zero]

/-- The attained Dirichlet minimum, with no assumed response conclusion. -/
theorem three_terminal_response_minimum (a b : E → V) (r : Fin 3 → V)
    (hr : Function.Injective r)
    (hB : ∀ x, ∃ y ∈ terminalSet r, (supportGraph a b).Reachable x y)
    (t : Fin 3 → ℝ) (f : V → ℝ) (hf : ∀ i, f (r i) = t i) :
    -responseEntry a b r hB 0 1 * (t 0 - t 1) ^ 2 +
    -responseEntry a b r hB 0 2 * (t 0 - t 2) ^ 2 +
    -responseEntry a b r hB 1 2 * (t 1 - t 2) ^ 2 ≤ energy a b f := by
  let h : V → ℝ := fun x => ∑ j, t j * responseBasis a b r hB j x
  have hs := response_potential_spec a b r hr hB t
  rw [← three_terminal_response_energy a b r hr hB t]
  change energy a b h ≤ energy a b f
  rw [energy_eq_add_energy_sub_of_harmonic a b (terminalSet r) f h
    (fun x hx => by
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact (hf i).trans (hs.1 i).symm) hs.2]
  exact le_add_of_nonneg_right (energy_nonneg a b _)

end FiniteAvalanches.Electrical
