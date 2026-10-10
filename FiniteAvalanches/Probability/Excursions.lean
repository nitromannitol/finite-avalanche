module

public import Mathlib.GroupTheory.Perm.Cycle.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic

@[expose] public section

/-!
# Excursions of a finite permutation

Cutting each permutation cycle at a stopping subset gives half-open excursions.
The return is the least positive forward visit, and each state is counted once.
-/

open scoped BigOperators Classical

namespace FiniteAvalanches.Probability.Excursions

variable {X : Type*} [Fintype X] (E : Equiv.Perm X) (B : Set X)

theorem return_exists (h : B) :
    ∃ n : ℕ, 0 < n ∧ (E : X → X)^[n] h.val ∈ B := by
  obtain ⟨n, hn, _, he⟩ := (Equiv.Perm.SameCycle.refl E h.val).exists_pow_eq''
  refine ⟨n, hn, ?_⟩
  have hi : (E : X → X)^[n] h.val = h.val := by
    simpa only [Equiv.Perm.coe_pow] using he
  rw [hi]
  exact h.property

/-- The least positive forward visit to the stopping subset. -/
noncomputable def firstReturn (h : B) : ℕ := Nat.find (return_exists E B h)

theorem firstReturn_pos (h : B) : 0 < firstReturn E B h :=
  (Nat.find_spec (return_exists E B h)).1

theorem firstReturn_mem (h : B) : (E : X → X)^[firstReturn E B h] h.val ∈ B :=
  (Nat.find_spec (return_exists E B h)).2

theorem not_mem_of_lt_firstReturn (h : B) {n : ℕ}
    (hn : 0 < n) (hlt : n < firstReturn E B h) :
    (E : X → X)^[n] h.val ∉ B := by
  intro hm
  exact Nat.find_min (return_exists E B h) hlt ⟨hn, hm⟩

/-- A starting state and an index strictly before its first positive return. -/
abbrev ExcursionPair := Σ h : B, Fin (firstReturn E B h)

/-- Evaluate an excursion pair by actual forward iteration of the permutation. -/
def excursionEval (p : ExcursionPair E B) : X := (E : X → X)^[p.2.val] p.1.val

private theorem index_le {h g : B} {i j : ℕ}
    (hi : i < firstReturn E B h)
    (he : (E : X → X)^[i] h.val = (E : X → X)^[j] g.val) : i ≤ j := by
  by_contra hle
  have hc : (E : X → X)^[i - j] h.val = g.val := by
    apply E.injective.iterate j
    calc
      (E : X → X)^[j] ((E : X → X)^[i - j] h.val) =
          (E : X → X)^[j + (i - j)] h.val :=
        (Function.iterate_add_apply E j (i - j) h.val).symm
      _ = (E : X → X)^[i] h.val := by congr 1; omega
      _ = (E : X → X)^[j] g.val := he
  exact not_mem_of_lt_firstReturn E B h (by omega) (by omega) (hc ▸ g.property)

theorem excursionEval_injective : Function.Injective (excursionEval E B) := by
  rintro ⟨h, i⟩ ⟨g, j⟩ he
  have hij : i.val = j.val := le_antisymm
    (index_le E B i.isLt he) (index_le E B j.isLt he.symm)
  have hhg : h = g := by
    apply Subtype.ext
    apply E.injective.iterate i.val
    simpa only [excursionEval, hij] using he
  subst g
  have hfin : i = j := Fin.ext hij
  subst j
  rfl

theorem backward_visit_exists
    (hcycle : ∀ x : X, ∃ h : B, E.SameCycle x h.val) (x : X) :
    ∃ n : ℕ, (E.symm : X → X)^[n] x ∈ B := by
  obtain ⟨h, hh⟩ := hcycle x
  obtain ⟨n, hn⟩ := hh.inv.exists_nat_pow_eq
  refine ⟨n, ?_⟩
  have he : (E.symm : X → X)^[n] x = h.val := by
    simpa only [Equiv.Perm.coe_pow, Equiv.Perm.inv_def] using hn
  exact he ▸ h.property

theorem excursionEval_surjective
    (hcycle : ∀ x : X, ∃ h : B, E.SameCycle x h.val) :
    Function.Surjective (excursionEval E B) := by
  intro x
  let d := Nat.find (backward_visit_exists E B hcycle x)
  let h : B := ⟨(E.symm : X → X)^[d] x,
    Nat.find_spec (backward_visit_exists E B hcycle x)⟩
  have hd : d < firstReturn E B h := by
    by_contra hlt
    have he : (E : X → X)^[firstReturn E B h] h.val =
        (E.symm : X → X)^[d - firstReturn E B h] x := by
      change (E : X → X)^[firstReturn E B h] ((E.symm : X → X)^[d] x) = _
      conv_lhs =>
        rw [show d = firstReturn E B h + (d - firstReturn E B h) by omega,
          Function.iterate_add_apply]
      exact (Function.LeftInverse.iterate E.apply_symm_apply (firstReturn E B h)) _
    have hm : (E.symm : X → X)^[d - firstReturn E B h] x ∈ B :=
      he ▸ firstReturn_mem E B h
    exact Nat.find_min (backward_visit_exists E B hcycle x)
      (by have := firstReturn_pos E B h; omega) hm
  refine ⟨⟨h, ⟨d, hd⟩⟩, ?_⟩
  exact (Function.LeftInverse.iterate E.apply_symm_apply d) x

/-- Every cycle meeting the stopping subset makes the excursion evaluation bijective. -/
theorem excursionEval_bijective
    (hcycle : ∀ x : X, ∃ h : B, E.SameCycle x h.val) :
    Function.Bijective (excursionEval E B) :=
  ⟨excursionEval_injective E B, excursionEval_surjective E B hcycle⟩

theorem occupation
    (hcycle : ∀ x : X, ∃ h : B, E.SameCycle x h.val) (q : X → ℝ) :
    (∑ h : B, ∑ j ∈ Finset.range (firstReturn E B h), (q ((E : X → X)^[j] h.val))) =
      ∑ x : X, q x := by
  have hs := Fintype.sum_bijective (excursionEval E B)
    (excursionEval_bijective E B hcycle) (fun p => q (excursionEval E B p)) q
    (fun _ => rfl)
  change (∑ p : (Σ h : B, Fin (firstReturn E B h)),
    q ((E : X → X)^[p.2.val] p.1.val)) = ∑ x : X, q x at hs
  rw [Fintype.sum_sigma] at hs
  refine Eq.trans ?_ hs
  apply Finset.sum_congr rfl
  intro h _
  exact (Fin.sum_univ_eq_sum_range
    (fun j => q ((E : X → X)^[j] h.val)) (firstReturn E B h)).symm

/-- An arbitrary common real mass is retained; no probability normalization is imposed. -/
theorem weighted_occupation
    (hcycle : ∀ x : X, ∃ h : B, E.SameCycle x h.val) (q : X → ℝ) (c : ℝ) :
    (∑ h : B, ∑ j ∈ Finset.range (firstReturn E B h),
      c * q ((E : X → X)^[j] h.val)) = c * ∑ x : X, q x := by
  simp_rw [← Finset.mul_sum]
  rw [occupation E B hcycle q]


end FiniteAvalanches.Probability.Excursions
