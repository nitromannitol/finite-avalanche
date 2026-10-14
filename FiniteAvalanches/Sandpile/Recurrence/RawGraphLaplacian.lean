import FiniteAvalanches.Sandpile.Recurrence.RawGraphDynamics
import FiniteAvalanches.Electrical.Green.Grounded

/-! The positive copied Laplacian and its single-site subtraction law. -/
namespace FiniteAvalanches.Sandpile.RawGraph
open FiniteAvalanches.Sandpile
open scoped Classical BigOperators
noncomputable section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : FiniteAvalanches.Trees.Multigraph V E) (s : V)

def lapInt (f : V → ℤ) (x : V) : ℤ := ∑ y, (copies G x y : ℤ) * (f x - f y)
def lapReal (f : V → ℝ) (x : V) : ℝ := ∑ y, (copies G x y : ℝ) * (f x - f y)

theorem lap_int_add (f g : V → ℤ) (x : V) :
    lapInt G (fun y => f y + g y) x = lapInt G f x + lapInt G g x := by
  simp only [lapInt, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem lap_int_nat_mul (k : ℕ) (f : V → ℤ) (x : V) :
    lapInt G (fun y => (k : ℤ) * f y) x = (k : ℤ) * lapInt G f x := by
  simp only [lapInt, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem lap_real_eq_cast (f : V → ℤ) (x : V) :
    lapReal G (fun y => (f y : ℝ)) x = (lapInt G f x : ℝ) := by
  simp [lapReal, lapInt]

theorem degree_eq_sum_copies (x : V) : Burning.degree G x = ∑ y, copies G x y :=
  degree_into_eq_sum G Finset.univ x

theorem lap_int_indicator (o x : V) :
    lapInt G (fun y => if y = o then 1 else 0) x =
      if x = o then (Burning.degree G o : ℤ) else -(copies G x o : ℤ) := by
  unfold lapInt
  by_cases hx : x = o
  · subst x
    rw [if_pos rfl]
    calc
      _ = ∑ y, (copies G o y : ℤ) := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y = o
        · subst y; simp [copies_self]
        · simp [hy]
      _ = (Burning.degree G o : ℤ) := by rw [degree_eq_sum_copies, Nat.cast_sum]
  · rw [if_neg hx]
    simp only [if_neg hx, zero_sub, mul_neg]
    simp

/-- The full integer field is zero only at the actual sink. -/
def zeroAtSink (η : Field s) (x : V) : ℤ :=
  if hx : x ∈ Finset.univ.erase s then η ⟨x, hx⟩ else 0

theorem zero_at_sink (η : Field s) : zeroAtSink s η s = 0 := by simp [zeroAtSink]
theorem zero_at_source (η : Field s) (x : Burning.SourceVertex s) :
    zeroAtSink s η x.val = η x := by simp [zeroAtSink, x.property]

/-- Fields reached by firing a given nonnegative multiplicity script. -/
def raised (η : Field s) (n : V → ℕ) : Field s := fun x => η x + lapInt G (fun y => n y) x.val

theorem raised_zero (η : Field s) : raised G s η (fun _ => 0) = η := by
  funext x
  simp [raised, lapInt]

theorem topple_raised_decrement (η : Field s) (n : V → ℕ)
    (o : Burning.SourceVertex s) (ho : 0 < n o.val) :
    topple G s (raised G s η n) o =
      raised G s η (Function.update n o.val (n o.val - 1)) := by
  let m := Function.update n o.val (n o.val - 1)
  have he : (fun y => (n y : ℤ)) =
      fun y => (m y : ℤ) + if y = o.val then 1 else 0 := by
    funext y
    by_cases hy : y = o.val
    · subst y
      dsimp only [m]
      rw [Function.update_self, if_pos (rfl : o.val = o.val)]
      exact_mod_cast (Nat.sub_add_cancel ho).symm
    · simp [m, hy]
  funext x
  have hh := congrArg (fun f : V → ℤ => lapInt G f x.val) he
  rw [lap_int_add, lap_int_indicator] at hh
  by_cases hx : x = o
  · subst x
    rw [if_pos (rfl : o.val = o.val)] at hh
    simp only [topple, raised]
    change η o + lapInt G (fun y => (n y : ℤ)) o.val - ↑(Burning.degree G o.val) =
      η o + lapInt G (fun y => (m y : ℤ)) o.val
    omega
  · have hxv : x.val ≠ o.val := fun h => hx (Subtype.ext h)
    rw [if_neg hxv] at hh
    simp only [topple, if_neg hx, raised]
    change η x + lapInt G (fun y => (n y : ℤ)) x.val + ↑(copies G x.val o.val) =
      η x + lapInt G (fun y => (m y : ℤ)) x.val
    omega

/-- Electrical conductance here is exactly the number of original copies. -/
theorem conductance_eq_copies (x y : V) :
    FiniteAvalanches.Electrical.conductance G.left G.right x y = (copies G x y : ℝ) := by
  by_cases hx : x = y
  · subst y
    simp [FiniteAvalanches.Electrical.conductance, copies_self]
  · rw [FiniteAvalanches.Electrical.conductance, if_neg hx]
    unfold copies Burning.degreeInto Burning.incidentInto
    rw [← Finset.sum_boole]
    apply Finset.sum_congr rfl
    intro e _
    simp only [Finset.mem_singleton]
    by_cases h1 : G.left e = x ∧ G.right e = y
    · have h2 : ¬(G.right e = x ∧ G.left e = y) := by
        intro h2; exact hx (h1.1.symm.trans h2.2)
      rw [if_pos h1, if_neg h2, if_pos (Or.inl h1)]
      ring
    · by_cases h2 : G.right e = x ∧ G.left e = y
      · rw [if_neg h1, if_pos h2, if_pos (Or.inr h2)]
        ring
      · rw [if_neg h1, if_neg h2, if_neg (not_or.mpr ⟨h1, h2⟩)]
        ring

theorem lap_real_eq_electrical (f : V → ℝ) (x : V) :
    lapReal G f x = FiniteAvalanches.Electrical.laplacian G.left G.right f x := by
  have h := FiniteAvalanches.Electrical.netLaplacian_eq_neg_laplacian G.left G.right f x
  rw [LatticeProb.Network.netLaplacian,
    FiniteAvalanches.Electrical.sum_neighbor_conductance_mul] at h
  simp_rw [conductance_eq_copies] at h
  have he : (∑ y, (copies G x y : ℝ) * (f y - f x)) = -lapReal G f x := by
    simp only [lapReal, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [he] at h
  linarith

end
end FiniteAvalanches.Sandpile.RawGraph
