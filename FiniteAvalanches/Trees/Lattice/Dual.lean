import FiniteAvalanches.Trees.Lattice.Space

set_option autoImplicit false
namespace FiniteAvalanches.Trees.Lattice
open LatticeProb MeasureTheory
open scoped Classical
noncomputable section

/-- The lattice edge from `x` to `x + e_i`, named by base point and direction. -/
def baseEdge (p : Site 2 × Fin 2) : LatticeEdge :=
  ⟨s(p.1, p.1 + unit p.2), by exact ⟨p.2, Or.inl rfl⟩⟩

theorem baseEdge_injective : Function.Injective baseEdge := by
  rintro ⟨x, i⟩ ⟨x', j⟩ h
  have hs := Sym2.eq_iff.mp (congrArg Subtype.val h)
  rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h1' : x = x' := h1
    subst h1'
    have hij : unit i = unit j := add_left_cancel h2
    have := congrFun hij i
    fin_cases i <;> fin_cases j <;> simp [unit] at this ⊢
  · exfalso
    have h1' : x = x' + unit j := h1
    have h2' : x + unit i = x' := h2
    have h3 : x' + (unit j + unit i) = x' + 0 := by
      rw [add_zero, ← add_assoc, ← h1']; exact h2'
    have h4 := congrFun (add_left_cancel h3) i
    fin_cases i <;> fin_cases j <;> simp [unit] at h4

theorem baseEdge_surjective : Function.Surjective baseEdge := by
  rintro ⟨e, he⟩
  revert he
  refine Sym2.inductionOn e ?_
  intro x y hxy
  rcases hxy with ⟨i, h | h⟩
  · change y = x + unit i at h
    exact ⟨(x, i), Subtype.ext (by change s(x, x + unit i) = s(x, y); rw [h])⟩
  · change x = y + unit i at h
    exact ⟨(y, i), Subtype.ext (by change s(y, y + unit i) = s(x, y); rw [h, Sym2.eq_swap])⟩

def edgeEquiv : Site 2 × Fin 2 ≃ LatticeEdge :=
  Equiv.ofBijective baseEdge ⟨baseEdge_injective, baseEdge_surjective⟩

theorem one_sub_one_sub (j : Fin 2) : (1 : Fin 2) - (1 - j) = j := by revert j; decide

/-- Dual edge `{y, y + e_j}` of the face lattice crosses the primal edge based at `y + e_j`. -/
def dualBase (p : Site 2 × Fin 2) : Site 2 × Fin 2 := (p.1 + unit p.2, 1 - p.2)
def dualBaseInv (q : Site 2 × Fin 2) : Site 2 × Fin 2 := (q.1 - unit (1 - q.2), 1 - q.2)

theorem dualBase_left_inv (p : Site 2 × Fin 2) : dualBaseInv (dualBase p) = p := by
  rcases p with ⟨y, j⟩
  simp [dualBase, dualBaseInv]

theorem dualBase_right_inv (q : Site 2 × Fin 2) : dualBase (dualBaseInv q) = q := by
  rcases q with ⟨z, k⟩
  simp [dualBase, dualBaseInv]

def dualBaseEquiv : Site 2 × Fin 2 ≃ Site 2 × Fin 2 :=
  ⟨dualBase, dualBaseInv, dualBase_left_inv, dualBase_right_inv⟩

/-- `T* = {e† : e ∉ T}` with dual edges named by face adjacency on `ℤ²`. -/
def dualField (ω : EdgeField) : EdgeField :=
  fun d => !ω (edgeEquiv (dualBase (edgeEquiv.symm d)))

theorem dualField_baseEdge (ω : EdgeField) (p : Site 2 × Fin 2) :
    dualField ω (baseEdge p) = !ω (baseEdge (p.1 + unit p.2, 1 - p.2)) := by
  have h : edgeEquiv.symm (baseEdge p) = p := edgeEquiv.symm_apply_apply p
  simp only [dualField, h]
  rfl

theorem measurable_dualField : Measurable dualField :=
  measurable_pi_lambda _ fun _ => (measurable_of_finite Bool.not).comp (measurable_pi_apply _)

/-- Sanity: the dual of the dual is the original field translated by `(1,1)`. -/
theorem dualField_dualField (ω : EdgeField) (p : Site 2 × Fin 2) :
    dualField (dualField ω) (baseEdge p) = ω (baseEdge (p.1 + (unit 0 + unit 1), p.2)) := by
  rw [dualField_baseEdge, dualField_baseEdge]
  rcases p with ⟨y, j⟩
  change Bool.not (Bool.not (ω (baseEdge (y + unit j + unit (1-j), 1-(1-j))))) =
    ω (baseEdge (y + (unit 0 + unit 1), j))
  have hu : unit j + unit (1-j) = unit (0 : Fin 2) + unit 1 := by
    fin_cases j <;> first | rfl | exact add_comm _ _
  rw [Bool.not_not, one_sub_one_sub, add_assoc, hu]

end
end FiniteAvalanches.Trees.Lattice
