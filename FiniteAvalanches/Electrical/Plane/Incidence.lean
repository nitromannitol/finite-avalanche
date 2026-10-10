import FiniteAvalanches.Electrical.Dirichlet

/-! Signed copy incidence and its anchored divergence. No plane conclusions are assumed. -/
namespace FiniteAvalanches.Electrical.Plane
open scoped Classical BigOperators

/-- Signed outgoing incidence of a once-oriented copied flow. Loops cancel. -/
noncomputable def copyBoundary {V E : Type*} [Fintype E] (a b : E → V)
    (j : E → ℝ) (x : V) : ℝ :=
  ∑ e, ((if a e = x then j e else 0)-(if b e = x then j e else 0))

noncomputable def boundaryMap {V E : Type*} [Fintype E] (a b : E → V) :
    (E → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun j := copyBoundary a b j
  map_add' j k := by
    funext x
    simp only [copyBoundary,Pi.add_apply,← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by split_ifs <;> ring
  map_smul' r j := by
    funext x
    simp only [copyBoundary,Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by split_ifs <;> ring

/-- Restrict divergence to vertices other than the chosen root. -/
noncomputable def anchoredBoundary {V E : Type*} [Fintype E] (a b : E → V) (root : V) :
    (E → ℝ) →ₗ[ℝ] ({x : V // x ≠ root} → ℝ) where
  toFun j x := copyBoundary a b j x.val
  map_add' j k := by funext x; exact congrFun ((boundaryMap a b).map_add j k) x
  map_smul' r j := by funext x; exact congrFun ((boundaryMap a b).map_smul r j) x

/-- Physical primal gradient, positive from the a endpoint to the b endpoint. -/
def copyGradient {V E : Type*} (a b : E → V) (q : V → ℝ) (e : E) : ℝ := q (a e)-q (b e)

theorem copyBoundary_gradient {V E : Type*} [Fintype E] (a b : E → V) (q : V → ℝ) (x : V) :
    copyBoundary a b (copyGradient a b q) x = laplacian a b q x := by
  unfold copyBoundary copyGradient laplacian
  apply Finset.sum_congr rfl
  intro e _
  split_ifs with ha hb <;> simp_all

theorem sum_copyBoundary {V E : Type*} [Fintype V] [Fintype E]
    (a b : E → V) (j : E → ℝ) : (∑ x, copyBoundary a b j x) = 0 := by
  unfold copyBoundary
  rw [Finset.sum_comm]
  simp only [Finset.sum_sub_distrib,Finset.sum_ite_eq,Finset.mem_univ,if_true,
    sub_self,Finset.sum_const_zero]

/-- Omitting the root loses no zero-divergence equation, since total divergence is zero. -/
theorem anchoredBoundary_eq_zero_iff {V E : Type*} [Fintype V] [Fintype E]
    (a b : E → V) (root : V) (j : E → ℝ) :
    anchoredBoundary a b root j = 0 ↔ ∀ x, copyBoundary a b j x = 0 := by
  constructor
  · intro h x
    have hz (y : V) (hy : y ≠ root) : copyBoundary a b j y = 0 := congrFun h ⟨y,hy⟩
    by_cases hx : x = root
    · subst x
      have hs := sum_copyBoundary a b j
      have ht : ∀ y, copyBoundary a b j y = if y = root then copyBoundary a b j root else 0 := by
        intro y
        by_cases hy : y = root
        · simp [hy]
        · simp [hy,hz y hy]
      rw [Finset.sum_congr rfl (fun y _ => ht y)] at hs
      simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true] at hs
      exact hs
    · exact hz x hx
  · intro h
    funext x
    exact h x.val

/-- Every nonroot divergence prescription is attained on a connected copied graph. -/
theorem anchoredBoundary_surjective {V E : Type*} [Fintype V] [Fintype E]
    (a b : E → V) (root : V) (hc : (supportGraph a b).Preconnected) :
    Function.Surjective (anchoredBoundary a b root) := by
  let B : Finset V := {root}
  have hB : ∀ x, ∃ y ∈ B, (supportGraph a b).Reachable x y :=
    fun x => ⟨root,Finset.mem_singleton_self root,hc x root⟩
  intro k
  let rhs : {x : V // x ∉ B} → ℝ := fun x => k ⟨x.val,by simpa only [B,Finset.mem_singleton] using x.property⟩
  obtain ⟨q,hq⟩ := LinearMap.surjective_of_injective (dirichletMap_injective a b B hB) rhs
  refine ⟨copyGradient a b (zeroExtend B q),?_⟩
  funext x
  change copyBoundary a b (copyGradient a b (zeroExtend B q)) x.val = k x
  rw [copyBoundary_gradient]
  exact congrFun hq ⟨x.val,by simpa only [B,Finset.mem_singleton] using x.property⟩

end FiniteAvalanches.Electrical.Plane
