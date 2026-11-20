import FiniteAvalanches.Support.Plane.BoundaryGradientBasis

/-!
# Face-boundary balance from cyclic orders

A permutation of the edge ends that preserves their vertices and carries each
outgoing face to the next incoming face gives the signed face-boundary law.
Both ends of a loop are retained as distinct edge ends.
-/

namespace FiniteAvalanches.Electrical.Plane

open scoped Classical BigOperators

/-- The vertex at an edge end, with `false` selecting the first endpoint. -/
def dartVertex {V E : Type*} (a b : E → V) (i : E × Bool) : V :=
  if i.2 then b i.1 else a i.1

/-- The face following an edge end in the chosen orientation. -/
def dartNextFace {E W : Type*} (c d : E → W) (i : E × Bool) : W :=
  if i.2 then d i.1 else c i.1

/-- The face preceding an edge end in the chosen orientation. -/
def dartPrevFace {E W : Type*} (c d : E → W) (i : E × Bool) : W :=
  if i.2 then c i.1 else d i.1

/-- A face-matching permutation of edge ends makes every dual boundary of a
primal gradient vanish. -/
theorem copyBoundary_gradient_eq_zero_of_dart_permutation {V E W : Type*}
    [Fintype V] [Fintype E] (a b : E → V) (c d : E → W)
    (σ : Equiv.Perm (E × Bool))
    (hvertex : ∀ i, dartVertex a b (σ i) = dartVertex a b i)
    (hface : ∀ i, dartPrevFace c d (σ i) = dartNextFace c d i) :
    ∀ (q : V → ℝ) (F : W), copyBoundary c d (copyGradient a b q) F = 0 := by
  classical
  apply (copyBoundary_gradient_eq_zero_iff_indicators a b c d).mpr
  intro v F
  let f : E × Bool → ℝ := fun i =>
    if dartVertex a b i = v ∧ dartPrevFace c d i = F then 1 else 0
  have heq : (∑ i, (if dartVertex a b i = v ∧ dartNextFace c d i = F then (1 : ℝ) else 0)) =
      ∑ i, f i := by
    calc
      _ = ∑ i, f (σ i) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [f, hvertex, hface]
      _ = _ := Equiv.sum_comp σ f
  have hs : copyBoundary c d (copyGradient a b (Pi.single v 1)) F =
      (∑ i, (if dartVertex a b i = v ∧ dartNextFace c d i = F then (1 : ℝ) else 0)) -
      ∑ i, f i := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    unfold copyBoundary
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    simp only [Fintype.sum_bool, f, dartVertex, dartNextFace, dartPrevFace,
      copyGradient, Pi.single_apply]
    by_cases ha : a e = v <;> by_cases hb : b e = v <;>
      by_cases hc : c e = F <;> by_cases hd : d e = F <;>
      simp [ha, hb, hc, hd]
  rw [hs, heq, sub_self]

/-- The face-boundary law is equivalent to matching edge ends by vertex and
face. The matching need not arise from a prescribed cyclic order. -/
theorem copyBoundary_gradient_eq_zero_iff_dart_permutation {V E W : Type*}
    [Fintype V] [Fintype E] (a b : E → V) (c d : E → W) :
    (∀ (q : V → ℝ) (F : W), copyBoundary c d (copyGradient a b q) F = 0) ↔
      ∃ σ : Equiv.Perm (E × Bool),
        (∀ i, dartVertex a b (σ i) = dartVertex a b i) ∧
        (∀ i, dartPrevFace c d (σ i) = dartNextFace c d i) := by
  classical
  constructor
  · intro h
    let next : E × Bool → V × W := fun i => (dartVertex a b i, dartNextFace c d i)
    let prev : E × Bool → V × W := fun i => (dartVertex a b i, dartPrevFace c d i)
    have hcard (p : V × W) :
        Fintype.card {i // next i = p} = Fintype.card {i // prev i = p} := by
      rcases p with ⟨v, F⟩
      have hs : copyBoundary c d (copyGradient a b (Pi.single v 1)) F =
          (∑ i : E × Bool,
            (if dartVertex a b i = v ∧ dartNextFace c d i = F then (1 : ℝ) else 0)) -
          ∑ i : E × Bool,
            (if dartVertex a b i = v ∧ dartPrevFace c d i = F then (1 : ℝ) else 0) := by
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
        unfold copyBoundary
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro e _
        simp only [Fintype.sum_bool, dartVertex, dartNextFace, dartPrevFace,
          copyGradient, Pi.single_apply]
        by_cases ha : a e = v <;> by_cases hb : b e = v <;>
          by_cases hc : c e = F <;> by_cases hd : d e = F <;>
          simp [ha, hb, hc, hd]
      have heq := (sub_eq_zero.mp (hs.symm.trans (h (Pi.single v 1) F)))
      rw [Fintype.card_subtype, Fintype.card_subtype]
      apply Nat.cast_injective (R := ℝ)
      simpa only [Finset.natCast_card_filter, next, prev, Prod.mk.injEq] using heq
    let σ : Equiv.Perm (E × Bool) :=
      Equiv.ofFiberEquiv (fun p => Fintype.equivOfCardEq (hcard p))
    have hmatch (i : E × Bool) : prev (σ i) = next i :=
      Equiv.ofFiberEquiv_map (fun p => Fintype.equivOfCardEq (hcard p)) i
    exact ⟨σ, fun i => congrArg Prod.fst (hmatch i), fun i => congrArg Prod.snd (hmatch i)⟩
  · rintro ⟨σ, hvertex, hface⟩
    exact copyBoundary_gradient_eq_zero_of_dart_permutation a b c d σ hvertex hface

end FiniteAvalanches.Electrical.Plane
