import FiniteAvalanches.Electrical.Geometry.OrientedDrawing
import FiniteAvalanches.Support.Plane.SelectedDrawing
import Mathlib.Topology.Subpath

/-!
# Paths along drawn edges through edge midpoints

A path built from drawn edge curves passes through the midpoint of an edge
exactly when it traverses that edge. The passage is recorded with its
direction: the path runs along the edge with an affine parametrization near
the passage time. This record is preserved by reversal, concatenation and
finite concatenation, provided that at most one piece passes through the
midpoint.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set Source
open scoped Classical

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- The midpoint parameter of an edge curve. -/
noncomputable def halfParameter : ArcParameter := ⟨1 / 2, by norm_num, by norm_num⟩

/-- A path passes once through the midpoint of an edge, running along the edge
in the direction `σ` with an affine parametrization near the passage time. -/
def PathCrossesEdge (D : Drawing J) (e : E) {a b : ℝ × ℝ} (P : Path a b) (σ : ℤ) : Prop :=
  (σ = 1 ∨ σ = -1) ∧ ∃ t₀ : unitInterval, 0 < (t₀ : ℝ) ∧ (t₀ : ℝ) < 1 ∧
    (∀ t, P t = D.curve e halfParameter → t = t₀) ∧
    ∃ ε > 0, ∃ κ > 0, ∀ t : unitInterval, |(t : ℝ) - t₀| < ε →
      P t = D.curve e (projIcc 0 1 zero_le_one (1 / 2 + σ * κ * ((t : ℝ) - t₀)))

/-- The signed passage of a path through the midpoint of an edge: either the
path avoids the midpoint and the sign is zero, or it crosses with sign `σ`. -/
def EdgeCrossingSign (D : Drawing J) (e : E) {a b : ℝ × ℝ} (P : Path a b) (σ : ℤ) : Prop :=
  (σ = 0 ∧ ∀ t, P t ≠ D.curve e halfParameter) ∨ PathCrossesEdge D e P σ

/-- The edge path evaluates to the drawn curve. -/
theorem Drawing.edgePath_apply (D : Drawing J) (e : E) (t : unitInterval) :
    D.edgePath e t = D.curve e t := rfl

/-- An edge curve passes through its own midpoint only at the midpoint parameter. -/
theorem Drawing.curve_eq_half_iff (D : Drawing J) (e : E) (t : ArcParameter) :
    D.curve e t = D.curve e halfParameter ↔ t = halfParameter := by
  constructor
  · intro h
    by_cases ht : t.val = 1
    · have he : t = ⟨1, by constructor <;> norm_num⟩ := Subtype.ext ht
      rw [he, D.finish] at h
      exact (D.avoids e halfParameter (by norm_num [halfParameter])
        (by norm_num [halfParameter]) _ h.symm).elim
    · exact D.injective e (lt_of_le_of_ne t.2.2 ht)
        (show (1 : ℝ) / 2 < 1 by norm_num) h
  · rintro rfl
    rfl

/-- The curve of an edge crosses its own midpoint forward. -/
theorem Drawing.edgePath_crossesEdge (D : Drawing J) (e : E) :
    PathCrossesEdge D e (D.edgePath e) 1 := by
  refine ⟨Or.inl rfl, halfParameter, by norm_num [halfParameter], by norm_num [halfParameter],
    fun t ht => (D.curve_eq_half_iff e t).mp ht, 1 / 2, by norm_num, 1, one_pos, ?_⟩
  intro t _
  rw [Drawing.edgePath_apply]
  congr 1
  apply Subtype.ext
  rw [coe_projIcc]
  simp only [Int.cast_one, one_mul]
  change (t : ℝ) = max 0 (min 1 (1 / 2 + ((t : ℝ) - 1 / 2)))
  rw [add_sub_cancel, min_eq_right t.2.2, max_eq_right t.2.1]

/-- The curve of another edge avoids the midpoint of an edge. -/
theorem Drawing.edgePath_avoids (D : Drawing J) {e f : E} (hef : f ≠ e) (t : unitInterval) :
    D.edgePath f t ≠ D.curve e halfParameter := by
  intro h
  have := (D.intersects f e hef t halfParameter h).2
  norm_num [halfParameter] at this

/-- The curve of an edge passes through its own midpoint with sign one. -/
theorem Drawing.edgePath_crossingSign_self (D : Drawing J) (e : E) :
    EdgeCrossingSign D e (D.edgePath e) 1 :=
  Or.inr (D.edgePath_crossesEdge e)

/-- The curve of another edge passes through the midpoint of an edge with sign zero. -/
theorem Drawing.edgePath_crossingSign_of_ne (D : Drawing J) {e f : E} (hef : f ≠ e) :
    EdgeCrossingSign D e (D.edgePath f) 0 :=
  Or.inl ⟨rfl, D.edgePath_avoids hef⟩

/-- Casting a path keeps its signed passage. -/
theorem EdgeCrossingSign.cast {D : Drawing J} {e : E} {a b a' b' : ℝ × ℝ} {P : Path a b}
    {σ : ℤ} (h : EdgeCrossingSign D e P σ) (ha : a' = a) (hb : b' = b) :
    EdgeCrossingSign D e (P.cast ha hb) σ := h

/-- Reversing a path reverses its signed passage. -/
theorem EdgeCrossingSign.symm {D : Drawing J} {e : E} {a b : ℝ × ℝ} {P : Path a b} {σ : ℤ}
    (h : EdgeCrossingSign D e P σ) : EdgeCrossingSign D e P.symm (-σ) := by
  rcases h with ⟨rfl, hav⟩ | ⟨hσ, t₀, h0, h1, huniq, ε, hε, κ, hκ, hloc⟩
  · exact Or.inl ⟨by simp, fun t => hav _⟩
  · refine Or.inr ⟨by omega, unitInterval.symm t₀, ?_, ?_, ?_, ε, hε, κ, hκ, ?_⟩
    · simp only [unitInterval.coe_symm_eq]; linarith
    · simp only [unitInterval.coe_symm_eq]; linarith
    · intro t ht
      have := huniq _ ht
      rw [← this, unitInterval.symm_symm]
    · intro t ht
      change P (unitInterval.symm t) = _
      rw [unitInterval.coe_symm_eq] at ht
      have h := hloc (unitInterval.symm t) (by
        rw [unitInterval.coe_symm_eq]
        rw [show 1 - (t : ℝ) - t₀ = -((t : ℝ) - (1 - t₀)) by ring, abs_neg]
        exact ht)
      rw [h]
      congr 2
      simp only [unitInterval.coe_symm_eq, Int.cast_neg]
      ring

/-- A concatenation of two paths, at most one of which passes through the
midpoint, passes through it with the sum of the signs. -/
theorem EdgeCrossingSign.trans {D : Drawing J} {e : E} {a b c : ℝ × ℝ} {P : Path a b}
    {Q : Path b c} {σ τ : ℤ} (hP : EdgeCrossingSign D e P σ) (hQ : EdgeCrossingSign D e Q τ)
    (hστ : σ = 0 ∨ τ = 0) : EdgeCrossingSign D e (P.trans Q) (σ + τ) := by
  rcases hP with ⟨rfl, havP⟩ | ⟨hσ, t₀, h0, h1, huniq, ε, hε, κ, hκ, hloc⟩
  · rcases hQ with ⟨rfl, havQ⟩ | ⟨hτ, t₀, h0, h1, huniq, ε, hε, κ, hκ, hloc⟩
    · refine Or.inl ⟨rfl, fun t => ?_⟩
      rw [Path.trans_apply]
      split_ifs
      · exact havP _
      · exact havQ _
    · refine Or.inr ⟨by simpa using hτ, ⟨((t₀ : ℝ) + 1) / 2, by constructor <;> linarith⟩,
        by simp only; linarith, by simp only; linarith, ?_, min (ε / 2) ((t₀ : ℝ) / 2),
        lt_min (by linarith) (by linarith), 2 * κ, by linarith, ?_⟩
      · intro t ht
        rw [Path.trans_apply] at ht
        split_ifs at ht with h
        · exact (havP _ ht).elim
        · have := congrArg Subtype.val (huniq _ ht)
          simp only at this
          apply Subtype.ext
          simp only
          linarith
      · intro t ht
        have hmin1 := min_le_left (ε / 2) ((t₀ : ℝ) / 2)
        have hmin2 := min_le_right (ε / 2) ((t₀ : ℝ) / 2)
        rw [abs_lt] at ht
        simp only at ht
        have hhalf : ¬ (t : ℝ) ≤ 1 / 2 := by
          intro h
          linarith [ht.1]
        rw [Path.trans_apply, dif_neg hhalf]
        rw [hloc _ (by
          simp only
          rw [abs_lt]
          constructor <;> linarith [ht.1, ht.2])]
        congr 2
        simp only [zero_add]
        ring
  · rcases hστ with hσ0 | rfl
    · rcases hσ with h | h <;> omega
    rcases hQ with ⟨-, havQ⟩ | ⟨hτ, -⟩
    · refine Or.inr ⟨by simpa using hσ, ⟨(t₀ : ℝ) / 2, by constructor <;> linarith⟩,
        by simp only; linarith, by simp only; linarith, ?_, min (ε / 2) ((1 - (t₀ : ℝ)) / 2),
        lt_min (by linarith) (by linarith), 2 * κ, by linarith, ?_⟩
      · intro t ht
        rw [Path.trans_apply] at ht
        split_ifs at ht with h
        · have := congrArg Subtype.val (huniq _ ht)
          simp only at this
          apply Subtype.ext
          simp only
          linarith
        · exact (havQ _ ht).elim
      · intro t ht
        have hmin1 := min_le_left (ε / 2) ((1 - (t₀ : ℝ)) / 2)
        have hmin2 := min_le_right (ε / 2) ((1 - (t₀ : ℝ)) / 2)
        rw [abs_lt] at ht
        simp only at ht
        have hhalf : (t : ℝ) ≤ 1 / 2 := by linarith [ht.2]
        rw [Path.trans_apply, dif_pos hhalf]
        rw [hloc _ (by
          simp only
          rw [abs_lt]
          constructor <;> linarith [ht.1, ht.2])]
        congr 2
        simp only [add_zero]
        ring
    · rcases hτ with h | h <;> omega

/-- A finite concatenation of paths, at most one of which passes through the
midpoint, passes through it with the sum of the signs. -/
theorem EdgeCrossingSign.concat {D : Drawing J} {e : E} {n : ℕ} (p : Fin (n + 1) → ℝ × ℝ)
    (F : (k : Fin n) → Path (p k.castSucc) (p k.succ)) (s : Fin n → ℤ)
    (hF : ∀ k, EdgeCrossingSign D e (F k) (s k))
    (hs : ∀ k k', k ≠ k' → s k = 0 ∨ s k' = 0)
    (hp : ∀ k, p k ≠ D.curve e halfParameter) :
    EdgeCrossingSign D e (Path.concat p F) (∑ k, s k) := by
  induction n with
  | zero =>
    rw [Path.concat_zero, Finset.univ_eq_empty, Finset.sum_empty]
    exact Or.inl ⟨rfl, fun _ => hp 0⟩
  | succ n ih =>
    rw [Path.concat_succ, Fin.sum_univ_castSucc]
    apply EdgeCrossingSign.trans
    · exact ih (p ∘ Fin.castSucc) (fun k => F k.castSucc) (fun k => s k.castSucc)
        (fun k => hF k.castSucc)
        (fun k k' hkk' => hs _ _ (fun h => hkk' (Fin.castSucc_injective _ h)))
        (fun k => hp _)
    · exact hF (Fin.last n)
    · by_cases hlast : s (Fin.last n) = 0
      · exact Or.inr hlast
      · left
        apply Finset.sum_eq_zero
        intro k _
        exact (hs k.castSucc (Fin.last n) (Fin.castSucc_ne_last k)).resolve_right hlast

/-- A finite concatenation of paths in a set stays in the set, when the
junction points lie in it. -/
theorem range_concat_subset {X : Type*} [TopologicalSpace X] {n : ℕ} (p : Fin (n + 1) → X)
    (F : (k : Fin n) → Path (p k.castSucc) (p k.succ)) (S : Set X)
    (hF : ∀ k, range (F k) ⊆ S) (hp : p 0 ∈ S) : range (Path.concat p F) ⊆ S := by
  induction n with
  | zero =>
    rw [Path.concat_zero]
    rintro z ⟨t, rfl⟩
    exact hp
  | succ n ih =>
    rw [Path.concat_succ]
    exact subset_trans (Path.trans_range _ _).subset (union_subset
      (ih (p ∘ Fin.castSucc) (fun k => F k.castSucc) (fun k => hF _) hp) (hF _))

end FiniteAvalanches.Electrical.StatementGeometry
