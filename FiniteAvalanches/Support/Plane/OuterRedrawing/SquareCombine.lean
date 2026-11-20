import FiniteAvalanches.Support.Plane.OuterRedrawing.SquareRealization

/-!
# Combining square realizations at a path vertex

Square realizations of two selections sharing only one path vertex, the first
carrying the stretch before that vertex and the second the stretch after it,
are squeezed side by side into the square and combined.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing

open Set Metric
open scoped Classical

noncomputable section

variable {V E : Type} {J : CopiedGraph V E} {m : ℕ} {path : Fin (m + 1) → V} {copies : Fin m → E}

theorem topPos_lt {p q : ℕ} (hpq : p < q) {i j : ℕ} (hij : i < j) : topPos p q i < topPos p q j := by
  have hqp : (0 : ℝ) < (q : ℝ) - p := sub_pos.mpr (by exact_mod_cast hpq)
  simp only [topPos]
  have h1 : (i : ℝ) < j := by exact_mod_cast hij
  have := div_lt_div_of_pos_right (mul_lt_mul_of_pos_left (show (i : ℝ) - p < j - p by linarith)
    (by norm_num : (0 : ℝ) < 2)) hqp
  linarith

/-- Two square realizations meeting at one path vertex combine. -/
theorem SquareRealization.combine {S₁ S₂ : Set V} {T₁ T₂ : Set E} {p a q : ℕ} (hpa : p < a)
    (haq : a < q) (hqm : q ≤ m)
    (L : SquareRealization J S₁ T₁ path copies p a)
    (R : SquareRealization J S₂ T₂ path copies a q)
    (hTS₁ : ∀ e ∈ T₁, J.left e ∈ S₁ ∧ J.right e ∈ S₁)
    (hTS₂ : ∀ e ∈ T₂, J.left e ∈ S₂ ∧ J.right e ∈ S₂)
    (hS : ∀ v ∈ S₁, v ∈ S₂ → v = path ⟨a, by omega⟩)
    (hp₁ : ∀ i : Fin (m + 1), p ≤ (i : ℕ) → (i : ℕ) ≤ a → path i ∈ S₁)
    (hp₂ : ∀ i : Fin (m + 1), a ≤ (i : ℕ) → (i : ℕ) ≤ q → path i ∈ S₂)
    (hT : ∀ e ∈ T₁, e ∉ T₂)
    (hc₁ : ∀ i : Fin m, p ≤ (i : ℕ) → (i : ℕ) < a → copies i ∈ T₁)
    (hc₂ : ∀ i : Fin m, a ≤ (i : ℕ) → (i : ℕ) < q → copies i ∈ T₂) :
    Nonempty (SquareRealization J (S₁ ∪ S₂) (T₁ ∪ T₂) path copies p q) := by
  have hqp : (0 : ℝ) < (q : ℝ) - p := sub_pos.mpr (by exact_mod_cast (by omega : p < q))
  set ℓ : ℝ := ((a : ℝ) - p) / ((q : ℝ) - p) with hℓ
  have hℓ0 : 0 < ℓ := div_pos (sub_pos.mpr (by exact_mod_cast hpa)) hqp
  have hℓ1 : ℓ < 1 := by
    rw [hℓ, div_lt_one hqp]
    have : (a : ℝ) < q := by exact_mod_cast haq
    linarith
  let σL := squeeze 0 ℓ
  let σR := squeeze ℓ 1
  have hσLc : Continuous σL := continuous_squeeze _ _
  have hσRc : Continuous σR := continuous_squeeze _ _
  have hσLi : Function.Injective σL := squeeze_injective hℓ0
  have hσRi : Function.Injective σR := squeeze_injective hℓ1
  -- positions
  have hposL : ∀ i : ℕ, -1 + 2 * 0 + (ℓ - 0) * (topPos p a i + 1) = topPos p q i := by
    intro i
    have h := squeeze_topPos (p := p) (q := q) (by omega) (r := p) (s := a) hpa i
    simp only [sub_self, zero_div] at h
    rw [← h, hℓ]
  have hposR : ∀ i : ℕ, -1 + 2 * ℓ + (1 - ℓ) * (topPos a q i + 1) = topPos p q i := by
    intro i
    have h := squeeze_topPos (p := p) (q := q) (by omega) (r := a) (s := q) haq i
    have h1 : ((q : ℝ) - p) / ((q : ℝ) - p) = 1 := div_self hqp.ne'
    rw [h1] at h
    rw [← h, hℓ]
  let L' := L.toPartialDrawing.map σL hσLc.continuousOn hσLi.injOn
  let R' := R.toPartialDrawing.map σR hσRc.continuousOn hσRi.injOn
  have hL'tr : L'.trace = σL '' L.toPartialDrawing.trace :=
    PartialDrawing.map_trace _ _ _ _
  have hR'tr : R'.trace = σR '' R.toPartialDrawing.trace :=
    PartialDrawing.map_trace _ _ _ _
  have hva : (⟨a, by omega⟩ : Fin (m + 1)) = ⟨a, by omega⟩ := rfl
  have hLa : L'.point (path ⟨a, by omega⟩) = (-1 + 2 * ℓ, 1) := by
    change σL (L.point (path ⟨a, by omega⟩)) = _
    rw [L.path_point _ (by simp; omega) (by simp)]
    simp only [σL, squeeze]
    rw [topPos_right hpa]
    ext
    · simp only
      ring
    · rfl
  have hRa : R'.point (path ⟨a, by omega⟩) = (-1 + 2 * ℓ, 1) := by
    change σR (R.point (path ⟨a, by omega⟩)) = _
    rw [R.path_point _ (by simp) (by simp; omega)]
    simp only [σR, squeeze]
    rw [topPos_left]
    ext <;> simp
  have hpt : ∀ v ∈ S₁ ∩ S₂, L'.point v = R'.point v := by
    rintro v ⟨hv1, hv2⟩
    rw [hS v hv1 hv2, hLa, hRa]
  have hmeet : ∀ z ∈ L'.trace, z ∈ R'.trace → ∃ v ∈ S₁ ∩ S₂, z = L'.point v := by
    intro z hzL hzR
    rw [hL'tr] at hzL
    rw [hR'tr] at hzR
    obtain ⟨w₁, hw₁, rfl⟩ := hzL
    obtain ⟨w₂, hw₂, hw₁₂⟩ := hzR
    have hw₁Q := (mem_closedBall_iff'.mp (L.trace_sub hw₁))
    have hw₂Q := (mem_closedBall_iff'.mp (R.trace_sub hw₂))
    have h1 : (σL w₁).1 ≤ -1 + 2 * ℓ := squeeze_fst_le hℓ0 (abs_le.mp hw₁Q.1).2
    have h2 : -1 + 2 * ℓ ≤ (σR w₂).1 := squeeze_fst_ge hℓ1 (abs_le.mp hw₂Q.1).1
    have hw₁1 : w₁.1 = 1 := by
      by_contra hne
      have := squeeze_fst_lt (a := 0) hℓ0 (lt_of_le_of_ne (abs_le.mp hw₁Q.1).2 hne)
      change (σL w₁).1 < _ at this
      rw [hw₁₂] at h2
      linarith
    have hw₁b : w₁ ∉ ball (0 : ℝ × ℝ) 1 := by
      rw [mem_ball_iff']
      rintro ⟨h, -⟩
      rw [hw₁1, abs_one] at h
      exact lt_irrefl _ h
    have hw₁2 := L.boundary w₁ hw₁ hw₁b
    refine ⟨path ⟨a, by omega⟩, ⟨hp₁ _ (by simp; omega) (by simp), hp₂ _ (by simp) (by simp; omega)⟩,
      ?_⟩
    rw [hLa]
    simp only [σL, squeeze]
    ext
    · simp [hw₁1]; ring
    · simp [hw₁2]
  let P := L'.union R' hTS₁ hTS₂ hpt hmeet
  have hPtr : P.trace ⊆ σL '' L.toPartialDrawing.trace ∪ σR '' R.toPartialDrawing.trace := by
    rw [← hL'tr, ← hR'tr]
    exact PartialDrawing.union_trace_subset _ _ _ _ _ _
  have hσLQ : ∀ w ∈ closedBall (0 : ℝ × ℝ) 1, σL w ∈ closedBall (0 : ℝ × ℝ) 1 :=
    fun w hw => squeeze_mem_closedBall le_rfl hℓ0 hℓ1.le hw
  have hσRQ : ∀ w ∈ closedBall (0 : ℝ × ℝ) 1, σR w ∈ closedBall (0 : ℝ × ℝ) 1 :=
    fun w hw => squeeze_mem_closedBall hℓ0.le hℓ1 le_rfl hw
  have hσLB : ∀ w ∈ ball (0 : ℝ × ℝ) 1, σL w ∈ ball (0 : ℝ × ℝ) 1 :=
    fun w hw => squeeze_mem_ball le_rfl hℓ0 hℓ1.le hw
  have hσRB : ∀ w ∈ ball (0 : ℝ × ℝ) 1, σR w ∈ ball (0 : ℝ × ℝ) 1 :=
    fun w hw => squeeze_mem_ball hℓ0.le hℓ1 le_rfl hw
  -- the cusps
  let cusp : Fin (m + 1) → ℝ × ℝ → ℝ × ℝ :=
    fun i => if (i : ℕ) ≤ a then σL ∘ L.cusp i else σR ∘ R.cusp i
  have hcuspL : ∀ i : Fin (m + 1), (i : ℕ) ≤ a → cusp i = σL ∘ L.cusp i := by
    intro i hi
    simp only [cusp, hi, if_true]
  have hcuspR : ∀ i : Fin (m + 1), ¬ (i : ℕ) ≤ a → cusp i = σR ∘ R.cusp i := by
    intro i hi
    simp only [cusp, hi, if_false]
  -- separation of the two halves
  have hLlt : ∀ w ∈ ball (0 : ℝ × ℝ) 1, (σL w).1 < -1 + 2 * ℓ :=
    fun w hw => squeeze_fst_lt hℓ0 (abs_lt.mp (mem_ball_iff'.mp hw).1).2
  have hRgt : ∀ w ∈ ball (0 : ℝ × ℝ) 1, -1 + 2 * ℓ < (σR w).1 :=
    fun w hw => squeeze_fst_gt hℓ1 (abs_lt.mp (mem_ball_iff'.mp hw).1).1
  have hLle : ∀ w ∈ closedBall (0 : ℝ × ℝ) 1, (σL w).1 ≤ -1 + 2 * ℓ :=
    fun w hw => squeeze_fst_le hℓ0 (abs_le.mp (mem_closedBall_iff'.mp hw).1).2
  have hRge : ∀ w ∈ closedBall (0 : ℝ × ℝ) 1, -1 + 2 * ℓ ≤ (σR w).1 :=
    fun w hw => squeeze_fst_ge hℓ1 (abs_le.mp (mem_closedBall_iff'.mp hw).1).1
  -- a right cusp point lies strictly to the right of the separating line
  have hRcusp : ∀ j : Fin (m + 1), a < (j : ℕ) → (j : ℕ) ≤ q → ∀ w ∈ cuspTri,
      -1 + 2 * ℓ < (σR (R.cusp j w)).1 := by
    intro j hj1 hj2 w hw
    by_cases hw0 : w = 0
    · rw [hw0, R.cusp_tip j hj1.le hj2, R.path_point j hj1.le hj2]
      simp only [σR, squeeze]
      have := topPos_lt (p := a) (q := q) haq hj1
      rw [topPos_left] at this
      nlinarith
    · exact hRgt _ (R.cusp_ball j hj1.le hj2 w hw hw0)
  have hLcusp : ∀ i : Fin (m + 1), p ≤ (i : ℕ) → (i : ℕ) ≤ a → ∀ w ∈ cuspTri,
      (σL (L.cusp i w)).1 ≤ -1 + 2 * ℓ := by
    intro i hi1 hi2 w hw
    by_cases hw0 : w = 0
    · rw [hw0, L.cusp_tip i hi1 hi2]
      exact hLle _ (L.trace_sub (L.toPartialDrawing.point_mem_trace (hp₁ i hi1 hi2)))
    · exact (hLlt _ (L.cusp_ball i hi1 hi2 w hw hw0)).le
  refine ⟨{ P with
    trace_sub := ?_
    path_point := ?_
    path_curve := ?_
    boundary := ?_
    cusp := cusp
    cusp_cont := ?_
    cusp_inj := ?_
    cusp_tip := ?_
    cusp_ball := ?_
    cusp_free := ?_
    cusp_disj := ?_ }⟩
  · intro z hz
    rcases hPtr hz with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
    · exact hσLQ _ (L.trace_sub hw)
    · exact hσRQ _ (R.trace_sub hw)
  · intro i hi1 hi2
    by_cases hia : (i : ℕ) ≤ a
    · rw [PartialDrawing.union_point_left _ _ _ _ _ _ (hp₁ i hi1 hia)]
      change σL (L.point (path i)) = _
      rw [L.path_point i hi1 hia]
      simp only [σL, squeeze]
      rw [hposL]
    · push Not at hia
      rw [PartialDrawing.union_point_right _ _ _ _ _ _ (hp₂ i hia.le hi2)]
      change σR (R.point (path i)) = _
      rw [R.path_point i hia.le hi2]
      simp only [σR, squeeze]
      rw [hposR]
  · intro i hi1 hi2 t
    by_cases hia : (i : ℕ) < a
    · rw [PartialDrawing.union_curve_left _ _ _ _ _ _ (hc₁ i hi1 hia)]
      have hc : L'.curve (copies i) t = (-1 + 2 * 0 + (ℓ - 0) * ((L.curve (copies i) t).1 + 1),
          (L.curve (copies i) t).2) := rfl
      rw [hc]
      obtain ⟨h1, h2, h3⟩ := L.path_curve i hi1 hia t
      refine ⟨h1, ?_, ?_⟩
      · rw [← hposL]
        nlinarith
      · rw [← hposL]
        nlinarith
    · push Not at hia
      have hcT := hc₂ i hia hi2
      rw [PartialDrawing.union_curve_right _ _ _ _ _ _ (fun h => hT _ h hcT)]
      have hc : R'.curve (copies i) t = (-1 + 2 * ℓ + (1 - ℓ) * ((R.curve (copies i) t).1 + 1),
          (R.curve (copies i) t).2) := rfl
      rw [hc]
      obtain ⟨h1, h2, h3⟩ := R.path_curve i hia hi2 t
      refine ⟨h1, ?_, ?_⟩
      · rw [← hposR]
        nlinarith
      · rw [← hposR]
        nlinarith
  · intro z hz hzb
    rcases hPtr hz with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
    · have hwb : w ∉ ball (0 : ℝ × ℝ) 1 := fun h => hzb (hσLB w h)
      exact L.boundary w hw hwb
    · have hwb : w ∉ ball (0 : ℝ × ℝ) 1 := fun h => hzb (hσRB w h)
      exact R.boundary w hw hwb
  · intro i hi1 hi2
    by_cases hia : (i : ℕ) ≤ a
    · rw [hcuspL i hia]
      exact hσLc.comp_continuousOn (L.cusp_cont i hi1 hia)
    · rw [hcuspR i hia]
      push Not at hia
      exact hσRc.comp_continuousOn (R.cusp_cont i hia.le hi2)
  · intro i hi1 hi2
    by_cases hia : (i : ℕ) ≤ a
    · rw [hcuspL i hia]
      exact hσLi.comp_injOn (L.cusp_inj i hi1 hia)
    · rw [hcuspR i hia]
      push Not at hia
      exact hσRi.comp_injOn (R.cusp_inj i hia.le hi2)
  · intro i hi1 hi2
    by_cases hia : (i : ℕ) ≤ a
    · rw [hcuspL i hia, Function.comp_apply, L.cusp_tip i hi1 hia,
        PartialDrawing.union_point_left _ _ _ _ _ _ (hp₁ i hi1 hia)]
      rfl
    · rw [hcuspR i hia]
      push Not at hia
      rw [Function.comp_apply, R.cusp_tip i hia.le hi2,
        PartialDrawing.union_point_right _ _ _ _ _ _ (hp₂ i hia.le hi2)]
      rfl
  · intro i hi1 hi2 w hw hw0
    by_cases hia : (i : ℕ) ≤ a
    · rw [hcuspL i hia]
      exact hσLB _ (L.cusp_ball i hi1 hia w hw hw0)
    · rw [hcuspR i hia]
      push Not at hia
      exact hσRB _ (R.cusp_ball i hia.le hi2 w hw hw0)
  · intro i hi1 hi2 w hw hw0 hz
    rcases hPtr hz with ⟨u, hu, hue⟩ | ⟨u, hu, hue⟩
    · by_cases hia : (i : ℕ) ≤ a
      · rw [hcuspL i hia] at hue
        exact L.cusp_free i hi1 hia w hw hw0 (hσLi hue ▸ hu)
      · rw [hcuspR i hia] at hue
        push Not at hia
        have h1 := hRcusp i hia hi2 w hw
        have h2 := hLle u (L.trace_sub hu)
        rw [hue] at h2
        exact absurd h1 (not_lt.mpr h2)
    · by_cases hia : (i : ℕ) ≤ a
      · rw [hcuspL i hia] at hue
        have h1 := hLlt _ (L.cusp_ball i hi1 hia w hw hw0)
        have h2 := hRge u (R.trace_sub hu)
        rw [hue] at h2
        exact absurd h1 (not_lt.mpr h2)
      · rw [hcuspR i hia] at hue
        push Not at hia
        exact R.cusp_free i hia.le hi2 w hw hw0 (hσRi hue ▸ hu)
  · intro i j hi1 hi2 hj1 hj2 hij w hw w' hw' heq
    by_cases hia : (i : ℕ) ≤ a <;> by_cases hja : (j : ℕ) ≤ a
    · rw [hcuspL i hia, hcuspL j hja] at heq
      exact L.cusp_disj i j hi1 hia hj1 hja hij w hw w' hw' (hσLi heq)
    · rw [hcuspL i hia, hcuspR j hja] at heq
      push Not at hja
      have h1 := hLcusp i hi1 hia w hw
      have h2 := hRcusp j hja hj2 w' hw'
      change (σL (L.cusp i w)).1 ≤ _ at h1
      rw [show σL (L.cusp i w) = σR (R.cusp j w') from heq] at h1
      exact absurd h2 (not_lt.mpr h1)
    · rw [hcuspR i hia, hcuspL j hja] at heq
      push Not at hia
      have h1 := hLcusp j hj1 hja w' hw'
      have h2 := hRcusp i hia hi2 w hw
      rw [show σL (L.cusp j w') = σR (R.cusp i w) from heq.symm] at h1
      exact absurd h2 (not_lt.mpr h1)
    · rw [hcuspR i hia, hcuspR j hja] at heq
      push Not at hia hja
      exact R.cusp_disj i j hia.le hi2 hja.le hj2 hij w hw w' hw' (hσRi heq)

end
end FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing
