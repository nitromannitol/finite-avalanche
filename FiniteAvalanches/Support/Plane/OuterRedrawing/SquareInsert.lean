import FiniteAvalanches.Support.Plane.OuterRedrawing.SquareCombine

/-!
# Inserting a pendant part into a cusp

A square realization of a part attached at a single path vertex is inserted
into one half of the cusp at that vertex of another square realization; the
other half of the cusp remains free.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing

open Set Metric
open scoped Classical

noncomputable section

variable {V E : Type} {J : CopiedGraph V E} {m : ℕ} {path : Fin (m + 1) → V} {copies : Fin m → E}

/-- The square folded into the standard cusp, its top left corner at the apex. -/
def cornerToCusp (w : ℝ × ℝ) : ℝ × ℝ := ((w.1 + 1 + (1 - w.2)) / 4, ((w.1 + 1) - (1 - w.2)) / 8)

/-- The upper half of the standard cusp. -/
def cuspUp (w : ℝ × ℝ) : ℝ × ℝ := (w.1, w.1 / 2 + w.2 / 6)

/-- The lower half of the standard cusp. -/
def cuspDown (w : ℝ × ℝ) : ℝ × ℝ := (w.1, -(w.1 / 2) + w.2 / 6)

theorem continuous_cornerToCusp : Continuous cornerToCusp := by
  unfold cornerToCusp
  fun_prop

theorem continuous_cuspUp : Continuous cuspUp := by
  unfold cuspUp
  fun_prop

theorem continuous_cuspDown : Continuous cuspDown := by
  unfold cuspDown
  fun_prop

theorem cornerToCusp_injective : Function.Injective cornerToCusp := by
  intro w w' h
  simp only [cornerToCusp, Prod.mk.injEq] at h
  exact Prod.ext (by linarith [h.1, h.2]) (by linarith [h.1, h.2])

theorem cuspUp_injective : Function.Injective cuspUp := by
  intro w w' h
  simp only [cuspUp, Prod.mk.injEq] at h
  exact Prod.ext h.1 (by linarith [h.1, h.2])

theorem cuspDown_injective : Function.Injective cuspDown := by
  intro w w' h
  simp only [cuspDown, Prod.mk.injEq] at h
  exact Prod.ext h.1 (by linarith [h.1, h.2])

theorem cornerToCusp_mem {w : ℝ × ℝ} (hw : w ∈ closedBall (0 : ℝ × ℝ) 1) :
    cornerToCusp w ∈ cuspTri := by
  rw [mem_closedBall_iff', abs_le, abs_le] at hw
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hw
  simp only [cuspTri, cornerToCusp, mem_setOf_eq]
  refine ⟨by linarith, by linarith, ?_⟩
  rw [abs_le]
  constructor <;> linarith

theorem cornerToCusp_corner : cornerToCusp (-1, 1) = 0 := by
  simp [cornerToCusp]

theorem cuspUp_mem {w : ℝ × ℝ} (hw : w ∈ cuspTri) : cuspUp w ∈ cuspTri := by
  obtain ⟨h1, h2, h3⟩ := hw
  rw [abs_le] at h3
  refine ⟨h1, h2, ?_⟩
  simp only [cuspUp]
  rw [abs_le]
  constructor <;> linarith

theorem cuspDown_mem {w : ℝ × ℝ} (hw : w ∈ cuspTri) : cuspDown w ∈ cuspTri := by
  obtain ⟨h1, h2, h3⟩ := hw
  rw [abs_le] at h3
  refine ⟨h1, h2, ?_⟩
  simp only [cuspDown]
  rw [abs_le]
  constructor <;> linarith

theorem cuspUp_zero : cuspUp 0 = 0 := by simp [cuspUp]

theorem cuspDown_zero : cuspDown 0 = 0 := by simp [cuspDown]

theorem cuspDown_ne_zero {w : ℝ × ℝ} (hw : w ∈ cuspTri) (hw0 : w ≠ 0) : cuspDown w ≠ 0 := by
  intro h
  apply hw0
  obtain ⟨h1, -, h3⟩ := hw
  simp only [cuspDown, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero] at h
  have hv : w.2 = 0 := by
    have := abs_le.mp (h.1 ▸ h3)
    linarith [this.1, this.2]
  exact Prod.ext h.1 hv

theorem cuspUp_eq_cuspDown {w w' : ℝ × ℝ} (hw : w ∈ cuspTri) (hw' : w' ∈ cuspTri)
    (h : cuspUp w = cuspDown w') : w' = 0 := by
  obtain ⟨h1, -, h3⟩ := hw
  obtain ⟨h1', -, h3'⟩ := hw'
  simp only [cuspUp, cuspDown, Prod.mk.injEq] at h
  rw [abs_le] at h3 h3'
  have hu : w'.1 = 0 := by
    rw [← h.1] at h3'
    nlinarith [h.2]
  have hv : w'.2 = 0 := by
    rw [hu] at h3'
    linarith [h3'.1, h3'.2]
  exact Prod.ext hu hv

/-- A square realization of a part attached at one path vertex is inserted into
the cusp at that vertex. -/
theorem SquareRealization.insert {S Y Y' : Set V} {T TY TY' : Set E} {p q a : ℕ}
    (hpa : p ≤ a) (haq : a < q) (hqm : q ≤ m)
    (M : SquareRealization J S T path copies p q)
    (Pd : SquareRealization J Y' TY' path copies a (a + 1)) (hY : Y ⊆ Y') (hTY : TY ⊆ TY')
    (hTS : ∀ e ∈ T, J.left e ∈ S ∧ J.right e ∈ S)
    (hTSY : ∀ e ∈ TY, J.left e ∈ Y ∧ J.right e ∈ Y)
    (hSY : ∀ v ∈ S, v ∈ Y → v = path ⟨a, by omega⟩)
    (haS : path ⟨a, by omega⟩ ∈ S) (haY : path ⟨a, by omega⟩ ∈ Y)
    (hpS : ∀ i : Fin (m + 1), p ≤ (i : ℕ) → (i : ℕ) ≤ q → path i ∈ S)
    (hcT : ∀ i : Fin m, p ≤ (i : ℕ) → (i : ℕ) < q → copies i ∈ T) :
    Nonempty (SquareRealization J (S ∪ Y) (T ∪ TY) path copies p q) := by
  let va : Fin (m + 1) := ⟨a, by omega⟩
  have hva1 : p ≤ (va : ℕ) := hpa
  have hva2 : (va : ℕ) ≤ q := haq.le
  let ψ : ℝ × ℝ → ℝ × ℝ := fun w => M.cusp va (cuspUp (cornerToCusp w))
  have hmapsQ : ∀ w ∈ closedBall (0 : ℝ × ℝ) 1, cuspUp (cornerToCusp w) ∈ cuspTri :=
    fun w hw => cuspUp_mem (cornerToCusp_mem hw)
  let P₀ := Pd.toPartialDrawing.restrict hY hTY
  have hP₀Q : P₀.trace ⊆ closedBall (0 : ℝ × ℝ) 1 :=
    (Pd.toPartialDrawing.restrict_trace_subset hY hTY).trans Pd.trace_sub
  have hψc : ContinuousOn ψ P₀.trace :=
    (M.cusp_cont va hva1 hva2).comp
      ((continuous_cuspUp.comp continuous_cornerToCusp).continuousOn)
      (fun w hw => hmapsQ w (hP₀Q hw))
  have hψi : InjOn ψ P₀.trace := by
    intro w hw w' hw' h
    have := M.cusp_inj va hva1 hva2 (hmapsQ w (hP₀Q hw)) (hmapsQ w' (hP₀Q hw')) h
    exact cornerToCusp_injective (cuspUp_injective this)
  let Y₁ := P₀.map ψ hψc hψi
  have hY₁tr : Y₁.trace = ψ '' P₀.trace := PartialDrawing.map_trace _ _ _ _
  have hcorner : Pd.point (path va) = (-1, 1) := by
    rw [Pd.path_point va le_rfl (by simp [va])]
    rw [topPos_left]
  have hψa : Y₁.point (path va) = M.point (path va) := by
    change ψ (Pd.point (path va)) = _
    rw [hcorner]
    simp only [ψ, cornerToCusp_corner, cuspUp_zero]
    exact M.cusp_tip va hva1 hva2
  have hpt : ∀ v ∈ S ∩ Y, M.point v = Y₁.point v := by
    rintro v ⟨hv1, hv2⟩
    rw [hSY v hv1 hv2, hψa]
  have hmeet : ∀ z ∈ M.trace, z ∈ Y₁.trace → ∃ v ∈ S ∩ Y, z = M.point v := by
    intro z hzM hzY
    rw [hY₁tr] at hzY
    obtain ⟨w, hw, rfl⟩ := hzY
    by_cases h0 : cuspUp (cornerToCusp w) = 0
    · refine ⟨path va, ⟨haS, haY⟩, ?_⟩
      simp only [ψ, h0]
      exact M.cusp_tip va hva1 hva2
    · exact absurd hzM (M.cusp_free va hva1 hva2 _ (hmapsQ w (hP₀Q hw)) h0)
  let U := M.toPartialDrawing.union Y₁ hTS hTSY hpt hmeet
  have hUtr : U.trace ⊆ M.trace ∪ Y₁.trace := PartialDrawing.union_trace_subset _ _ _ _ _ _
  have hY₁cusp : ∀ z ∈ Y₁.trace, ∃ w ∈ cuspTri, z = M.cusp va (cuspUp w) := by
    intro z hz
    rw [hY₁tr] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨cornerToCusp w, cornerToCusp_mem (hP₀Q hw), rfl⟩
  let cusp : Fin (m + 1) → ℝ × ℝ → ℝ × ℝ :=
    fun i => if i = va then M.cusp va ∘ cuspDown else M.cusp i
  have hcusp_a : cusp va = M.cusp va ∘ cuspDown := by simp only [cusp, if_true]
  have hcusp_ne : ∀ i, i ≠ va → cusp i = M.cusp i := by
    intro i hi
    simp only [cusp, hi, if_false]
  have hdownmem : ∀ w ∈ cuspTri, cuspDown w ∈ cuspTri := fun w hw => cuspDown_mem hw
  refine ⟨{ U with
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
    rcases hUtr hz with h | h
    · exact M.trace_sub h
    · obtain ⟨w, hw, rfl⟩ := hY₁cusp z h
      by_cases hw0 : cuspUp w = 0
      · rw [hw0, M.cusp_tip va hva1 hva2]
        exact M.trace_sub (M.toPartialDrawing.point_mem_trace haS)
      · exact ball_subset_closedBall (M.cusp_ball va hva1 hva2 _ (cuspUp_mem hw) hw0)
  · intro i hi1 hi2
    rw [PartialDrawing.union_point_left _ _ _ _ _ _ (hpS i hi1 hi2)]
    exact M.path_point i hi1 hi2
  · intro i hi1 hi2 t
    rw [PartialDrawing.union_curve_left _ _ _ _ _ _ (hcT i hi1 hi2)]
    exact M.path_curve i hi1 hi2 t
  · intro z hz hzb
    rcases hUtr hz with h | h
    · exact M.boundary z h hzb
    · obtain ⟨w, hw, rfl⟩ := hY₁cusp z h
      by_cases hw0 : cuspUp w = 0
      · rw [hw0, M.cusp_tip va hva1 hva2] at hzb ⊢
        exact M.boundary _ (M.toPartialDrawing.point_mem_trace haS) hzb
      · exact absurd (M.cusp_ball va hva1 hva2 _ (cuspUp_mem hw) hw0) hzb
  · intro i hi1 hi2
    by_cases hia : i = va
    · rw [hia, hcusp_a]
      exact (M.cusp_cont va hva1 hva2).comp continuous_cuspDown.continuousOn
        (fun w hw => hdownmem w hw)
    · rw [hcusp_ne i hia]
      exact M.cusp_cont i hi1 hi2
  · intro i hi1 hi2
    by_cases hia : i = va
    · rw [hia, hcusp_a]
      exact (M.cusp_inj va hva1 hva2).comp (cuspDown_injective.injOn) (fun w hw => hdownmem w hw)
    · rw [hcusp_ne i hia]
      exact M.cusp_inj i hi1 hi2
  · intro i hi1 hi2
    rw [PartialDrawing.union_point_left _ _ _ _ _ _ (hpS i hi1 hi2)]
    by_cases hia : i = va
    · rw [hia, hcusp_a, Function.comp_apply, cuspDown_zero]
      exact M.cusp_tip va hva1 hva2
    · rw [hcusp_ne i hia]
      exact M.cusp_tip i hi1 hi2
  · intro i hi1 hi2 w hw hw0
    by_cases hia : i = va
    · rw [hia, hcusp_a, Function.comp_apply]
      exact M.cusp_ball va hva1 hva2 _ (hdownmem w hw) (cuspDown_ne_zero hw hw0)
    · rw [hcusp_ne i hia]
      exact M.cusp_ball i hi1 hi2 w hw hw0
  · intro i hi1 hi2 w hw hw0 hz
    rcases hUtr hz with h | h
    · by_cases hia : i = va
      · rw [hia, hcusp_a, Function.comp_apply] at h
        exact M.cusp_free va hva1 hva2 _ (hdownmem w hw) (cuspDown_ne_zero hw hw0) h
      · rw [hcusp_ne i hia] at h
        exact M.cusp_free i hi1 hi2 w hw hw0 h
    · obtain ⟨w', hw', heq⟩ := hY₁cusp _ h
      by_cases hia : i = va
      · rw [hia, hcusp_a, Function.comp_apply] at heq
        have := M.cusp_inj va hva1 hva2 (hdownmem w hw) (cuspUp_mem hw') heq
        exact hw0 (cuspUp_eq_cuspDown hw' hw this.symm)
      · rw [hcusp_ne i hia] at heq
        exact M.cusp_disj i va hi1 hi2 hva1 hva2 hia w hw _ (cuspUp_mem hw') heq
  · intro i j hi1 hi2 hj1 hj2 hij w hw w' hw' heq
    by_cases hia : i = va <;> by_cases hja : j = va
    · exact hij (hia.trans hja.symm)
    · rw [hia, hcusp_a, hcusp_ne j hja, Function.comp_apply] at heq
      exact M.cusp_disj va j hva1 hva2 hj1 hj2 (Ne.symm hja) _ (hdownmem w hw) w' hw' heq
    · rw [hja, hcusp_a, hcusp_ne i hia, Function.comp_apply] at heq
      exact M.cusp_disj i va hi1 hi2 hva1 hva2 hia w hw _ (hdownmem w' hw') heq
    · rw [hcusp_ne i hia, hcusp_ne j hja] at heq
      exact M.cusp_disj i j hi1 hi2 hj1 hj2 hij w hw w' hw' heq

end
end FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing
