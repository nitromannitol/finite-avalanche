import FiniteAvalanches.Support.Plane.OuterRedrawing.StraightSetting
import FiniteAvalanches.Electrical.Geometry.DrawingBoundaryPath

/-!
# The curve of a simple path of a drawing

The curves of the edges of a simple path, each traversed from its earlier to its
later path vertex, are glued into one simple curve parametrized by the unit
interval, the `i`-th edge by the subinterval `[i / m, (i + 1) / m]`.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing

open Set
open scoped Classical

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}
variable {m : ℕ} {path : Fin (m + 1) → V} {copies : Fin m → E}

/-- The reversed parameter. -/
def flipParam (s : ArcParameter) : ArcParameter :=
  ⟨1 - s.val, by constructor <;> linarith [s.2.1, s.2.2]⟩

theorem flipParam_flipParam (s : ArcParameter) : flipParam (flipParam s) = s :=
  Subtype.ext (by simp [flipParam])

theorem continuous_flipParam : Continuous flipParam :=
  Continuous.subtype_mk (continuous_const.sub continuous_subtype_val) _

/-- The curve of a path edge, traversed from its earlier to its later path vertex. -/
def edgeArc (D : Drawing J) (path : Fin (m + 1) → V) (copies : Fin m → E) (i : Fin m)
    (s : ArcParameter) : ℝ × ℝ :=
  if J.left (copies i) = path i.castSucc then D.curve (copies i) s
  else D.curve (copies i) (flipParam s)

/-- The parameter of a point of the unit interval along the `i`-th subinterval. -/
def localParam (m : ℕ) (i : ℕ) (t : ArcParameter) : ArcParameter :=
  projIcc 0 1 zero_le_one ((m : ℝ) * t.val - i)

/-- The `i`-th closed subinterval of the unit interval. -/
def piece (m : ℕ) (i : ℕ) : Set ArcParameter :=
  {t | (i : ℝ) / m ≤ t.val ∧ t.val ≤ ((i : ℝ) + 1) / m}

section Ends

variable (D : Drawing J)
variable (hinj : Function.Injective path)
variable (hends : ∀ i, (J.left (copies i) = path i.castSucc ∧ J.right (copies i) = path i.succ) ∨
  (J.right (copies i) = path i.castSucc ∧ J.left (copies i) = path i.succ))
include hends

theorem edgeArc_zero (i : Fin m) :
    edgeArc D path copies i zeroParam = D.point (path i.castSucc) := by
  unfold edgeArc
  split_ifs with hf
  · rw [D.start, hf]
  · rcases hends i with ⟨hl, -⟩ | ⟨hr, -⟩
    · exact absurd hl hf
    · have : flipParam zeroParam = oneParam := Subtype.ext (by simp [flipParam])
      rw [this, D.finish, hr]

include hinj in
theorem edgeArc_one (i : Fin m) :
    edgeArc D path copies i oneParam = D.point (path i.succ) := by
  have hne : path i.castSucc ≠ path i.succ := fun h => by
    have := congrArg Fin.val (hinj h)
    simp at this
  unfold edgeArc
  split_ifs with hf
  · rcases hends i with ⟨-, hr⟩ | ⟨-, hl⟩
    · rw [D.finish, hr]
    · exact absurd (hf.symm.trans hl) hne
  · rcases hends i with ⟨hl, -⟩ | ⟨-, hl⟩
    · exact absurd hl hf
    · have : flipParam oneParam = zeroParam := Subtype.ext (by simp [flipParam])
      rw [this, D.start, hl]

omit [Fintype V] [Fintype E] in
include hinj in
theorem left_ne_right (i : Fin m) : J.left (copies i) ≠ J.right (copies i) := by
  have hne : path i.castSucc ≠ path i.succ := fun h => by
    have := congrArg Fin.val (hinj h)
    simp at this
  rcases hends i with ⟨hl, hr⟩ | ⟨hr, hl⟩
  · rw [hl, hr]
    exact hne
  · rw [hl, hr]
    exact hne.symm

include hinj in
theorem edgeArc_injective (i : Fin m) : Function.Injective (edgeArc D path copies i) := by
  have hc := D.nonloop_curve_injective (copies i) (left_ne_right hinj hends i)
  unfold edgeArc
  split_ifs
  · exact hc
  · intro s t hst
    have := hc hst
    rw [← flipParam_flipParam s, ← flipParam_flipParam t, this]

omit hends in
theorem continuous_edgeArc (i : Fin m) : Continuous (edgeArc D path copies i) := by
  unfold edgeArc
  split_ifs
  · exact D.continuous _
  · exact (D.continuous _).comp continuous_flipParam

omit hends in
theorem edgeArc_eq_curve (i : Fin m) (s : ArcParameter) :
    ∃ s', edgeArc D path copies i s = D.curve (copies i) s' ∧
      ((s'.val = 0 ∨ s'.val = 1) → (s.val = 0 ∨ s.val = 1)) := by
  unfold edgeArc
  split_ifs
  · exact ⟨s, rfl, id⟩
  · refine ⟨flipParam s, rfl, ?_⟩
    simp only [flipParam]
    rintro (h | h)
    · right
      linarith
    · left
      linarith

omit hends in
theorem curve_eq_edgeArc (i : Fin m) (s : ArcParameter) :
    ∃ s', edgeArc D path copies i s' = D.curve (copies i) s := by
  unfold edgeArc
  split_ifs
  · exact ⟨s, rfl⟩
  · exact ⟨flipParam s, by rw [flipParam_flipParam]⟩

end Ends

theorem localParam_of_mem {m i : ℕ} (hm : (0 : ℝ) < m) {t : ArcParameter} (ht : t ∈ piece m i) :
    (localParam m i t).val = (m : ℝ) * t.val - i := by
  obtain ⟨h0, h1⟩ := ht
  have h0' : (i : ℝ) ≤ m * t.val := by
    rw [div_le_iff₀ hm] at h0
    linarith
  have h1' : (m : ℝ) * t.val ≤ i + 1 := by
    rw [le_div_iff₀ hm] at h1
    linarith
  unfold localParam
  rw [projIcc_of_mem]
  constructor <;> linarith

theorem isClosed_piece (m i : ℕ) : IsClosed (piece m i) :=
  (isClosed_le continuous_const continuous_subtype_val).inter
    (isClosed_le continuous_subtype_val continuous_const)

section Glue

variable (D : Drawing J)
variable (hinj : Function.Injective path)
variable (hends : ∀ i, (J.left (copies i) = path i.castSucc ∧ J.right (copies i) = path i.succ) ∨
  (J.right (copies i) = path i.castSucc ∧ J.left (copies i) = path i.succ))
include hinj hends

theorem edgeArc_agree (hm : 0 < m) (i j : Fin m) {t : ArcParameter} (hi : t ∈ piece m i)
    (hj : t ∈ piece m j) :
    edgeArc D path copies i (localParam m i t) = edgeArc D path copies j (localParam m j t) := by
  have hmr : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hti := localParam_of_mem hmr hi
  have htj := localParam_of_mem hmr hj
  obtain ⟨hi0, hi1⟩ := hi
  obtain ⟨hj0, hj1⟩ := hj
  rw [div_le_iff₀ hmr] at hi0 hj0
  rw [le_div_iff₀ hmr] at hi1 hj1
  rcases lt_trichotomy (i : ℕ) j with hij | hij | hij
  · have hij' : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    have h1 : localParam m i t = oneParam := Subtype.ext (by rw [hti]; linarith)
    have h2 : localParam m j t = zeroParam := Subtype.ext (by rw [htj]; linarith)
    rw [h1, h2, edgeArc_one D hinj hends, edgeArc_zero D hends]
    congr 2
    ext
    simp only [Fin.val_succ, Fin.val_castSucc]
    have : ((i : ℕ) : ℝ) + 1 = j := by linarith
    exact_mod_cast this
  · rw [Fin.ext hij]
  · have hji' : (j : ℝ) + 1 ≤ i := by exact_mod_cast hij
    have h1 : localParam m j t = oneParam := Subtype.ext (by rw [htj]; linarith)
    have h2 : localParam m i t = zeroParam := Subtype.ext (by rw [hti]; linarith)
    rw [h1, h2, edgeArc_one D hinj hends, edgeArc_zero D hends]
    congr 2
    ext
    simp only [Fin.val_succ, Fin.val_castSucc]
    have : ((j : ℕ) : ℝ) + 1 = i := by linarith
    exact_mod_cast this.symm

/-- The simple curve of the path, its `i`-th edge on the `i`-th subinterval. -/
theorem exists_pathCurve (hm : 0 < m) :
    ∃ γ : ArcParameter → ℝ × ℝ, Continuous γ ∧ Function.Injective γ ∧
      (∀ (k : Fin (m + 1)) (t : ArcParameter), t.val = (k : ℝ) / m → γ t = D.point (path k)) ∧
      ∀ (i : Fin m) (s : ArcParameter), ∃ t : ArcParameter, (i : ℝ) / m ≤ t.val ∧
        t.val ≤ ((i : ℝ) + 1) / m ∧ γ t = D.curve (copies i) s := by
  have hmr : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hcov : ∀ t : ArcParameter, ∃ i : Fin m, t ∈ piece m i := fun t =>
    exists_index_of_mem_Icc hm t.2.1 t.2.2
  let γ : ArcParameter → ℝ × ℝ := fun t =>
    edgeArc D path copies (Classical.choose (hcov t)) (localParam m (Classical.choose (hcov t)).val t)
  have hγ : ∀ (i : Fin m) (t : ArcParameter), t ∈ piece m i →
      γ t = edgeArc D path copies i (localParam m i t) := fun i t ht =>
    edgeArc_agree D hinj hends hm _ i (Classical.choose_spec (hcov t)) ht
  have hcont : Continuous γ := by
    refine LocallyFinite.continuous (locallyFinite_of_finite fun i : Fin m => piece m i) ?_
      (fun i => isClosed_piece m i) fun i => ?_
    · exact eq_univ_of_forall fun t => mem_iUnion.mpr (hcov t)
    · refine ContinuousOn.congr (f := fun t => edgeArc D path copies i (localParam m i t))
        ?_ fun t ht => hγ i t ht
      exact ((continuous_edgeArc D i).comp
        (continuous_projIcc.comp ((continuous_const.mul continuous_subtype_val).sub
          continuous_const))).continuousOn
  have hvert : ∀ (k : Fin (m + 1)) (t : ArcParameter), t.val = (k : ℝ) / m →
      γ t = D.point (path k) := by
    intro k t htk
    by_cases hk : (k : ℕ) < m
    · have ht : t ∈ piece m (⟨k, hk⟩ : Fin m) := by
        refine ⟨by rw [htk], ?_⟩
        rw [htk]
        exact div_le_div_of_nonneg_right (by simp) hmr.le
      rw [hγ _ t ht]
      have h0 : localParam m (⟨k, hk⟩ : Fin m) t = zeroParam := by
        apply Subtype.ext
        rw [localParam_of_mem hmr ht, htk]
        field_simp
        ring
      rw [h0, edgeArc_zero D hends]
      rfl
    · have hkm : (k : ℕ) = m := by omega
      have hm1 : m - 1 < m := by omega
      have ht : t ∈ piece m (⟨m - 1, hm1⟩ : Fin m) := by
        have hc : ((m - 1 : ℕ) : ℝ) = m - 1 := by
          rw [Nat.cast_sub (by omega), Nat.cast_one]
        refine ⟨?_, ?_⟩
        · rw [htk, hkm]
          change ((m - 1 : ℕ) : ℝ) / m ≤ (m : ℝ) / m
          rw [hc]
          exact div_le_div_of_nonneg_right (by linarith) hmr.le
        · rw [htk, hkm]
          change (m : ℝ) / m ≤ (((m - 1 : ℕ) : ℝ) + 1) / m
          rw [hc, sub_add_cancel]
      rw [hγ _ t ht]
      have h1 : localParam m (⟨m - 1, hm1⟩ : Fin m) t = oneParam := by
        apply Subtype.ext
        rw [localParam_of_mem hmr ht, htk, hkm]
        change (m : ℝ) * ((m : ℝ) / m) - ((m - 1 : ℕ) : ℝ) = 1
        rw [Nat.cast_sub (by omega), Nat.cast_one]
        field_simp
        ring
      rw [h1, edgeArc_one D hinj hends]
      congr 1
      congr 1
      ext
      simp only [Fin.val_succ]
      omega
  have hedge : ∀ (i : Fin m) (s : ArcParameter), ∃ t : ArcParameter, (i : ℝ) / m ≤ t.val ∧
      t.val ≤ ((i : ℝ) + 1) / m ∧ γ t = D.curve (copies i) s := by
    intro i s
    obtain ⟨s', hs'⟩ := curve_eq_edgeArc D i s
    have hi : (i : ℝ) + 1 ≤ m := by exact_mod_cast i.2
    let t : ArcParameter := ⟨((i : ℝ) + s'.val) / m, div_nonneg (by linarith [s'.2.1]) hmr.le,
      (div_le_one hmr).mpr (by linarith [s'.2.2])⟩
    have ht : t ∈ piece m i := ⟨div_le_div_of_nonneg_right (by linarith [s'.2.1]) hmr.le,
      div_le_div_of_nonneg_right (by linarith [s'.2.2]) hmr.le⟩
    refine ⟨t, ht.1, ht.2, ?_⟩
    rw [hγ i t ht, ← hs']
    congr 1
    apply Subtype.ext
    rw [localParam_of_mem hmr ht]
    change (m : ℝ) * (((i : ℝ) + s'.val) / m) - i = s'.val
    field_simp
    ring
  refine ⟨γ, hcont, ?_, hvert, hedge⟩
  -- injectivity
  have hcopies := Drawing.simple_path_copies_injective D m path hinj copies hends
  have hend : ∀ (i : Fin m) (t : ArcParameter), t ∈ piece m i →
      ((localParam m i t).val = 0 ∨ (localParam m i t).val = 1) →
      ∃ k : Fin (m + 1), t.val = (k : ℝ) / m := by
    intro i t ht hl
    rw [localParam_of_mem hmr ht] at hl
    rcases hl with hl | hl
    · refine ⟨i.castSucc, ?_⟩
      simp only [Fin.val_castSucc]
      field_simp
      linarith
    · refine ⟨i.succ, ?_⟩
      simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
      field_simp
      linarith
  have hparam : ∀ (k k' : Fin (m + 1)) (t t' : ArcParameter), t.val = (k : ℝ) / m →
      t'.val = (k' : ℝ) / m → γ t = γ t' → t = t' := by
    intro k k' t t' hk hk' h
    rw [hvert k t hk, hvert k' t' hk'] at h
    have := hinj (D.point_injective h)
    apply Subtype.ext
    rw [hk, hk', this]
  intro t t' h
  obtain ⟨i, hi⟩ := hcov t
  obtain ⟨j, hj⟩ := hcov t'
  have h' := h
  change γ t = γ t' at h'
  rw [hγ i t hi, hγ j t' hj] at h'
  by_cases hij : i = j
  · subst hij
    have := edgeArc_injective D hinj hends i h'
    have h1 := congrArg Subtype.val this
    rw [localParam_of_mem hmr hi, localParam_of_mem hmr hj] at h1
    apply Subtype.ext
    have : (m : ℝ) * t.val = m * t'.val := by linarith
    exact mul_left_cancel₀ hmr.ne' this
  · obtain ⟨s, hs, hs01⟩ := edgeArc_eq_curve D i (localParam m i t)
    obtain ⟨s', hs', hs'01⟩ := edgeArc_eq_curve D j (localParam m j t')
    rw [hs, hs'] at h'
    obtain ⟨h1, h2⟩ := D.intersects _ _ (hcopies.ne hij) s s' h'
    obtain ⟨k, hk⟩ := hend i t hi (hs01 h1)
    obtain ⟨k', hk'⟩ := hend j t' hj (hs'01 h2)
    exact hparam k k' t t' hk hk' h

end Glue

end
end FiniteAvalanches.Electrical.StatementGeometry.OuterRedrawing
