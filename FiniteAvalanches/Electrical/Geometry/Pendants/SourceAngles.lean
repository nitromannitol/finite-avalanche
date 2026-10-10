import FiniteAvalanches.Electrical.Geometry.Pendants.SixLeafDrawing
import FiniteAvalanches.Electrical.Geometry.BoundaryReflection

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.StatementGeometry.SixLeaf
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] {J : CopiedGraph V E}

/-- Literal six occurrences in the source, with the original ground first. -/
def sourceSix {m : ℕ} (p : Fin (m+1) → V) (i j : Fin m) : Fin 6 → V :=
  ![p (Fin.last m),p 0,p i.castSucc,p i.succ,p j.castSucc,p j.succ]

def sourceAngles {m : ℕ} (β : Fin (m+1) → ℝ) (i j : Fin m) : Fin 6 → ℝ :=
  ![β (Fin.last m),β 0+2*Real.pi,β i.castSucc+2*Real.pi,
    β i.succ+2*Real.pi,β j.castSucc+2*Real.pi,β j.succ+2*Real.pi]

theorem sourceAngles_monotone {m : ℕ} (β : Fin (m+1) → ℝ)
    (hβ : StrictMono β) (hb : β (Fin.last m)<β 0+2*Real.pi)
    (i j : Fin m) (hij : i<j) : Monotone (sourceAngles β i j) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro k
  fin_cases k
  · change β (Fin.last m) ≤ β 0+2*Real.pi
    exact hb.le
  · change β 0+2*Real.pi ≤ β i.castSucc+2*Real.pi
    exact add_le_add (hβ.monotone (show (0:Fin (m+1)) ≤ i.castSucc by
      change 0 ≤ i.val; omega)) (le_refl (2*Real.pi))
  · change β i.castSucc+2*Real.pi ≤ β i.succ+2*Real.pi
    exact add_le_add (hβ.monotone (show i.castSucc ≤ i.succ by
      change i.val ≤ i.val+1; omega)) (le_refl (2*Real.pi))
  · change β i.succ+2*Real.pi ≤ β j.castSucc+2*Real.pi
    exact add_le_add (hβ.monotone (show i.succ ≤ j.castSucc by
      change i.val+1 ≤ j.val; exact Nat.succ_le_of_lt hij)) (le_refl (2*Real.pi))
  · change β j.castSucc+2*Real.pi ≤ β j.succ+2*Real.pi
    exact add_le_add (hβ.monotone (show j.castSucc ≤ j.succ by
      change j.val ≤ j.val+1; omega)) (le_refl (2*Real.pi))

theorem sourceAngles_window {m : ℕ} (β : Fin (m+1) → ℝ) (hβ : StrictMono β)
    (i j : Fin m) : sourceAngles β i j 5 ≤ sourceAngles β i j 0+2*Real.pi := by
  change β j.succ+2*Real.pi ≤ β (Fin.last m)+2*Real.pi
  exact add_le_add (hβ.monotone (show j.succ ≤ Fin.last m by
    change j.val+1 ≤ m; exact Nat.succ_le_of_lt j.isLt)) (le_refl (2*Real.pi))

theorem sourceAngles_points {m : ℕ} (D : Drawing J) (p : Fin (m+1) → V)
    (β : Fin (m+1) → ℝ) (hp : ∀ k, D.point (p k)=unitPoint (β k))
    (i j : Fin m) : ∀ k, D.point (sourceSix p i j k)=unitPoint (sourceAngles β i j k) := by
  intro k
  fin_cases k <;> simp [sourceSix,sourceAngles,hp,unitPoint]

/-- The source ordered boundary-path angles produce the drawing, including cyclic endpoint coincidences. -/
theorem source_ordered_six_leaf_drawing {m : ℕ} (D : Drawing J)
    (p : Fin (m+1) → V) (β : Fin (m+1) → ℝ) (hβ : StrictMono β)
    (hb : β (Fin.last m)<β 0+2*Real.pi) (hp : ∀ k, D.point (p k)=unitPoint (β k))
    (hpoints : ∀ v, D.point v ∈ disk) (hcurves : ∀ e t, D.curve e t ∈ disk)
    (i j : Fin m) (hij : i<j) :
    ∃ (l : ℝ) (D' : Drawing (J.withPendants (sourceSix p i j))),
      0<l ∧ l<1 ∧
      (∀ v, D'.point (Sum.inl v)=scaledPoint (1-l) (D.point v)) ∧
      (∀ e t, D'.curve (Sum.inl e) t=scaledPoint (1-l) (D.curve e t)) ∧
      (∀ v, D'.point v ∈ disk) ∧ (∀ e t, D'.curve e t ∈ disk) ∧
      cyclic_order D' (sixTerminals (V:=V)) :=
  exists_six_leaf_drawing D (sourceSix p i j) (sourceAngles β i j)
    (sourceAngles_monotone β hβ hb i j hij) (sourceAngles_window β hβ i j)
    (sourceAngles_points D p β hp i j) hpoints hcurves

/-- Complete source boundary-path application; the only optional orientation change is explicit. -/
theorem source_boundary_six_leaf_drawing (D : Drawing J) (m : ℕ)
    (p : Fin (m+1) → V) (hp : Function.Injective p) (copies : Fin m → E)
    (hends : ∀ i, (J.left (copies i)=p i.castSucc ∧ J.right (copies i)=p i.succ) ∨
      (J.right (copies i)=p i.castSucc ∧ J.left (copies i)=p i.succ))
    (hboundary : ∀ i t, D.curve (copies i) t ∈ circle)
    (hpoints : ∀ v, D.point v ∈ disk) (hcurves : ∀ e t, D.curve e t ∈ disk)
    (i j : Fin m) (hij : i<j) :
    ∃ D₀ : Drawing J, (D₀=D ∨ D₀=D.reflect) ∧
      ∃ (l : ℝ) (D' : Drawing (J.withPendants (sourceSix p i j))),
        0<l ∧ l<1 ∧
        (∀ v, D'.point (Sum.inl v)=scaledPoint (1-l) (D₀.point v)) ∧
        (∀ e t, D'.curve (Sum.inl e) t=scaledPoint (1-l) (D₀.curve e t)) ∧
        (∀ v, D'.point v ∈ disk) ∧ (∀ e t, D'.curve e t ∈ disk) ∧
        cyclic_order D' (sixTerminals (V:=V)) := by
  obtain ⟨D₀,hD₀,β,hβ,hspan,hβpoint⟩ :=
    D.boundary_path_ordered_angles m (by omega) p hp copies hends hboundary
  have hpoint₀ : ∀ v, D₀.point v ∈ disk := by
    rcases hD₀ with hD₀|hD₀
    · rw [hD₀]; exact hpoints
    · rw [hD₀]
      intro v
      exact (reflectPoint_mem_disk _).mpr (hpoints v)
  have hcurve₀ : ∀ e t, D₀.curve e t ∈ disk := by
    rcases hD₀ with hD₀|hD₀
    · rw [hD₀]; exact hcurves
    · rw [hD₀]
      intro e t
      exact (reflectPoint_mem_disk _).mpr (hcurves e t)
  exact ⟨D₀,hD₀,source_ordered_six_leaf_drawing D₀ p β hβ hspan hβpoint hpoint₀ hcurve₀ i j hij⟩

end
end FiniteAvalanches.Electrical.StatementGeometry.SixLeaf
