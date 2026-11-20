import FiniteAvalanches.Support.Plane.LoopPathReduction

/-!
# Residual points of a loop cancellation

For a maximal loop cancellation, endpoints remain outside every loop interior
and no interior residual point is isolated.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set

/-- The points not belonging to the interior of any cancelled loop. -/
def loopResidual (S : Set (unitInterval × unitInterval)) : Set unitInterval :=
  {t | ∀ v ∈ S, t ∉ Ioo v.1 v.2}

/-- The residual of a family of loop interiors is closed. -/
theorem isClosed_loopResidual (S : Set (unitInterval × unitInterval)) :
    IsClosed (loopResidual S) := by
  have heq : loopResidual S = (⋃ v ∈ S, Ioo v.1 v.2)ᶜ := by
    ext t
    simp only [loopResidual, mem_setOf_eq, mem_compl_iff, mem_iUnion, not_exists]
  rw [heq]
  exact (isOpen_iUnion fun v => isOpen_iUnion fun _ => isOpen_Ioo).isClosed_compl

/-- Both endpoints of each maximal cancelled loop are residual. -/
theorem IsLoopCancellation.endpoints_mem_loopResidual_of_maximal
    {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    {S : Set (unitInterval × unitInterval)} (hS : IsLoopCancellation p S)
    (hmax : ∀ T, IsLoopCancellation p T → LoopFamilyRefines S T → LoopFamilyRefines T S)
    {v : unitInterval × unitInterval} (hv : v ∈ S) :
    v.1 ∈ loopResidual S ∧ v.2 ∈ loopResidual S := by
  constructor <;> intro w hw hmem
  · by_cases heq : v = w
    · subst w
      exact (lt_irrefl v.1) hmem.1
    · rcases hS.separated_of_maximal p hmax hv hw heq with hlt | hlt
      · exact (not_lt_of_ge ((hS.1 v hv).1.le.trans hlt.le)) hmem.1
      · exact (not_lt_of_ge hlt.le) hmem.2
  · by_cases heq : v = w
    · subst w
      exact (lt_irrefl v.2) hmem.2
    · rcases hS.separated_of_maximal p hmax hv hw heq with hlt | hlt
      · exact (not_lt_of_ge hlt.le) hmem.1
      · exact (not_lt_of_ge (hlt.le.trans (hS.1 v hv).1.le)) hmem.2

/-- No residual point strictly inside the parameter interval is isolated. -/
theorem IsLoopCancellation.residual_not_isolated_of_maximal
    {X : Type*} [TopologicalSpace X] {x y : X} (p : Path x y)
    {S : Set (unitInterval × unitInterval)} (hS : IsLoopCancellation p S)
    (hmax : ∀ T, IsLoopCancellation p T → LoopFamilyRefines S T → LoopFamilyRefines T S)
    {z l r : unitInterval} (hz : z ∈ loopResidual S) (hl : l < z) (hr : z < r) :
    ∃ t ∈ loopResidual S, t ∈ Ioo l r ∧ t ≠ z := by
  classical
  by_contra hnone
  have hbad : ∀ t ∈ loopResidual S, t ∈ Ioo l r → t = z := by
    intro t htF htlr
    by_contra hne
    exact hnone ⟨t, htF, htlr, hne⟩
  obtain ⟨a, hla, haz⟩ := exists_between hl
  obtain ⟨b, hzb, hbr⟩ := exists_between hr
  have haF : a ∉ loopResidual S := by
    intro ha
    exact (ne_of_lt haz) (hbad a ha ⟨hla, lt_trans haz hr⟩)
  have hbF : b ∉ loopResidual S := by
    intro hb
    exact (ne_of_gt hzb) (hbad b hb ⟨lt_trans hl hzb, hbr⟩)
  have haLoop : ∃ v ∈ S, a ∈ Ioo v.1 v.2 := by
    by_contra h
    apply haF
    intro v hv hav
    exact h ⟨v, hv, hav⟩
  have hbLoop : ∃ w ∈ S, b ∈ Ioo w.1 w.2 := by
    by_contra h
    apply hbF
    intro w hw hbw
    exact h ⟨w, hw, hbw⟩
  obtain ⟨v, hv, hav⟩ := haLoop
  obtain ⟨w, hw, hbw⟩ := hbLoop
  have hvz : v.2 ≤ z := by
    by_contra h
    exact hz v hv ⟨lt_trans hav.1 haz, lt_of_not_ge h⟩
  have hzw : z ≤ w.1 := by
    by_contra h
    exact hz w hw ⟨lt_of_not_ge h, lt_trans hzb hbw.2⟩
  have hv2 : v.2 = z := by
    apply hbad v.2 (hS.endpoints_mem_loopResidual_of_maximal p hmax hv).2
    exact ⟨lt_trans hla hav.2, lt_of_le_of_lt hvz hr⟩
  have hw1 : w.1 = z := by
    apply hbad w.1 (hS.endpoints_mem_loopResidual_of_maximal p hmax hw).1
    exact ⟨lt_of_lt_of_le hl hzw, lt_trans hbw.1 hbr⟩
  exact hS.not_adjacent_of_maximal p hmax hv hw (hv2.trans hw1.symm)

end FiniteAvalanches.Electrical.StatementGeometry
