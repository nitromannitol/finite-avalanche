import FiniteAvalanches.Support.Schoenflies.PolygonBridge
import FiniteAvalanches.Support.Schoenflies.Polygonal

/-!
# A Jordan loop with a straight parametrized side

A triangular loop supplies a standard target for straightening a simple arc.
-/

namespace Schoenflies

open Set unitInterval Plane

/-- There is a simple loop whose first half traverses the unit horizontal segment
at constant speed. -/
theorem exists_loop_with_straight_side :
    ∃ g : ℝ → Plane, IsLoop g ∧
      ∀ t ∈ I, g (t / 2) = Plane.mk t 0 := by
  let A : Plane := Plane.mk 0 0
  let B : Plane := Plane.mk 1 0
  let C : Plane := Plane.mk 0 1
  have hAB : A ≠ B := by
    intro h
    have h' := congrArg (fun z : Plane => z 0) h
    norm_num [A, B] at h'
  have hBC : B ≠ C := by
    intro h
    have h' := congrArg (fun z : Plane => z 0) h
    norm_num [B, C] at h'
  have hCA : C ≠ A := by
    intro h
    have h' := congrArg (fun z : Plane => z 1) h
    norm_num [C, A] at h'
  have h₁ : segment ℝ A B ∩ segment ℝ B C ⊆ {B} :=
    segment_inter_shared (by norm_num [Plane.det, Plane.sub_apply, A, B, C])
  have h₂ : segment ℝ B C ∩ segment ℝ C A ⊆ {C} :=
    segment_inter_shared (by norm_num [Plane.det, Plane.sub_apply, A, B, C])
  have h₃ : segment ℝ C A ∩ segment ℝ A B ⊆ {A} :=
    segment_inter_shared (by norm_num [Plane.det, Plane.sub_apply, A, B, C])
  have hreturn : IsArcBetween (segment ℝ B C ∪ segment ℝ C A) B A :=
    (isArcBetween_segment hBC).concatenate (isArcBetween_segment hCA)
      (fun z hz₁ hz₂ => mem_singleton_iff.mp (h₂ ⟨hz₁, hz₂⟩))
  obtain ⟨v, hvc, hvi, hvim, hv0, hv1⟩ := hreturn
  let u : ℝ → Plane := AffineMap.lineMap A B
  have huc : ContinuousOn u I := AffineMap.lineMap_continuous.continuousOn
  have hui : InjOn u I := injOn_lineMap hAB
  have huim : u '' I = segment ℝ A B := (segment_eq_image_lineMap ℝ A B).symm
  have hu0 : u 0 = A := by simp [u]
  have hu1 : u 1 = B := by simp [u]
  have hmeet : ∀ z ∈ u '' I, z ∈ v '' I → z = u 0 ∨ z = u 1 := by
    intro z hz hv
    rw [huim] at hz
    rw [hvim] at hv
    rcases hv with hv | hv
    · right
      rw [hu1]
      exact mem_singleton_iff.mp (h₁ ⟨hz, hv⟩)
    · left
      rw [hu0]
      exact mem_singleton_iff.mp (h₃ ⟨hv, hz⟩)
  have hloop : IsLoop (concatenate u v) :=
    IsLoop.concatenate huc hui hvc hvi (hu1.trans hv0.symm) (hv1.trans hu0.symm) hmeet
  refine ⟨concatenate u v, hloop, ?_⟩
  intro t ht
  rw [concatenate_of_le (by linarith [ht.2])]
  have h2 : 2 * (t / 2) = t := by ring
  rw [h2]
  ext i
  fin_cases i <;> simp [u, AffineMap.lineMap_apply_module, A, B, Plane.mk]

end Schoenflies
