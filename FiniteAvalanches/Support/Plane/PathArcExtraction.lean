import FiniteAvalanches.Support.Plane.DiffuseCDF

/-!
# Extracting an arc from a path

A maximal cancellation of subloops and a distribution function supported on
its perfect residual core give an injective path in the original path's image.
The loop-deletion argument follows J. Brazas, *Constructing arcs from paths
using Zorn's Lemma*, https://arxiv.org/abs/2207.07242.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set MeasureTheory

/-- A path in a Hausdorff space with distinct endpoints contains an injective
path with the same endpoints in its range. -/
theorem exists_injective_path_in_range
    {X : Type*} [TopologicalSpace X] [T2Space X] {x y : X} (p : Path x y) (hxy : x ≠ y) :
    ∃ q : Path x y, Function.Injective q ∧ range q ⊆ range p := by
  obtain ⟨S, hS, hmax⟩ := exists_maximal_loopCancellation p
  let K := closure (loopResidual S ∩ Ioo 0 1)
  have hK : Perfect K := hS.perfect_interior_loopResidual_of_maximal p hmax
  have hKne : K.Nonempty :=
    (hS.interior_loopResidual_nonempty_of_maximal p hxy hmax).mono subset_closure
  obtain ⟨μ, hμprob, hμatom, hμK, hμfull⟩ :=
    Perfect.exists_diffuse_full_support_probability hK hKne
  letI : IsProbabilityMeasure μ := hμprob
  let g := unitIntervalCDF μ
  have hg := unitIntervalCDF_continuous_monotone μ hμatom
  have hend := unitIntervalCDF_endpoints μ hμatom
  have hKF : K ⊆ loopResidual S := closure_minimal inter_subset_left (isClosed_loopResidual S)
  have hKnull : μ Kᶜ = 0 := by
    rw [measure_compl hK.closed.measurableSet (measure_ne_top μ K), measure_univ, hμK]
    simp
  have hflat : ∀ v ∈ S, g v.1 = g v.2 := by
    intro v hv
    apply (unitIntervalCDF_eq_iff_measure_Ioc_eq_zero μ (hS.1 v hv).1.le).mpr
    apply measure_mono_null (t := Kᶜ ∪ {v.2}) _ (measure_union_null hKnull (hμatom v.2))
    intro z hz
    by_cases hzeq : z = v.2
    · exact Or.inr hzeq
    · left
      intro hzK
      have hzF := hKF hzK
      exact hzF v hv ⟨hz.1, lt_of_le_of_ne hz.2 hzeq⟩
  have honly : ∀ s t : unitInterval, s < t → g s = g t →
      ∃ v ∈ S, v.1 ≤ s ∧ t ≤ v.2 := by
    intro s t hst heq
    have hzero : μ (Ioc s t) = 0 :=
      (unitIntervalCDF_eq_iff_measure_Ioc_eq_zero μ hst.le).mp heq
    have hdisj : Disjoint (Ioo s t) K := by
      apply Set.disjoint_left.mpr
      intro z hz hzK
      have hpos : 0 < μ (Ioo s t) := hμfull _ isOpen_Ioo ⟨z, hz, hzK⟩
      have hle : μ (Ioo s t) ≤ μ (Ioc s t) := measure_mono Ioo_subset_Ioc_self
      rw [hzero] at hle
      exact (not_lt_of_ge hle) hpos
    exact hS.exists_loop_of_disjoint_residual_core p hmax hst hdisj
  exact exists_injective_path_of_exact_loop_collapse p S hS hmax g hg.1 hg.2
    hend.1 hend.2 hflat honly

end FiniteAvalanches.Electrical.StatementGeometry
