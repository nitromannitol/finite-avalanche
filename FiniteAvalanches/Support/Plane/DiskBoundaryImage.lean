import FiniteAvalanches.Support.Plane.ConjugateChart
import FiniteAvalanches.Support.Plane.TopoSep

/-!
# Plane disks from their boundaries

A plane homeomorphism preserving the boundary of a disk preserves the disk.
The same property holds for two homeomorphisms with the same boundary image.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set
open FiniteAvalanches.Electrical.Source

noncomputable section

private theorem unbounded_complex_exterior :
    ¬ Bornology.IsBounded {z : ℂ | 2 < ‖z‖} := by
  intro h
  have hcover : Metric.closedBall (0 : ℂ) 2 ∪ {z : ℂ | 2 < ‖z‖} = univ := by
    ext z
    simp only [mem_union, Metric.mem_closedBall, dist_zero_right, mem_setOf_eq, mem_univ,
      iff_true]
    exact le_or_gt ‖z‖ 2
  have hb : Bornology.IsBounded (Metric.closedBall (0 : ℂ) 2 ∪ {z : ℂ | 2 < ‖z‖}) :=
    Metric.isBounded_closedBall.union h
  rw [hcover] at hb
  have hc := hb.isCompact_closure
  rw [closure_univ] at hc
  exact noncompact_univ ℂ hc

private theorem exterior_mapsTo_of_sphere_image (f : ℂ ≃ₜ ℂ)
    (hf : f '' Metric.sphere (0 : ℂ) 2 = Metric.sphere 0 2) :
    MapsTo f {z | 2 < ‖z‖} {z | 2 < ‖z‖} := by
  let U : Set ℂ := {z | 2 < ‖z‖}
  have havoid : ∀ z ∈ U, ‖f z‖ ≠ 2 := by
    intro z hz heq
    have hm : f z ∈ Metric.sphere (0 : ℂ) 2 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using heq
    rw [← hf] at hm
    obtain ⟨w, hw, he⟩ := hm
    have hwz : w = z := f.injective he
    subst w
    have : ‖z‖ = 2 := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
    exact (ne_of_gt hz) this
  have hex : ∃ z ∈ U, 2 < ‖f z‖ := by
    by_contra h
    have hs : U ⊆ f.symm '' Metric.closedBall (0 : ℂ) 2 := by
      intro z hz
      refine ⟨f z, ?_, f.symm_apply_apply z⟩
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact le_of_not_gt (fun hz' => h ⟨z, hz, hz'⟩)
    have hk : IsCompact (f.symm '' Metric.closedBall (0 : ℂ) 2) :=
      (isCompact_closedBall (0 : ℂ) 2).image f.symm.continuous
    exact unbounded_complex_exterior (hk.isBounded.subset hs)
  intro z hz
  exact (QuantumZipper.CA.Topo.isPreconnected_setOf_lt_norm 2).lt_of_ne
    (continuous_norm.comp f.continuous).continuousOn havoid hex hz

/-- A complex-plane homeomorphism preserving a circle preserves its closed disk. -/
theorem image_closedBall_of_image_sphere (f : ℂ ≃ₜ ℂ)
    (hf : f '' Metric.sphere (0 : ℂ) 2 = Metric.sphere 0 2) :
    f '' Metric.closedBall (0 : ℂ) 2 = Metric.closedBall 0 2 := by
  have hfs : f.symm '' Metric.sphere (0 : ℂ) 2 = Metric.sphere 0 2 := by
    calc
      f.symm '' Metric.sphere (0 : ℂ) 2 =
          f.symm '' (f '' Metric.sphere (0 : ℂ) 2) := congrArg _ hf.symm
      _ = Metric.sphere 0 2 := by
        rw [← image_comp]
        simp only [Homeomorph.symm_comp_self, image_id]
  have h1 := exterior_mapsTo_of_sphere_image f hf
  have h2 := exterior_mapsTo_of_sphere_image f.symm hfs
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right] at hx ⊢
    by_contra h
    have hz : 2 < ‖f x‖ := lt_of_not_ge h
    have := h2 hz
    simp only [Homeomorph.symm_apply_apply] at this
    exact (not_lt_of_ge hx) this
  · intro hz
    refine ⟨f.symm z, ?_, f.apply_symm_apply z⟩
    simp only [Metric.mem_closedBall, dist_zero_right] at hz ⊢
    by_contra h
    have hx : 2 < ‖f.symm z‖ := lt_of_not_ge h
    have := h1 hx
    simp only [Homeomorph.apply_symm_apply] at this
    exact (not_lt_of_ge hz) this


/-- Equal images of the disk boundary determine equal images of the disk. -/
theorem image_complexDisk_eq_of_image_frontier_eq (f g : Plane ≃ₜ Plane)
    (h : f '' frontier complexDisk = g '' frontier complexDisk) :
    f '' complexDisk = g '' complexDisk := by
  let C : ℂ ≃ₜ Plane := Complex.equivRealProdCLM.toHomeomorph
  let H : ℂ ≃ₜ ℂ := (C.trans (f.trans g.symm)).trans C.symm
  have hfront : (f.trans g.symm) '' frontier complexDisk = frontier complexDisk := by
    change (g.symm ∘ f) '' frontier complexDisk = frontier complexDisk
    rw [image_comp, h, ← image_comp]
    simp only [Homeomorph.symm_comp_self, image_id]
  have hcircle : H '' Metric.sphere (0 : ℂ) 2 = Metric.sphere 0 2 := by
    have hC : C '' Metric.sphere (0 : ℂ) 2 = frontier complexDisk := by
      change C '' Metric.sphere (0 : ℂ) 2 = frontier (C '' Metric.closedBall (0 : ℂ) 2)
      rw [← C.image_frontier, frontier_closedBall _ (by norm_num : (2 : ℝ) ≠ 0)]
    change (C.symm ∘ (f.trans g.symm) ∘ C) '' Metric.sphere (0 : ℂ) 2 = _
    rw [image_comp, image_comp, hC, hfront, ← hC, ← image_comp]
    simp only [Homeomorph.symm_comp_self, image_id]
  have hdisk := image_closedBall_of_image_sphere H hcircle
  have hplane : (f.trans g.symm) '' complexDisk = complexDisk := by
    change (g.symm ∘ f) '' (C '' Metric.closedBall (0 : ℂ) 2) = C '' Metric.closedBall 0 2
    have hdisk' := congrArg (fun s : Set ℂ => C '' s) hdisk
    change C '' ((C.symm ∘ (g.symm ∘ f) ∘ C) '' Metric.closedBall (0 : ℂ) 2) = _ at hdisk'
    simp only [image_comp] at hdisk'
    rw [← image_comp, show (C ∘ C.symm : Plane → Plane) = id from
      funext C.apply_symm_apply, image_id] at hdisk'
    simpa only [image_comp] using hdisk'
  change (g.symm ∘ f) '' complexDisk = complexDisk at hplane
  rw [image_comp] at hplane
  have := congrArg (fun s : Set Plane => g '' s) hplane
  rw [← image_comp, show (g ∘ g.symm : Plane → Plane) = id from
    funext g.apply_symm_apply, image_id] at this
  exact this

/-- A straightening has an oriented realization if an oriented chart realizes
its inverse disk boundary. -/
theorem exists_orientedChart_straightening_of_boundary_image
    (gamma : unitInterval → Plane) (f : Plane ≃ₜ Plane)
    (hf : ∀ t, f (gamma t) = (t.val, 0))
    (c : OrientedChart)
    (hc : c.map '' frontier complexDisk = f.symm '' frontier complexDisk) :
    ∃ d : OrientedChart, ∀ t, d.map (gamma t) = (t.val, 0) :=
  exists_orientedChart_straightening_of_disk_image gamma f hf c
    (image_complexDisk_eq_of_image_frontier_eq c.map f.symm hc)

end
end FiniteAvalanches.Electrical.StatementGeometry
