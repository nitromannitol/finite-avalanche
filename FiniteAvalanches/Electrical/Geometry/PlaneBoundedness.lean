import FiniteAvalanches.Electrical.Geometry.BSST
import Mathlib.Topology.MetricSpace.Bounded

/-! The limitation of global plane homeomorphisms in choosing an outside face. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.DeletedArc
open FiniteAvalanches.Electrical.Source

/-- A global plane homeomorphism preserves boundedness in both directions. -/
theorem plane_homeomorph_bounded_iff (h : Plane ≃ₜ Plane) (s : Set Plane) :
    Bornology.IsBounded (h '' s) ↔ Bornology.IsBounded s := by
  have forward (f : Plane ≃ₜ Plane) (t : Set Plane) (ht : Bornology.IsBounded t) :
      Bornology.IsBounded (f '' t) :=
    (ht.isCompact_closure.image f.continuous).isBounded.subset (Set.image_mono subset_closure)
  constructor
  · intro hs
    have hb := forward h.symm (h '' s) hs
    simpa only [Set.image_image, Homeomorph.symm_apply_apply, Set.image_id'] using hb
  · exact forward h s

end FiniteAvalanches.Electrical.DeletedArc
