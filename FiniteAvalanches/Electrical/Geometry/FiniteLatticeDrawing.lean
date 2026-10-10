import FiniteAvalanches.Electrical.Geometry.ConnectedDrawingQuotient
import FiniteAvalanches.Electrical.Geometry.UnitSegments
import FiniteAvalanches.Electrical.Reference.Lattice
import Mathlib.Tactic.Rify

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb
open FiniteAvalanches.Electrical.StatementGeometry
open FiniteAvalanches.Electrical.Source
open FiniteAvalanches.Electrical.LatticeCell
open FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical
noncomputable section

theorem segment_injective (p : Site 2) (i : Fin 2) :
    Function.Injective (unitSegment p i) := by
  intro s t h
  have hi := congrArg (fun z : Plane => if i = 0 then z.1 else z.2) h
  fin_cases i <;> norm_num [unitSegment, unit, Pi.single_apply, Fin.ext_iff] at hi
  all_goals exact hi

theorem segment_start (p : Site 2) (i : Fin 2) : unitSegment p i 0 = sitePoint p := by
  simp only [unitSegment, sitePoint, zero_mul, add_zero]

theorem segment_finish (p : Site 2) (i : Fin 2) :
    unitSegment p i 1 = sitePoint (p + unit i) := by
  simp only [unitSegment, sitePoint, one_mul, Pi.add_apply, Int.cast_add]

theorem segment_intersects (p q : Site 2) (i j : Fin 2) (s t : ArcParameter)
    (h : unitSegment p i s.val = unitSegment q j t.val) :
    (p = q ∧ i = j) ∨ ((s.val = 0 ∨ s.val = 1) ∧ (t.val = 0 ∨ t.val = 1)) := by
  have h0 := congrArg Prod.fst h
  have h1 := congrArg Prod.snd h
  have hi : i = 0 ∨ i = 1 := by omega
  have hj : j = 0 ∨ j = 1 := by omega
  obtain hp | hp | hp | hp :=
    unitSegment_intersection_shared p q i j s.val t.val s.property t.property h
  all_goals
    have hp0 := congrArg (fun z : Site 2 => (z 0 : ℝ)) hp
    have hp1 := congrArg (fun z : Site 2 => (z 1 : ℝ)) hp
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  all_goals try exact Or.inl ⟨hp, rfl⟩
  all_goals try exact Or.inl ⟨add_right_cancel hp, rfl⟩
  all_goals norm_num [unitSegment, unit, Pi.add_apply, Pi.single_apply, Fin.ext_iff] at h0 h1 hp0 hp1
  all_goals try rify at hp0
  all_goals try rify at hp1
  all_goals
    right
    constructor
    · first | left; linarith [s.property.1, s.property.2, t.property.1, t.property.2]
            | right; linarith [s.property.1, s.property.2, t.property.1, t.property.2]
    · first | left; linarith [s.property.1, s.property.2, t.property.1, t.property.2]
            | right; linarith [s.property.1, s.property.2, t.property.1, t.property.2]

def latticeCopies (U : Finset (Site 2)) : Finset OriginalCopy :=
  (U ×ˢ (Finset.univ : Finset (Fin 2))).filter (fun e => originalB e ∈ U)

theorem mem_latticeCopies (U : Finset (Site 2)) (e : OriginalCopy) :
    e ∈ latticeCopies U ↔ originalA e ∈ U ∧ originalB e ∈ U := by
  simp only [latticeCopies, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    and_true, originalA]

def finiteLatticeGraph (U : Finset (Site 2)) : CopiedGraph U ↥(latticeCopies U) :=
  ⟨fun e => ⟨originalA e.val, ((mem_latticeCopies U e.val).mp e.property).1⟩,
    fun e => ⟨originalB e.val, ((mem_latticeCopies U e.val).mp e.property).2⟩⟩

def finiteLatticeDrawing (U : Finset (Site 2)) : Drawing (finiteLatticeGraph U) where
  point := fun v => sitePoint v.val
  point_injective := fun _ _ h => Subtype.ext (sitePoint_injective h)
  curve := fun e t => unitSegment e.val.1 e.val.2 t.val
  continuous := by
    intro e
    unfold unitSegment
    fun_prop
  injective := fun e _ _ _ _ h => Subtype.ext (segment_injective e.val.1 e.val.2 h)
  start := fun e => segment_start e.val.1 e.val.2
  finish := fun e => segment_finish e.val.1 e.val.2
  avoids := by
    intro e t ht0 ht1 v h
    obtain hp | hp := sitePoint_mem_unitSegment v.val e.val.1 e.val.2 t.val t.property h.symm
    · have he := segment_injective e.val.1 e.val.2
        (h.trans ((congrArg sitePoint hp).trans (segment_start e.val.1 e.val.2).symm))
      exact (ne_of_gt ht0) he
    · have he := segment_injective e.val.1 e.val.2
        (h.trans ((congrArg sitePoint hp).trans (segment_finish e.val.1 e.val.2).symm))
      exact (ne_of_lt ht1) he
  intersects := by
    intro e f hne s t h
    rcases segment_intersects e.val.1 f.val.1 e.val.2 f.val.2 s t h with he | he
    · exact (hne (Subtype.ext (Prod.ext he.1 he.2))).elim
    · exact he

end
end FiniteAvalanches.Electrical.LatticeDrawing
