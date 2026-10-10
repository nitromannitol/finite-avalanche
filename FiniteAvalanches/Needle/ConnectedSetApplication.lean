import FiniteAvalanches.Needle.ConnectedSet
import FiniteAvalanches.Needle.Logarithm

namespace FiniteAvalanches.Needle.ConnectedSetApplication
open LatticeProb FiniteAvalanches.Needle FiniteAvalanches.Sandpile.FiniteWired
open scoped Classical

theorem steps_reachable_in_induced (Z : Finset Point) {x y : Point} (hx : x ∈ Z)
    (hxy : Relation.ReflTransGen (stepIn Z) x y) :
    ∀ hy : y ∈ Z, ((lattice 2).induce (Z : Set Point)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction hxy with
  | refl => intro hy; exact .rfl
  | @tail b c hbc hstep ih =>
    intro hy
    exact (ih hstep.1).trans
      ((show ((lattice 2).induce (Z : Set Point)).Adj ⟨b, hstep.1⟩ ⟨c, hy⟩
        from hstep.2.2).reachable)

theorem induced_connected_of_lattice_connected (Z : Finset Point) (hne : Z.Nonempty)
    (hZ : LatticeConnectedSet Z) : ((lattice 2).induce (Z : Set Point)).Connected := by
  obtain ⟨w, hw⟩ := hne
  letI : Nonempty (Z : Set Point) := ⟨⟨w, hw⟩⟩
  refine SimpleGraph.Connected.mk ?_
  intro x y
  exact steps_reachable_in_induced Z x.property
    (hZ x.val x.property y.val y.property) y.property

theorem source_needle_connected_set : ∃ C : ℝ, 0 < C ∧
    ∀ h : ℕ, 10 ≤ h → ∀ w : Point, FiniteAvalanches.Needle.radius w = 2 * h →
    ∃ Z : Finset Point, ((lattice 2).induce (Z : Set Point)).Connected ∧
      (Z : Set Point) ⊆ box 2 (2 * h) ∧ box 2 h ⊆ (Z : Set Point) ∧ w ∈ Z ∧
      wiredConductance (2 * h)
        (Finset.univ.filter (fun x : Active (2 * h) => site x ∈ Z)) ≤ C * Real.log h := by
  obtain ⟨C, hC, H⟩ := ct_needle_log_h
  refine ⟨C, hC, ?_⟩
  intro h hh w hw
  obtain ⟨L, p, _, hb, he, ha, hc⟩ := H h hh w hw
  have hwend : w ∈ target h L p.val := by
    rw [← he]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  refine ⟨target h L p.val,
    induced_connected_of_lattice_connected _ ⟨w, hwend⟩ (target_connected h L p.val hb ha),
    ?_, ?_, hwend, hc⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hbox | hpath
    · have hr := (mem_box_iff x h).mp ((mem_boxPoints h x).mp hbox)
      exact (mem_box_iff x (2 * h)).mpr (by omega)
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hpath
      exact p.property t
  · exact fun x hx => Finset.mem_union_left _ ((mem_boxPoints h x).mpr hx)

end FiniteAvalanches.Needle.ConnectedSetApplication
