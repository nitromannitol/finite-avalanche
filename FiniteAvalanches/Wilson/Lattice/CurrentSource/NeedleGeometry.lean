import FiniteAvalanches.Needle.Direct.Proof
import FiniteAvalanches.Wilson.Lattice.LocalComparison.NeedleGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.CurrentNeedleGeometry
open LatticeProb FiniteAvalanches.Needle FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

/-- Reversing a finite path changes neither its vertex set nor the box/path union. -/
theorem target_reverse (h L : ℕ) (p : Fin (L+1) → Point) :
    target h L (fun t => p t.rev) = target h L p := by
  unfold target
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨t.rev, ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t.rev, by simpa only [Fin.rev_rev] using ht⟩

theorem target_connected_of_path_end (h L : ℕ) (p : Fin (L+1) → Point)
    (hend : p ⟨L, by omega⟩ ∈ box 2 h)
    (hstep : ∀ t : Fin L, (lattice 2).Adj (p ⟨t.val, by omega⟩)
      (p ⟨t.val+1, by omega⟩)) : LatticeConnectedSet (target h L p) := by
  let q : Fin (L+1) → Point := fun t => p t.rev
  have hqstart : q ⟨0, by omega⟩ ∈ box 2 h := by
    have he : (⟨0, by omega⟩ : Fin (L+1)).rev = ⟨L, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev, Nat.add_sub_cancel]
    change p (⟨0, by omega⟩ : Fin (L+1)).rev ∈ box 2 h
    rw [he]
    exact hend
  have hqstep : ∀ t : Fin L, (lattice 2).Adj (q ⟨t.val, by omega⟩)
      (q ⟨t.val+1, by omega⟩) := by
    intro t
    let k : Fin L := ⟨L-(t.val+1), by omega⟩
    have he0 : (⟨t.val+1, by omega⟩ : Fin (L+1)).rev = ⟨k.val, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev]
      change L+1-(t.val+1+1) = L-(t.val+1)
      omega
    have he1 : (⟨t.val, by omega⟩ : Fin (L+1)).rev = ⟨k.val+1, by omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_rev]
      change L+1-(t.val+1) = L-(t.val+1)+1
      omega
    change (lattice 2).Adj (p (⟨t.val, by omega⟩ : Fin (L+1)).rev)
      (p (⟨t.val+1, by omega⟩ : Fin (L+1)).rev)
    rw [he1, he0]
    exact (hstep k).symm
  have hc := target_connected h L q hqstart hqstep
  rw [target_reverse] at hc
  exact hc

/-- The literal current greedy path supplies the enlargement and its 2304 budget. -/
theorem exists_needle_enlargement (h : ℕ) (hh : 10 ≤ h) (w : Point)
    (hw : FiniteAvalanches.Needle.radius w = 2*h) (K : Finset Point)
    (hK : ((lattice 2).induce (K : Set Point)).Connected) (h0 : (0 : Point) ∈ K)
    (γ Γ' : Set Point) (hd : Disjoint (K : Set Point) γ)
    (hΓ : Γ' ⊆ γ) (hout : Γ' ⊆ (box 2 (2*h))ᶜ) :
    ∃ Z : Finset Point,
      ((lattice 2).induce (Z : Set Point)).Connected ∧
      (Z : Set Point) ⊆ box 2 (2*h) ∧ box 2 h ⊆ (Z : Set Point) ∧ w ∈ Z ∧
      ((lattice 2).induce ((K ∪ Z : Finset Point) : Set Point)).Connected ∧
      Disjoint ((K ∪ Z : Finset Point) : Set Point) Γ' ∧
      wiredConductance (2*h)
        (Finset.univ.filter (fun x : FiniteWired.Active (2*h) => FiniteWired.site x ∈ Z)) ≤
          2304 * Real.log h := by
  obtain ⟨L,p,_hi,hs,he,ha,hbudget⟩ := needle_greedy_path_budget h hh w hw
  let Z := target h L p.val
  have hwZ : w ∈ Z := by
    rw [← hs]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hZc : ((lattice 2).induce (Z : Set Point)).Connected :=
    FiniteAvalanches.Needle.ConnectedSetApplication.induced_connected_of_lattice_connected
      Z ⟨w, hwZ⟩ (target_connected_of_path_end h L p.val he ha)
  have hZo : (Z : Set Point) ⊆ box 2 (2*h) := by
    intro x hx
    rcases Finset.mem_union.mp hx with hbox | hpath
    · have hr := (mem_box_iff x h).mp ((mem_boxPoints h x).mp hbox)
      exact (mem_box_iff x (2*h)).mpr (by omega)
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hpath
      exact p.property t
  have hZi : box 2 h ⊆ (Z : Set Point) :=
    fun x hx => Finset.mem_union_left _ ((mem_boxPoints h x).mpr hx)
  refine ⟨Z,hZc,hZo,hZi,hwZ,?_,?_,hbudget⟩
  · have h0Z : (0 : Point) ∈ (Z : Set Point) := hZi (by simp [box])
    have hc := SimpleGraph.induce_union_connected hK.preconnected hZc.preconnected
      (show ((K : Set Point) ∩ (Z : Set Point)).Nonempty from ⟨0,h0,h0Z⟩)
    have heq : ((K ∪ Z : Finset Point) : Set Point) = (K : Set Point) ∪ (Z : Set Point) := by
      ext x
      exact Finset.mem_union
    rw [heq]
    exact hc
  · apply Set.disjoint_left.mpr
    intro x hx hxΓ
    rcases Finset.mem_union.mp hx with hxK | hxZ
    · exact Set.disjoint_left.mp hd hxK (hΓ hxΓ)
    · exact hout hxΓ (hZo hxZ)

end
end FiniteAvalanches.Wilson.Lattice.CurrentNeedleGeometry
