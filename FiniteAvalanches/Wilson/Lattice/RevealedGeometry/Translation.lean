import FiniteAvalanches.Wilson.Lattice.RevealedGeometry.Metric
import FiniteAvalanches.Wilson.Lattice.TranslationGeometry

set_option autoImplicit false
namespace JointTranslatedGeometry
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.Lattice
open scoped Classical
noncomputable section

theorem connected_shift (S : Set (Site 2)) (z : Site 2)
    (h : ((lattice 2).induce S).Connected) :
    ((lattice 2).induce {x | x-z ∈ S}).Connected := by
  let f : (lattice 2).induce S →g (lattice 2).induce {x | x-z ∈ S} :=
    { toFun := fun x => ⟨x.val+z,by simpa only [Set.mem_setOf_eq,add_sub_cancel_right] using x.property⟩
      map_rel' := fun h => (Translation.adjacency_add _ _ z).mpr h }
  apply h.map f
  intro x
  exact ⟨⟨x.val-z,x.property⟩,Subtype.ext (sub_add_cancel x.val z)⟩

theorem finite_complement_shift (S : Set (Site 2)) (z : Site 2) (hf : Sᶜ.Finite) :
    {x : Site 2 | x-z ∈ S}ᶜ.Finite := by
  apply (hf.image (fun x => x+z)).subset
  intro x hx
  exact ⟨x-z,hx,sub_add_cancel x z⟩

theorem radius_shift_center (w x : Site 2) : siteRadius 0 (x + -w) = siteRadius w x := by
  have h := Translation.siteRadius_add w x (-w)
  simpa only [add_neg_cancel] using h

theorem radius_unshift_center (w x : Site 2) : siteRadius w (x+w) = siteRadius 0 x := by
  have he := radius_shift_center w (x+w)
  simpa only [add_neg_cancel_right] using he.symm

theorem window_shift (w : Site 2) (r : ℕ) :
    Translation.finiteSet (window w r) (-w) = window 0 r := by
  ext x
  rw [Translation.mem_finiteSet,mem_window,mem_window,sub_neg_eq_add,radius_unshift_center]

theorem local_contact_set_shift (R : RootPair) (w : Site 2) (r : ℕ) :
    Translation.finiteSet ((window w r).filter (fun x => x ∈ R.zero)) (-w) =
      (window 0 r).filter (fun x => x ∈ (Translation.roots R (-w)).zero) := by
  ext x
  rw [Translation.mem_finiteSet]
  simp only [Finset.mem_filter,mem_window,sub_neg_eq_add,radius_unshift_center,Translation.roots,
    Set.mem_setOf_eq]

theorem local_contacts_shift (R : RootPair) (w : Site 2) (r : ℕ) (σ : ColorField) :
    localContacts (Translation.roots R (-w)).zero 0 r (Translation.colors (-w) σ) =
      localContacts R.zero w r σ := by
  unfold localContacts
  rw [← local_contact_set_shift]
  exact Translation.contacts_translate _ _ _

/-- Every premise of the local comparison at the same r, after the exact shift -w. -/
theorem translated_local_hypotheses (R : RootPair) (w : Site 2) (r : ℕ)
    (hf : R.oneᶜ.Finite) (hw : w ∈ R.zero)
    (hn : ∃ z ∈ R.one, (lattice 2).Adj w z)
    (h0c : ((lattice 2).induce R.zero).Connected)
    (hfar : ∃ x ∈ R.zero, 2*r ≤ siteRadius w x)
    (h1c : ((lattice 2).induce R.one).Connected)
    (hmeet : ∃ y ∈ R.one, siteRadius w y = r) :
    ((Translation.roots R (-w)).zero ∪ (Translation.roots R (-w)).one)ᶜ.Finite ∧
    0 ∈ (Translation.roots R (-w)).zero ∧
    (∃ b ∈ (Translation.roots R (-w)).one, (lattice 2).Adj 0 b) ∧
    ((lattice 2).induce (Translation.roots R (-w)).zero).Connected ∧
    (∃ x ∈ (Translation.roots R (-w)).zero, 2*r ≤ siteRadius 0 x) ∧
    ((lattice 2).induce (Translation.roots R (-w)).one).Connected ∧
    (∃ y ∈ (Translation.roots R (-w)).one, siteRadius 0 y = r) := by
  have hfs := finite_complement_shift R.one (-w) hf
  refine ⟨hfs.subset (fun _ hx hy => hx (Or.inr hy)),?_,?_,
    connected_shift _ _ h0c,?_,connected_shift _ _ h1c,?_⟩
  · change 0 - -w ∈ R.zero
    simpa only [zero_sub,neg_neg] using hw
  · obtain ⟨z,hz,he⟩ := hn
    refine ⟨z + -w,?_,?_⟩
    · change z + -w - -w ∈ R.one
      simpa only [add_sub_cancel_right] using hz
    · simpa only [add_neg_cancel] using (Translation.adjacency_add w z (-w)).mpr he
  · obtain ⟨x,hx,he⟩ := hfar
    refine ⟨x + -w,?_,?_⟩
    · change x + -w - -w ∈ R.zero
      simpa only [add_sub_cancel_right] using hx
    · simpa only [radius_shift_center] using he
  · obtain ⟨y,hy,he⟩ := hmeet
    refine ⟨y + -w,?_,?_⟩
    · change y + -w - -w ∈ R.one
      simpa only [add_sub_cancel_right] using hy
    · simpa only [radius_shift_center] using he

end
end JointTranslatedGeometry
