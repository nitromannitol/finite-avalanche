import FiniteAvalanches.Sandpile.Components.SourceFields
import FiniteAvalanches.Sandpile.Waves.BurnedSet

/-! The original lattice held burn and the canonical induced copied-graph burn
have the same entire stopping set. Heights are the actual core restriction;
no tree, conditional law, or recurrence characterization enters this adapter. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Components FiniteAvalanches.Sandpile.Waves
open scoped Classical
noncomputable section

/-- The actual lattice coordinate of every nonsink vertex in the inside graph. -/
def innerSite {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (v : Burning.SourceVertex (innerRoot C)) : Site2 :=
  ((innerSourceVertexEquiv C).symm v).val

theorem inner_site_injective {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :
    Function.Injective (innerSite C) := by
  intro v w he
  exact (innerSourceVertexEquiv C).symm.injective (Subtype.ext he)

theorem inner_site_mem {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (v : Burning.SourceVertex (innerRoot C)) :
    innerSite C v ∈ C.val.erase (FiniteWired.site o) :=
  ((innerSourceVertexEquiv C).symm v).property

/-- Literal preimage, on the whole source-vertex carrier, of any lattice set. -/
def innerVertices {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (D : Finset Site2) : Finset (Burning.SourceVertex (innerRoot C)) :=
  Finset.univ.filter fun v => innerSite C v ∈ D

theorem mem_inner_vertices {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (D : Finset Site2) (v : Burning.SourceVertex (innerRoot C)) :
    v ∈ innerVertices C D ↔ innerSite C v ∈ D := by simp [innerVertices]

theorem image_inner_vertices {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o)
    (D : Finset Site2) (hD : D ⊆ C.val.erase (FiniteWired.site o)) :
    (innerVertices C D).image (innerSite C) = D := by
  ext x
  constructor
  · rintro hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_inner_vertices C D v).mp hv
  · intro hx
    let v := innerSourceVertexEquiv C ⟨x, hD hx⟩
    have he : innerSite C v = x := by
      exact congrArg Subtype.val ((innerSourceVertexEquiv C).symm_apply_apply ⟨x, hD hx⟩)
    exact Finset.mem_image.mpr ⟨v, (mem_inner_vertices C D v).mpr (he ▸ hx), he⟩

theorem inner_degree_every_subset {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (T : Finset (Burning.SourceVertex (innerRoot C)))
    (v : Burning.SourceVertex (innerRoot C)) (hv : v ∈ T) :
    Burning.activeDegree (inducedGraph (insideSupport C)) (Finset.univ.erase (innerRoot C)) T v =
      degree (T.image (innerSite C)) (innerSite C v) := by
  let S := T.image (innerSourceVertexEquiv C).symm
  let x := (innerSourceVertexEquiv C).symm v
  have hx : x ∈ S := Finset.mem_image_of_mem _ hv
  have he : S.image (innerSourceVertexEquiv C) = T := by simp [S, Finset.image_image]
  have hd := inner_subset_degree C S x hx
  rw [he, Equiv.apply_symm_apply] at hd
  simp only [S, x, Finset.image_image, Function.comp_def] at hd
  exact hd

theorem core_inner_height {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (h : CoreField o C.val)
    (v : Burning.SourceVertex (innerRoot C)) :
    wiredHeight 4 h.val.val (innerSite C v) = (((coreGraphFieldEquiv C h).2.val v).val : ℤ) := by
  let x := (innerSourceVertexEquiv C).symm v
  have he : ((coreGraphFieldEquiv C h).2.val v).val = (restrictInner h x).val := by
    change ((innerSourceHeightsEquiv C (restrictInner h)) v).val = _
    conv_lhs => rw [← (innerSourceVertexEquiv C).apply_symm_apply v]
    exact ComponentTransport.reindex_heights_val _ _ _ _ _ _
  rw [he]
  change wiredHeight 4 h.val.val x.val = _
  rw [wired_height_off 4 (-1) h.val.val (Finset.mem_erase.mp x.property).1]
  exact restrict_inner_height h x

theorem core_held_closed_iff {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (h : CoreField o C.val)
    (B T : Finset (Burning.SourceVertex (innerRoot C))) :
    Burning.heldClosed (inducedGraph (insideSupport C)) (Finset.univ.erase (innerRoot C))
      (coreGraphFieldEquiv C h).2.val B T ↔
    held_closed (wiredHeight 4 h.val.val) (B.image (innerSite C)) (T.image (innerSite C)) := by
  constructor
  · rintro ⟨hb, ht⟩
    refine ⟨Finset.image_subset_image hb, ?_⟩
    intro x hx hxb
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    have hvb : v ∉ B := fun hvb => hxb (Finset.mem_image_of_mem _ hvb)
    rw [core_inner_height]
    have hd := inner_degree_every_subset C T v hv
    have hh := ht v hv hvb
    rw [hd] at hh
    exact_mod_cast hh
  · rintro ⟨hb, ht⟩
    refine ⟨?_, ?_⟩
    · intro v hv
      obtain ⟨w, hw, he⟩ := Finset.mem_image.mp (hb (Finset.mem_image_of_mem _ hv))
      exact (inner_site_injective C he) ▸ hw
    · intro v hv hvb
      have hn : innerSite C v ∉ B.image (innerSite C) := by
        intro hm
        obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hm
        exact hvb ((inner_site_injective C he) ▸ hw)
      have hh := ht (innerSite C v) (Finset.mem_image_of_mem _ hv) hn
      rw [core_inner_height, ← inner_degree_every_subset C T v hv] at hh
      exact_mod_cast hh

/-- Entire actual stopping sets agree; source is removed as sink in both burns. -/
theorem core_held_stop_eq {N : ℕ} {o : FiniteWired.Active N}
    (C : ComponentShape o) (h : CoreField o C.val)
    (B : Finset (Burning.SourceVertex (innerRoot C))) :
    (Burning.heldBurning (inducedGraph (insideSupport C)) (Finset.univ.erase (innerRoot C))
      (coreGraphFieldEquiv C h).2.val B).image (innerSite C) =
    heldBurning (wiredHeight 4 h.val.val) (B.image (innerSite C))
      (C.val.erase (FiniteWired.site o)) (by
        intro x hx
        obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
        exact inner_site_mem C v) := by
  let G := inducedGraph (insideSupport C)
  let U := Finset.univ.erase (innerRoot C)
  let g := (coreGraphFieldEquiv C h).2.val
  have hB : B.image (innerSite C) ⊆ C.val.erase (FiniteWired.site o) := by
    intro x hx
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
    exact inner_site_mem C v
  let T := Burning.heldBurning G U g B
  let D := heldBurning (wiredHeight 4 h.val.val) (B.image (innerSite C))
    (C.val.erase (FiniteWired.site o)) hB
  obtain ⟨ht, htmax⟩ := Burning.held_burning_largest G U g B
  obtain ⟨hd, hdsub, hdmax⟩ := held_burning_largest (wiredHeight 4 h.val.val)
    (B.image (innerSite C)) (C.val.erase (FiniteWired.site o)) hB
  change T.image (innerSite C) = D
  apply Finset.Subset.antisymm
  · apply hdmax
    · intro x hx
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
      exact inner_site_mem C v
    · exact (core_held_closed_iff C h B T).mp ht
  · have hi := image_inner_vertices C D hdsub
    have hc : Burning.heldClosed G U g B (innerVertices C D) := by
      apply (core_held_closed_iff C h B (innerVertices C D)).mpr
      rw [hi]
      exact hd
    have hh := Finset.image_subset_image (f := innerSite C) (htmax _ hc)
    rw [hi] at hh
    exact hh


end
end FiniteAvalanches.Sandpile.Components
