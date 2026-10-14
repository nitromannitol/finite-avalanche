import FiniteAvalanches.Sandpile.Recurrence.GammaGraph
import FiniteAvalanches.Sandpile.Burning.DegreeTransport

/-! Every tested Gamma subset uses its literal lattice neighbor degree; no
connectedness, bounding-shape truncation or supplied degree identity is assumed. -/
namespace FiniteAvalanches.Sandpile.GammaGraph
open LatticeProb FiniteAvalanches.Sandpile
open scoped Classical
noncomputable section

def ambient {Γ : Finset Site2} (x : Γ) : FiniteWired.Active (radius Γ) :=
  FiniteWired.activeOfSite (radius Γ) x.val (in_radius x)

theorem site_ambient {Γ : Finset Site2} (x : Γ) : FiniteWired.site (ambient x) = x.val := rfl

theorem ambient_injective (Γ : Finset Site2) : Function.Injective (@ambient Γ) := by
  intro x y h
  exact Subtype.ext (congrArg FiniteWired.site h)

theorem active_equiv_value {Γ : Finset Site2} (x : Γ) :
    (activeEquiv Γ x).val = some (ambient x) := rfl

theorem original_subset_degree {Γ : Finset Site2} (S : Finset Γ) (x : Γ) (hx : x ∈ S) :
    Burning.degreeInto (WiredTrees.graph (radius Γ)) (S.image (fun y => some (ambient y)))
      (some (ambient x)) = Waves.degree (S.image Subtype.val) x.val := by
  have hs := Components.wired_subset_degree (S.image ambient) (ambient x)
    (Finset.mem_image_of_mem ambient hx)
  unfold Burning.activeDegree at hs
  rw [Finset.image_image, Finset.image_image] at hs
  have hv : (S.image ambient).image FiniteWired.site = S.image Subtype.val := by
    rw [Finset.image_image]
    rfl
  unfold FiniteWired.internalDegree at hs
  rw [hv] at hs
  exact hs

theorem subset_degree {Γ : Finset Site2} (S : Finset Γ) (x : Γ) (hx : x ∈ S) :
    Burning.activeDegree (graph Γ) (Finset.univ.erase none)
      (S.image (vertexEquiv Γ)) (vertexEquiv Γ x) =
      Waves.degree (S.image Subtype.val) x.val := by
  have hi : ((S.image (vertexEquiv Γ)).image Subtype.val) =
      (S.image (activeEquiv Γ)).image some := by
    rw [Finset.image_image, Finset.image_image]
    rfl
  have hd := Burning.degree_into_held_graph (WiredTrees.graph (radius Γ)) none
    (activeVertices Γ) (activeVertices Γ) (none_not_active Γ) (fun _ h => h)
    (S.image (activeEquiv Γ)) (activeEquiv Γ x)
  change Burning.degreeInto (graph Γ) _ (vertexEquiv Γ x).val = _
  rw [hi]
  apply hd.trans
  rw [Finset.image_image]
  exact original_subset_degree S x hx

/-- Adding the tested vertex itself contributes zero on both loopless carriers. -/
theorem subset_degree_all {Γ : Finset Site2} (S : Finset Γ) (x : Γ) :
    Burning.activeDegree (graph Γ) (Finset.univ.erase none)
      (S.image (vertexEquiv Γ)) (vertexEquiv Γ x) =
      Waves.degree (S.image Subtype.val) x.val := by
  by_cases hx : x ∈ S
  · exact subset_degree S x hx
  · have h := subset_degree (insert x S) x (Finset.mem_insert_self _ _)
    have he : (insert x S).image (vertexEquiv Γ) =
        {vertexEquiv Γ x} ∪ S.image (vertexEquiv Γ) := by simp
    have hd : Disjoint ({(vertexEquiv Γ x).val} : Finset (Vertex Γ))
        ((S.image (vertexEquiv Γ)).image Subtype.val) := by
      apply Finset.disjoint_singleton_left.mpr
      intro hm
      obtain ⟨a, ha, hav⟩ := Finset.mem_image.mp hm
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ha
      have hyx : y = x := (vertexEquiv Γ).injective (Subtype.ext hav)
      exact hx (hyx ▸ hy)
    unfold Burning.activeDegree at h ⊢
    rw [he, Finset.image_union, Finset.image_singleton, Burning.degree_into_union _ hd,
      Burning.degree_into_self, zero_add] at h
    have hs : Waves.degree ((insert x S).image Subtype.val) x.val =
        Waves.degree (S.image Subtype.val) x.val := by
      unfold Waves.degree
      rw [Finset.image_insert]
      have he' : LatticeProb.nbrFinset x.val ∩ insert x.val (S.image Subtype.val) =
          LatticeProb.nbrFinset x.val ∩ S.image Subtype.val := by
        ext y
        simp only [Finset.mem_inter, Finset.mem_insert]
        constructor
        · rintro ⟨hy, he | hm⟩
          · subst y; exact (Waves.not_mem_neighbors_self _ hy).elim
          · exact ⟨hy, hm⟩
        · rintro ⟨hy, hm⟩; exact ⟨hy, Or.inr hm⟩
      rw [he']
    rw [hs] at h
    exact h

end
end FiniteAvalanches.Sandpile.GammaGraph
