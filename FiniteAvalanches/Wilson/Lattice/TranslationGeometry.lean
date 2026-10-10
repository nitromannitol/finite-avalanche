import FiniteAvalanches.Wilson.Lattice.TranslationSampler
import FiniteAvalanches.Wilson.Lattice.ForestEvents

/-! Literal translations of all finite-set sites, all neighbor contacts, entire
simple rays, and the exact natural-valued sup diameter used by ct:reciprocal:v2. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice.Translation
open LatticeProb FiniteAvalanches.Sandpile MeasureTheory
open scoped Classical
noncomputable section

/-- Every original lattice site is translated bijectively. -/
def finiteSet (K : Finset (Site 2)) (z : Site 2) : Finset (Site 2) :=
  K.image (fun x => x + z)

theorem mem_finiteSet (K : Finset (Site 2)) (z x : Site 2) :
    x ∈ finiteSet K z ↔ x - z ∈ K := by
  constructor
  · rintro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa only [add_sub_cancel_right] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x - z, hx, sub_add_cancel x z⟩

theorem adjacency_add (x y z : Site 2) :
    (lattice 2).Adj (x + z) (y + z) ↔ (lattice 2).Adj x y := by
  change (∃ i, y + z = (x + z) + unit i ∨ x + z = (y + z) + unit i) ↔
    ∃ i, y = x + unit i ∨ x = y + unit i
  simp only [add_right_comm x z, add_right_comm y z, add_left_inj]

/-- A bijection of the full original neighbor set, retaining all four lattice copies. -/
theorem neighbors_image (x z : Site 2) :
    (nbrFinset x).image (fun y => y + z) = nbrFinset (x + z) := by
  ext y
  rw [FiniteWired.mem_neighbors_iff]
  constructor
  · rintro hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    exact (adjacency_add x v z).mpr ((FiniteWired.mem_neighbors_iff x v).mp hv)
  · intro hy
    have hv : (lattice 2).Adj x (y - z) := by
      apply (adjacency_add x (y - z) z).mp
      simpa only [sub_add_cancel] using hy
    exact Finset.mem_image.mpr ⟨y - z, (FiniteWired.mem_neighbors_iff _ _).mpr hv,
      sub_add_cancel y z⟩

/-- Contact counts transport pointwise for EVERY Boolean field, including all
original neighbors regardless of whether the forest contains their edges. -/
theorem contacts_translate (K : Finset (Site 2)) (z : Site 2) (σ : ColorField) :
    contacts (finiteSet K z) (colors z σ) = contacts K σ := by
  unfold contacts finiteSet
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro x _
    rw [← neighbors_image x z, Finset.sum_image]
    · simp only [colors, add_sub_cancel_right]
    · intro x _ y _ hxy
      exact add_right_cancel hxy
  · intro x _ y _ hxy
    exact add_right_cancel hxy

/-- The entire infinite ray, with every vertex retained in its original order. -/
def ray (γ : SimpleRay) (z : Site 2) : SimpleRay where
  vertex n := γ.vertex n + z
  adjacent n := (adjacency_add _ _ z).mpr (γ.adjacent n)
  injective := fun _ _ h => γ.injective (add_right_cancel h)

theorem ray_vertices (γ : SimpleRay) (z : Site 2) :
    (ray γ z).vertices = {x | x - z ∈ γ.vertices} := by
  ext x
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← hn]; exact (add_sub_cancel_right _ _).symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by change γ.vertex n + z = x; rw [hn, sub_add_cancel]⟩

theorem disjoint_translate (K : Finset (Site 2)) (γ : SimpleRay) (z : Site 2)
    (h : Disjoint (K : Set (Site 2)) γ.vertices) :
    Disjoint (finiteSet K z : Set (Site 2)) (ray γ z).vertices := by
  apply Set.disjoint_left.mpr
  intro x hx hγ
  rw [ray_vertices] at hγ
  exact Set.disjoint_left.mp h ((mem_finiteSet K z x).mp hx) hγ

theorem connected_translate (K : Finset (Site 2)) (z : Site 2)
    (h : ((lattice 2).induce (K : Set (Site 2))).Connected) :
    ((lattice 2).induce (finiteSet K z : Set (Site 2))).Connected := by
  let φ : (lattice 2).induce (K : Set (Site 2)) →g
      (lattice 2).induce (finiteSet K z : Set (Site 2)) := {
    toFun := fun x => ⟨x.val + z, Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩
    map_rel' := fun hxy => (adjacency_add _ _ z).mpr hxy }
  apply SimpleGraph.Connected.map φ _ h
  intro x
  refine ⟨⟨x.val - z, (mem_finiteSet K z x.val).mp x.property⟩, ?_⟩
  exact Subtype.ext (sub_add_cancel x.val z)

theorem siteRadius_add (x y z : Site 2) :
    siteRadius (x + z) (y + z) = siteRadius x y := by
  unfold siteRadius
  simp only [Pi.add_apply, add_sub_add_right_eq_sub]

theorem diameter_translate (K : Finset (Site 2)) (z : Site 2) :
    (finiteSet K z).sup (fun x => (finiteSet K z).sup (fun y => siteRadius x y)) =
      K.sup (fun x => K.sup (fun y => siteRadius x y)) := by
  simp only [finiteSet, Finset.sup_image, Function.comp_def, siteRadius_add]

/-- The source adjacent site really becomes the origin, while the full ray
starts at its translated neighbor. -/
theorem origin_geometry (K : Finset (Site 2)) (γ : SimpleRay) (k : Site 2)
    (hk : k ∈ K) (hadj : (lattice 2).Adj k (γ.vertex 0)) :
    0 ∈ finiteSet K (-k) ∧ (lattice 2).Adj 0 ((ray γ (-k)).vertex 0) := by
  constructor
  · exact Finset.mem_image.mpr ⟨k, hk, add_neg_cancel k⟩
  · have he := (adjacency_add k (γ.vertex 0) (-k)).mpr hadj
    simpa only [add_neg_cancel, ray] using he

end
end FiniteAvalanches.Wilson.Lattice.Translation
