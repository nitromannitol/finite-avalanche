import FiniteAvalanches.Sandpile.Limit.HeldInner
import FiniteAvalanches.Sandpile.Limit.GammaHeights

/-! The inner allowed fields of held burning in the wired graph of `Γ` are described by
lattice degrees alone, so their numbers depend only on the stopping set and the held set,
not on the volume `Γ`. -/

set_option autoImplicit false

namespace FiniteAvalanches.Sandpile.GammaGraph

open LatticeProb FiniteAvalanches.Trees
open scoped Classical

noncomputable section

/-- Inner allowed heights on a finite set `S` of sites with held set `B`: below the number
of neighbours in `S` off `B`, and without a forbidden subset of `S`. -/
def latticeInner (B S : Finset Site2) : Finset (S → Fin 4) :=
  Finset.univ.filter fun a =>
    (∀ x : S, x.val ∉ B → (a x).val < Waves.degree S x.val) ∧
    ∀ T ⊆ S, T.Nonempty → ∃ x : S, x.val ∈ T ∧ Waves.degree T x.val ≤ (a x).val

/-- Inner allowed heights with prescribed values on the held set. -/
def latticeInnerValues (B S : Finset Site2) (ξ : Site2 → ℕ) : Finset (S → Fin 4) :=
  (latticeInner B S).filter fun a => ∀ x : S, x.val ∈ B → (a x).val = ξ x.val

/-- The sites of `S` among the sites of `Γ`. -/
def sitesIn (Γ S : Finset Site2) : Finset Γ := Γ.attach.filter fun x => x.val ∈ S

theorem mem_sitesIn {Γ S : Finset Site2} {x : Γ} : x ∈ sitesIn Γ S ↔ x.val ∈ S := by
  simp [sitesIn]

theorem sitesIn_image {Γ S : Finset Site2} (hS : S ⊆ Γ) :
    (sitesIn Γ S).image Subtype.val = S := by
  ext y
  simp only [Finset.mem_image, mem_sitesIn]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    exact ⟨⟨y, hS hy⟩, hy, rfl⟩

/-- The vertices of the wired graph of `Γ` at the sites of `S`. -/
def vertexSet (Γ S : Finset Site2) : Finset (Burning.SourceVertex (none : Vertex Γ)) :=
  (sitesIn Γ S).image (vertexEquiv Γ)

theorem mem_vertexSet {Γ S : Finset Site2} {x : Γ} :
    vertexEquiv Γ x ∈ vertexSet Γ S ↔ x.val ∈ S := by
  simp only [vertexSet, Finset.mem_image, mem_sitesIn]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [← (vertexEquiv Γ).injective hyx]
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem mem_vertexSet_iff {Γ S : Finset Site2} (v : Burning.SourceVertex (none : Vertex Γ)) :
    v ∈ vertexSet Γ S ↔ ((vertexEquiv Γ).symm v).val ∈ S := by
  rw [← mem_vertexSet, Equiv.apply_symm_apply]

theorem vertexSet_mono {Γ S T : Finset Site2} (h : S ⊆ T) : vertexSet Γ S ⊆ vertexSet Γ T := by
  intro v hv
  rw [mem_vertexSet_iff] at hv ⊢
  exact h hv

/-- The sites of a set of vertices of the wired graph of `Γ`. -/
def siteSet (Γ : Finset Site2) (H : Finset (Burning.SourceVertex (none : Vertex Γ))) :
    Finset Site2 := H.image fun v => ((vertexEquiv Γ).symm v).val

theorem siteSet_subset (Γ : Finset Site2) (H : Finset (Burning.SourceVertex (none : Vertex Γ))) :
    siteSet Γ H ⊆ Γ := by
  intro y hy
  obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp hy
  exact ((vertexEquiv Γ).symm v).property

theorem vertexSet_siteSet (Γ : Finset Site2) (H : Finset (Burning.SourceVertex (none : Vertex Γ))) :
    vertexSet Γ (siteSet Γ H) = H := by
  ext v
  rw [mem_vertexSet_iff, siteSet, Finset.mem_image]
  constructor
  · rintro ⟨w, hw, hwv⟩
    have : w = v := (vertexEquiv Γ).symm.injective (Subtype.ext hwv)
    exact this ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem siteSet_vertexSet {Γ S : Finset Site2} (hS : S ⊆ Γ) : siteSet Γ (vertexSet Γ S) = S := by
  ext y
  rw [siteSet, Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (mem_vertexSet_iff v).mp hv
  · intro hy
    refine ⟨vertexEquiv Γ ⟨y, hS hy⟩, mem_vertexSet.mpr hy, ?_⟩
    rw [Equiv.symm_apply_apply]

theorem activeDegree_vertexSet {Γ T : Finset Site2} (hT : T ⊆ Γ) (x : Γ) :
    Burning.activeDegree (graph Γ) (Finset.univ.erase none) (vertexSet Γ T) (vertexEquiv Γ x) =
      Waves.degree T x.val := by
  rw [vertexSet, subset_degree_all, sitesIn_image hT]

theorem degree_vertex (Γ : Finset Site2) (v : Burning.SourceVertex (none : Vertex Γ)) :
    Burning.degree (graph Γ) v.val = 4 := by
  rw [← Equiv.apply_symm_apply (vertexEquiv Γ) v]
  exact degree_four _

section Inner

variable {Γ B S : Finset Site2} (hSΓ : S ⊆ Γ) (hBS : B ⊆ S)

/-- The site of `S` at an inner vertex. -/
def innerSite (y : {y : Burning.SourceVertex (none : Vertex Γ) // y ∈ vertexSet Γ S}) : S :=
  ⟨((vertexEquiv Γ).symm y.val).val, (mem_vertexSet_iff y.val).mp y.property⟩

include hSΓ in
/-- The inner vertex at a site of `S`. -/
def innerVertex (x : S) : {y : Burning.SourceVertex (none : Vertex Γ) // y ∈ vertexSet Γ S} :=
  ⟨vertexEquiv Γ ⟨x.val, hSΓ x.property⟩, mem_vertexSet.mpr x.property⟩

omit hBS in
theorem innerSite_innerVertex (x : S) : innerSite (innerVertex hSΓ x) = x := by
  apply Subtype.ext
  simp [innerSite, innerVertex]

omit hBS in
theorem innerVertex_innerSite (y : {y : Burning.SourceVertex (none : Vertex Γ) // y ∈ vertexSet Γ S}) :
    innerVertex hSΓ (innerSite y) = y := by
  apply Subtype.ext
  simp [innerSite, innerVertex]

omit hBS in
theorem inner_bound_le
    (a : Burning.InnerField (graph Γ) (Finset.univ.erase none) (vertexSet Γ B) (vertexSet Γ S))
    (y : {y : Burning.SourceVertex (none : Vertex Γ) // y ∈ vertexSet Γ S}) :
    (a y).val < 4 := by
  have h := (a y).isLt
  split_ifs at h
  · exact lt_of_lt_of_eq h (degree_vertex Γ y.val)
  · have hle := Burning.degree_into_le_degree (graph Γ)
      ((vertexSet Γ S).image Subtype.val) y.val.val
    rw [degree_vertex] at hle
    unfold Burning.activeDegree at h
    omega

/-- Lattice heights of an inner field. -/
def toLattice
    (a : Burning.InnerField (graph Γ) (Finset.univ.erase none) (vertexSet Γ B) (vertexSet Γ S)) :
    S → Fin 4 :=
  fun x => ⟨(a (innerVertex hSΓ x)).val, inner_bound_le a _⟩

omit hBS in
theorem toLattice_injective :
    Function.Injective (toLattice (B := B) hSΓ) := by
  intro a b h
  funext y
  apply Fin.ext
  have := congrArg Fin.val (congrFun h (innerSite y))
  change (a (innerVertex hSΓ (innerSite y))).val = (b (innerVertex hSΓ (innerSite y))).val at this
  rwa [innerVertex_innerSite] at this

theorem innerVertex_val (x : S) : (innerVertex hSΓ x).val = vertexEquiv Γ ⟨x.val, hSΓ x.property⟩ :=
  rfl

omit hBS in
theorem toLattice_val
    (a : Burning.InnerField (graph Γ) (Finset.univ.erase none) (vertexSet Γ B) (vertexSet Γ S))
    (x : S) : (toLattice hSΓ a x).val = (a (innerVertex hSΓ x)).val := rfl

omit hBS in
theorem toLattice_mem_iff
    (a : Burning.InnerField (graph Γ) (Finset.univ.erase none) (vertexSet Γ B) (vertexSet Γ S)) :
    Burning.InnerAllowed (graph Γ) (Finset.univ.erase none) (vertexSet Γ B) (vertexSet Γ S) a ↔
      toLattice hSΓ a ∈ latticeInner B S := by
  have hcond1 : ∀ x : S, x.val ∉ B → (toLattice hSΓ a x).val < Waves.degree S x.val := by
    intro x hx
    have h := (a (innerVertex hSΓ x)).isLt
    have hxB : (innerVertex hSΓ x).val ∉ vertexSet Γ B := by
      rw [innerVertex_val, mem_vertexSet]
      exact hx
    exact lt_of_lt_of_eq h ((if_neg hxB).trans (by
      rw [innerVertex_val, activeDegree_vertexSet hSΓ]))
  simp only [latticeInner, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun ha => ⟨hcond1, fun T hTS hT => ?_⟩, fun ⟨_, h2⟩ H hHA hf => ?_⟩
  · have hHA : vertexSet Γ T ⊆ vertexSet Γ S := vertexSet_mono hTS
    by_contra hno
    push Not at hno
    apply ha (vertexSet Γ T) hHA
    obtain ⟨z, hz⟩ := hT
    refine ⟨⟨vertexEquiv Γ ⟨z, hSΓ (hTS hz)⟩, mem_vertexSet.mpr hz⟩, fun v hv => ?_⟩
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hv
    have hxT : x.val ∈ T := mem_vertexSet.mp hv
    have hlt := hno ⟨x.val, hTS hxT⟩ hxT
    rw [activeDegree_vertexSet (hTS.trans hSΓ)]
    exact hlt
  · obtain ⟨z, hzT, hz⟩ := h2 (siteSet Γ H) (by
      intro y hy
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      exact (mem_vertexSet_iff v).mp (hHA hv)) (hf.1.image _)
    have hvH : vertexEquiv Γ ⟨z.val, hSΓ z.property⟩ ∈ H := by
      rw [← vertexSet_siteSet Γ H, mem_vertexSet]
      exact hzT
    have hlt := hf.2 _ hvH
    rw [← vertexSet_siteSet Γ H, activeDegree_vertexSet (siteSet_subset Γ H)] at hlt
    rw [toLattice_val] at hz
    exact absurd hlt (not_lt.mpr hz)

omit hBS in
theorem toLattice_surjective (f : S → Fin 4) (hf : f ∈ latticeInner B S) :
    ∃ a : Burning.InnerField (graph Γ) (Finset.univ.erase none) (vertexSet Γ B) (vertexSet Γ S),
      toLattice hSΓ a = f := by
  simp only [latticeInner, Finset.mem_filter, Finset.mem_univ, true_and] at hf
  refine ⟨fun y => ⟨(f (innerSite y)).val, ?_⟩, ?_⟩
  · split_ifs with hy
    · rw [degree_vertex]
      exact (f (innerSite y)).isLt
    · have hyS : y.val = vertexEquiv Γ ⟨(innerSite y).val, hSΓ (innerSite y).property⟩ := by
        rw [← innerVertex_val, innerVertex_innerSite]
      rw [hyS, activeDegree_vertexSet hSΓ]
      apply hf.1
      intro hB
      apply hy
      rw [hyS, mem_vertexSet]
      exact hB
  · funext x
    apply Fin.ext
    rw [toLattice_val]
    change (f (innerSite (innerVertex hSΓ x))).val = (f x).val
    rw [innerSite_innerVertex]

/-- Inner allowed fields of the wired graph of `Γ` and lattice inner heights. -/
def innerEquiv :
    {a // Burning.InnerAllowed (graph Γ) (Finset.univ.erase none) (vertexSet Γ B)
      (vertexSet Γ S) a} ≃ {f // f ∈ latticeInner B S} :=
  Equiv.ofBijective (fun a => ⟨toLattice hSΓ a.val, (toLattice_mem_iff hSΓ a.val).mp a.property⟩)
    ⟨fun a b h => Subtype.ext (toLattice_injective hSΓ (congrArg Subtype.val h)),
      fun f => by
        obtain ⟨a, ha⟩ := toLattice_surjective hSΓ f.val f.property
        refine ⟨⟨a, (toLattice_mem_iff hSΓ a).mpr (ha ▸ f.property)⟩, Subtype.ext ha⟩⟩

omit hBS in
include hSΓ in
theorem card_inner :
    Nat.card {a // Burning.InnerAllowed (graph Γ) (Finset.univ.erase none) (vertexSet Γ B)
      (vertexSet Γ S) a} = (latticeInner B S).card := by
  rw [Nat.card_congr (innerEquiv hSΓ)]
  exact Nat.card_eq_finsetCard _

include hSΓ in
theorem card_inner_values (ξ : Site2 → ℕ) :
    Nat.card {a : {a // Burning.InnerAllowed (graph Γ) (Finset.univ.erase none)
        (vertexSet Γ B) (vertexSet Γ S) a} //
      ∀ x (hx : x ∈ vertexSet Γ B),
        (a.val ⟨x, vertexSet_mono hBS hx⟩).val = ξ ((vertexEquiv Γ).symm x).val} =
      (latticeInnerValues B S ξ).card := by
  have he : {a : {a // Burning.InnerAllowed (graph Γ) (Finset.univ.erase none)
        (vertexSet Γ B) (vertexSet Γ S) a} //
      ∀ x (hx : x ∈ vertexSet Γ B),
        (a.val ⟨x, vertexSet_mono hBS hx⟩).val = ξ ((vertexEquiv Γ).symm x).val} ≃
      {f // f ∈ latticeInnerValues B S ξ} := by
    refine ((innerEquiv hSΓ).subtypeEquiv (q := fun f => ∀ x : S, x.val ∈ B →
      (f.val x).val = ξ x.val) ?_).trans ?_
    · intro a
      constructor
      · intro h x hx
        have hv : (innerVertex hSΓ x).val ∈ vertexSet Γ B := by
          rw [innerVertex_val, mem_vertexSet]
          exact hx
        have := h _ hv
        have h2 : ((vertexEquiv Γ).symm (innerVertex hSΓ x).val).val = x.val := by
          rw [innerVertex_val, Equiv.symm_apply_apply]
        rw [h2] at this
        exact this
      · intro h v hv
        have hx : (innerSite ⟨v, vertexSet_mono hBS hv⟩).val ∈ B :=
          (mem_vertexSet_iff v).mp hv
        have := h _ hx
        change (a.val (innerVertex hSΓ (innerSite ⟨v, vertexSet_mono hBS hv⟩))).val =
          ξ (innerSite ⟨v, vertexSet_mono hBS hv⟩).val at this
        rw [innerVertex_innerSite] at this
        exact this
    · exact {
        toFun := fun f => ⟨f.val.val, Finset.mem_filter.mpr ⟨f.val.property, f.property⟩⟩
        invFun := fun f => ⟨⟨f.val, (Finset.mem_filter.mp f.property).1⟩,
          (Finset.mem_filter.mp f.property).2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [Nat.card_congr he]
  exact Nat.card_eq_finsetCard _

end Inner

end

end FiniteAvalanches.Sandpile.GammaGraph
