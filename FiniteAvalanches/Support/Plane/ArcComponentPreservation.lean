import FiniteAvalanches.Support.Plane.ThreeCompactSeparation
import FiniteAvalanches.Support.Plane.ArcRemoval

/-!
# Complement components after adjoining an arc

An arc that attaches successively to two compact pieces along preconnected
intersections preserves their complement components.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set
open LatticeProb.PlaneTopology
open QuantumZipper.CA.Topo MatedCRTHarmonic.Topology

/-- A simple plane path preserves a complement component when it meets each
successive compact piece in a preconnected set. -/
theorem connectedComponentIn_compl_union_path_two
    {K L : Set (ℝ × ℝ)} {x y a b : ℝ × ℝ}
    (hK : IsCompact K) (hL : IsCompact L) (p : Path x y) (hp : Function.Injective p)
    (hPK : IsPreconnected (range p ∩ K))
    (hPKL : IsPreconnected ((range p ∪ K) ∩ L))
    (ha : a ∉ (range p ∪ K) ∪ L) (hb : b ∉ (range p ∪ K) ∪ L)
    (hconn : b ∈ connectedComponentIn (K ∪ L)ᶜ a) :
    b ∈ connectedComponentIn ((range p ∪ K) ∪ L)ᶜ a := by
  let h : (ℝ × ℝ) ≃ₜ ℂ := Complex.equivRealProdCLM.symm.toHomeomorph
  let q := p.map h.continuous
  have hq : Function.Injective q := h.injective.comp hp
  have hqr : range q = h '' range p := by
    ext z
    simp only [q, Path.map_coe, Function.comp_apply, mem_range, mem_image]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨p t, ⟨t, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨t, rfl⟩, rfl⟩
      exact ⟨t, rfl⟩
  have hPK' : IsPreconnected (range q ∩ h '' K) := by
    rw [hqr, ← image_inter h.injective]
    exact hPK.image h h.continuous.continuousOn
  have hPKL' : IsPreconnected ((range q ∪ h '' K) ∩ h '' L) := by
    rw [hqr, ← image_union, ← image_inter h.injective]
    exact hPKL.image h h.continuous.continuousOn
  have htrace : (range q ∪ h '' K) ∪ h '' L = h '' ((range p ∪ K) ∪ L) := by
    rw [hqr, image_union, image_union]
  have ha' : h a ∉ (range q ∪ h '' K) ∪ h '' L := by
    rw [htrace]
    intro hx
    obtain ⟨z, hz, heq⟩ := hx
    exact ha (h.injective heq ▸ hz)
  have hb' : h b ∉ (range q ∪ h '' K) ∪ h '' L := by
    rw [htrace]
    intro hx
    obtain ⟨z, hz, heq⟩ := hx
    exact hb (h.injective heq ▸ hz)
  have haKL : a ∈ (K ∪ L)ᶜ := by
    rintro (hk | hl)
    · exact ha (Or.inl (Or.inr hk))
    · exact ha (Or.inr hl)
  have hconn' : h b ∈ connectedComponentIn ((h '' K) ∪ (h '' L))ᶜ (h a) := by
    rw [← image_union, ← image_compl_eq h.bijective,
      ← h.image_connectedComponentIn haKL]
    exact ⟨b, hconn, rfl⟩
  have hresult := connectedComponentIn_compl_union_arc_two (isArcSet_range q hq)
    (hK.image h.continuous) (hL.image h.continuous) hPK' hPKL' ha' hb' hconn'
  have haAll : a ∈ ((range p ∪ K) ∪ L)ᶜ := ha
  rw [htrace, ← image_compl_eq h.bijective,
    ← h.image_connectedComponentIn haAll] at hresult
  obtain ⟨z, hz, heq⟩ := hresult
  exact h.injective heq ▸ hz

end FiniteAvalanches.Electrical.StatementGeometry
