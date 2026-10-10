import FiniteAvalanches.Electrical.Geometry.UnitSegments

set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeCell
open LatticeProb
open FiniteAvalanches.Electrical.StatementGeometry (ArcParameter)
open scoped Classical
noncomputable section

theorem unitSegment_start (p : Site 2) (i : Fin 2) : unitSegment p i 0 = sitePoint p := by
  simp [unitSegment,sitePoint]
theorem unitSegment_finish (p : Site 2) (i : Fin 2) :
    unitSegment p i 1 = sitePoint (p + unit i) := by
  simp [unitSegment,sitePoint]

theorem adjacent_continuum (D : Set (Site 2)) (x y : Site 2)
    (hx : x ∈ D) (hy : y ∈ D) (hxy : (lattice 2).Adj x y) :
    ∃ A : Set (ℝ × ℝ), IsCompact A ∧ IsConnected A ∧ A ⊆ latticeTrace D ∧
      sitePoint x ∈ A ∧ sitePoint y ∈ A := by
  have segment (p : Site 2) (i : Fin 2) (hp : p ∈ D) (hpi : p + unit i ∈ D) :
      ∃ A : Set (ℝ × ℝ), IsCompact A ∧ IsConnected A ∧ A ⊆ latticeTrace D ∧
        sitePoint p ∈ A ∧ sitePoint (p + unit i) ∈ A := by
    let f : ArcParameter → ℝ × ℝ := fun t => unitSegment p i t.val
    have hf : Continuous f := by unfold f unitSegment; fun_prop
    refine ⟨Set.range f,isCompact_range hf,isConnected_range hf,?_,?_,?_⟩
    · rintro z ⟨t,rfl⟩
      exact Or.inr ⟨p,i,hp,hpi,t.val,t.property,rfl⟩
    · exact ⟨⟨0,by constructor <;> norm_num⟩,unitSegment_start p i⟩
    · exact ⟨⟨1,by constructor <;> norm_num⟩,unitSegment_finish p i⟩
  change ∃ i : Fin 2, y = x + unit i ∨ x = y + unit i at hxy
  obtain ⟨i,h | h⟩ := hxy
  · subst y
    exact segment x i hx hy
  · subst x
    obtain ⟨A,hc,hconn,hsub,hp,hq⟩ := segment y i hy hx
    exact ⟨A,hc,hconn,hsub,hq,hp⟩

/-- A literal finite nearest-neighbor path supplies compact connected straight-edge trace. -/
theorem reachable_continuum (D : Set (Site 2)) {x y : Site 2} (hx : x ∈ D)
    (hxy : Relation.ReflTransGen (fun u v => u ∈ D ∧ v ∈ D ∧ (lattice 2).Adj u v) x y) :
    ∃ K : Set (ℝ × ℝ), IsCompact K ∧ IsConnected K ∧ K ⊆ latticeTrace D ∧
      sitePoint x ∈ K ∧ sitePoint y ∈ K := by
  induction hxy with
  | refl =>
    refine ⟨{sitePoint x},isCompact_singleton,isConnected_singleton,?_,by simp,by simp⟩
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact Or.inl ⟨x,hx,rfl⟩
  | @tail u v _ huv ih =>
    obtain ⟨K,hKc,hKconn,hKt,hxK,huK⟩ := ih
    obtain ⟨A,hAc,hAconn,hAt,huA,hvA⟩ := adjacent_continuum D u v huv.1 huv.2.1 huv.2.2
    refine ⟨K ∪ A,hKc.union hAc,hKconn.union ⟨sitePoint u,huK,huA⟩ hAconn,?_,
      Or.inl hxK,Or.inr hvA⟩
    exact Set.union_subset hKt hAt

/-- Literal D/D-complement paths give disjoint genuine compact connected plane sets. -/
theorem opposite_paths_continua (D : Set (Site 2)) (x y z w : Site 2)
    (hD : ((lattice 2).induce D).Connected) (hDc : ((lattice 2).induce Dᶜ).Connected)
    (hx : x ∈ D) (hy : y ∈ D) (hz : z ∉ D) (hw : w ∉ D) :
    ∃ K L : Set (ℝ × ℝ), IsCompact K ∧ IsConnected K ∧ IsCompact L ∧ IsConnected L ∧
      K ⊆ latticeTrace D ∧ L ⊆ latticeTrace Dᶜ ∧ Disjoint K L ∧
      sitePoint x ∈ K ∧ sitePoint y ∈ K ∧ sitePoint z ∈ L ∧ sitePoint w ∈ L := by
  obtain ⟨K,hKc,hKconn,hKt,hxK,hyK⟩ := reachable_continuum D hx (induced_reaches D hD x y hx hy)
  obtain ⟨L,hLc,hLconn,hLt,hzL,hwL⟩ := reachable_continuum Dᶜ hz (induced_reaches Dᶜ hDc z w hz hw)
  refine ⟨K,L,hKc,hKconn,hLc,hLconn,hKt,hLt,?_,hxK,hyK,hzL,hwL⟩
  exact (latticeTrace_disjoint (Set.disjoint_left.mpr (by intro x hx hxc; exact hxc hx))).mono hKt hLt

end
end FiniteAvalanches.Electrical.LatticeCell
