import FiniteAvalanches.Wilson.Lattice.RevealedGeometry.LastExit

set_option autoImplicit false
namespace JointRevealedPath
open LatticeProb FiniteAvalanches
open scoped Classical
noncomputable section

theorem support_in_component (U : Set (Site 2)) (c : U) {a : Site 2}
    (p : (lattice 2).Walk a c.val) (hU : ∀ x ∈ p.support, x ∈ U) :
    ∀ x ∈ p.support, x ∈ JointExterior.component U c := by
  intro x hx
  let q := p.dropUntil x hx
  have hq : ∀ y ∈ q.support, y ∈ U := fun y hy =>
    hU y (p.support_dropUntil_subset_support hx hy)
  exact JointExterior.reachable_mem_component U c ⟨x,hU x hx⟩
    (SimpleGraph.Walk.reachable (q.induce U hq)).symm

/-- A finite simple gamma path, decomposed at its last box vertex, with the
whole remaining suffix in one actual cofinite exterior component. -/
theorem exists_revealed_path (γ : Set (Site 2))
    (hc : ((lattice 2).induce γ).Connected) (hf : γᶜ.Finite)
    (hn : ∃ b ∈ γ, (lattice 2).Adj 0 b) (h : ℕ) (hh : 10 ≤ h) :
    ∃ (c : ↥(γ \ box 2 (2*h))) (b w z : Site 2)
      (P : (lattice 2).Walk b c.val)
      (q₀ : (lattice 2).Walk b w) (e : (lattice 2).Adj w z)
      (q₁ : (lattice 2).Walk z c.val),
      (JointExterior.component (γ \ box 2 (2*h)) c)ᶜ.Finite ∧
      b ∈ γ ∧ (lattice 2).Adj 0 b ∧ P.IsPath ∧
      (∀ x ∈ P.support, x ∈ γ) ∧ P = q₀.append (.cons e q₁) ∧
      Needle.radius w = 2*h ∧ w ∈ γ ∧
      (∀ x ∈ q₁.support, x ∈ JointExterior.component (γ \ box 2 (2*h)) c) := by
  obtain ⟨c,hcf⟩ := JointCofiniteComponent.exists_cofinite_component γ hf (2*h)
  obtain ⟨b,hb,hadj⟩ := hn
  obtain ⟨p,hp⟩ := hc.exists_isPath ⟨b,hb⟩ ⟨c.val,c.property.1⟩
  let f := (SimpleGraph.Embedding.induce γ (G := lattice 2)).toHom
  let P := p.map f
  have hP : P.IsPath := hp.map (show Function.Injective f from Subtype.val_injective)
  have hPγ : ∀ x ∈ P.support, x ∈ γ := by
    intro x hx
    rw [SimpleGraph.Walk.support_map] at hx
    obtain ⟨y,_,he⟩ := List.mem_map.mp hx
    exact he ▸ y.property
  have hbB : b ∈ box 2 (2*h) := by
    have he := Needle.radius_sub_neighbor hadj.symm
    have he' : Needle.radius b = 1 := by simpa only [sub_zero] using he
    apply (Needle.mem_box_iff b (2*h)).mpr
    rw [he']; omega
  obtain ⟨w,z,q₀,e,q₁,hdecomp,hw,hout⟩ := JointLastExit.last_exit (lattice 2)
    (box 2 (2*h)) P ⟨b,P.start_mem_support,hbB⟩ c.property.2
  have hqsub : ∀ x ∈ q₁.support, x ∈ P.support := by
    intro x hx
    rw [hdecomp]
    exact SimpleGraph.Walk.support_subset_support_append_right q₀ (.cons e q₁)
      (SimpleGraph.Walk.support_subset_support_cons q₁ e hx)
  have hqU : ∀ x ∈ q₁.support, x ∈ γ \ box 2 (2*h) :=
    fun x hx => ⟨hPγ x (hqsub x hx),hout x hx⟩
  refine ⟨c,b,w,z,P,q₀,e,q₁,hcf,hb,hadj,hP,hPγ,hdecomp,
    JointLastExit.boundary_of_exit (2*h) w z hw (hout z q₁.start_mem_support) e,?_,
    support_in_component _ c q₁ hqU⟩
  apply hPγ w
  rw [hdecomp]
  exact SimpleGraph.Walk.support_subset_support_append_left q₀ (.cons e q₁) q₀.end_mem_support

end
end JointRevealedPath
