import FiniteAvalanches.Wilson.Lattice.LocalComparison.Complement
import FiniteAvalanches.Wilson.Lattice.LocalComparison.BoundarySize

set_option autoImplicit false
namespace LocalStoppedPath
open LatticeProb FiniteAvalanches FiniteAvalanches.Sandpile FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical
noncomputable section

/-- Stop at the first vertex at the prescribed radius. -/
theorem first_radius_prefix (r : ℕ) {a z : Site 2} (p : (lattice 2).Walk a z)
    (ha : siteRadius 0 a ≤ r) (hz : siteRadius 0 z = r) :
    ∃ (y : Site 2) (q : (lattice 2).Walk a y) (t : (lattice 2).Walk y z),
      p = q.append t ∧ siteRadius 0 y = r ∧
      (∀ x ∈ q.support, siteRadius 0 x ≤ r) ∧
      (∀ x ∈ q.support, x ≠ y → siteRadius 0 x < r) := by
  induction p with
  | nil =>
    refine ⟨_,.nil,.nil,rfl,hz,?_,?_⟩
    · intro x hx
      simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hx
      exact hx ▸ ha
    · intro x hx hne
      simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hx
      exact (hne hx).elim
  | @cons a c z e p ih =>
    by_cases he : siteRadius 0 a = r
    · refine ⟨a,.nil,.cons e p,rfl,he,?_,?_⟩
      · intro x hx
        simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hx
        exact hx ▸ ha
      · intro x hx hne
        simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hx
        exact (hne hx).elim
    · have halt : siteRadius 0 a < r := Nat.lt_of_le_of_ne ha he
      have hc : siteRadius 0 c ≤ r := by
        have ht := JointMetricGeometry.radius_triangle 0 a c
        have hs := JointMetricGeometry.radius_adj_le_one a c e
        omega
      obtain ⟨y,q,t,hp,hy,hq,hqlt⟩ := ih hc hz
      refine ⟨y,.cons e q,t,?_,hy,?_,?_⟩
      · simp only [SimpleGraph.Walk.cons_append,← hp]
      · intro x hx
        simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hx
        exact hx.elim (fun he => he ▸ ha) (hq x)
      · intro x hx hne
        simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hx
        exact hx.elim (fun he => he ▸ halt) (fun hx => hqlt x hx hne)

theorem exists_stopped_path (r : ℕ) (hr : 1 ≤ r) (R : RootPair)
    (b : Site 2) (hb : b ∈ R.one) (hadj : (lattice 2).Adj 0 b)
    (hOne : ((lattice 2).induce R.one).Connected)
    (hmeet : ∃ z ∈ R.one, siteRadius 0 z = r) :
    ∃ (y : Site 2) (q : (lattice 2).Walk b y),
      q.IsPath ∧ siteRadius 0 y = r ∧
      (∀ x ∈ q.support, x ∈ R.one ∧ x ∈ boxSites r) ∧
      (∀ x ∈ q.support, x ≠ y → siteRadius 0 x < r) := by
  obtain ⟨z,hz,hzr⟩ := hmeet
  obtain ⟨p,hp⟩ := hOne.exists_isPath ⟨b,hb⟩ ⟨z,hz⟩
  let f := (SimpleGraph.Embedding.induce R.one (G := lattice 2)).toHom
  have hmap : (p.map f).IsPath := hp.map Subtype.val_injective
  obtain ⟨y,q,t,he,hy,hqr,hqlt⟩ := first_radius_prefix r (p.map f)
    ((JointMetricGeometry.radius_adj_le_one 0 b hadj).trans hr) hzr
  have hq : q.IsPath := (he ▸ hmap).of_append_left
  refine ⟨y,q,hq,hy,?_,hqlt⟩
  intro x hx
  have hxp : x ∈ (p.map f).support := he ▸ q.support_subset_support_append_left t hx
  rw [SimpleGraph.Walk.support_map] at hxp
  obtain ⟨u,_,hu⟩ := List.mem_map.mp hxp
  refine ⟨hu ▸ u.property,?_⟩
  apply (mem_box_sites r x).mpr
  intro i
  simpa only [Pi.zero_apply,sub_zero,abs_le] using
    (siteRadius_le_iff 0 x r).mp (hqr x hx) i

/-- Lift a literal finite set of original sites into the unchanged one-root carrier. -/
def oneSet (D Q : Finset (Site 2)) (hQD : Q ⊆ D) (hQ : Q.Nonempty) : OneSet D :=
  ⟨Finset.univ.filter (fun x : D => x.val ∈ Q), by
    obtain ⟨x,hx⟩ := hQ
    exact ⟨⟨x,hQD hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩⟩⟩

theorem oneSet_image (D Q : Finset (Site 2)) (hQD : Q ⊆ D) (hQ : Q.Nonempty) :
    (oneSet D Q hQD hQ).val.image Subtype.val = Q := by
  ext x
  constructor
  · rintro hx
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    exact (Finset.mem_filter.mp hu).2
  · intro hx
    exact Finset.mem_image.mpr ⟨⟨x,hQD hx⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,rfl⟩

/-- The distinguished copy is specifically the source edge from zero to b. -/
theorem exists_origin_mark (D : Finset (Site 2)) (P : OneSet D)
    (h0 : (0 : Site 2) ∉ D) (b : Site 2) (hb : b ∈ P.val.image Subtype.val)
    (hadj : (lattice 2).Adj 0 b) :
    ∃ marked : MarkedCopy D P,
      (originalA marked.val = 0 ∧ originalB marked.val = b) ∨
      (originalA marked.val = b ∧ originalB marked.val = 0) := by
  have ha := (project_eq_alpha_iff D P 0).mpr h0
  have hbeta := (project_eq_beta_iff D P b).mpr hb
  obtain ⟨i,he | he⟩ := Graph.Zd.adj_iff.mp hadj
  · have hbunit : b = unit i := by simpa only [zero_add] using he
    refine ⟨⟨(0,i), Or.inl ⟨ha,?_⟩⟩,Or.inl ⟨rfl,?_⟩⟩
    · simpa only [originalB,zero_add,← hbunit] using hbeta
    · simpa only [originalB,zero_add] using hbunit.symm
  · have hbunit : b = -unit i := by simpa only [zero_sub] using he
    have hB : originalB (b,i) = 0 := by
      simp only [originalB,hbunit,neg_add_cancel]
    refine ⟨⟨(b,i),Or.inr ⟨hbeta,hB ▸ ha⟩⟩,Or.inr ⟨rfl,hB⟩⟩

end
end LocalStoppedPath
