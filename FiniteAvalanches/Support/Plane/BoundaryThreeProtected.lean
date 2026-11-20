import FiniteAvalanches.Support.Plane.BoundaryThreeArms

/-!
# Three boundary arms avoiding other accesses

Three accesses with distinct endpoints can be joined while avoiding the
interiors of all other accesses in a finite family.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- Boundary accesses disjoint inside a region are disjoint when their
boundary endpoints are distinct. -/
theorem disjoint_boundary_paths_of_ne_targets
    {U : Set (ℝ × ℝ)} {a b c d : ℝ × ℝ}
    (p : Path a b) (q : Path c d)
    (hp : ∀ t : unitInterval, t ≠ 1 → p t ∈ U)
    (hq : ∀ t : unitInterval, t ≠ 1 → q t ∈ U)
    (hb : b ∉ U) (hd : d ∉ U)
    (hdisj : Disjoint (range p ∩ U) (range q)) (hne : b ≠ d) :
    Disjoint (range p) (range q) := by
  apply disjoint_left.mpr
  intro x hxp hxq
  by_cases hxU : x ∈ U
  · exact disjoint_left.mp hdisj ⟨hxp, hxU⟩ hxq
  · have hxb : x = b := mem_singleton_iff.mp
      (range_inter_compl_of_mem_except_target p hp hb ▸ ⟨hxp, hxU⟩)
    have hxd : x = d := mem_singleton_iff.mp
      (range_inter_compl_of_mem_except_target q hq hd ▸ ⟨hxq, hxU⟩)
    exact hne (hxb.symm.trans hxd)

/-- Three accesses with distinct endpoints admit separated arms avoiding the
other accesses in the region, with all three terminal speeds prescribed. -/
theorem exists_three_boundary_arms_avoiding_accesses
    {ι : Type*} [DecidableEq ι] {U S : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hconn : IsPreconnected U) (s : Finset ι)
    {x y : ι → ℝ × ℝ} (p : ∀ i, Path (x i) (y i))
    (hp : ∀ i ∈ s, Function.Injective (p i))
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Disjoint (range (p i) ∩ U) (range (p j)))
    (hinside : ∀ i ∈ s, ∀ t : unitInterval, t ≠ 1 → p i t ∈ U)
    (hout : ∀ i ∈ s, y i ∉ U) (hS : S.Finite)
    (hobs : ∀ i ∈ s, Disjoint (range (p i)) S)
    {i j k : ι} (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hyij : y i ≠ y j) (hyik : y i ≠ y k) (hyjk : y j ≠ y k) :
    ∃ r ∈ U, ∃ (a : Path r (y i)) (b : Path r (y j)) (c : Path r (y k)),
      Function.Injective a ∧ Function.Injective b ∧ Function.Injective c ∧
      Disjoint (range a) S ∧ Disjoint (range b) S ∧ Disjoint (range c) S ∧
      range a ∩ Uᶜ = {y i} ∧ range b ∩ Uᶜ = {y j} ∧ range c ∩ Uᶜ = {y k} ∧
      range a ∩ range b = {r} ∧ range a ∩ range c = {r} ∧ range b ∩ range c = {r} ∧
      Disjoint ((range a ∪ range b ∪ range c) ∩ U)
        (⋃ l ∈ ((s.erase i).erase j).erase k, range (p l)) ∧
      (∃ t : unitInterval, t ≠ 1 ∧ ∀ (u : unitInterval)
        (hu : ((t : ℝ) + 1) / 2 ≤ (u : ℝ)),
        a u = p i ⟨2 * (u : ℝ) - 1, by constructor <;> linarith [t.property.1, u.property.2]⟩) ∧
      (∃ t : unitInterval, t ≠ 1 ∧ ∀ (u : unitInterval)
        (hu : ((t : ℝ) + 1) / 2 ≤ (u : ℝ)),
        b u = p j ⟨2 * (u : ℝ) - 1, by constructor <;> linarith [t.property.1, u.property.2]⟩) ∧
      (∃ t : unitInterval, t ≠ 1 ∧ ∀ (u : unitInterval)
        (hu : ((t : ℝ) + 1) / 2 ≤ (u : ℝ)),
        c u = p k ⟨2 * (u : ℝ) - 1, by constructor <;> linarith [t.property.1, u.property.2]⟩) := by
  let t := ((s.erase i).erase j).erase k
  let A := ⋃ l ∈ t, range (p l)
  let W := U \ A
  have htS : t ⊆ s := fun l hl => Finset.mem_of_mem_erase
    (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hl))
  have hAclosed : IsClosed A :=
    (t.isCompact_biUnion (fun l _ => isCompact_range (p l).continuous)).isClosed
  have hW : IsOpen W := hU.sdiff hAclosed
  have hWconn : IsPreconnected W := by
    apply isPreconnected_sdiff_finset_paths_of_disjoint_inside hU hconn t p
    · exact fun l hl => hp l (htS hl)
    · exact fun l hl m hm hne => hd l (htS hl) m (htS hm) hne
    · exact fun l hl => isPreconnected_range_inter_compl_of_mem_except_target
        (p l) (hinside l (htS hl)) (hout l (htS hl))
  have hne_i : ∀ l ∈ t, i ≠ l := by
    intro l hl heq
    subst l
    exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hl))).1 rfl
  have hne_j : ∀ l ∈ t, j ≠ l := by
    intro l hl heq
    subst l
    exact (Finset.mem_erase.mp (Finset.mem_of_mem_erase hl)).1 rfl
  have hne_k : ∀ l ∈ t, k ≠ l := by
    intro l hl heq
    subst l
    exact (Finset.mem_erase.mp hl).1 rfl
  have hinsW {v : ι} (hv : v ∈ s) (hvne : ∀ l ∈ t, v ≠ l)
      (u : unitInterval) (hu : u ≠ 1) : p v u ∈ W := by
    refine ⟨hinside v hv u hu, ?_⟩
    intro h
    obtain ⟨l, hl, hlp⟩ := mem_iUnion₂.mp h
    exact disjoint_left.mp (hd v hv l (htS hl) (hvne l hl))
      ⟨⟨u, rfl⟩, hinside v hv u hu⟩ hlp
  have disj {v w : ι} (hv : v ∈ s) (hw : w ∈ s) (hne : v ≠ w)
      (hy : y v ≠ y w) : Disjoint (range (p v)) (range (p w)) :=
    disjoint_boundary_paths_of_ne_targets (p v) (p w) (hinside v hv) (hinside w hw)
      (hout v hv) (hout w hw) (hd v hv w hw hne) hy
  obtain ⟨r, hr, a, b, c, ha, hb, hc, haS, hbS, hcS, haW, hbW, hcW,
      hab, hac, hbc, hat, hbt, hct⟩ :=
    exists_three_boundary_arms_of_disjoint_accesses hW hWconn (p i) (p j) (p k)
      (hp i hi) (hp j hj) (hp k hk) (disj hi hj hij hyij) (disj hi hk hik hyik)
      (disj hj hk hjk hyjk) (hinsW hi hne_i) (hinsW hj hne_j) (hinsW hk hne_k)
      (fun h => hout i hi h.1) (fun h => hout j hj h.1) (fun h => hout k hk h.1)
      hS (hobs i hi) (hobs j hj) (hobs k hk)
  have convert_boundary {z : ℝ × ℝ} (v : Path r z) (hz : z ∉ U)
      (hv : range v ∩ Wᶜ = {z}) : range v ∩ Uᶜ = {z} := by
    apply subset_antisymm
    · exact (inter_subset_inter_right _ (compl_subset_compl.mpr sdiff_subset)).trans hv.le
    · exact singleton_subset_iff.mpr ⟨v.target_mem_range, hz⟩
  have avoid {z : ℝ × ℝ} (v : Path r z) (hz : z ∉ U)
      (hv : range v ∩ Wᶜ = {z}) : Disjoint (range v ∩ U) A := by
    apply disjoint_left.mpr
    intro z' ⟨hzv, hzU⟩ hzA
    have hz' : z' ∈ ({z} : Set (ℝ × ℝ)) := hv ▸ ⟨hzv, fun h => h.2 hzA⟩
    exact hz ((mem_singleton_iff.mp hz').symm ▸ hzU)
  refine ⟨r, hr.1, a, b, c, ha, hb, hc, haS, hbS, hcS,
    convert_boundary a (hout i hi) haW, convert_boundary b (hout j hj) hbW,
    convert_boundary c (hout k hk) hcW, hab, hac, hbc, ?_, hat, hbt, hct⟩
  rw [union_inter_distrib_right, union_inter_distrib_right, disjoint_union_left,
    disjoint_union_left]
  exact ⟨⟨avoid a (hout i hi) haW, avoid b (hout j hj) hbW⟩,
    avoid c (hout k hk) hcW⟩

end FiniteAvalanches.Electrical.StatementGeometry
