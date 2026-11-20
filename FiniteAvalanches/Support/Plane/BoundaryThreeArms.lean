import FiniteAvalanches.Support.Plane.BoundaryTripodTails
import FiniteAvalanches.Support.Plane.BoundaryFirstComplement

/-!
# Three boundary arms

Three disjoint boundary accesses admit separated arms with a common root and
prescribed terminal parametrizations.
-/

namespace FiniteAvalanches.Electrical.StatementGeometry

open Set unitInterval

/-- Three disjoint boundary accesses can be joined by separated arms that
preserve their terminal parametrizations and avoid a finite set. -/
theorem exists_three_boundary_arms_of_disjoint_accesses
    {U S : Set (ℝ × ℝ)} {a b c d e f : ℝ × ℝ}
    (hU : IsOpen U) (hconn : IsPreconnected U)
    (p : Path a b) (q : Path c d) (s : Path e f)
    (hp : Function.Injective p) (hq : Function.Injective q) (hs : Function.Injective s)
    (hpq : Disjoint (range p) (range q))
    (hps : Disjoint (range p) (range s)) (hqs : Disjoint (range q) (range s))
    (hpU : ∀ t : unitInterval, t ≠ 1 → p t ∈ U)
    (hqU : ∀ t : unitInterval, t ≠ 1 → q t ∈ U)
    (hsU : ∀ t : unitInterval, t ≠ 1 → s t ∈ U)
    (hb : b ∉ U) (hd : d ∉ U) (hf : f ∉ U)
    (hS : S.Finite) (hpS : Disjoint (range p) S)
    (hqS : Disjoint (range q) S) (hsS : Disjoint (range s) S) :
    ∃ r ∈ U, ∃ (v : Path r b) (w : Path r d) (z : Path r f),
      Function.Injective v ∧ Function.Injective w ∧ Function.Injective z ∧
      Disjoint (range v) S ∧ Disjoint (range w) S ∧ Disjoint (range z) S ∧
      range v ∩ Uᶜ = {b} ∧ range w ∩ Uᶜ = {d} ∧ range z ∩ Uᶜ = {f} ∧
      range v ∩ range w = {r} ∧ range v ∩ range z = {r} ∧ range w ∩ range z = {r} ∧
      (∃ t : unitInterval, t ≠ 1 ∧ ∀ (u : unitInterval)
        (hu : ((t : ℝ) + 1) / 2 ≤ (u : ℝ)),
        v u = p ⟨2 * (u : ℝ) - 1, by constructor <;> linarith [t.property.1, u.property.2]⟩) ∧
      (∃ t : unitInterval, t ≠ 1 ∧ ∀ (u : unitInterval)
        (hu : ((t : ℝ) + 1) / 2 ≤ (u : ℝ)),
        w u = q ⟨2 * (u : ℝ) - 1, by constructor <;> linarith [t.property.1, u.property.2]⟩) ∧
      (∃ t : unitInterval, t ≠ 1 ∧ ∀ (u : unitInterval)
        (hu : ((t : ℝ) + 1) / 2 ≤ (u : ℝ)),
        z u = s ⟨2 * (u : ℝ) - 1, by constructor <;> linarith [t.property.1, u.property.2]⟩) := by
  let W := U \ range s
  have hW : IsOpen W := hU.sdiff (isCompact_range s.continuous).isClosed
  have hWconn : IsPreconnected W := isPreconnected_sdiff_boundary_path hU hconn s hs hsU hf
  have hpW : ∀ t : unitInterval, t ≠ 1 → p t ∈ W := by
    intro t ht
    exact ⟨hpU t ht, fun h => disjoint_left.mp hps ⟨t, rfl⟩ h⟩
  have hqW : ∀ t : unitInterval, t ≠ 1 → q t ∈ W := by
    intro t ht
    exact ⟨hqU t ht, fun h => disjoint_left.mp hqs ⟨t, rfl⟩ h⟩
  obtain ⟨cross, hcross, hcrossS, hboundary, hpTail, hqTail⟩ :=
    exists_injective_path_between_boundary_accesses_with_tails hW hWconn p q hp hq hpq
      hpW hqW (fun h => hb h.1) (fun h => hd h.1) hS hpS hqS
  let m : unitInterval := ⟨1 / 2, by norm_num⟩
  let x := cross m
  have hm0 : m ≠ 0 := by intro h; have := congrArg Subtype.val h; norm_num [m] at this
  have hm1 : m ≠ 1 := by intro h; have := congrArg Subtype.val h; norm_num [m] at this
  have hxW : x ∈ W := by
    by_contra h
    have hx : x ∈ ({d, b} : Set (ℝ × ℝ)) := hboundary ▸ ⟨⟨m, rfl⟩, h⟩
    rcases hx with hx | hx
    · exact hm0 (hcross (hx.trans cross.source.symm))
    · exact hm1 (hcross (hx.trans cross.target.symm))
  have hxS : x ∉ S := fun h => disjoint_left.mp hcrossS ⟨m, rfl⟩ h
  let paths : Unit → Path e f := fun _ => s
  have hroot : x ∈ (U \ (⋃ i ∈ ({()} : Finset Unit), range (paths i))) \ S := by
    refine ⟨⟨hxW.1, ?_⟩, hxS⟩
    intro hx
    obtain ⟨_, _, hx⟩ := mem_iUnion₂.mp hx
    exact hxW.2 hx
  obtain ⟨access, haccess, haccessS, haccessboundary, _, t, ht, htail⟩ :=
    exists_path_to_boundary_avoiding_paths_disjoint_inside_and_finite
      hU hconn ({()} : Finset Unit) paths (by simpa [paths] using hs) (by simp)
      (by simpa [paths] using hsU) (by simpa [paths] using hf)
      hS (by simpa [paths] using hsS) hroot (i := ()) (by simp)
  have hfb : f ≠ b := fun h => disjoint_left.mp hps (h.symm ▸ p.target_mem_range) s.target_mem_range
  have hfd : f ≠ d := fun h => disjoint_left.mp hqs (h.symm ▸ q.target_mem_range) s.target_mem_range
  have hfCross : f ∉ range cross := by
    intro h
    have h' : f ∈ ({d, b} : Set (ℝ × ℝ)) := hboundary ▸ ⟨h, fun hw => hf hw.1⟩
    rcases h' with h' | h'
    · exact hfd h'
    · exact hfb h'
  have hbAccess : b ∉ range access := by
    intro h
    have h' : b ∈ ({f} : Set (ℝ × ℝ)) := haccessboundary ▸ ⟨h, hb⟩
    exact hfb (mem_singleton_iff.mp h').symm
  have hdAccess : d ∉ range access := by
    intro h
    have h' : d ∈ ({f} : Set (ℝ × ℝ)) := haccessboundary ▸ ⟨h, hd⟩
    exact hfd (mem_singleton_iff.mp h').symm
  have hrev : Function.Injective access.symm :=
    haccess.comp unitInterval.symm_involutive.injective
  obtain ⟨r, v, w, z, hv, hw, hz, hvCross, hwCross, hzAccess, hvw, hvz, hwz,
      hvTail, hwTail, hzTail⟩ :=
    exists_tripod_of_path_first_hit_with_tails cross access.symm q p s hcross hrev hq hp hs
      hfCross ⟨m, rfl⟩ (by simpa only [Path.symm_range] using hdAccess)
      (by simpa only [Path.symm_range] using hbAccess) hqTail hpTail
      ⟨t, ht, by simpa only [Path.symm_range] using htail⟩
  have hrU : r ∈ U := by
    by_contra h
    have h' : r ∈ ({f} : Set (ℝ × ℝ)) := haccessboundary ▸
      ⟨by simpa only [Path.symm_range] using hzAccess z.source_mem_range, h⟩
    exact hfCross ((mem_singleton_iff.mp h').symm ▸ hvCross v.source_mem_range)
  have hvU : range v ∩ Uᶜ = {d} := by
    apply subset_antisymm
    · intro y hy
      have hy' : y ∈ ({d, b} : Set (ℝ × ℝ)) := hboundary ▸
        ⟨hvCross hy.1, fun h => hy.2 h.1⟩
      rcases hy' with h | h
      · exact h
      · subst y
        have h' : b ∈ range v ∩ range w := ⟨hy.1, w.target_mem_range⟩
        rw [hvw] at h'
        exact (hb ((mem_singleton_iff.mp h').symm ▸ hrU)).elim
    · exact singleton_subset_iff.mpr ⟨v.target_mem_range, hd⟩
  have hwU : range w ∩ Uᶜ = {b} := by
    apply subset_antisymm
    · intro y hy
      have hy' : y ∈ ({d, b} : Set (ℝ × ℝ)) := hboundary ▸
        ⟨hwCross hy.1, fun h => hy.2 h.1⟩
      rcases hy' with h | h
      · subst y
        have h' : d ∈ range v ∩ range w := ⟨v.target_mem_range, hy.1⟩
        rw [hvw] at h'
        exact (hd ((mem_singleton_iff.mp h').symm ▸ hrU)).elim
      · exact h
    · exact singleton_subset_iff.mpr ⟨w.target_mem_range, hb⟩
  have hzU : range z ∩ Uᶜ = {f} := by
    apply subset_antisymm
    · exact (inter_subset_inter_left _ (by simpa only [Path.symm_range] using hzAccess)).trans
        haccessboundary.le
    · exact singleton_subset_iff.mpr ⟨z.target_mem_range, hf⟩
  exact ⟨r, hrU, w, v, z, hw, hv, hz, hcrossS.mono_left hwCross,
    hcrossS.mono_left hvCross, haccessS.mono_left (by simpa only [Path.symm_range] using hzAccess),
    hwU, hvU, hzU, by simpa only [inter_comm] using hvw,
    hwz, hvz, hwTail, hvTail, hzTail⟩

end FiniteAvalanches.Electrical.StatementGeometry
