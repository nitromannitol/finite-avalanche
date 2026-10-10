import FiniteAvalanches.Sandpile.LocalConfinement

/-! The literal one-grain radius is locally determined at every source. A finite
radius supplies its actual legal list; no avalanche-finiteness assumption is used.
The enclosing box is larger than a centered box and has the same exact event. -/
namespace FiniteAvalanches.Sandpile
open LatticeProb FiniteAvalanches
open scoped Classical
noncomputable section

theorem mem_box_of_site_radius_le {o x : Site2} {R : ℕ}
    (h : siteRadius o x ≤ R) : x ∈ boxSites (siteRadius 0 o + R) := by
  have hx := (siteRadius_le_iff o x R).mp h
  have ho := (siteRadius_le_iff 0 o (siteRadius 0 o)).mp le_rfl
  rw [mem_box_sites]
  intro i
  have hi := abs_le.mp (hx i)
  have hi' := abs_le.mp (ho i)
  simp only [Pi.zero_apply, sub_zero] at hi'
  constructor <;> push_cast <;> omega

theorem radius_le_of_agree_box {η η' : StableField} (o : Site2) (R : ℕ)
    (heq : ∀ x ∈ boxSites (siteRadius 0 o + R + 1), η' x = η x)
    (hr : radius η o ≤ (R : WithTop ℕ)) : radius η' o ≤ (R : WithTop ℕ) := by
  have hf : FiniteStabilizable η o := by
    by_contra hn
    rw [(radius_eq_top_iff η o).mpr hn] at hr
    simp at hr
  obtain ⟨w, hw⟩ := hf
  rw [radius_of_stabilizes hw] at hr
  have hb := (countsRadius_le_iff o (listCounts w) R).mp (WithTop.coe_le_coe.mp hr)
  have hu : (listCounts w).support ⊆ boxSites (siteRadius 0 o + R) := by
    intro x hx
    exact mem_box_of_site_radius_le (hb x (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hx)))
  have ho : o ∈ boxSites (siteRadius 0 o + R) :=
    (site_radius_zero_le_iff o _).mp (Nat.le_add_right _ _)
  have ha := affected_subset_box_succ (one_grain_support_subset_box ho) hu
  have hw' := stabilizes_transfer hw (fun x hx => heq x (ha hx))
  rw [radius_of_stabilizes hw']
  exact hr

theorem radius_le_iff_of_agree_box {η η' : StableField} (o : Site2) (R : ℕ)
    (heq : ∀ x ∈ boxSites (siteRadius 0 o + R + 1), η' x = η x) :
    radius η' o ≤ (R : WithTop ℕ) ↔ radius η o ≤ (R : WithTop ℕ) :=
  ⟨radius_le_of_agree_box o R (fun x hx => (heq x hx).symm),
    radius_le_of_agree_box o R heq⟩

end
end FiniteAvalanches.Sandpile
