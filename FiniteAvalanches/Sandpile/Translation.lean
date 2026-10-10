import FiniteAvalanches.Sandpile.WiredTermination
import FiniteAvalanches.Sandpile.ExtendedObservables

/-! Translation of legal lists and a uniform source-centered toppling bound. -/
namespace FiniteAvalanches.Sandpile
open LatticeProb LatticeProb.Sandpile FiniteAvalanches
open scoped Classical
noncomputable section

theorem lap_translate (u : Site2 → ℤ) (z x : Site2) :
    lap (fun y => u (y+z)) x = lap u (x+z) := by
  simp only [lap,nbrSumZ]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1 <;> congr 1 <;> abel

theorem listCounts_map_sub (w : List Site2) (z x : Site2) :
    listCounts (w.map (fun y => y-z)) x = listCounts w (x+z) := by
  simp only [listCounts_apply]
  have h := List.count_map_of_injective w (fun y : Site2 => y-z)
    (by intro a b h; have h' := congrArg (fun t : Site2 => t+z) h; simpa using h') (x+z)
  simpa only [add_sub_cancel_right] using h

theorem prefixCounts_map_sub (w : List Site2) (z : Site2) (k : ℕ) :
    prefixCounts (w.map (fun y => y-z)) k = fun x => prefixCounts w k (x+z) := by
  funext x
  have h := listCounts_map_sub (w.take k) z x
  simp only [prefixCounts]
  simp only [listCounts_apply,List.map_take] at h
  exact_mod_cast h

theorem LegalList.map_sub {s : Site2 → ℤ} {w : List Site2}
    (hw : LegalList s w) (z : Site2) :
    LegalList (fun x => s (x+z)) (w.map (fun y => y-z)) := by
  intro k hk
  have hk' : k < w.length := by simpa only [List.length_map] using hk
  simp only [List.getElem_map]
  rw [prefixCounts_map_sub,lap_translate,sub_add_cancel]
  exact hw k hk'

/-- The same bound holds for every translated box and every addition source. -/
theorem one_grain_legal_list_centered_box_bound (η : StableField) (o : Site2) (R : ℕ)
    {w : List Site2} (hw : LegalList (initial η (oneGrain o)) w)
    (hwR : ∀ x ∈ w, siteRadius o x ≤ R) :
    (∀ x, listCounts w x ≤ 2*(R+1)^2) ∧ w.length ≤ 8*(R+1)^4 := by
  have hi : (fun x => initial η (oneGrain o) (x+o)) =
      initial (translate o η) (oneGrain 0) := by
    funext x
    simp [initial_oneGrain,translate,dirac]
  have ht := hw.map_sub o
  rw [hi] at ht
  have hb : ∀ y ∈ w.map (fun x => x-o), y ∈ boxSites R := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    rw [mem_box_sites]
    intro i
    simpa only [Pi.sub_apply,abs_le] using (siteRadius_le_iff o x R).mp (hwR x hx) i
  obtain ⟨hc,hl⟩ := one_grain_legal_list_box_bound (translate o η) 0 R ht hb
  refine ⟨?_,?_⟩
  · intro x
    have h := hc (x-o)
    simpa only [listCounts_map_sub,sub_add_cancel] using h
  · simpa only [List.length_map] using hl

/-- Confinement alone bounds the literal total number of topplings. -/
theorem totalTopplings_le_of_radius_le (η : StableField) (o : Site2) (R : ℕ)
    (hr : radius η o ≤ (R : WithTop ℕ)) :
    totalTopplings η o ≤ ((8*(R+1)^4 : ℕ) : WithTop ℕ) := by
  have hf : FiniteStabilizable η o := by
    by_contra hn
    rw [(radius_eq_top_iff η o).mpr hn] at hr
    simp at hr
  obtain ⟨w,hw⟩ := hf
  have hrad : countsRadius o (listCounts w) ≤ R := by
    rw [radius_of_stabilizes hw] at hr
    exact WithTop.coe_le_coe.mp hr
  have hmem : ∀ x ∈ w, siteRadius o x ≤ R := by
    intro x hx
    apply (countsRadius_le_iff o (listCounts w) R).mp hrad
    rw [listCounts_apply]
    exact List.count_pos_iff.mpr hx
  rw [totalTopplings_of_stabilizes hw]
  exact WithTop.coe_le_coe.mpr (one_grain_legal_list_centered_box_bound η o R hw.1 hmem).2

end
end FiniteAvalanches.Sandpile
