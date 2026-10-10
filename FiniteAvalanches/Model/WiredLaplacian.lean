import FiniteAvalanches.Sandpile.WiredTermination

/-! The wired Laplacian retains all four direction copies, including sink exits. -/

namespace FiniteAvalanches.Sandpile.FiniteWired

open LatticeProb LatticeProb.Sandpile
open scoped Classical

noncomputable section

/-- The actual edge copy traversed in a direction from an active vertex. -/
def directionEdge {R : ℕ} (x : Active R) : Direction → Edge R
  | (i, true) =>
      if h : inBox R (site x + unit i) then
        .inl ⟨(x, activeOfSite R (site x + unit i) h), ⟨i, rfl⟩⟩
      else .inr ⟨(x, (i, true)), by simpa only [step, if_true] using h⟩
  | (i, false) =>
      if h : inBox R (site x - unit i) then
        .inl ⟨(activeOfSite R (site x - unit i) h, x), ⟨i, by
          change site x = site x - unit i + unit i
          abel⟩⟩
      else .inr ⟨(x, (i, false)), by simpa only [step, Bool.false_eq_true, if_false,
        ← sub_eq_add_neg] using h⟩

theorem direction_edge_exit {R : ℕ} (x : Active R) (d : Direction)
    (hd : ¬inBox R (site x + step d)) : directionEdge x d = .inr ⟨(x, d), hd⟩ := by
  rcases d with ⟨i, b⟩
  cases b <;> simp only [step, Bool.false_eq_true, if_false, if_true,
    ← sub_eq_add_neg] at hd ⊢ <;> simp [directionEdge, hd] <;> rfl

theorem direction_edge_exit_injective {R : ℕ} (x : Active R) {d e : Direction}
    (hd : ¬inBox R (site x + step d)) (he : ¬inBox R (site x + step e))
    (h : directionEdge x d = directionEdge x e) : d = e := by
  rw [direction_edge_exit x d hd, direction_edge_exit x e he] at h
  exact congrArg (fun z : ExitEdge R => z.val.2) (Sum.inr.inj h)

theorem conductance_direction_edge {R : ℕ} (x : Active R) (d : Direction) :
    conductance (directionEdge x d) = 1 := rfl

/-- Auxiliary zero extension of active toppling counts to the sink exterior. -/
def wiredCountExtension (R : ℕ) (u : Active R → ℤ) (x : Site2) : ℤ :=
  if hx : inBox R x then u (activeOfSite R x hx) else 0

theorem wired_count_extension_site (R : ℕ) (u : Active R → ℤ) (x : Active R) :
    wiredCountExtension R u (site x) = u x := by
  have hx : inBox R (site x) := fun i => (x i).property
  simp only [wiredCountExtension, dif_pos hx]
  congr 1

/-- Each direction contributes once; exterior directions are separate sink edge copies. -/
def wiredLap (R : ℕ) (u : Active R → ℤ) (x : Active R) : ℤ :=
  ∑ d : Direction, (wiredCountExtension R u (site x + step d) - u x)

theorem wired_lap_eq_lap (R : ℕ) (u : Active R → ℤ) (x : Active R) :
    wiredLap R u x = lap (wiredCountExtension R u) (site x) := by
  simp only [wiredLap, Direction, Fintype.sum_prod_type, Fintype.sum_bool, step,
    Bool.false_eq_true, if_false, if_true, ← sub_eq_add_neg,
    lap, nbrSumZ, Fin.sum_univ_two, wired_count_extension_site]
  ring

theorem wired_count_extension_counts {R : ℕ} (u : Counts)
    (hu : u.support ⊆ boxSites R) :
    wiredCountExtension R (fun x => (u (site x) : ℤ)) = fun x => (u x : ℤ) := by
  funext x
  unfold wiredCountExtension
  split
  · rfl
  · rename_i hx
    have hz : u x = 0 := Finsupp.notMem_support_iff.mp
      (fun h => hx ((mem_box_sites R x).mp (hu h)))
    simp [hz]

theorem wired_lap_counts {R : ℕ} (u : Counts) (hu : u.support ⊆ boxSites R)
    (x : Active R) :
    wiredLap R (fun y => (u (site y) : ℤ)) x = lap (fun y => (u y : ℤ)) (site x) := by
  rw [wired_lap_eq_lap, wired_count_extension_counts u hu]


end
end FiniteAvalanches.Sandpile.FiniteWired
