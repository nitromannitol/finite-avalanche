import FiniteAvalanches.Needle.Proof

open FiniteAvalanches.Sandpile.FiniteWired

namespace FiniteAvalanches.Needle
open LatticeProb
open scoped BigOperators Classical

/-- Lattice steps that stay inside `Z`.  -/
abbrev stepIn (Z : Finset Point) (a b : Point) : Prop :=
  a ∈ Z ∧ b ∈ Z ∧ (lattice 2).Adj a b

/-- any two sites of `Z` are joined by steps inside `Z`. -/
def LatticeConnectedSet (Z : Finset Point) : Prop :=
  ∀ x ∈ Z, ∀ y ∈ Z, Relation.ReflTransGen (stepIn Z) x y

theorem reflTransGen_reverse {α : Type*} {r : α → α → Prop} (hr : ∀ ⦃a b⦄, r a b → r b a) {a b : α}
    (hab : Relation.ReflTransGen r a b) : Relation.ReflTransGen r b a := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | @tail d e _ hde ih => exact Relation.ReflTransGen.head (hr hde) ih

/-- One lattice step toward the origin in a nonzero coordinate `i`. -/
theorem exists_axis_step (x : Point) (i : Fin 2) (hi : x i ≠ 0) :
    ∃ y : Point, (lattice 2).Adj x y ∧ |y i| + 1 = |x i| ∧ ∀ j, j ≠ i → y j = x j := by
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · refine ⟨x + unit i, ⟨i, Or.inl rfl⟩, ?_, fun j hj => ?_⟩
    · simp [unit, abs_eq_max_neg]
      omega
    · simp [unit, hj]
  · refine ⟨x - unit i, ⟨i, Or.inr (sub_add_cancel x (unit i)).symm⟩, ?_, fun j hj => ?_⟩
    · simp [unit, abs_eq_max_neg]
      omega
    · simp [unit, hj]

theorem radius_le_of_step (h : ℕ) (x y : Point) (i : Fin 2) (hr : radius x ≤ h)
    (hyi : |y i| + 1 = |x i|) (hyj : ∀ j, j ≠ i → y j = x j) : radius y ≤ h := by
  have hx := (radius_le_iff x h).mp hr
  refine (radius_le_iff y h).mpr fun j => ?_
  by_cases hj : j = i
  · rw [hj]
    have := hx i
    omega
  · rw [hyj j hj]
    exact hx j

/-- Every site of a set `Z` containing the ℓ∞ ball `B_h` reaches the origin by steps inside `Z`. -/
theorem box_reaches_zero (h : ℕ) (Z : Finset Point) (hB : ∀ x : Point, radius x ≤ h → x ∈ Z) :
    ∀ x : Point, radius x ≤ h → Relation.ReflTransGen (stepIn Z) x 0 := by
  have key : ∀ n : ℕ, ∀ x : Point, radius x ≤ h → |x 0| + |x 1| ≤ n →
      Relation.ReflTransGen (stepIn Z) x 0 := by
    intro n
    induction n with
    | zero =>
      intro x _ hn
      have hn' : |x 0| + |x 1| ≤ 0 := by exact_mod_cast hn
      have hx0 : x 0 = 0 :=
        abs_eq_zero.mp (le_antisymm (by linarith [abs_nonneg (x 1)]) (abs_nonneg _))
      have hx1 : x 1 = 0 :=
        abs_eq_zero.mp (le_antisymm (by linarith [abs_nonneg (x 0)]) (abs_nonneg _))
      have hx : x = 0 := funext fun j => by fin_cases j <;> simp [hx0, hx1]
      subst hx
      exact Relation.ReflTransGen.refl
    | succ n ih =>
      intro x hr hn
      by_cases hx : x = 0
      · subst hx
        exact Relation.ReflTransGen.refl
      have hn' : |x 0| + |x 1| ≤ (n : ℤ) + 1 := by exact_mod_cast hn
      by_cases hx0 : x 0 = 0
      · have hx1 : x 1 ≠ 0 := fun h1 => hx (funext fun j => by fin_cases j <;> simp [hx0, h1])
        obtain ⟨y, hadj, hyi, hyj⟩ := exists_axis_step x 1 hx1
        have hy0 : y 0 = 0 := (hyj 0 (by decide)).trans hx0
        have hyr : radius y ≤ h := radius_le_of_step h x y 1 hr hyi hyj
        refine Relation.ReflTransGen.head ⟨hB x hr, hB y hyr, hadj⟩ (ih y hyr ?_)
        have e0 : |y 0| = 0 := by rw [hy0, abs_zero]
        have e1 : |x 0| = 0 := by rw [hx0, abs_zero]
        omega
      · obtain ⟨y, hadj, hyi, hyj⟩ := exists_axis_step x 0 hx0
        have hy1 : y 1 = x 1 := hyj 1 (by decide)
        have hyr : radius y ≤ h := radius_le_of_step h x y 0 hr hyi hyj
        refine Relation.ReflTransGen.head ⟨hB x hr, hB y hyr, hadj⟩ (ih y hyr ?_)
        rw [hy1]
        omega
  intro x hx
  have hnn : (0 : ℤ) ≤ |x 0| + |x 1| := by positivity
  exact key (|x 0| + |x 1|).toNat x hx (le_of_eq (Int.toNat_of_nonneg hnn).symm)

/-- The central square together with an injective lattice path is lattice-connected. -/
theorem target_connected (h L : ℕ) (p : Fin (L+1) → Point)
    (hstart : p ⟨0, by omega⟩ ∈ box 2 h)
    (hstep : ∀ t : Fin L, (lattice 2).Adj (p ⟨t.val, by omega⟩) (p ⟨t.val+1, by omega⟩)) :
    LatticeConnectedSet (target h L p) := by
  have hB : ∀ x : Point, radius x ≤ h → x ∈ target h L p := fun x hx =>
    Finset.mem_union_left _ ((mem_boxPoints h x).mpr ((mem_box_iff x h).mpr hx))
  have hP : ∀ t : Fin (L+1), p t ∈ target h L p := fun t =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem p (Finset.mem_univ t))
  have hbox := box_reaches_zero h (target h L p) hB
  have hp0 : radius (p ⟨0, by omega⟩) ≤ h := (mem_box_iff _ h).mp hstart
  have hpath : ∀ t : ℕ, ∀ ht : t < L + 1,
      Relation.ReflTransGen (stepIn (target h L p)) (p ⟨t, ht⟩) (p ⟨0, by omega⟩) := by
    intro t
    induction t with
    | zero => intro ht; exact Relation.ReflTransGen.refl
    | succ t ih =>
      intro ht
      exact Relation.ReflTransGen.head ⟨hP _, hP _, (hstep ⟨t, by omega⟩).symm⟩ (ih (by omega))
  have hsymm : ∀ ⦃a b⦄, stepIn (target h L p) a b → stepIn (target h L p) b a := fun {a b} hab =>
    ⟨hab.2.1, hab.1, hab.2.2.symm⟩
  have key : ∀ x ∈ target h L p, Relation.ReflTransGen (stepIn (target h L p)) x 0 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hb | hpx
    · exact hbox x ((mem_box_iff x h).mp ((mem_boxPoints h x).mp hb))
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hpx
      exact (hpath t.val t.isLt).trans (hbox _ hp0)
  intro x hx y hy
  exact (key x hx).trans (reflTransGen_reverse hsymm (key y hy))

/-- Set form of `ct:needle`: Z = B_h ∪ path, with the existing conductance bound rescaled. -/
theorem ct_needle_connected : ∃ C : ℝ, 0 < C ∧ ∀ h : ℕ, 10 ≤ h → ∀ z : Point,
    radius z = 2*h → ∃ Z : Finset Point,
      LatticeConnectedSet Z ∧ (∀ x ∈ Z, x ∈ box 2 (2*h)) ∧ (∀ x ∈ box 2 h, x ∈ Z) ∧ z ∈ Z ∧
      wiredConductance (2*h) (Finset.univ.filter (fun x : Active (2*h) => site x ∈ Z)) ≤
        C * Real.log h := by
  refine ⟨7680, by norm_num, ?_⟩
  intro h hh z hz
  obtain ⟨L, p, _, hb, he, ha, _, hc⟩ := needle h hh z hz
  have hh' : (10:ℝ) ≤ h := by exact_mod_cast hh
  have hlog : Real.log ((h:ℝ)+2) ≤ 2 * Real.log h := by
    have h1 : Real.log ((h:ℝ)+2) ≤ Real.log ((h:ℝ)^2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have h2 : Real.log ((h:ℝ)^2) = 2 * Real.log h := by
      rw [Real.log_pow]; norm_num
    linarith
  refine ⟨target h L p.val, target_connected h L p.val hb ha, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hb' | hpx
    · have hr := (mem_box_iff x h).mp ((mem_boxPoints h x).mp hb')
      exact (mem_box_iff x (2*h)).mpr (by omega)
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hpx
      exact p.property t
  · exact fun x hx => Finset.mem_union_left _ ((mem_boxPoints h x).mpr hx)
  · rw [← he]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  · refine hc.trans ?_
    linarith [hlog]

end FiniteAvalanches.Needle
