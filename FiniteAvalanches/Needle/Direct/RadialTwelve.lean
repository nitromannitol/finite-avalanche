import FiniteAvalanches.Needle.Sharp.SquareEnergy
import Mathlib.Tactic

/-! The literal incoming radial cutoff, with original copied radial edges.
Source: cd552a5075922522da04d2284b5bff12ee16cbd5, main.tex line 436. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FiniteAvalanches.Needle.CurrentRadial

open LatticeProb FiniteAvalanches.Sandpile.FiniteWired
open scoped BigOperators Classical

/-- The author's radial trial on the actual wired vertex carrier. -/
noncomputable def radialTrial (ell : ℕ) : Vertex (2 * ell - 1) → ℝ
  | none => 0
  | some x => min 1 (max 0 (2 - (radius (site x) : ℝ) / (ell : ℝ)))

/-- Literal characterization by the complementary, affine annular tent. -/
theorem cutoff_eq_one_sub_tent (ell : ℕ) (hell : 1 ≤ ell) (R : ℤ) :
    min 1 (max 0 (2 - (R : ℝ) / ell)) = 1 - Needle107Square.tent ell R := by
  have hp : (0 : ℝ) < ell := by exact_mod_cast (by omega : 0 < ell)
  by_cases hsmall : R ≤ ell
  · rw [Needle107Square.tent_zero ell R hsmall]
    have hR : (R : ℝ) ≤ ell := by exact_mod_cast hsmall
    have hdiv : (R : ℝ) / ell ≤ 1 := (div_le_iff₀ hp).mpr (by simpa using hR)
    rw [min_eq_left (by
      exact (by linarith only [hdiv] : (1 : ℝ) ≤ 2 - (R : ℝ) / ell).trans
        (le_max_right _ _))]
    ring
  · by_cases hlarge : 2 * (ell : ℤ) ≤ R
    · rw [Needle107Square.tent_one ell hell R hlarge]
      have hR : 2 * (ell : ℝ) ≤ R := by exact_mod_cast hlarge
      have hdiv : (2 : ℝ) ≤ (R : ℝ) / ell :=
        (le_div_iff₀ hp).mpr (by simpa using hR)
      rw [max_eq_left (by linarith only [hdiv])]
      norm_num
    · have hRlo : (ell : ℝ) ≤ R := by exact_mod_cast (by omega : (ell : ℤ) ≤ R)
      have hRhi : (R : ℝ) ≤ 2 * ell := by exact_mod_cast (by omega : R ≤ 2 * (ell : ℤ))
      have hdivlo : (1 : ℝ) ≤ (R : ℝ) / ell :=
        (le_div_iff₀ hp).mpr (by simpa using hRlo)
      have hdivhi : (R : ℝ) / ell ≤ 2 :=
        (div_le_iff₀ hp).mpr (by simpa using hRhi)
      rw [max_eq_right (by linarith only [hdivhi]), min_eq_right (by linarith only [hdivlo])]
      rw [Needle107Square.tent, max_eq_right (sub_nonneg.mpr hRlo), min_eq_right]
      · field_simp
        ring
      · apply (div_le_iff₀ hp).mpr
        linarith only [hRhi]

theorem radial_trial_eq_one_sub_wire (ell : ℕ) (hell : 1 ≤ ell) :
    radialTrial ell = fun v => 1 - Needle107SquareEnergy.wire (2 * ell - 1) ell 0 v := by
  funext v
  cases v with
  | none => norm_num [radialTrial, Needle107SquareEnergy.wire]
  | some x =>
    simpa only [radialTrial, Needle107SquareEnergy.wire, sub_zero] using
      cutoff_eq_one_sub_tent ell hell (radius (site x))

/-- A shell copy is indexed by its outward side and tangential coordinate.
Negative sides use the positive-coordinate base outside the inner shell. -/
noncomputable def shellKey (j : ℕ) (p : Direction × ℤ) : Point × Fin 2 :=
  let a : ℤ := if p.1.2 then j else -(j : ℤ) - 1
  (if p.1.1 = 0 then ![a, p.2] else ![p.2, a], p.1.1)

theorem shell_key_injective (j : ℕ) : Function.Injective (shellKey j) := by
  rintro ⟨⟨i, b⟩, t⟩ ⟨⟨k, c⟩, v⟩ h
  have haxis := congrArg Prod.snd h
  change i = k at haxis
  subst k
  have hpoint := congrArg Prod.fst h
  have h0 := congrFun hpoint 0
  have h1 := congrFun hpoint 1
  fin_cases i <;> cases b <;> cases c
  all_goals simp [shellKey] at h0 h1
  all_goals first | exact Prod.ext rfl h0 | exact Prod.ext rfl h1 | omega

/-- Four sides, each with `2*j+1` outward original copies. -/
noncomputable def shellKeys (j : ℕ) : Finset (Point × Fin 2) :=
  (Finset.univ ×ˢ Finset.Icc (-(j : ℤ)) (j : ℤ)).image (shellKey j)

theorem shell_keys_card (j : ℕ) : (shellKeys j).card = 8 * j + 4 := by
  have hc : (Finset.Icc (-(j : ℤ)) (j : ℤ)).card = 2 * j + 1 := by
    rw [Int.card_Icc]
    omega
  rw [shellKeys, Finset.card_image_of_injective _ (shell_key_injective j),
    Finset.card_product, Finset.card_univ, hc]
  norm_num [Fintype.card_prod]
  ring

theorem shell_key_radii (j : ℕ) (d : Direction) (t : ℤ)
    (ht : t ∈ Finset.Icc (-(j : ℤ)) (j : ℤ)) :
    if d.2 then
      radius (shellKey j (d, t)).1 = j ∧
        radius ((shellKey j (d, t)).1 + unit (shellKey j (d, t)).2) = (j : ℤ) + 1
    else
      radius (shellKey j (d, t)).1 = (j : ℤ) + 1 ∧
        radius ((shellKey j (d, t)).1 + unit (shellKey j (d, t)).2) = j := by
  have ht' := Finset.mem_Icc.mp ht
  rcases d with ⟨i, b⟩
  fin_cases i <;> cases b <;> simp [shellKey, radius, unit, abs_eq_max_neg]
  all_goals omega

theorem shell_key_min_radius (j : ℕ) (d : Direction) (t : ℤ)
    (ht : t ∈ Finset.Icc (-(j : ℤ)) (j : ℤ)) :
    min (radius (shellKey j (d, t)).1)
      (radius ((shellKey j (d, t)).1 + unit (shellKey j (d, t)).2)) = j := by
  have h := shell_key_radii j d t ht
  cases hb : d.2
  · rw [hb] at h
    rw [h.1, h.2]
    omega
  · rw [hb] at h
    rw [h.1, h.2]
    omega

theorem shell_keys_disjoint {j k : ℕ} (hjk : j ≠ k) : Disjoint (shellKeys j) (shellKeys k) := by
  apply Finset.disjoint_left.mpr
  intro p hpj hpk
  obtain ⟨⟨d, t⟩, hdt, he⟩ := Finset.mem_image.mp hpj
  obtain ⟨⟨f, v⟩, hfv, hf⟩ := Finset.mem_image.mp hpk
  have hj := shell_key_min_radius j d t (Finset.mem_product.mp hdt).2
  have hk := shell_key_min_radius k f v (Finset.mem_product.mp hfv).2
  rw [he] at hj
  rw [hf] at hk
  exact hjk (by omega)

/-- All radial-changing physical keys, at the exact consecutive shell indices. -/
noncomputable def annulusKeys (ell : ℕ) : Finset (Point × Fin 2) :=
  (Finset.Ico ell (2 * ell)).biUnion shellKeys

theorem shell_count_sum (a n : ℕ) :
    (∑ j ∈ Finset.Ico a (a + n), (8 * j + 4)) = 8 * a * n + 4 * n ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.add_succ, Finset.sum_Ico_succ_top (by omega : a ≤ a + n), ih]
    ring

theorem annulus_keys_card (ell : ℕ) : (annulusKeys ell).card = 12 * ell ^ 2 := by
  rw [annulusKeys, Finset.card_biUnion]
  · simp_rw [shell_keys_card]
    rw [show 2 * ell = ell + ell by omega, shell_count_sum]
    ring
  · intro j _ k _ hjk
    exact shell_keys_disjoint hjk

private theorem unit_injective_two : Function.Injective (unit (d := 2)) := by
  intro i j h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  fin_cases i <;> fin_cases j <;> simp [unit] at h0 h1
  all_goals rfl

/-- Every geometric positive-coordinate key with an endpoint in the box is
represented by one original interior or exit copy. -/
theorem exists_edge_of_key (N : ℕ) (p : Point) (i : Fin 2)
    (hin : inBox N p ∨ inBox N (p + unit i)) :
    ∃ e : Edge N, Needle107Edges.key N e = (p, i) := by
  by_cases hp : inBox N p
  · by_cases htop : inBox N (p + unit i)
    · let x := activeOfSite N p hp
      let y := activeOfSite N (p + unit i) htop
      let f : InteriorEdge N := ⟨(x, y), i, rfl⟩
      have hi : f.property.choose = i := by
        have h : p + unit i = p + unit f.property.choose := f.property.choose_spec
        exact unit_injective_two ((add_left_cancel h).symm)
      refine ⟨Sum.inl f, ?_⟩
      change (p, f.property.choose) = (p, i)
      rw [hi]
    · let f : ExitEdge N := ⟨(activeOfSite N p hp, (i, true)), htop⟩
      exact ⟨Sum.inr f, rfl⟩
  · have htop := hin.resolve_left hp
    let x := activeOfSite N (p + unit i) htop
    have he : ¬inBox N (site x + step (i, false)) := by
      change ¬inBox N (p + unit i + -unit i)
      simpa only [add_neg_cancel_right] using hp
    let f : ExitEdge N := ⟨(x, (i, false)), he⟩
    refine ⟨Sum.inr f, ?_⟩
    change (p + unit i - unit i, i) = (p, i)
    rw [add_sub_cancel_right]

theorem shell_key_has_active_endpoint (N j : ℕ) (hj : j ≤ N) (d : Direction) (t : ℤ)
    (ht : t ∈ Finset.Icc (-(j : ℤ)) (j : ℤ)) :
    inBox N (shellKey j (d, t)).1 ∨
      inBox N ((shellKey j (d, t)).1 + unit (shellKey j (d, t)).2) := by
  have hmin : min (radius (shellKey j (d, t)).1)
      (radius ((shellKey j (d, t)).1 + unit (shellKey j (d, t)).2)) ≤ N := by
    rw [shell_key_min_radius j d t ht]
    exact_mod_cast hj
  rcases min_le_iff.mp hmin with hbase | htop
  · exact Or.inl ((inBox_iff N _).mpr ((mem_box_iff _ N).mpr hbase))
  · exact Or.inr ((inBox_iff N _).mpr ((mem_box_iff _ N).mpr htop))

theorem shell_key_represented (N j : ℕ) (hj : j ≤ N) (p : Point × Fin 2)
    (hp : p ∈ shellKeys j) : p ∈ Finset.univ.image (Needle107Edges.key N) := by
  obtain ⟨⟨d, t⟩, hdt, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨e, he⟩ := exists_edge_of_key N (shellKey j (d, t)).1 (shellKey j (d, t)).2
    (shell_key_has_active_endpoint N j hj d t (Finset.mem_product.mp hdt).2)
  exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, he⟩

/-- Exactly `8*j+4` original copies cross shell `j`, including wired exits. -/
theorem wired_shell_copies_card (N j : ℕ) (hj : j ≤ N) :
    (Finset.univ.filter (fun e : Edge N => Needle107Edges.key N e ∈ shellKeys j)).card =
      8 * j + 4 := by
  have himage : (Finset.univ.filter
      (fun e : Edge N => Needle107Edges.key N e ∈ shellKeys j)).image (Needle107Edges.key N) =
      shellKeys j := by
    ext p
    constructor
    · intro hp
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hp
      exact (Finset.mem_filter.mp he).2
    · intro hp
      obtain ⟨e, _, he⟩ := Finset.mem_image.mp (shell_key_represented N j hj p hp)
      exact Finset.mem_image.mpr ⟨e,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [he] using hp⟩, he⟩
  have hcard := congrArg Finset.card himage
  rw [Finset.card_image_of_injective _ (Needle107Edges.key_injective N)] at hcard
  exact hcard.trans (shell_keys_card j)

theorem tent_on_band (ell : ℕ) (hell : 1 ≤ ell) (R : ℤ)
    (hlo : (ell : ℤ) ≤ R) (hhi : R ≤ 2 * (ell : ℤ)) :
    Needle107Square.tent ell R = ((R : ℝ) - ell) / ell := by
  have hp : (0 : ℝ) < ell := by exact_mod_cast (by omega : 0 < ell)
  have hRlo : (ell : ℝ) ≤ R := by exact_mod_cast hlo
  have hRhi : (R : ℝ) ≤ 2 * ell := by exact_mod_cast hhi
  rw [Needle107Square.tent, max_eq_right (sub_nonneg.mpr hRlo), min_eq_right]
  apply (div_le_iff₀ hp).mpr
  linarith only [hRhi]

theorem tent_step_square (ell j : ℕ) (hell : 1 ≤ ell) (hlo : ell ≤ j) (hhi : j < 2 * ell) :
    (Needle107Square.tent ell (j : ℤ) - Needle107Square.tent ell ((j : ℤ) + 1)) ^ 2 =
      (1 / (ell : ℝ)) ^ 2 := by
  rw [tent_on_band ell hell (j : ℤ) (by omega) (by omega),
    tent_on_band ell hell ((j : ℤ) + 1) (by omega) (by omega)]
  push_cast
  ring

theorem changed_coordinates_shell (ell : ℕ) (hell : 1 ≤ ell) (a b : ℤ)
    (hne : Needle107Square.tent ell (max |a| |b|) ≠
      Needle107Square.tent ell (max |a + 1| |b|)) :
    ∃ j ∈ Finset.Ico ell (2 * ell), ∃ c : Bool,
      a = (if c then (j : ℤ) else -(j : ℤ) - 1) ∧
        b ∈ Finset.Icc (-(j : ℤ)) (j : ℤ) := by
  have hband := (Needle107Square.tent_changed_band ell hell a b hne).1
  rw [Needle107Square.band] at hband
  rcases Finset.mem_union.mp hband with hpos | hneg
  · have hbounds := Finset.mem_Icc.mp hpos
    have hb : |b| ≤ a := by
      by_contra hbad
      have ha0 : 0 ≤ a := by omega
      have ha1 : 0 ≤ a + 1 := by omega
      have hb0 : a ≤ |b| := by omega
      have hb1 : a + 1 ≤ |b| := by omega
      exact hne (by rw [abs_of_nonneg ha0, abs_of_nonneg ha1,
        max_eq_right hb0, max_eq_right hb1])
    have hcast : (a.toNat : ℤ) = a := Int.toNat_of_nonneg (by omega)
    refine ⟨a.toNat, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, true, ?_, ?_⟩
    · change a = (a.toNat : ℤ)
      exact hcast.symm
    · rw [Finset.mem_Icc, hcast]
      exact abs_le.mp hb
  · have hbounds := Finset.mem_Icc.mp hneg
    have hb : |b| ≤ -a - 1 := by
      by_contra hbad
      have ha0 : a ≤ 0 := by omega
      have ha1 : a + 1 ≤ 0 := by omega
      have hb0 : -a ≤ |b| := by omega
      have hb1 : -(a + 1) ≤ |b| := by omega
      exact hne (by rw [abs_of_nonpos ha0, abs_of_nonpos ha1,
        max_eq_right hb0, max_eq_right hb1])
    have hcast : ((-a - 1).toNat : ℤ) = -a - 1 := Int.toNat_of_nonneg (by omega)
    refine ⟨(-a - 1).toNat, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, false, ?_, ?_⟩
    · change a = -((-a - 1).toNat : ℤ) - 1
      rw [hcast]
      ring
    · rw [Finset.mem_Icc, hcast]
      exact abs_le.mp hb

theorem changed_key_mem_annulus (ell : ℕ) (hell : 1 ≤ ell) (x : Point) (i : Fin 2)
    (hne : Needle107Square.tent ell (radius x) ≠
      Needle107Square.tent ell (radius (x + unit i))) :
    (x, i) ∈ annulusKeys ell := by
  have hx : ![x 0, x 1] = x := by funext k; fin_cases k <;> rfl
  fin_cases i
  · have h0 : (x + unit (0 : Fin 2)) 0 = x 0 + 1 := by simp [unit]
    have h1 : (x + unit (0 : Fin 2)) 1 = x 1 := by simp [unit]
    change Needle107Square.tent ell (max |x 0| |x 1|) ≠
      Needle107Square.tent ell (max |(x + unit (0 : Fin 2)) 0| |(x + unit (0 : Fin 2)) 1|) at hne
    rw [h0, h1] at hne
    obtain ⟨j, hj, c, ha, ht⟩ := changed_coordinates_shell ell hell (x 0) (x 1) hne
    apply Finset.mem_biUnion.mpr
    refine ⟨j, hj, Finset.mem_image.mpr ⟨((0, c), x 1),
      Finset.mem_product.mpr ⟨Finset.mem_univ _, ht⟩, ?_⟩⟩
    apply Prod.ext
    · change ![if c then (j : ℤ) else -(j : ℤ) - 1, x 1] = x
      rw [← ha]
      exact hx
    · rfl
  · have h0 : (x + unit (1 : Fin 2)) 0 = x 0 := by simp [unit]
    have h1 : (x + unit (1 : Fin 2)) 1 = x 1 + 1 := by simp [unit]
    change Needle107Square.tent ell (max |x 0| |x 1|) ≠
      Needle107Square.tent ell (max |(x + unit (1 : Fin 2)) 0| |(x + unit (1 : Fin 2)) 1|) at hne
    rw [h0, h1] at hne
    obtain ⟨j, hj, c, ha, ht⟩ := changed_coordinates_shell ell hell (x 1) (x 0)
      (by simpa only [max_comm] using hne)
    apply Finset.mem_biUnion.mpr
    refine ⟨j, hj, Finset.mem_image.mpr ⟨((1, c), x 0),
      Finset.mem_product.mpr ⟨Finset.mem_univ _, ht⟩, ?_⟩⟩
    apply Prod.ext
    · change ![x 0, if c then (j : ℤ) else -(j : ℤ) - 1] = x
      rw [← ha]
      exact hx
    · rfl

/-- Squared drop at the two physical lattice endpoints of a geometric copy. -/
noncomputable def radialEdgeEnergy (ell : ℕ) (p : Point × Fin 2) : ℝ :=
  (Needle107Square.tent ell (radius p.1) -
    Needle107Square.tent ell (radius (p.1 + unit p.2))) ^ 2

theorem radial_edge_energy_of_shell (ell j : ℕ) (hell : 1 ≤ ell)
    (hlo : ell ≤ j) (hhi : j < 2 * ell) (p : Point × Fin 2) (hp : p ∈ shellKeys j) :
    radialEdgeEnergy ell p = (1 / (ell : ℝ)) ^ 2 := by
  obtain ⟨⟨d, t⟩, hdt, rfl⟩ := Finset.mem_image.mp hp
  have hrad := shell_key_radii j d t (Finset.mem_product.mp hdt).2
  unfold radialEdgeEnergy
  cases hd : d.2
  · rw [hd] at hrad
    rw [hrad.1, hrad.2, sub_sq_comm]
    exact tent_step_square ell j hell hlo hhi
  · rw [hd] at hrad
    rw [hrad.1, hrad.2]
    exact tent_step_square ell j hell hlo hhi

theorem radial_edge_energy_eq_zero (ell : ℕ) (hell : 1 ≤ ell) (p : Point × Fin 2)
    (hp : p ∉ annulusKeys ell) : radialEdgeEnergy ell p = 0 := by
  have he : Needle107Square.tent ell (radius p.1) =
      Needle107Square.tent ell (radius (p.1 + unit p.2)) := by
    by_contra hne
    exact hp (changed_key_mem_annulus ell hell p.1 p.2 hne)
  simp only [radialEdgeEnergy, he, sub_self, zero_pow (by decide : 2 ≠ 0)]

theorem edge_radial_energy_key (ell : ℕ) (hell : 1 ≤ ell)
    (e : Edge (2 * ell - 1)) :
    (radialTrial ell (endpoints e).1 - radialTrial ell (endpoints e).2) ^ 2 =
      radialEdgeEnergy ell (Needle107Edges.key (2 * ell - 1) e) := by
  have hc : radius (0 : Point) + 2 * ell - 1 ≤ (2 * ell - 1 : ℕ) := by
    norm_num [radius]
    omega
  have he := Needle107SquareEnergy.edge_wire_square (2 * ell - 1) ell hell 0 hc e
  simp only [sub_zero] at he
  rw [radial_trial_eq_one_sub_wire ell hell]
  calc
    ((1 - Needle107SquareEnergy.wire (2 * ell - 1) ell 0 (endpoints e).1) -
        (1 - Needle107SquareEnergy.wire (2 * ell - 1) ell 0 (endpoints e).2)) ^ 2 =
      (Needle107SquareEnergy.wire (2 * ell - 1) ell 0 (endpoints e).1 -
        Needle107SquareEnergy.wire (2 * ell - 1) ell 0 (endpoints e).2) ^ 2 := by ring
    _ = radialEdgeEnergy ell (Needle107Edges.key (2 * ell - 1) e) := he

/-- Exact energy of the literal incoming radial trial, once per original copy. -/
theorem radial_trial_energy_eq_twelve (ell : ℕ) (hell : 1 ≤ ell) :
    FiniteAvalanches.Electrical.energy
      (fun e : Edge (2 * ell - 1) => (endpoints e).1)
      (fun e => (endpoints e).2) (radialTrial ell) = 12 := by
  have hp : (0 : ℝ) < ell := by exact_mod_cast (by omega : 0 < ell)
  have hsubset : annulusKeys ell ⊆
      Finset.univ.image (Needle107Edges.key (2 * ell - 1)) := by
    intro p hp
    obtain ⟨j, hj, hps⟩ := Finset.mem_biUnion.mp hp
    have hbounds := Finset.mem_Ico.mp hj
    exact shell_key_represented (2 * ell - 1) j (by omega) p hps
  calc
    FiniteAvalanches.Electrical.energy
        (fun e : Edge (2 * ell - 1) => (endpoints e).1)
        (fun e => (endpoints e).2) (radialTrial ell) =
        ∑ e : Edge (2 * ell - 1), radialEdgeEnergy ell (Needle107Edges.key (2 * ell - 1) e) :=
      Finset.sum_congr rfl (fun e _ => edge_radial_energy_key ell hell e)
    _ = ∑ p ∈ Finset.univ.image (Needle107Edges.key (2 * ell - 1)), radialEdgeEnergy ell p :=
      (Finset.sum_image (fun _ _ _ _ he => Needle107Edges.key_injective (2 * ell - 1) he)).symm
    _ = ∑ p ∈ annulusKeys ell, radialEdgeEnergy ell p :=
      (Finset.sum_subset hsubset (fun p _ hnot => radial_edge_energy_eq_zero ell hell p hnot)).symm
    _ = ∑ _p ∈ annulusKeys ell, (1 / (ell : ℝ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p hp
      obtain ⟨j, hj, hps⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hj
      exact radial_edge_energy_of_shell ell j hell hlo hhi p hps
    _ = ((annulusKeys ell).card : ℝ) * (1 / (ell : ℝ)) ^ 2 := by simp
    _ = 12 := by
      rw [annulus_keys_card]
      push_cast
      field_simp

theorem radial_trial_eq_one (ell : ℕ) (hell : 1 ≤ ell) (x : Active (2 * ell - 1))
    (hx : site x ∈ box 2 ell) : radialTrial ell (some x) = 1 := by
  have hR := (mem_box_iff (site x) ell).mp hx
  rw [radial_trial_eq_one_sub_wire ell hell]
  change 1 - Needle107Square.tent ell (radius (site x - 0)) = 1
  rw [sub_zero, Needle107Square.tent_zero ell _ hR, sub_zero]

/-- Actual wired conductance of the central active square is at most twelve. -/
theorem radial_conductance_le_twelve (ell : ℕ) (hell : 1 ≤ ell) :
    wiredConductance (2 * ell - 1)
      (Finset.univ.filter (fun x : Active (2 * ell - 1) => site x ∈ box 2 ell)) ≤ 12 := by
  calc
    wiredConductance (2 * ell - 1)
        (Finset.univ.filter (fun x : Active (2 * ell - 1) => site x ∈ box 2 ell)) ≤
        FiniteAvalanches.Electrical.energy
          (fun e : Edge (2 * ell - 1) => (endpoints e).1)
          (fun e => (endpoints e).2) (fun v => 1 - radialTrial ell v) := by
      apply wiredConductance_le_trial
      · norm_num [radialTrial]
      · intro x hx
        rw [radial_trial_eq_one ell hell x (Finset.mem_filter.mp hx).2]
        ring
    _ = FiniteAvalanches.Electrical.energy
        (fun e : Edge (2 * ell - 1) => (endpoints e).1)
        (fun e => (endpoints e).2) (radialTrial ell) :=
      FiniteAvalanches.Electrical.energy_one_sub _ _ _
    _ = 12 := radial_trial_energy_eq_twelve ell hell

end FiniteAvalanches.Needle.CurrentRadial
