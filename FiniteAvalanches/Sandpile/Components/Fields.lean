import FiniteAvalanches.Sandpile.Components.Restriction

/-! Restricted heights have the literal induced degrees, including degree zero.
Restriction and reconstruction use every vertex in their declared carriers;
there is no exterior default and no choice. These are allowed fields, before
identification with Markov recurrence or a spanning-tree counting measure. -/
namespace FiniteAvalanches.Sandpile.Components
open LatticeProb LatticeProb.Sandpile FiniteAvalanches.Sandpile
open FiniteAvalanches.Sandpile.Waves
open scoped Classical
noncomputable section

/-- No forbidden subconfiguration on the actual finite vertex carrier. -/
def allowedOn (V : Finset Site2) (r : {x : Site2 // x ∈ V} → ℕ) : Prop :=
  ∀ (A : Finset Site2) (hA : A ⊆ V),
    ¬(A.Nonempty ∧ ∀ (x : Site2) (hx : x ∈ A), r ⟨x, hA hx⟩ < degree A x)

theorem allowed_iff_allowedOn {V : Finset Site2} {s : Site2 → ℤ}
    {r : {x : Site2 // x ∈ V} → ℕ}
    (he : ∀ (x : Site2) (hx : x ∈ V), s x = (r ⟨x, hx⟩ : ℤ)) :
    allowed V s ↔ allowedOn V r := by
  constructor
  · intro ha A hA hf
    apply ha A hA
    refine ⟨hf.1, ?_⟩
    intro x hx
    rw [he x (hA hx)]
    exact_mod_cast hf.2 x hx
  · intro ha A hA hf
    apply ha A hA
    refine ⟨hf.1, ?_⟩
    intro x hx
    have hh := hf.2 x hx
    rw [he x (hA hx)] at hh
    exact_mod_cast hh

abbrev InnerField {N : ℕ} (o : FiniteWired.Active N) (C : ComponentShape o) :=
  (x : {x : Site2 // x ∈ C.val.erase (FiniteWired.site o)}) → Fin (degree C.val x.val)
abbrev OuterField {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :=
  (x : {x : Site2 // x ∈ boxSites N \ C.val}) → Fin (4 - degree C.val x.val)
abbrev InnerAllowed {N : ℕ} (o : FiniteWired.Active N) (C : ComponentShape o) :=
  {r : InnerField o C // allowedOn (C.val.erase (FiniteWired.site o)) (fun x => (r x).val)}
abbrev OuterAllowed {N : ℕ} {o : FiniteWired.Active N} (C : ComponentShape o) :=
  {r : OuterField C // allowedOn (boxSites N \ C.val) (fun x => (r x).val)}
abbrev CoreField {N : ℕ} (o : FiniteWired.Active N) (C : Finset Site2) :=
  {h : Punctured N o // core h.val = C}


def offVertexOfSite {N : ℕ} {o : FiniteWired.Active N} {x : Site2}
    (hx : x ∈ boxSites N) (hxo : x ≠ FiniteWired.site o) : OffVertex N o :=
  ⟨FiniteWired.activeOfSite N x ((mem_box_sites N x).mp hx),
    fun he => hxo (congrArg FiniteWired.site he)⟩

theorem wired_height_off_vertex {N : ℕ} {o : FiniteWired.Active N}
    (h : OffField N o) (x : OffVertex N o) :
    wiredHeight (-1) h (FiniteWired.site x.val) = ((h x).val : ℤ) := by
  rw [wired_height_site, active_height_off]

/-- Reconstruct h on its whole off-source carrier by the two-phase formula. -/
def joinField {N : ℕ} {o : FiniteWired.Active N} {C : ComponentShape o}
    (rC : InnerField o C) (rD : OuterField C) : OffField N o := fun x =>
  if hx : FiniteWired.site x.val ∈ C.val then
    let y : {y : Site2 // y ∈ C.val.erase (FiniteWired.site o)} :=
      ⟨FiniteWired.site x.val, Finset.mem_erase.mpr
        ⟨fun he => x.property (FiniteWired.site_injective N he), hx⟩⟩
    ⟨(rC y).val, lt_of_lt_of_le (rC y).isLt (degree_le_four C.val y.val)⟩
  else
    let y : {y : Site2 // y ∈ boxSites N \ C.val} :=
      ⟨FiniteWired.site x.val, Finset.mem_sdiff.mpr ⟨site_mem_box x.val, hx⟩⟩
    ⟨(rD y).val + degree C.val y.val, by
      have hd := degree_le_four C.val y.val
      have hr := (rD y).isLt
      omega⟩

theorem join_field_height_inner {N : ℕ} {o : FiniteWired.Active N} {C : ComponentShape o}
     (rC : InnerField o C) (rD : OuterField C)
    (x : {x : Site2 // x ∈ C.val.erase (FiniteWired.site o)}) :
    wiredHeight (-1) (joinField rC rD) x.val = ((rC x).val : ℤ) := by
  let y := offVertexOfSite (C.property.1 (Finset.mem_erase.mp x.property).2)
    (Finset.mem_erase.mp x.property).1
  change wiredHeight (-1) (joinField rC rD) (FiniteWired.site y.val) = _
  rw [wired_height_off_vertex]
  have hy : FiniteWired.site y.val = x.val := rfl
  simp only [joinField, hy, dif_pos (Finset.mem_erase.mp x.property).2]
  rfl

theorem join_field_height_outer {N : ℕ} {o : FiniteWired.Active N} {C : ComponentShape o}
     (rC : InnerField o C) (rD : OuterField C)
    (x : {x : Site2 // x ∈ boxSites N \ C.val}) :
    wiredHeight (-1) (joinField rC rD) x.val =
      ((rD x).val : ℤ) + (degree C.val x.val : ℤ) := by
  have hxo : x.val ≠ FiniteWired.site o := fun he =>
    (Finset.mem_sdiff.mp x.property).2 (by simpa only [he] using C.property.2)
  let y := offVertexOfSite (Finset.mem_sdiff.mp x.property).1 hxo
  change wiredHeight (-1) (joinField rC rD) (FiniteWired.site y.val) = _
  rw [wired_height_off_vertex]
  have hy : FiniteWired.site y.val = x.val := rfl
  simp only [joinField, hy, dif_neg (Finset.mem_sdiff.mp x.property).2, Nat.cast_add]
  rfl

/-- Every pair reconstructs an allowed punctured field with exactly core C.val. -/
theorem join_field_allowed_core {N : ℕ} {o : FiniteWired.Active N} {C : ComponentShape o}
    
    (rC : InnerAllowed o C) (rD : OuterAllowed C) :
    punctured_allowed (joinField rC.val rD.val) ∧ core (joinField rC.val rD.val) = C.val := by
  apply (punctured_core_iff _ C.val C.property.1 C.property.2).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx hxo
    let y : {x : Site2 // x ∈ C.val.erase (FiniteWired.site o)} :=
      ⟨x, Finset.mem_erase.mpr ⟨hxo, hx⟩⟩
    rw [join_field_height_inner rC.val rD.val y]
    exact_mod_cast (rC.val y).isLt
  · exact (allowed_iff_allowedOn (fun x hx =>
      join_field_height_inner rC.val rD.val ⟨x, hx⟩)).mpr rC.property
  · intro x hx
    rw [join_field_height_outer rC.val rD.val ⟨x, hx⟩]
    have hn : (0 : ℤ) ≤ ((rD.val ⟨x, hx⟩).val : ℤ) := Nat.cast_nonneg _
    dsimp only [Subtype.coe_mk]
    omega
  · apply (allowed_iff_allowedOn ?_).mpr rD.property
    intro x hx
    dsimp only
    rw [join_field_height_outer rC.val rD.val ⟨x, hx⟩]
    ring

/-- Restriction of a core-C.val field to the C.val-side induced graph. -/
def restrictInner {N : ℕ} {o : FiniteWired.Active N} {C : ComponentShape o}
     (h : CoreField o C.val) : InnerField o C := fun x =>
  let y := offVertexOfSite (C.property.1 (Finset.mem_erase.mp x.property).2)
    (Finset.mem_erase.mp x.property).1
  ⟨(h.val.val y).val, by
    have hh := (core_forbidden h.val.val).2 x.val (by rw [h.property]; exact (Finset.mem_erase.mp x.property).2)
    rw [h.property] at hh
    change wiredHeight (-1) h.val.val (FiniteWired.site y.val) < _ at hh
    rw [wired_height_off_vertex] at hh
    exact_mod_cast hh⟩

/-- Restriction of a core-C.val field to D, subtracting the original edges into C.val. -/
def restrictOuter {N : ℕ} {o : FiniteWired.Active N} {C : ComponentShape o}
    (h : CoreField o C.val) : OuterField C := fun x =>
  ⟨(wiredHeight (-1) h.val.val x.val - (degree C.val x.val : ℤ)).toNat, by
    have hh := shifted_core_height_stable h.val.val
      (Finset.mem_sdiff.mp x.property).1
      (fun hx => (Finset.mem_sdiff.mp x.property).2 (by simpa only [h.property] using hx))
    rw [h.property] at hh
    omega⟩

theorem restrict_inner_height {N : ℕ} {o : FiniteWired.Active N} {C : ComponentShape o}
     (h : CoreField o C.val)
    (x : {x : Site2 // x ∈ C.val.erase (FiniteWired.site o)}) :
    wiredHeight (-1) h.val.val x.val = ((restrictInner h x).val : ℤ) := by
  exact wired_height_off_vertex h.val.val
    (offVertexOfSite (C.property.1 (Finset.mem_erase.mp x.property).2) (Finset.mem_erase.mp x.property).1)

theorem restrict_outer_height {N : ℕ} {o : FiniteWired.Active N} {C : ComponentShape o}
    (h : CoreField o C.val) (x : {x : Site2 // x ∈ boxSites N \ C.val}) :
    wiredHeight (-1) h.val.val x.val - (degree C.val x.val : ℤ) =
      ((restrictOuter h x).val : ℤ) := by
  have hh := height_ge_degree_core_outside h.val.val
    (Finset.mem_sdiff.mp x.property).1
    (fun hx => (Finset.mem_sdiff.mp x.property).2 (by simpa only [h.property] using hx))
  rw [h.property] at hh
  exact (Int.toNat_of_nonneg (by omega)).symm

def splitField {N : ℕ} {o : FiniteWired.Active N} {C : ComponentShape o}
     (h : CoreField o C.val) :
    InnerAllowed o C × OuterAllowed C := by
  have hs := (punctured_core_iff h.val.val C.val C.property.1 C.property.2).mp ⟨h.val.property, h.property⟩
  exact (⟨restrictInner h,
    (allowed_iff_allowedOn (fun x hx => restrict_inner_height h ⟨x, hx⟩)).mp hs.2.1⟩,
    ⟨restrictOuter h,
    (allowed_iff_allowedOn (fun x hx => restrict_outer_height h ⟨x, hx⟩)).mp hs.2.2.2⟩)

def assembleField {N : ℕ} {o : FiniteWired.Active N} {C : ComponentShape o}
    
    (r : InnerAllowed o C × OuterAllowed C) : CoreField o C.val :=
  ⟨⟨joinField r.1.val r.2.val, (join_field_allowed_core r.1 r.2).1⟩,
    (join_field_allowed_core r.1 r.2).2⟩

theorem assemble_split_field {N : ℕ} {o : FiniteWired.Active N} {C : ComponentShape o}
     (h : CoreField o C.val) :
    assembleField (splitField h) = h := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  apply Fin.ext
  have hxo : FiniteWired.site x.val ≠ FiniteWired.site o :=
    fun he => x.property (FiniteWired.site_injective N he)
  have hxB := site_mem_box x.val
  by_cases hxC : FiniteWired.site x.val ∈ C.val
  · let y : {y : Site2 // y ∈ C.val.erase (FiniteWired.site o)} :=
      ⟨FiniteWired.site x.val, Finset.mem_erase.mpr ⟨hxo, hxC⟩⟩
    have h1 := join_field_height_inner (restrictInner h) (restrictOuter h) y
    have h2 := restrict_inner_height h y
    rw [wired_height_off_vertex] at h1 h2
    change (joinField (restrictInner h) (restrictOuter h) x).val = (h.val.val x).val
    exact_mod_cast h1.trans h2.symm
  · let y : {y : Site2 // y ∈ boxSites N \ C.val} :=
      ⟨FiniteWired.site x.val, Finset.mem_sdiff.mpr ⟨hxB, hxC⟩⟩
    have h1 := join_field_height_outer (restrictInner h) (restrictOuter h) y
    have h2 := restrict_outer_height h y
    rw [wired_height_off_vertex] at h1 h2
    change (joinField (restrictInner h) (restrictOuter h) x).val = (h.val.val x).val
    exact_mod_cast (show ((joinField (restrictInner h) (restrictOuter h) x).val : ℤ) =
        ((h.val.val x).val : ℤ) by omega)

theorem split_assemble_field {N : ℕ} {o : FiniteWired.Active N} {C : ComponentShape o}
    
    (r : InnerAllowed o C × OuterAllowed C) :
    splitField (assembleField r) = r := by
  apply Prod.ext
  · apply Subtype.ext
    funext x
    apply Fin.ext
    have h1 := restrict_inner_height (assembleField r) x
    have h2 := join_field_height_inner r.1.val r.2.val x
    exact_mod_cast h1.symm.trans h2
  · apply Subtype.ext
    funext x
    apply Fin.ext
    have h1 := restrict_outer_height (assembleField r) x
    have h2 := join_field_height_outer r.1.val r.2.val x
    change wiredHeight (-1) (joinField r.1.val r.2.val) x.val - (degree C.val x.val : ℤ) =
      ((restrictOuter (assembleField r) x).val : ℤ) at h1
    rw [h2, add_sub_cancel_right] at h1
    exact_mod_cast h1.symm

/-- The deterministic field product: literal restriction and reconstruction are inverse. -/
def componentFieldEquiv {N : ℕ} {o : FiniteWired.Active N} {C : ComponentShape o}
     :
    CoreField o C.val ≃ InnerAllowed o C × OuterAllowed C where
  toFun := splitField
  invFun := assembleField
  left_inv := assemble_split_field
  right_inv := split_assemble_field

end
end FiniteAvalanches.Sandpile.Components
