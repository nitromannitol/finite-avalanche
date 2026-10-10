import FiniteAvalanches.Trees.Lattice.Topology
import FiniteAvalanches.Trees.Lattice.WiredLaw

/-! Literal two-color rooted lattice forests. All vertices and all unordered
nearest-neighbor edges are retained. No probability law is selected. -/
namespace FiniteAvalanches.Wilson.Lattice
open LatticeProb FiniteAvalanches.Trees.Lattice MeasureTheory
open scoped Classical
noncomputable section

/-- The source's two disjoint nonempty sets, retaining every root separately. -/
structure RootPair where
  zero : Set (Site 2)
  one : Set (Site 2)
  disjoint : Disjoint zero one
  zero_nonempty : zero.Nonempty
  one_nonempty : one.Nonempty

abbrev ColorField := Site 2 → Bool
abbrev ForestField := EdgeField × ColorField

/-- Acyclic on all sites, with exactly one original root in each component. -/
def is_rooted_forest (R : RootPair) (f : EdgeField) : Prop :=
  (toGraph f).IsAcyclic ∧ ∀ x, ∃ r ∈ R.zero ∪ R.one,
    (toGraph f).Reachable x r ∧
      ∀ r' ∈ R.zero ∪ R.one, (toGraph f).Reachable x r' → r' = r

abbrev RootedForest (R : RootPair) := {f : EdgeField // is_rooted_forest R f}

def oneVertices (R : RootPair) (f : RootedForest R) : Set (Site 2) :=
  {x | ∃ r ∈ R.one, (toGraph f.val).Reachable x r}

theorem reachable_roots_eq (R : RootPair) (f : RootedForest R)
    {x r s : Site 2} (hr : r ∈ R.zero ∪ R.one) (hs : s ∈ R.zero ∪ R.one)
    (hxr : (toGraph f.val).Reachable x r) (hxs : (toGraph f.val).Reachable x s) : r = s := by
  obtain ⟨u, _, _, hu⟩ := f.property.2 x
  exact (hu r hr hxr).trans (hu s hs hxs).symm

/-- Component root colors, defined by literal reachability, without choosing a root. -/
def colors (R : RootPair) (f : RootedForest R) : ColorField :=
  fun x => decide (x ∈ oneVertices R f)

theorem colors_eq_true_iff (R : RootPair) (f : RootedForest R) (x : Site 2) :
    colors R f x = true ↔ ∃ r ∈ R.one, (toGraph f.val).Reachable x r := by
  simp only [colors, decide_eq_true_eq, oneVertices, Set.mem_setOf_eq]

theorem colors_of_one_root (R : RootPair) (f : RootedForest R) {x : Site 2}
    (hx : x ∈ R.one) : colors R f x = true :=
  (colors_eq_true_iff R f x).mpr ⟨x, hx, .refl x⟩

theorem colors_of_zero_root (R : RootPair) (f : RootedForest R) {x : Site 2}
    (hx : x ∈ R.zero) : colors R f x = false := by
  have hn : ¬colors R f x = true := by
    intro h
    obtain ⟨r, hr, hxr⟩ := (colors_eq_true_iff R f x).mp h
    have he := reachable_roots_eq R f (Or.inl hx) (Or.inr hr) (.refl x) hxr
    exact Set.disjoint_left.mp R.disjoint hx (he.symm ▸ hr)
  cases h : colors R f x <;> simp_all

/-- Raw full product carrier; valid fields have precisely the original component colors. -/
def is_colored_forest (R : RootPair) (ω : ForestField) : Prop :=
  is_rooted_forest R ω.1 ∧ ∀ x,
    ω.2 x = true ↔ ∃ r ∈ R.one, (toGraph ω.1).Reachable x r

theorem colored_iff_colors (R : RootPair) (f : RootedForest R) (σ : ColorField) :
    is_colored_forest R (f.val, σ) ↔ σ = colors R f := by
  constructor
  · intro h
    funext x
    have he := (h.2 x).trans (colors_eq_true_iff R f x).symm
    cases hσ : σ x <;> cases hf : colors R f x <;> simp_all
  · rintro rfl
    exact ⟨f.property, colors_eq_true_iff R f⟩

theorem existsUnique_colors (R : RootPair) (f : RootedForest R) :
    ∃! σ : ColorField, is_colored_forest R (f.val, σ) :=
  ⟨colors R f, (colored_iff_colors R f _).mpr rfl,
    fun σ hσ => (colored_iff_colors R f σ).mp hσ⟩

def colorCylinder (F : Finset (Site 2)) (p : F → Bool) : Set ColorField :=
  {σ | F.restrict σ = p}

theorem isClopen_colorCylinder (F : Finset (Site 2)) (p : F → Bool) :
    IsClopen (colorCylinder F p) :=
  (isClopen_discrete {p}).preimage (continuous_pi (fun x => continuous_apply x.val))

theorem measurableSet_colorCylinder (F : Finset (Site 2)) (p : F → Bool) :
    MeasurableSet (colorCylinder F p) := (isClopen_colorCylinder F p).isClosed.measurableSet

end
end FiniteAvalanches.Wilson.Lattice
