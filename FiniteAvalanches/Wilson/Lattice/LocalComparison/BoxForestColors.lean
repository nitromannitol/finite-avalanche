import FiniteAvalanches.Wilson.Lattice.LocalComparison.BoxForestEquiv

set_option autoImplicit false
namespace LocalBoxContraction
open LatticeProb FiniteAvalanches FiniteAvalanches.Wilson FiniteAvalanches.Wilson.Lattice
open FiniteAvalanches.Sandpile FiniteAvalanches.Trees
open FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical
noncomputable section

theorem vertexMap_beta_iff (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (v : FiniteWired.Vertex N) :
    vertexMap D P N v = beta D P ↔
      v ∈ wiredZero (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N := by
  cases v with
  | none =>
    change alpha D P = beta D P ↔ False
    exact ⟨(fun h => by cases h), False.elim⟩
  | some x => exact project_eq_beta_iff D P (FiniteWired.site x)

theorem vertexMap_alpha_iff (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (v : FiniteWired.Vertex N) :
    vertexMap D P N v = alpha D P ↔
      v ∈ wiredOne (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N := by
  cases v with
  | none => exact iff_of_true rfl trivial
  | some x => exact project_eq_alpha_iff D P (FiniteWired.site x)

theorem vertexMap_root (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    {v : FiniteWired.Vertex N} (hv : v ∈ (boxRoots D P N).val) :
    vertexMap D P N v ∈ (primalRoots D P).val := by
  rcases hv with hp | hd
  · exact Or.inr ((vertexMap_beta_iff D P N v).mpr hp)
  · exact Or.inl ((vertexMap_alpha_iff D P N v).mpr hd)

/-- Reachability to beta means reachability to an original P root, on the entire carrier. -/
theorem reaches_beta_iff (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x)
    (F : FiniteForest (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N)
    (x : FiniteWired.Vertex N) :
    (primalGraph D P).reaches (forestEquiv D P N hDbox F).val (vertexMap D P N x) (beta D P) ↔
      ∃ r ∈ wiredZero (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N,
        (WiredTrees.graph N).reaches F.val x r := by
  constructor
  · intro hx
    obtain ⟨r,hr,hxr,_⟩ := F.property.2 x
    obtain ⟨u,_,_,hu⟩ := (forestEquiv D P N hDbox F).property.2 (vertexMap D P N x)
    have he : vertexMap D P N r = beta D P :=
      (hu _ (vertexMap_root D P N hr) (reaches_map D P N hDbox F hxr)).trans
        (hu _ (Or.inr rfl) hx).symm
    exact ⟨r, (vertexMap_beta_iff D P N r).mp he, hxr⟩
  · rintro ⟨r,hr,hxr⟩
    have h := reaches_map D P N hDbox F hxr
    rw [(vertexMap_beta_iff D P N r).mpr hr] at h
    exact h

/-- Reachability to alpha means reachability to an original exterior root, including the sink. -/
theorem reaches_alpha_iff (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x)
    (F : FiniteForest (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N)
    (x : FiniteWired.Vertex N) :
    (primalGraph D P).reaches (forestEquiv D P N hDbox F).val (vertexMap D P N x) (alpha D P) ↔
      ∃ r ∈ wiredOne (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N,
        (WiredTrees.graph N).reaches F.val x r := by
  constructor
  · intro hx
    obtain ⟨r,hr,hxr,_⟩ := F.property.2 x
    obtain ⟨u,_,_,hu⟩ := (forestEquiv D P N hDbox F).property.2 (vertexMap D P N x)
    have he : vertexMap D P N r = alpha D P :=
      (hu _ (vertexMap_root D P N hr) (reaches_map D P N hDbox F hxr)).trans
        (hu _ (Or.inl rfl) hx).symm
    exact ⟨r, (vertexMap_alpha_iff D P N r).mp he, hxr⟩
  · rintro ⟨r,hr,hxr⟩
    have h := reaches_map D P N hDbox F hxr
    rw [(vertexMap_alpha_iff D P N r).mpr hr] at h
    exact h

/-- The unique original root maps to the unique source root at every vertex. -/
theorem unique_root_transport (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x)
    (F : FiniteForest (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N)
    (x r : FiniteWired.Vertex N) (hr : r ∈ (boxRoots D P N).val)
    (hxr : (WiredTrees.graph N).reaches F.val x r) :
    vertexMap D P N r ∈ (primalRoots D P).val ∧
      (primalGraph D P).reaches (forestEquiv D P N hDbox F).val
        (vertexMap D P N x) (vertexMap D P N r) ∧
      ∀ s ∈ (primalRoots D P).val,
        (primalGraph D P).reaches (forestEquiv D P N hDbox F).val (vertexMap D P N x) s →
          s = vertexMap D P N r := by
  have hm := reaches_map D P N hDbox F hxr
  have hroot := vertexMap_root D P N hr
  obtain ⟨u,_,_,hu⟩ := (forestEquiv D P N hDbox F).property.2 (vertexMap D P N x)
  exact ⟨hroot,hm,fun s hs hxs => (hu s hs hxs).trans (hu _ hroot hm).symm⟩

def primalField (D : Finset (Site 2)) (P : OneSet D) (F : PrimalForest D P) : ColorField :=
  fun x => decide ((primalGraph D P).reaches F.val (project D P x) (beta D P))

/-- The source one color is the original P color, after the required complement. -/
theorem field_transport (D : Finset (Site 2)) (P : OneSet D) (N : ℕ)
    (hDbox : ∀ x ∈ D, FiniteWired.inBox N x)
    (F : FiniteForest (LocalColorSwap.roots (LocalZeroExterior.domainRoots D P)) N) :
    primalField D P (forestEquiv D P N hDbox F) =
      LocalZeroExterior.field (LocalZeroExterior.domainRoots D P) N F := by
  funext x
  apply Bool.eq_iff_iff.mpr
  change decide ((primalGraph D P).reaches (forestEquiv D P N hDbox F).val
    (project D P x) (beta D P)) = true ↔
      LocalZeroExterior.field (LocalZeroExterior.domainRoots D P) N F x = true
  rw [decide_eq_true_eq, LocalZeroExterior.field_true_iff]
  rw [← vertexMap_wiredSite D P N hDbox x]
  exact reaches_beta_iff D P N hDbox F (wiredSite N x)

end
end LocalBoxContraction
