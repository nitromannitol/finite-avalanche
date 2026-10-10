import FiniteAvalanches.Wilson.RootContraction.Subsets

/-! Simultaneous contraction sends an actual rooted copied forest to a copied tree. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] (G : Multigraph V E)
  (R : CopiedNetwork.Roots (V := V))

/-- The unique prescribed original root of the actual component. -/
def componentRoot {F : Finset E} (hF : G.is_rooted_forest R.val F) (v : V) : V :=
  (hF.2 v).choose

theorem componentRoot_spec {F : Finset E} (hF : G.is_rooted_forest R.val F) (v : V) :
    componentRoot G R hF v ∈ R.val ∧ G.reaches F v (componentRoot G R hF v) ∧
      ∀ r ∈ R.val, G.reaches F v r → r = componentRoot G R hF v := (hF.2 v).choose_spec

theorem componentRoot_eq_of_reachable {F : Finset E} (hF : G.is_rooted_forest R.val F)
    {a b : V} (hab : G.reaches F a b) : componentRoot G R hF a = componentRoot G R hF b := by
  obtain ⟨hr, hb, _⟩ := componentRoot_spec G R hF b
  exact ((componentRoot_spec G R hF a).2.2 _ hr (hab.trans hb)).symm

theorem componentRoot_of_mem {F : Finset E} (hF : G.is_rooted_forest R.val F)
    {r : V} (hr : r ∈ R.val) : componentRoot G R hF r = r :=
  ((componentRoot_spec G R hF r).2.2 r hr .refl).symm

/-- Retract the quotient to one original component; other components collapse to its root. -/
def componentRetract {F : Finset E} (hF : G.is_rooted_forest R.val F) (r : V) : Vertex R → V
  | none => r
  | some v => if componentRoot G R hF v.val = r then v.val else r

theorem componentRetract_project {F : Finset E} (hF : G.is_rooted_forest R.val F) (r v : V) :
    componentRetract G R hF r (project R v) =
      if componentRoot G R hF v = r then v else r := by
  by_cases hv : v ∈ R.val
  · simp only [project, dif_pos hv, componentRetract, componentRoot_of_mem G R hF hv]
    split_ifs with h <;> simp_all
  · simp [project, hv, componentRetract]

theorem tree_of_rooted_forest {F : Finset E} (hF : G.is_rooted_forest R.val F) :
    (graph G R).is_tree Set.univ (projectCopies G R F) := by
  have hc (v : Vertex R) : (graph G R).reaches (projectCopies G R F) v none := by
    obtain ⟨x, rfl⟩ := project_surjective R v
    obtain ⟨r, hr, hx, _⟩ := hF.2 x
    have h := reaches_project_copies G R hx
    simpa only [(project_eq_none R r).mpr hr] using h
  refine ⟨⟨none, Set.mem_univ _⟩, (by intro e he; simp), ?_, ?_⟩
  · intro x _ y _
    exact (hc x).trans ((graph G R).reaches_symm (hc y))
  · intro e he halt
    let a := G.left e.val
    let b := G.right e.val
    let r := componentRoot G R hF a
    have heF : e.val ∈ F := (mem_projectCopies G R F e).mp he
    have hab : G.reaches F a b := .single ⟨e.val, heF, Or.inl ⟨rfl, rfl⟩⟩
    have hba : componentRoot G R hF b = r := (componentRoot_eq_of_reachable G R hF hab).symm
    have hlift : G.reaches (F.erase e.val)
        (componentRetract G R hF r ((graph G R).left e))
        (componentRetract G R hF r ((graph G R).right e)) := by
      apply Relation.ReflTransGen.lift' (componentRetract G R hF r) (fun u v hf => ?_) _ _ halt
      obtain ⟨f, hf, h | h⟩ := hf
      all_goals
        have hfe : f.val ≠ e.val := fun hval => (Finset.mem_erase.mp hf).1 (Subtype.ext hval)
        have hfF : f.val ∈ F := (mem_projectCopies G R F f).mp (Finset.mem_erase.mp hf).2
        have hfab : G.reaches F (G.left f.val) (G.right f.val) :=
          .single ⟨f.val, hfF, Or.inl ⟨rfl, rfl⟩⟩
        have hroots := componentRoot_eq_of_reachable G R hF hfab
        change project R _ = u ∧ project R _ = v at h
        change G.reaches (F.erase e.val) (componentRetract G R hF r u) (componentRetract G R hF r v)
        rw [← h.1, ← h.2, componentRetract_project, componentRetract_project]
        by_cases hl : componentRoot G R hF (G.left f.val) = r
        · have hr := hroots.symm.trans hl
          simp only [hl, hr, ↓reduceIte]
          exact .single ⟨f.val, Finset.mem_erase.mpr ⟨hfe, hfF⟩, by
            first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr ⟨rfl, rfl⟩⟩
        · have hr : componentRoot G R hF (G.right f.val) ≠ r := fun hh => hl (hroots.trans hh)
          simp only [hl, hr, ↓reduceIte]
          exact .refl
    apply hF.1 e.val heF
    simpa [graph, componentRetract_project, a, b, r, hba] using hlift

end
end FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient
