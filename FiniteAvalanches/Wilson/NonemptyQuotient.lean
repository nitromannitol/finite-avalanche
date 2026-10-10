import FiniteAvalanches.Wilson.CopiedWalk

/-! Literal contraction of nonempty root sets on a copied multigraph. This
implementation imports no unrestricted empty-root quotient. Copies retain E IDs;
only copies whose endpoints become equal are removed. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient
open FiniteAvalanches.Trees
open scoped Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]

abbrev Vertex (R : CopiedNetwork.Roots (V := V)) := Option {v : V // v ∉ R.val}

def project (R : CopiedNetwork.Roots (V := V)) (v : V) : Vertex R :=
  if h : v ∈ R.val then none else some ⟨v, h⟩

omit [Fintype V] in
theorem project_eq_none (R : CopiedNetwork.Roots (V := V)) (v : V) :
    project R v = none ↔ v ∈ R.val := by
  by_cases hv : v ∈ R.val <;> simp [project, hv]

omit [Fintype V] in
theorem project_eq_iff (R : CopiedNetwork.Roots (V := V)) (v w : V) :
    project R v = project R w ↔ v = w ∨ (v ∈ R.val ∧ w ∈ R.val) := by
  by_cases hv : v ∈ R.val <;> by_cases hw : w ∈ R.val
  · simp [project, hv, hw]
  · simp [project, hv, hw, show v ≠ w from fun h => hw (h ▸ hv)]
  · simp [project, hv, hw, show v ≠ w from fun h => hv (h.symm ▸ hw)]
  · simp [project, hv, hw, Subtype.ext_iff]

omit [Fintype V] in
theorem project_surjective (R : CopiedNetwork.Roots (V := V)) : Function.Surjective (project R) := by
  intro v
  cases v with
  | none => obtain ⟨r, hr⟩ := R.property; exact ⟨r, (project_eq_none R r).mpr hr⟩
  | some v => exact ⟨v.val, by simp [project, v.property]⟩

def rootSetoid (R : CopiedNetwork.Roots (V := V)) : Setoid V := Setoid.ker (project R)

/-- A genuine equivalence quotient, with surjectivity proved before forming the equivalence. -/
def quotientEquiv (R : CopiedNetwork.Roots (V := V)) : Quotient (rootSetoid R) ≃ Vertex R :=
  Equiv.ofBijective (Quotient.lift (project R) (fun _ _ h => h)) (by
    constructor
    · intro a b h
      induction a using Quotient.inductionOn
      induction b using Quotient.inductionOn
      exact Quotient.sound h
    · intro v
      obtain ⟨x, hx⟩ := project_surjective R v
      exact ⟨Quotient.mk _ x, hx⟩)

omit [Fintype V] in
@[simp] theorem quotientEquiv_mk (R : CopiedNetwork.Roots (V := V)) (v : V) :
    quotientEquiv R (Quotient.mk _ v) = project R v := rfl

variable (G : Multigraph V E) (R : CopiedNetwork.Roots (V := V))

abbrev Copy := {e : E // project R (G.left e) ≠ project R (G.right e)}

instance vertexFintype : Fintype (Vertex R) := inferInstanceAs (Fintype (Option {v : V // v ∉ R.val}))
instance copyFintype : Fintype (Copy G R) :=
  inferInstanceAs (Fintype {e : E // project R (G.left e) ≠ project R (G.right e)})

def copyID : Copy G R ↪ E := ⟨Subtype.val, Subtype.coe_injective⟩

def graph : Multigraph (Vertex R) (Copy G R) :=
  ⟨fun e => project R (G.left e.val), fun e => project R (G.right e.val), fun e => e.property⟩

theorem contracted_loop_iff (e : E) :
    project R (G.left e) = project R (G.right e) ↔ G.left e ∈ R.val ∧ G.right e ∈ R.val := by
  rw [project_eq_iff]
  simp only [G.loopless e, false_or]

theorem nonroot_incident_survives (v : V) (hv : v ∉ R.val) (e : Incident G v) :
    project R (G.left e.val) ≠ project R (G.right e.val) := by
  intro h
  obtain ⟨hl, hr⟩ := (contracted_loop_iff G R e.val).mp h
  rcases e.property with he | he
  · exact hv (he ▸ hl)
  · exact hv (he ▸ hr)

def projectIncident (v : V) (hv : v ∉ R.val) (e : Incident G v) :
    Incident (graph G R) (project R v) :=
  ⟨⟨e.val, nonroot_incident_survives G R v hv e⟩, by
    rcases e.property with h | h
    · exact Or.inl (congrArg (project R) h)
    · exact Or.inr (congrArg (project R) h)⟩

theorem projectIncident_bijective (v : V) (hv : v ∉ R.val) :
    Function.Bijective (projectIncident G R v hv) := by
  constructor
  · intro e f h
    exact Subtype.ext (congrArg (fun a => a.val.val) h)
  · intro e
    have hl : G.left e.val.val = v ∨ G.right e.val.val = v := by
      rcases e.property with h | h
      · rcases (project_eq_iff R _ v).mp h with he | he
        · exact Or.inl he
        · exact False.elim (hv he.2)
      · rcases (project_eq_iff R _ v).mp h with he | he
        · exact Or.inr he
        · exact False.elim (hv he.2)
    refine ⟨⟨e.val.val, hl⟩, ?_⟩
    apply Subtype.ext
    exact Subtype.ext rfl

/-- The incident-copy bijection exists before its bundled equivalence is formed. -/
def nonrootIncidentEquiv (v : V) (hv : v ∉ R.val) :
    Incident G v ≃ Incident (graph G R) (project R v) :=
  Equiv.ofBijective (projectIncident G R v hv) (projectIncident_bijective G R v hv)

@[simp] theorem nonrootIncidentEquiv_copy (v : V) (hv : v ∉ R.val) (e : Incident G v) :
    (nonrootIncidentEquiv G R v hv e).val.val = e.val := rfl

theorem reaches_project {x y : V} (h : G.reaches Finset.univ x y) :
    (graph G R).reaches Finset.univ (project R x) (project R y) := by
  induction h with
  | refl => exact .refl
  | @tail y z h he ih =>
    apply ih.trans
    by_cases hz : project R y = project R z
    · exact hz ▸ Relation.ReflTransGen.refl
    · obtain ⟨e, _, he | he⟩ := he
      · have hs : project R (G.left e) ≠ project R (G.right e) := by rwa [he.1, he.2]
        exact Relation.ReflTransGen.single ⟨⟨e, hs⟩, Finset.mem_univ _, Or.inl
          ⟨congrArg (project R) he.1, congrArg (project R) he.2⟩⟩
      · have hs : project R (G.left e) ≠ project R (G.right e) := by
          rw [he.1, he.2]; exact Ne.symm hz
        exact Relation.ReflTransGen.single ⟨⟨e, hs⟩, Finset.mem_univ _, Or.inr
          ⟨congrArg (project R) he.1, congrArg (project R) he.2⟩⟩

theorem graph_connected (hconn : ∀ x y, G.reaches Finset.univ x y) :
    ∀ x y, (graph G R).reaches Finset.univ x y := by
  intro x y
  obtain ⟨a, rfl⟩ := project_surjective R x
  obtain ⟨b, rfl⟩ := project_surjective R y
  exact reaches_project G R (hconn a b)

omit [Fintype V] in
theorem all_roots_vertex_subsingleton (hR : R.val = Set.univ) : Subsingleton (Vertex R) := by
  have hall : ∀ v : V, v ∈ R.val := fun v => hR.symm ▸ Set.mem_univ v
  refine ⟨fun v w => ?_⟩
  have hz (z : Vertex R) : z = none := by
    cases z with
    | none => rfl
    | some v => exact False.elim (v.property (hall v.val))
  exact (hz v).trans (hz w).symm

theorem all_roots_copy_empty (hR : R.val = Set.univ) : IsEmpty (Copy G R) := by
  have hall : ∀ v : V, v ∈ R.val := fun v => hR.symm ▸ Set.mem_univ v
  refine ⟨fun e => e.property ?_⟩
  exact ((project_eq_none R _).mpr (hall (G.left e.val))).trans
    ((project_eq_none R _).mpr (hall (G.right e.val))).symm

end
end FiniteAvalanches.Wilson.CopiedNetwork.NonemptyQuotient
