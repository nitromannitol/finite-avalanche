import FiniteAvalanches.Electrical.Geometry.SourceHDual

/-! Connectivity after removing the exterior terminal, and its original-copy bond. -/
set_option autoImplicit false
namespace FiniteAvalanches.Electrical.LatticeDrawing
open LatticeProb
open FiniteAvalanches.Electrical.Plane.SourceLattice
open scoped Classical
noncomputable section

/-- The full original H carrier is connected from the source domain connectivity. -/
theorem primal_connected (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (marked : MarkedCopy D P) :
    (supportGraph (primalGraph D P).left (primalGraph D P).right).Connected := by
  letI : Nonempty (Vertex D P) := ⟨alpha D P⟩
  exact ⟨primal_preconnected D P hD marked⟩

theorem project_ne_alpha_of_mem (D : Finset (Site 2)) (P : OneSet D)
    (x : Site 2) (hx : x ∈ D) : project D P x ≠ alpha D P :=
  fun h => ((project_eq_alpha_iff D P x).mp h) hx

theorem internal_primal_copy_reaches_without_alpha
    (D : Finset (Site 2)) (P : OneSet D) (e : OriginalCopy)
    (ha : originalA e ∈ D) (hb : originalB e ∈ D) :
    (Plane.SourceLattice.primalGraph D P).reaches
      (Finset.univ.filter fun f => (primalGraph D P).left f ≠ alpha D P ∧
        (primalGraph D P).right f ≠ alpha D P)
      (project D P (originalA e)) (project D P (originalB e)) := by
  by_cases heq : project D P (originalA e) = project D P (originalB e)
  · rw [heq]
    exact .refl
  · let f : PrimalCopy D P := ⟨e, Finset.mem_filter.mpr
        ⟨(mem_domainCopies D e).mpr (Or.inl ha), heq⟩⟩
    exact .single ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      project_ne_alpha_of_mem D P _ ha, project_ne_alpha_of_mem D P _ hb⟩,
      Or.inl ⟨rfl, rfl⟩⟩

theorem internal_primal_reaches_without_alpha
    (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) (x y : D) :
    (Plane.SourceLattice.primalGraph D P).reaches
      (Finset.univ.filter fun f => (primalGraph D P).left f ≠ alpha D P ∧
        (primalGraph D P).right f ≠ alpha D P)
      (project D P x.val) (project D P y.val) := by
  have hr := (SimpleGraph.reachable_iff_reflTransGen x y).mp (hD x y)
  induction hr with
  | refl => exact .refl
  | @tail u v _ huv ih =>
    change ∃ i : Fin 2, v.val = u.val + unit i ∨ u.val = v.val + unit i at huv
    obtain ⟨i, h | h⟩ := huv
    · have he := internal_primal_copy_reaches_without_alpha D P (u.val, i)
        u.property (by change u.val + unit i ∈ D; rw [← h]; exact v.property)
      change (Plane.SourceLattice.primalGraph D P).reaches _
        (project D P u.val) (project D P (u.val + unit i)) at he
      rw [← h] at he
      exact ih.trans he
    · have he := internal_primal_copy_reaches_without_alpha D P (v.val, i)
        v.property (by change v.val + unit i ∈ D; rw [← h]; exact u.property)
      change (Plane.SourceLattice.primalGraph D P).reaches _
        (project D P v.val) (project D P (v.val + unit i)) at he
      rw [← h] at he
      exact ih.trans ((Plane.SourceLattice.primalGraph D P).reaches_symm he)

theorem exists_site_of_ne_alpha (D : Finset (Site 2)) (P : OneSet D)
    (v : Vertex D P) (hv : v ≠ alpha D P) : ∃ x : D, project D P x.val = v := by
  cases v with
  | inl b => cases b with
    | false => exact (hv rfl).elim
    | true =>
      obtain ⟨p, hp⟩ := P.property
      exact ⟨p, (project_eq_beta_iff D P _).mpr (Finset.mem_image.mpr ⟨p, hp, rfl⟩)⟩
  | inr x => exact ⟨x.val, project_free D P x⟩

/-- Every pair of remaining vertices is joined using only edges off the alpha star. -/
theorem primal_reaches_without_alpha (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
    (x y : Vertex D P) (hx : x ≠ alpha D P) (hy : y ≠ alpha D P) :
    (Plane.SourceLattice.primalGraph D P).reaches
      (Finset.univ.filter fun f => (primalGraph D P).left f ≠ alpha D P ∧
        (primalGraph D P).right f ≠ alpha D P) x y := by
  obtain ⟨u, rfl⟩ := exists_site_of_ne_alpha D P x hx
  obtain ⟨v, rfl⟩ := exists_site_of_ne_alpha D P y hy
  exact internal_primal_reaches_without_alpha D P hD u v

/-- The graph obtained by deleting alpha is connected on its entire remaining carrier. -/
theorem primal_without_alpha_connected (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) :
    ((supportGraph (primalGraph D P).left (primalGraph D P).right).induce
      {v : Vertex D P | v ≠ alpha D P}).Connected := by
  have hba : beta D P ≠ alpha D P := Sum.inl_injective.ne (by decide)
  letI : Nonempty ↥({v : Vertex D P | v ≠ alpha D P} : Set (Vertex D P)) :=
    ⟨⟨beta D P, hba⟩⟩
  refine ⟨?_⟩
  intro x y
  have hr := primal_reaches_without_alpha D P hD x.val y.val x.property y.property
  have lift (u v : Vertex D P) (h : (Plane.SourceLattice.primalGraph D P).reaches
      (Finset.univ.filter fun f => (primalGraph D P).left f ≠ alpha D P ∧
        (primalGraph D P).right f ≠ alpha D P) u v)
      (hu : u ≠ alpha D P) (hv : v ≠ alpha D P) :
      ((supportGraph (primalGraph D P).left (primalGraph D P).right).induce
        {w : Vertex D P | w ≠ alpha D P}).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
    induction h with
    | refl => exact .rfl
    | @tail v w _ hadj ih =>
      obtain ⟨e, he, hor⟩ := hadj
      have hend := (Finset.mem_filter.mp he).2
      have hv' : v ≠ alpha D P := hor.elim
        (fun h => h.1 ▸ hend.1) (fun h => h.1 ▸ hend.2)
      refine (ih hv').trans (SimpleGraph.Adj.reachable ?_)
      refine ⟨?_, e, hor⟩
      intro hvw
      rcases hor with h | h
      · exact primal_loopless D P e (h.1.trans (hvw.trans h.2.symm))
      · exact primal_loopless D P e (h.2.trans (hvw.symm.trans h.1.symm))
  exact lift x.val y.val hr x.property y.property

/-- Deleting any one original H copy leaves all vertices connected. -/
theorem primal_reaches_erase (D : Finset (Site 2)) (P : OneSet D)
    (e : PrimalCopy D P) (x y : Vertex D P) :
    (Plane.SourceLattice.primalGraph D P).reaches (Finset.univ.erase e) x y := by
  have hr := primal_reaches_of_deleted_card_le_three D P {e.val} (by simp) x y
  apply (Plane.SourceLattice.primalGraph D P).reaches_mono _ hr
  intro f hf
  have hne : f.val ≠ e.val := by
    simpa only [primalSurviving, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton] using hf
  exact Finset.mem_erase.mpr ⟨fun h => hne (congrArg Subtype.val h), Finset.mem_univ _⟩

/-- The alpha star is a bond: its deletion disconnects H, while every proper
subset of those original copied IDs can be deleted without disconnecting H. -/
theorem alpha_star_is_bond (D : Finset (Site 2)) (P : OneSet D)
    (hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected) :
    let star := Finset.univ.filter fun e : PrimalCopy D P =>
      (primalGraph D P).left e = alpha D P ∨ (primalGraph D P).right e = alpha D P
    (¬∀ x y, (Plane.SourceLattice.primalGraph D P).reaches (Finset.univ \ star) x y) ∧
      ∀ deleted : Finset (PrimalCopy D P), deleted ⊂ star →
        ∀ x y, (Plane.SourceLattice.primalGraph D P).reaches (Finset.univ \ deleted) x y := by
  let G := Plane.SourceLattice.primalGraph D P
  let star := Finset.univ.filter fun e : PrimalCopy D P =>
    G.left e = alpha D P ∨ G.right e = alpha D P
  have hba : beta D P ≠ alpha D P := Sum.inl_injective.ne (by decide)
  constructor
  · intro hconn
    have hsame : ∀ e ∈ Finset.univ \ star,
        G.left e ∈ ({alpha D P} : Set (Vertex D P)) ↔ G.right e ∈ ({alpha D P} : Set (Vertex D P)) := by
      intro e he
      have hn := (Finset.mem_sdiff.mp he).2
      exact iff_of_false
        (fun h => hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl h⟩))
        (fun h => hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr h⟩))
    exact hba ((G.reaches_mem_iff hsame (hconn (alpha D P) (beta D P))).mp rfl)
  · intro deleted hd x y
    obtain ⟨e, hes, hed⟩ := Finset.exists_of_ssubset hd
    have hi := (Finset.mem_filter.mp hes).2
    let survivors := Finset.univ \ deleted
    have hsub : (Finset.univ.filter fun f =>
        G.left f ≠ alpha D P ∧ G.right f ≠ alpha D P) ⊆ survivors := by
      intro f hf
      have hends := (Finset.mem_filter.mp hf).2
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hfd
      exact ((Finset.mem_filter.mp (hd.1 hfd)).2).elim hends.1 hends.2
    have off (v : Vertex D P) (hv : v ≠ alpha D P) : G.reaches survivors v (beta D P) :=
      G.reaches_mono hsub (primal_reaches_without_alpha D P hD v (beta D P) hv hba)
    have hab : G.reaches survivors (alpha D P) (beta D P) := by
      have he : e ∈ survivors := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hed⟩
      rcases hi with hi | hi
      · have hother : G.right e ≠ alpha D P :=
          fun h => G.loopless e (hi.trans h.symm)
        exact (Relation.ReflTransGen.single ⟨e, he, Or.inl ⟨hi, rfl⟩⟩).trans (off _ hother)
      · have hother : G.left e ≠ alpha D P :=
          fun h => G.loopless e (h.trans hi.symm)
        exact (Relation.ReflTransGen.single ⟨e, he, Or.inr ⟨hi, rfl⟩⟩).trans (off _ hother)
    have all_to_beta (v : Vertex D P) : G.reaches survivors v (beta D P) := by
      by_cases hv : v = alpha D P
      · rw [hv]
        exact hab
      · exact off v hv
    exact (all_to_beta x).trans (G.reaches_symm (all_to_beta y))

/-- The full alpha star includes at least four distinct physical lattice IDs. -/
theorem alpha_star_card_ge_four (D : Finset (Site 2)) (P : OneSet D) :
    4 ≤ (Finset.univ.filter fun e : PrimalCopy D P =>
      (primalGraph D P).left e = alpha D P ∨ (primalGraph D P).right e = alpha D P).card := by
  let star := Finset.univ.filter fun e : PrimalCopy D P =>
    (primalGraph D P).left e = alpha D P ∨ (primalGraph D P).right e = alpha D P
  have exits (e : ↥(latticeExits D)) : ∃ f : ↥star, f.val.val = e.val := by
    obtain h | h := (mem_latticeExits D e.val).mp e.property
    · have ha := project_ne_alpha_of_mem D P _ h.1
      have hb := (project_eq_alpha_iff D P _).mpr h.2
      let f : PrimalCopy D P := ⟨e.val, Finset.mem_filter.mpr
        ⟨(mem_domainCopies D _).mpr (Or.inl h.1), fun he => ha (he.trans hb)⟩⟩
      exact ⟨⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr hb⟩⟩, rfl⟩
    · have ha := (project_eq_alpha_iff D P _).mpr h.2
      have hb := project_ne_alpha_of_mem D P _ h.1
      let f : PrimalCopy D P := ⟨e.val, Finset.mem_filter.mpr
        ⟨(mem_domainCopies D _).mpr (Or.inr h.1), fun he => hb (he.symm.trans ha)⟩⟩
      exact ⟨⟨f, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ha⟩⟩, rfl⟩
  let f : ↥(latticeExits D) → ↥star := fun e => (exits e).choose
  have hf : Function.Injective f := by
    intro e g h
    apply Subtype.ext
    exact (exits e).choose_spec.symm.trans
      ((congrArg (fun z : ↥star => z.val.val) h).trans (exits g).choose_spec)
  have hcard := Fintype.card_le_of_injective f hf
  obtain ⟨p, _⟩ := P.property
  exact (latticeExits_card_ge_four D ⟨p.val, p.property⟩).trans
    (by simpa only [Fintype.card_coe] using hcard)

end
end FiniteAvalanches.Electrical.LatticeDrawing
