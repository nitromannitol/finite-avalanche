import FiniteAvalanches.Trees.RootedForests
import FiniteAvalanches.Model.FiniteWired
import FiniteAvalanches.Electrical.Plane.TerminalEnumeration

/-! Literal copied edges of a finite lattice domain with two contracted terminals.
The free incidence order uses the physical clockwise lattice directions. -/

namespace FiniteAvalanches.Electrical.Plane.SourceLattice

open LatticeProb
open FiniteAvalanches.Sandpile.FiniteWired (Direction step)
open scoped Classical
noncomputable section

/-- Positive-coordinate orientation gives each physical lattice edge one ID. -/
abbrev OriginalCopy := Site 2 × Fin 2

def originalA (e : OriginalCopy) : Site 2 := e.1
def originalB (e : OriginalCopy) : Site 2 := e.1 + unit e.2

/-- The original edge ID incident to x in a specified physical direction. -/
def incidentID (x : Site 2) (d : Direction) : OriginalCopy :=
  (if d.2 then x else x - unit d.1, d.1)

def originalDart (x : Site 2) (d : Direction) : Dart OriginalCopy :=
  (incidentID x d, !d.2)

@[simp] theorem originalDart_tail (x : Site 2) (d : Direction) :
    tail originalA originalB (originalDart x d) = x := by
  rcases d with ⟨i,b⟩
  cases b <;> simp [originalDart, incidentID, tail, originalA, originalB]

@[simp] theorem originalDart_head (x : Site 2) (d : Direction) :
    head originalA originalB (originalDart x d) = x + step d := by
  rcases d with ⟨i,b⟩
  cases b <;> simp [originalDart, incidentID, head, reverse, tail,
    originalA, originalB, step, sub_eq_add_neg]

/-- All original copies incident to D; there is no voltage-dependent deletion. -/
def domainCopies (D : Finset (Site 2)) : Finset OriginalCopy :=
  (D ×ˢ (Finset.univ : Finset Direction)).image (fun xd => incidentID xd.1 xd.2)

theorem mem_domainCopies (D : Finset (Site 2)) (e : OriginalCopy) :
    e ∈ domainCopies D ↔ originalA e ∈ D ∨ originalB e ∈ D := by
  constructor
  · intro h
    obtain ⟨⟨x,⟨i,b⟩⟩,hx,he⟩ := Finset.mem_image.mp h
    have hD := (Finset.mem_product.mp hx).1
    cases b
    · right
      rw [← he]
      simpa [incidentID, originalB] using hD
    · left
      rw [← he]
      simpa [incidentID, originalA] using hD
  · intro h
    rcases h with h | h
    · apply Finset.mem_image.mpr
      exact ⟨(originalA e,(e.2,true)), Finset.mem_product.mpr ⟨h,Finset.mem_univ _⟩,
        by rcases e with ⟨x,i⟩; rfl⟩
    · apply Finset.mem_image.mpr
      refine ⟨(originalB e,(e.2,false)), Finset.mem_product.mpr ⟨h,Finset.mem_univ _⟩, ?_⟩
      rcases e with ⟨x,i⟩
      simp [incidentID, originalB]

abbrev OneSet (D : Finset (Site 2)) := {P : Finset D // P.Nonempty}

variable (D : Finset (Site 2)) (P : OneSet D)

/-- Zero and one are distinct terminals; the other vertices are exactly D minus P. -/
abbrev Vertex := Bool ⊕ {x : D // x ∉ P.val}

def alpha : Vertex D P := .inl false
def beta : Vertex D P := .inl true

def project (x : Site 2) : Vertex D P :=
  if hx : x ∈ D then
    if hp : (⟨x,hx⟩ : D) ∈ P.val then .inl true else .inr ⟨⟨x,hx⟩,hp⟩
  else .inl false

@[simp] theorem project_free (x : {x : D // x ∉ P.val}) :
    project D P x.val.val = .inr x := by
  simp [project, x.val.property, x.property]

theorem project_eq_free_iff (x : {x : D // x ∉ P.val}) (y : Site 2) :
    project D P y = .inr x ↔ y = x.val.val := by
  constructor
  · intro h
    unfold project at h
    split at h
    · split at h
      · cases h
      · exact congrArg (fun z : {x : D // x ∉ P.val} => z.val.val) (Sum.inr.inj h)
    · cases h
  · rintro rfl
    exact project_free D P x

theorem project_eq_alpha_iff (x : Site 2) :
    project D P x = alpha D P ↔ x ∉ D := by
  by_cases hx : x ∈ D
  · simp only [project,dif_pos hx,alpha]
    split <;> simp [hx]
  · simp [project,hx,alpha]

theorem project_eq_beta_iff (x : Site 2) :
    project D P x = beta D P ↔ x ∈ P.val.image Subtype.val := by
  constructor
  · intro h
    unfold project at h
    split at h
    · rename_i hx
      split at h
      · rename_i hp
        exact Finset.mem_image.mpr ⟨⟨x,hx⟩,hp,rfl⟩
      · cases h
    · cases h
  · intro h
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp h
    simp [project,y.property,hy,beta]

/-- The distinguished copy really joins the zero set to the one set. -/
abbrev MarkedCopy := {e : OriginalCopy //
  (project D P (originalA e) = alpha D P ∧ project D P (originalB e) = beta D P) ∨
  (project D P (originalA e) = beta D P ∧ project D P (originalB e) = alpha D P)}

/-- Delete exactly the distinguished ID and the copies whose endpoints become equal. -/
def retainedCopies (marked : MarkedCopy D P) : Finset OriginalCopy :=
  (domainCopies D).filter (fun e =>
    project D P (originalA e) ≠ project D P (originalB e) ∧ e ≠ marked.val)

abbrev Copy (marked : MarkedCopy D P) := ↥(retainedCopies D P marked)

def copyA (marked : MarkedCopy D P) (e : Copy D P marked) : Vertex D P :=
  project D P (originalA e.val)

def copyB (marked : MarkedCopy D P) (e : Copy D P marked) : Vertex D P :=
  project D P (originalB e.val)

theorem mem_retainedCopies (marked : MarkedCopy D P) (e : OriginalCopy) :
    e ∈ retainedCopies D P marked ↔
    (originalA e ∈ D ∨ originalB e ∈ D) ∧
      project D P (originalA e) ≠ project D P (originalB e) ∧ e ≠ marked.val := by
  simp only [retainedCopies, Finset.mem_filter, mem_domainCopies]

theorem copy_loopless (marked : MarkedCopy D P) (e : Copy D P marked) :
    copyA D P marked e ≠ copyB D P marked e :=
  (Finset.mem_filter.mp e.property).2.1

/-- The physical clockwise order is east, south, west, north. -/
def clockwise (d : Direction) : Direction :=
  if d.1 = 0 then (1, !d.2) else (0,d.2)

def counterclockwise (d : Direction) : Direction :=
  if d.1 = 0 then (1,d.2) else (0,!d.2)

def clockwisePerm : Equiv.Perm Direction where
  toFun := clockwise
  invFun := counterclockwise
  left_inv d := by rcases d with ⟨i,b⟩; fin_cases i <;> cases b <;> rfl
  right_inv d := by rcases d with ⟨i,b⟩; fin_cases i <;> cases b <;> rfl

theorem original_endpoints_ne (e : OriginalCopy) : originalA e ≠ originalB e := by
  intro h
  have hi := congrFun h e.2
  simp [originalA, originalB, unit] at hi

theorem free_incident_survives (marked : MarkedCopy D P)
    (x : {x : D // x ∉ P.val}) (e : OriginalCopy)
    (he : originalA e = x.val.val ∨ originalB e = x.val.val) :
    project D P (originalA e) ≠ project D P (originalB e) ∧ e ≠ marked.val := by
  constructor
  · intro h
    rcases he with he | he
    · rw [he, project_free] at h
      have hb := (project_eq_free_iff D P x _).mp h.symm
      exact original_endpoints_ne e (he.trans hb.symm)
    · rw [he, project_free] at h
      have ha := (project_eq_free_iff D P x _).mp h
      exact original_endpoints_ne e (ha.trans he.symm)
  · intro h
    subst e
    rcases marked.property with ⟨ha,hb⟩ | ⟨ha,hb⟩
    all_goals rcases he with he | he
    · rw [he, project_free] at ha; cases ha
    · rw [he, project_free] at hb; cases hb
    · rw [he, project_free] at ha; cases ha
    · rw [he, project_free] at hb; cases hb

theorem incidentID_retained (marked : MarkedCopy D P)
    (x : {x : D // x ∉ P.val}) (d : Direction) :
    incidentID x.val.val d ∈ retainedCopies D P marked := by
  have he : originalA (incidentID x.val.val d) = x.val.val ∨
      originalB (incidentID x.val.val d) = x.val.val := by
    rcases d with ⟨i,b⟩
    cases b
    · right; simp [incidentID,originalB]
    · left; rfl
  apply (mem_retainedCopies D P marked _).mpr
  refine ⟨?_, free_incident_survives D P marked x _ he⟩
  rcases he with he | he
  · left; rw [he]; exact x.val.property
  · right; rw [he]; exact x.val.property

/-- The actual copied outgoing dart at a free site; its original ID is preserved. -/
def freeDart (marked : MarkedCopy D P) (x : {x : D // x ∉ P.val}) (d : Direction) :
    Dart (Copy D P marked) :=
  (⟨incidentID x.val.val d, incidentID_retained D P marked x d⟩, !d.2)

@[simp] theorem freeDart_original (marked : MarkedCopy D P)
    (x : {x : D // x ∉ P.val}) (d : Direction) :
    ((freeDart D P marked x d).1.val, (freeDart D P marked x d).2) =
      originalDart x.val.val d := rfl

theorem copy_tail_project (marked : MarkedCopy D P) (d : Dart (Copy D P marked)) :
    tail (copyA D P marked) (copyB D P marked) d =
      project D P (tail originalA originalB (d.1.val,d.2)) := by
  rcases d with ⟨e,b⟩
  cases b <;> rfl

@[simp] theorem freeDart_tail (marked : MarkedCopy D P)
    (x : {x : D // x ∉ P.val}) (d : Direction) :
    tail (copyA D P marked) (copyB D P marked) (freeDart D P marked x d) = .inr x := by
  rw [copy_tail_project, freeDart_original, originalDart_tail, project_free]

@[simp] theorem freeDart_head (marked : MarkedCopy D P)
    (x : {x : D // x ∉ P.val}) (d : Direction) :
    head (copyA D P marked) (copyB D P marked) (freeDart D P marked x d) =
      project D P (x.val.val + step d) := by
  rcases d with ⟨i,b⟩
  cases b <;> simp [freeDart, head, reverse, tail, copyA, copyB,
    incidentID,originalA,originalB,step,sub_eq_add_neg]

theorem originalDart_injective (x : Site 2) : Function.Injective (originalDart x) := by
  intro d d' h
  have hi := congrArg (fun z : Dart OriginalCopy => (z.1.2,!z.2)) h
  simpa [originalDart, incidentID] using hi

theorem originalDart_reconstruct (d : Dart OriginalCopy) :
    originalDart (tail originalA originalB d) (d.1.2,!d.2) = d := by
  rcases d with ⟨⟨x,i⟩,b⟩
  cases b <;> simp [originalDart, incidentID, tail, originalA,originalB]

/-- Physical clockwise successor on the full lattice's original copied darts. -/
def latticeNext (d : Dart OriginalCopy) : Dart OriginalCopy :=
  originalDart (tail originalA originalB d) (clockwise (d.1.2,!d.2))

@[simp] theorem latticeNext_originalDart (x : Site 2) (d : Direction) :
    latticeNext (originalDart x d) = originalDart x (clockwise d) := by
  unfold latticeNext
  rw [originalDart_tail]
  simp only [originalDart,incidentID,Bool.not_not]

/-- The full four-direction incidence equivalence, including parallel neighbor images. -/
def freeIncidenceEquiv (marked : MarkedCopy D P) (x : {x : D // x ∉ P.val}) :
    Direction ≃ Incidences (copyA D P marked) (copyB D P marked) (.inr x) :=
  Equiv.ofBijective (fun d => ⟨freeDart D P marked x d, freeDart_tail D P marked x d⟩) (by
    constructor
    · intro d d' h
      apply originalDart_injective x.val.val
      exact congrArg (fun z : Incidences (copyA D P marked) (copyB D P marked) (.inr x) =>
        (z.val.1.val,z.val.2)) h
    · intro d
      have ht : tail originalA originalB (d.val.1.val,d.val.2) = x.val.val := by
        apply (project_eq_free_iff D P x _).mp
        rw [← copy_tail_project]
        exact d.property
      refine ⟨(d.val.1.val.2,!d.val.2), ?_⟩
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        have hh := congrArg Prod.fst (originalDart_reconstruct (d.val.1.val,d.val.2))
        rw [ht] at hh
        exact hh
      · simp [freeDart])

/-- Clockwise successor on the exact post-contraction free incidence fiber. -/
def freeClockwise (marked : MarkedCopy D P) (x : {x : D // x ∉ P.val}) :
    Equiv.Perm (Incidences (copyA D P marked) (copyB D P marked) (.inr x)) :=
  ((freeIncidenceEquiv D P marked x).symm.trans clockwisePerm).trans
    (freeIncidenceEquiv D P marked x)

theorem freeClockwise_original (marked : MarkedCopy D P)
    (x : {x : D // x ∉ P.val}) (d : Direction) :
    (freeClockwise D P marked x (freeIncidenceEquiv D P marked x d)).val =
      freeDart D P marked x (clockwise d) := by
  simp only [freeClockwise,Equiv.trans_apply,Equiv.symm_apply_apply]
  rfl

/-- Contraction and deletion retain the literal physical successor at every free vertex. -/
theorem freeClockwise_transport (marked : MarkedCopy D P)
    (x : {x : D // x ∉ P.val})
    (d : Incidences (copyA D P marked) (copyB D P marked) (.inr x)) :
    ((freeClockwise D P marked x d).val.1.val,(freeClockwise D P marked x d).val.2) =
      latticeNext (d.val.1.val,d.val.2) := by
  obtain ⟨c,rfl⟩ := (freeIncidenceEquiv D P marked x).surjective d
  rw [freeClockwise_original]
  change originalDart x.val.val (clockwise c) = latticeNext (originalDart x.val.val c)
  exact (latticeNext_originalDart x.val.val c).symm

theorem free_incidenceCount (marked : MarkedCopy D P) (x : {x : D // x ∉ P.val}) :
    incidenceCount (copyA D P marked) (copyB D P marked) (.inr x) = 4 := by
  classical
  letI : DecidableEq (Vertex D P) := Classical.decEq _
  unfold incidenceCount
  have h := Fintype.card_congr (freeIncidenceEquiv D P marked x)
  simpa [Direction] using h.symm

/-- The source degree bound counts each original edge copy once. -/
theorem free_degree (marked : MarkedCopy D P) (x : {x : D // x ∉ P.val}) :
    Geometry.degree (copyA D P marked) (copyB D P marked) (.inr x) = 4 := by
  rw [← incidenceCount_eq_degree, free_incidenceCount]
  norm_num

theorem source_free_degree_bound (marked : MarkedCopy D P) (x : Vertex D P)
    (ha : x ≠ alpha D P) (hb : x ≠ beta D P) :
    Geometry.degree (copyA D P marked) (copyB D P marked) x ≤ 4 := by
  cases x with
  | inl b => cases b
             · exact (ha rfl).elim
             · exact (hb rfl).elim
  | inr x => exact (free_degree D P marked x).le

theorem clockwise_reaches (d d' : Direction) :
    ∃ n : ℕ, n < 4 ∧ (clockwisePerm ^ n) d = d' := by
  rcases d with ⟨i,b⟩
  rcases d' with ⟨j,c⟩
  fin_cases i <;> fin_cases j <;> cases b <;> cases c
  all_goals first
    | exact ⟨0, by decide, rfl⟩
    | exact ⟨1, by decide, rfl⟩
    | exact ⟨2, by decide, rfl⟩
    | exact ⟨3, by decide, rfl⟩

theorem freeClockwise_pow (marked : MarkedCopy D P) (x : {x : D // x ∉ P.val})
    (n : ℕ) (d : Direction) :
    (freeClockwise D P marked x ^ n) (freeIncidenceEquiv D P marked x d) =
      freeIncidenceEquiv D P marked x ((clockwisePerm ^ n) d) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]
    simp [freeClockwise, Equiv.trans_apply]

/-- Every surviving free incidence lies on this one physical clockwise cycle. -/
theorem freeClockwise_cyclic (marked : MarkedCopy D P) (x : {x : D // x ∉ P.val})
    (d d' : Incidences (copyA D P marked) (copyB D P marked) (.inr x)) :
    (freeClockwise D P marked x).SameCycle d d' := by
  obtain ⟨a,rfl⟩ := (freeIncidenceEquiv D P marked x).surjective d
  obtain ⟨b,rfl⟩ := (freeIncidenceEquiv D P marked x).surjective d'
  obtain ⟨n,_,hn⟩ := clockwise_reaches a b
  have h := freeClockwise_pow D P marked x n a
  rw [hn] at h
  rw [← h]
  simpa only [Equiv.Perm.sameCycle_pow_right] using
    Equiv.Perm.SameCycle.refl (freeClockwise D P marked x) (freeIncidenceEquiv D P marked x a)

/-- Coincident contracted neighbors cannot identify distinct physical copied darts. -/
theorem parallel_free_copies (marked : MarkedCopy D P) (x : {x : D // x ∉ P.val})
    (d d' : Direction) (hne : d ≠ d')
    (hh : project D P (x.val.val + step d) = project D P (x.val.val + step d')) :
    freeDart D P marked x d ≠ freeDart D P marked x d' ∧
      head (copyA D P marked) (copyB D P marked) (freeDart D P marked x d) =
        head (copyA D P marked) (copyB D P marked) (freeDart D P marked x d') := by
  constructor
  · intro h
    apply hne
    apply (freeIncidenceEquiv D P marked x).injective
    exact Subtype.ext h
  · simpa only [freeDart_head] using hh

theorem root_copy_retained (marked : MarkedCopy D P) (e : OriginalCopy)
    (hd : originalA e ∈ D ∨ originalB e ∈ D) (hne : e ≠ marked.val)
    (ha : project D P (originalA e) = alpha D P)
    (hb : project D P (originalB e) = beta D P) :
    e ∈ retainedCopies D P marked := by
  apply (mem_retainedCopies D P marked e).mpr
  refine ⟨hd, ?_, hne⟩
  rw [ha,hb]
  intro h
  cases h

namespace SquareConsumer

def xy (x y : ℤ) : Site 2 := fun i => if i = 0 then x else y

def domain : Finset (Site 2) := {xy 0 0, xy 0 1, xy 1 0, xy 1 1}

/-- The two vertices in the left column are the one terminal. -/
def one : OneSet domain :=
  ⟨Finset.univ.filter (fun x => x.val 0 = 0), by
    refine ⟨⟨xy 0 0,by simp [domain]⟩,?_⟩
    simp [xy]⟩

def lower : {x : domain // x ∉ one.val} :=
  ⟨⟨xy 1 0, by simp [domain]⟩,by simp [one,xy]⟩

def upper : {x : domain // x ∉ one.val} :=
  ⟨⟨xy 1 1, by simp [domain]⟩,by simp [one,xy]⟩

/-- The single deleted copy goes from (0,-1) to (0,0). -/
def marked : MarkedCopy domain one :=
  ⟨(xy 0 (-1),1),by
    left
    constructor
    · simp [project,alpha,domain,originalA,xy,funext_iff,Fin.forall_fin_two]
    · have he : originalB (xy 0 (-1),1) = xy 0 0 := by
        ext i
        fin_cases i <;> norm_num [originalB,xy,unit]
      rw [he]
      unfold project
      rw [dif_pos (by simp [domain])]
      rw [dif_pos (by simp only [one,Finset.mem_filter,Finset.mem_univ,true_and]; rfl)]
      rfl⟩

/-- Two different original copies reach the same zero terminal after contraction. -/
theorem east_south_parallel :
    (freeDart domain one marked lower (0,true)).1 ≠
      (freeDart domain one marked lower (1,false)).1 ∧
    head (copyA domain one marked) (copyB domain one marked)
      (freeDart domain one marked lower (0,true)) = alpha domain one ∧
    head (copyA domain one marked) (copyB domain one marked)
      (freeDart domain one marked lower (1,false)) = alpha domain one := by
  constructor
  · intro h
    have he := congrArg (fun e : Copy domain one marked => e.val.2) h
    norm_num [freeDart,incidentID] at he
  · constructor <;>
      simp [freeDart_head,project,lower,alpha,domain,one,xy,step,unit,
        funext_iff,Fin.forall_fin_two] <;> rfl

def potential (x : Vertex domain one) : ℝ :=
  match x with
  | .inl false => 0
  | .inl true => 1
  | .inr _ => 1/3

/-- The vertical free-to-free copy survives, even when its current is zero. -/
theorem zero_current_copy :
    head (copyA domain one marked) (copyB domain one marked)
      (freeDart domain one marked lower (1,true)) = .inr upper ∧
    current (copyA domain one marked) (copyB domain one marked) potential
      (freeDart domain one marked lower (1,true)) = 0 := by
  have h : head (copyA domain one marked) (copyB domain one marked)
      (freeDart domain one marked lower (1,true)) = .inr upper := by
    rw [freeDart_head]
    have he : lower.val.val + step (1,true) = upper.val.val := by
      ext i
      fin_cases i <;> norm_num [lower,upper,xy,step,unit]
    rw [he,project_free]
  refine ⟨h,?_⟩
  simp [current,freeDart_tail,h,potential]

theorem four_copied_incidents :
    incidenceCount (copyA domain one marked) (copyB domain one marked) (.inr lower) = 4 ∧
      Geometry.degree (copyA domain one marked) (copyB domain one marked) (.inr lower) = 4 :=
  ⟨free_incidenceCount domain one marked lower,free_degree domain one marked lower⟩

end SquareConsumer

end
end FiniteAvalanches.Electrical.Plane.SourceLattice

namespace FiniteAvalanches.Electrical.Plane.SourceLattice.StatementTypes
open LatticeProb
open scoped Classical BigOperators
noncomputable section

/-- The actual copied source multigraph, with its proved looplessness. -/
def graph (D : Finset (Site 2)) (P : OneSet D) (marked : MarkedCopy D P) :
    Trees.Multigraph (Vertex D P) (Copy D P marked) :=
  ⟨copyA D P marked,copyB D P marked,copy_loopless D P marked⟩

-- Literal uniform averages over the actual rooted-forest sample carrier.
-- No theorem, axiom, measure replacement or second-moment premise is installed.
#check (∃ C : ℝ, ∀ (D : Finset (Site 2)) (P : OneSet D)
  (_hD : ((lattice 2).induce (↑D : Set (Site 2))).Connected)
  (_hDc : ((lattice 2).induce (↑D : Set (Site 2))ᶜ).Connected)
  (_hP : ((lattice 2).induce (↑(P.val.image Subtype.val) : Set (Site 2))).Connected)
  (marked : MarkedCopy D P) (phi : Vertex D P → ℝ)
  (_hp0 : phi (alpha D P) = 0) (_hp1 : phi (beta D P) = 1)
  (_hh : ∀ x, x ≠ alpha D P → x ≠ beta D P →
    laplacian (copyA D P marked) (copyB D P marked) phi x = 0),
  let a := copyA D P marked
  let b := copyB D P marked
  let G := graph D P marked
  let F := G.RootedForest ({alpha D P,beta D P} : Set (Vertex D P))
  let Y : F → ℝ := fun f => ∑ z : Dart (Copy D P marked),
    if tail a b z = alpha D P ∧ G.reaches f.val (head a b z) (beta D P) then 1 else 0
  let mean := (∑ f : F, Y f) / (Fintype.card F : ℝ)
  let variance := (∑ f : F, (Y f - mean)^2) / (Fintype.card F : ℝ)
  let M := energy a b phi
  let m := ((domainCopies D).filter fun e =>
    (originalA e ∈ D ∧ originalB e ∉ D) ∨
    (originalB e ∈ D ∧ originalA e ∉ D)).card - 1
  mean = M ∧ variance ≤ C * M * (1 + Real.log ((m : ℝ) * min 1 M / M)) : Prop)

#print axioms graph
end
end FiniteAvalanches.Electrical.Plane.SourceLattice.StatementTypes
