import FiniteAvalanches.Wilson.Lattice.Sampler

/-! Every successful finite Wilson exploration is locally constant in its actual
walk increments. Thus its full history and every finite joint observation are
measurable before any law is selected or any recurrence input is trusted. -/
set_option autoImplicit false
namespace FiniteAvalanches.Wilson.Lattice
open LatticeProb FiniteAvalanches.Trees.Lattice MeasureTheory Filter
open scoped Classical
noncomputable section

theorem continuous_position (x : Site 2) (n : ℕ) :
    Continuous (fun w : WalkDriver => position x w n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact ih.add ((continuous_of_discreteTopology (f := FiniteAvalanches.Sandpile.FiniteWired.step)).comp
      (continuous_apply n))

theorem samplerStep_eq_of_positions (st : SamplerState) (x : Site 2)
    (w w' : WalkDriver) (T : ℕ) (hT : hitTime st.covered x w = some T)
    (hp : ∀ n ≤ T, position x w' n = position x w n) :
    samplerStep st x w' = samplerStep st x w := by
  have hT' : hitTime st.covered x w' = some T := by
    apply (hitTime_eq_some_iff _ _ _ _).mpr
    obtain ⟨hh, hf⟩ := (hitTime_eq_some_iff _ _ _ _).mp hT
    exact ⟨by rwa [hp T le_rfl], fun n hn => by
      rw [hp n (Nat.le_of_lt hn)]; exact hf n hn⟩
  have he : walkErase x w' T = walkErase x w T := by
    have hm : (List.range (T + 1)).map (position x w') =
        (List.range (T + 1)).map (position x w) :=
      List.map_congr_left (fun n hn => hp n (by
        have hn' : n < T + 1 := List.mem_range.mp hn
        omega))
    calc
      walkErase x w' T = ((List.range (T + 1)).map (position x w')).foldl eraseStep [] :=
        List.foldl_map.symm
      _ = ((List.range (T + 1)).map (position x w)).foldl eraseStep [] :=
        congrArg (fun l => l.foldl eraseStep []) hm
      _ = walkErase x w T := List.foldl_map
  have hw : dirWalkFinite x w' T = dirWalkFinite x w T := by
    unfold dirWalkFinite
    congr 1
    funext i
    exact hp i.val (by omega)
  simp only [samplerStep, hT, hT', he, hp T le_rfl, hw]

/-- No assumptions on termination: a given actual success has an open neighborhood
of drivers producing exactly the same complete state. -/
theorem samplerStep_eventually_eq_of_some (st out : SamplerState) (x : Site 2)
    (w : WalkDriver) (h : samplerStep st x w = some out) :
    ∀ᶠ w' in nhds w, samplerStep st x w' = some out := by
  by_cases hx : x ∈ st.covered
  · exact Eventually.of_forall (fun _ => by simpa [samplerStep, hx] using h)
  · cases hT : hitTime st.covered x w with
    | none => simp [samplerStep, hx, hT] at h
    | some T =>
      have hp : ∀ᶠ w' in nhds w, ∀ n : Fin (T + 1),
          position x w' n.val = position x w n.val :=
        eventually_all.mpr (fun n =>
          (continuous_position x n.val).continuousAt.eventually_mem
            ((isOpen_discrete ({position x w n.val} : Set (Site 2))).mem_nhds
              (Set.mem_singleton _)))
      filter_upwards [hp] with w' hw'
      exact (samplerStep_eq_of_positions st x w w' T hT
        (fun n hn => hw' ⟨n, Nat.lt_succ_of_le hn⟩)).trans h

/-- Repeated/covered queries and full stopped histories are retained exactly. -/
theorem samplerRun_eventually_eq_of_some (st out : SamplerState)
    (L : List (Site 2)) (ξ : ℕ → WalkDriver) (h : samplerRun st L ξ = some out) :
    ∀ᶠ ξ' in nhds ξ, samplerRun st L ξ' = some out := by
  induction L generalizing st out ξ with
  | nil => exact Eventually.of_forall (fun _ => h)
  | cons x xs ih =>
    cases hs : samplerStep st x (ξ 0) with
    | none => simp [samplerRun, hs] at h
    | some mid =>
      have ht : samplerRun mid xs (fun i => ξ (i + 1)) = some out := by
        simpa only [samplerRun, hs, Option.bind_some] using h
      have hhead := (continuous_apply 0 : Continuous (fun ζ : ℕ → WalkDriver => ζ 0)).continuousAt.eventually (samplerStep_eventually_eq_of_some st mid x (ξ 0) hs)
      have htail := (continuous_pi (fun i => continuous_apply (i + 1)) :
        Continuous (fun ζ : ℕ → WalkDriver => fun i => ζ (i + 1))).continuousAt.eventually
          (ih mid out (fun i => ξ (i + 1)) ht)
      filter_upwards [hhead, htail] with ξ' hh ht'
      simpa only [samplerRun, hh, Option.bind_some] using ht'

theorem isOpen_samplerEvent (R : RootPair) (L : List (Site 2)) (B : Finset LatticeEdge)
    (D : Finset (Site 2)) (pe : LatticeEdge → Bool) (pc : Site 2 → Bool) :
    IsOpen (samplerEvent R L B D pe pc) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro ξ ⟨st, hs, hb, hd⟩
  filter_upwards [samplerRun_eventually_eq_of_some _ st L ξ hs] with ξ' h'
  exact ⟨st, h', hb, hd⟩

theorem isOpen_sampler_success (st : SamplerState) (L : List (Site 2)) :
    IsOpen {ξ : ℕ → WalkDriver | ∃ out, samplerRun st L ξ = some out} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro ξ ⟨out, h⟩
  filter_upwards [samplerRun_eventually_eq_of_some st out L ξ h] with ξ' h'
  exact ⟨out, h'⟩

theorem measurableSet_samplerEvent (R : RootPair) (L : List (Site 2))
    (B : Finset LatticeEdge) (D : Finset (Site 2))
    (pe : LatticeEdge → Bool) (pc : Site 2 → Bool) :
    MeasurableSet (samplerEvent R L B D pe pc) :=
  (isOpen_samplerEvent R L B D pe pc).measurableSet

theorem measurableSet_sampler_success (st : SamplerState) (L : List (Site 2)) :
    MeasurableSet {ξ : ℕ → WalkDriver | ∃ out, samplerRun st L ξ = some out} :=
  (isOpen_sampler_success st L).measurableSet

end
end FiniteAvalanches.Wilson.Lattice
