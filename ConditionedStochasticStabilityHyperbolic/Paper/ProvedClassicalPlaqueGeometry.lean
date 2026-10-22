module
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedPseudoReferenceCapture
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoisePlaqueCover

/-! The forward random-plaque packet is constructed from literal smooth noise and compact hyperbolic
geometry. Rescaling controls preserves the exact original path, and does not require continuity
in scale. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle NNReal
open LeanShared.HyperbolicBasicSet LeanShared.ControlledPlaqueClosure

set_option maxHeartbeats 3200000 in
theorem Maps.eventually_classical_plaque_geometry
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {r : ℝ} {Λ V K G : Set M} {h : HyperbolicData (E := E) T Λ}
    (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (geometry : PseudoReferenceGeometry h) (a : IsometricFraming h)
    (compactK : IsCompact K) (core : LeanShared.isolatedCore T K ⊆ Λ)
    (compactΛ : IsCompact Λ) (invariant : MapsTo (T : M → M) Λ Λ)
    (openV : IsOpen V) (insideK : V ⊆ K) (containsV : Λ ⊆ V)
    (openG : IsOpen G) (containsG : Λ ⊆ G) :
    ∃ window : ℝ≥0, 0 < window ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ window →
      Nonempty (ClassicalPlaqueGeometry (fun p : M × FixedControl (ι := ι) => F.fixedMap ε p.1 p.2) V K G) := by
  obtain ⟨window,positiveWindow,make⟩ := F.exists_constructed_capturing_plaques regularity deterministic
    geometry a compactK core compactΛ invariant (openV.inter openG)
      (fun _ hx => ⟨containsV hx,containsG hx⟩)
  refine ⟨window,positiveWindow,fun ε hp hw => ?_⟩
  obtain ⟨raw,lower,backward,capture⟩ := make ε hp hw
  let e := LeanShared.NoiseCubeRescaling.rescale (ι := ι) (ε : ℝ) hp
  let pathMap : (ℤ → FixedControl (ι := ι)) → ℤ → cube (ι := ι) ε := fun path n => e (path n)
  have continuousPath : Continuous pathMap := continuous_pi fun n => e.continuous.comp (continuous_apply n)
  have identity (x : M) (z : FixedControl (ι := ι)) : F.fixedMap ε x z = F.family ε (e z).val x := by
    simp only [Maps.fixedMap, dite_eq_left hp, e]
  refine ⟨{ plaque := fun path => raw (pathMap path)
            lower_semicontinuous := ?_
            backward_orbit := ?_
            capture := ?_ }⟩
  · intro path paths limit x member
    obtain ⟨xn,converges,belongs⟩ := lower (pathMap path) (fun n => pathMap (paths n))
      ((continuousPath.tendsto path).comp limit) x member
    exact ⟨xn,converges,belongs⟩
  · intro path x member
    obtain ⟨b,initial,inside,step⟩ := backward (pathMap path) x member
    refine ⟨b,initial,inside,fun n => ?_⟩
    rw [identity]
    exact step n
  · intro path b inside step _eventuallyG
    have rawStep (n : ℕ) : F.family ε (backwardNoise (pathMap path) n).val (b (n + 1)) = b n := by
      have relation := step n
      change F.fixedMap ε (b (n + 1)) (backwardNoise path n) = b n at relation
      rw [identity] at relation
      exact relation
    obtain ⟨j,member⟩ := capture (pathMap path) b (fun n => insideK (inside n)) rawStep
    exact ⟨j,member⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
