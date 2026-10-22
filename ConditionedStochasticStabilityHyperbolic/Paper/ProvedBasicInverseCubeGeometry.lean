module
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedInversePseudoReferenceCapture
public import ConditionedStochasticStabilityHyperbolic.Paper.InverseCubeGeometry
public import LeanShared.Dynamics.ReversedHyperbolicBasicData

/-! The full inverse cube geometry is constructed from the ORIGINAL noise
family and actual basic hyperbolicity. Joint inverse calculus, random plaques,
lower semicontinuity and finite capture are all proved outputs. The controls,
noise scale and driving laws have not been reparametrized. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold Bundle Filter
open scoped Topology Manifold ContDiff Bundle NNReal
open LeanShared.HyperbolicBasicSet

set_option maxHeartbeats 3200000 in
theorem InverseFamily.eventually_basic_inverse_geometry
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ,E)) ∞ M] [Fintype ι]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ,E)) x)]
    {T : M ≃ₜ M} {r : ℝ} {Λ V₀ V K G : Set M}
    {F : Maps (E := E) (ι := ι) T r} (J : InverseFamily F) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) 1 T.symm)
    (basic : BasicData (E := E) T Λ V₀)
    (compactK : IsCompact K) (core : LeanShared.isolatedCore T K ⊆ Λ)
    (openV : IsOpen V) (insideK : V ⊆ K) (containsV : Λ ⊆ V)
    (openG : IsOpen G) (containsG : Λ ⊆ G) :
    ∃ window : ℝ≥0, 0 < window ∧ window ≤ J.window ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ window →
      ∃ d : InverseCubeGeometry F ε V G, d.map = J.map ε := by
  have forwardD := deterministic.mdifferentiable (by norm_num)
  have inverseD := inverse.mdifferentiable (by norm_num)
  let reversed := basic.reversed forwardD inverseD
  obtain ⟨geometry⟩ := reversed.hyperbolic.exists_pseudo_reference_geometry inverseD forwardD
  obtain ⟨a⟩ := reversed.exists_isometricFraming inverseD forwardD
  have coreReverse : LeanShared.isolatedCore T.symm K ⊆ Λ := by
    simpa only [LeanShared.ReversibleTransitivity.isolatedCore_symm] using core
  obtain ⟨wp,positiveP,plaques⟩ := J.exists_constructed_capturing_plaques regularity deterministic inverse
    geometry a compactK coreReverse reversed.hyperbolic.compact
    (fun x hx => reversed.hyperbolic.invariant ▸ mem_image_of_mem T.symm hx)
    (openV.inter openG) (fun x hx => ⟨containsV hx,containsG hx⟩)
  obtain ⟨wd,positiveD,differentials⟩ := F.exists_global_differential_window regularity deterministic inverseD
  refine ⟨min J.window (min wp wd),lt_min J.positive (lt_min positiveP positiveD),min_le_left _ _,
    fun ε hp hw => ?_⟩
  have smallJ := hw.trans (min_le_left _ _)
  have smallP := hw.trans ((min_le_right _ _).trans (min_le_left _ _))
  have smallD := hw.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨plaque,lower,backward,capture⟩ := plaques ε hp smallP
  refine ⟨{
    map := J.map ε
    joint := ⟨J.domain ε,J.open_domain ε,J.contains ε hp smallJ,J.smooth ε hp smallJ⟩
    identity := ?_
    spatial := fun control y => (differentials ε hp smallD control _).1
    plaque := plaque
    lower_semicontinuous := lower
    backward_orbit := backward
    capture := ?_ },rfl⟩
  · intro control y
    have near : ∀ᶠ z in 𝓝 control.val, z ∈ J.domain ε :=
      (J.open_domain ε).mem_nhds (J.contains ε hp smallJ control.property)
    exact near.mono (fun z hz => J.right ε hp smallJ z hz y)
  · intro path b inside step _eventuallyG
    exact capture path b (fun n => insideK (inside n)) step

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
