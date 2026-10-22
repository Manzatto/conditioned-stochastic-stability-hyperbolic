module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoisePseudoReferenceDerivatives
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoisePseudoReferenceForcing
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoisePseudoReferenceContinuity
public import LeanShared.Geometry.PseudoReferenceNonlinearBlocks
public import LeanShared.Geometry.PseudoReferenceForcing
public import LeanShared.Geometry.PseudoReferenceDecodeBounds
public import LeanShared.Dynamics.RandomHyperbolicCocyclePlaques

/-! Constructed random graph-transform data along EVERY sufficiently accurate
pseudo-reference orbit. Geometry, diagonal contraction, nonlinear/noisy errors,
forcing and joint continuity all come from actual hyperbolicity and Whitney
noise. The radius is fixed BEFORE its forcing and noise thresholds. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle NNReal
open LeanShared.FiniteJetComposition LeanShared.CenteredManifoldCoordinates
open LeanShared.PseudoReferenceCoordinateMaps LeanShared.HyperbolicBasicSet

set_option maxHeartbeats 3200000 in
theorem Maps.exists_pseudo_reference_plaques
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {r : ℝ} {Λ : Set M} {h : HyperbolicData (E := E) T Λ}
    (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (geometry : PseudoReferenceGeometry h) (a : IsometricFraming h)
    (cap : ℝ) (positiveCap : 0 < cap) :
    ∃ radius : ℝ, 0 < radius ∧ radius ≤ cap ∧
      (∀ x : Λ, ∀ z : EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension),
        ‖z‖ ≤ radius → chart geometry x x.val + linear geometry a.whole x z ∈ (chart geometry x).target) ∧
      ∃ tolerance : ℝ, 0 < tolerance ∧ ∃ window : ℝ≥0, 0 < window ∧
      ∀ ε : ℝ≥0, 0 < ε → ε ≤ window → ∀ reference : ℕ → Λ,
      (∀ n, dist ((T : M → M)^[geometry.blockLength] (reference (n + 1)).val)
        (reference n).val < tolerance) →
      ∃ d : LeanShared.RandomHyperbolicCocyclePlaques.Data (ℕ → cube (ι := ι) ε)
        (EuclideanSpace ℝ (Fin a.unstableDimension)) (EuclideanSpace ℝ (Fin a.stableDimension)),
        d.radius = radius ∧ (∀ n controls z, d.map n controls z =
          coordinate geometry a.whole (reference n)
            (word (fun j => F.family ε (controls j).val) geometry.blockLength
              (decode geometry a.whole (reference (n + 1)) z))) ∧
        ∀ n z, ‖z‖ ≤ radius → ∀ controls : ℕ → cube (ι := ι) ε,
          word (fun j => F.family ε (controls j).val) geometry.blockLength
            (decode geometry a.whole (reference (n + 1)) z) ∈ (chart geometry (reference n)).source := by
  obtain ⟨B,positiveB,bounds⟩ := a.exists_uniform_bound
  obtain ⟨detRadius,positiveDetRadius,detTolerance,positiveDetTolerance,detBlocks⟩ :=
    exists_nonlinear_blocks geometry a deterministic (1 / 32) (by norm_num)
  obtain ⟨noiseRadius,positiveNoiseRadius,noiseTolerance,positiveNoiseTolerance,derivativeWindow,
      positiveDerivativeWindow,derivatives⟩ := F.pseudo_reference_derivative_window regularity deterministic
    geometry a.whole positiveB bounds (1 / 32) (by norm_num)
  obtain ⟨continuousRadius,positiveContinuousRadius,continuousTolerance,positiveContinuousTolerance,
      continuousWindow,positiveContinuousWindow,continuity⟩ :=
    F.pseudo_reference_continuity_window geometry a.whole positiveB bounds
  obtain ⟨decodeRadius,positiveDecodeRadius,decodes⟩ := exists_decode_radius geometry a.whole
    positiveB bounds 1 zero_lt_one
  let radius := min cap (min detRadius (min noiseRadius (min continuousRadius decodeRadius)))
  have positiveRadius : 0 < radius := lt_min positiveCap (lt_min positiveDetRadius
    (lt_min positiveNoiseRadius (lt_min positiveContinuousRadius positiveDecodeRadius)))
  have radiusDet : radius ≤ detRadius := (min_le_right _ _).trans (min_le_left _ _)
  have radiusNoise : radius ≤ noiseRadius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have radiusContinuous : radius ≤ continuousRadius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have radiusDecode : radius ≤ decodeRadius :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨forceTolerance,positiveForceTolerance,detForcing⟩ := exists_forcing_window geometry a.whole
    positiveB bounds ((T : M → M)^[geometry.blockLength]) (radius / 8) (by positivity)
  obtain ⟨noiseForceTolerance,positiveNoiseForceTolerance,forceWindow,positiveForceWindow,noiseForcing⟩ :=
    F.pseudo_reference_noise_forcing_window regularity deterministic geometry a.whole positiveB bounds
      (radius / 8) (by positivity)
  let tolerance := min detTolerance (min noiseTolerance
    (min continuousTolerance (min forceTolerance noiseForceTolerance)))
  have positiveTolerance : 0 < tolerance := lt_min positiveDetTolerance (lt_min positiveNoiseTolerance
    (lt_min positiveContinuousTolerance (lt_min positiveForceTolerance positiveNoiseForceTolerance)))
  have toleranceDet : tolerance ≤ detTolerance := min_le_left _ _
  have toleranceNoise : tolerance ≤ noiseTolerance := (min_le_right _ _).trans (min_le_left _ _)
  have toleranceContinuous : tolerance ≤ continuousTolerance :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have toleranceForce : tolerance ≤ forceTolerance :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have toleranceNoiseForce : tolerance ≤ noiseForceTolerance :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨radius,positiveRadius,min_le_left _ _,fun x z hz => (decodes x z (hz.trans radiusDecode)).1,
    tolerance,positiveTolerance,min derivativeWindow (min continuousWindow forceWindow),
    lt_min positiveDerivativeWindow (lt_min positiveContinuousWindow positiveForceWindow),
    fun ε hp hw reference step => ?_⟩
  have smallDerivative : ε ≤ derivativeWindow := hw.trans (min_le_left _ _)
  have smallContinuous : ε ≤ continuousWindow := hw.trans ((min_le_right _ _).trans (min_le_left _ _))
  have smallForce : ε ≤ forceWindow := hw.trans ((min_le_right _ _).trans (min_le_right _ _))
  have deterministicPairs (n : ℕ) := detBlocks (reference (n + 1)) (reference n)
    (by simpa only [LeanShared.DiffeomorphismIterates.coe_pow] using (step n).trans_le toleranceDet)
  choose contracting expanding stableBound inverseBound detEstimates using deterministicPairs
  let maps := fun n (controls : ℕ → cube (ι := ι) ε) =>
    centered (linear geometry a.whole (reference (n + 1))) (linear geometry a.whole (reference n))
      (chart geometry (reference (n + 1)) (reference (n + 1)).val)
      (chart geometry (reference n) (reference n).val)
      (chart geometry (reference n) ∘ word (fun j => F.family ε (controls j).val) geometry.blockLength ∘
        (chart geometry (reference (n + 1))).symm)
  let deterministicMaps := fun n =>
    centered (linear geometry a.whole (reference (n + 1))) (linear geometry a.whole (reference n))
      (chart geometry (reference (n + 1)) (reference (n + 1)).val)
      (chart geometry (reference n) (reference n).val)
      (chart geometry (reference n) ∘ (T : M → M)^[geometry.blockLength] ∘
        (chart geometry (reference (n + 1))).symm)
  have zeroBound (n : ℕ) (controls : ℕ → cube (ι := ι) ε) : ‖maps n controls 0‖ ≤ radius / 4 := by
    have noisy := noiseForcing ε hp smallForce _ _ ((step n).trans_le toleranceNoiseForce) controls
    have deterministicBound := (detForcing _ _ ((step n).trans_le toleranceForce)).2
    change ‖maps n controls 0 - deterministicMaps n 0‖ ≤ radius / 8 at noisy
    change ‖deterministicMaps n 0‖ ≤ radius / 8 at deterministicBound
    have triangle := norm_add_le (maps n controls 0 - deterministicMaps n 0) (deterministicMaps n 0)
    rw [sub_add_cancel] at triangle
    linarith
  have differentiate (n : ℕ) (controls : ℕ → cube (ι := ι) ε)
      (z : EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension))
      (hz : ‖z‖ ≤ radius) : DifferentiableAt ℝ (maps n controls) z :=
    (derivatives ε hp smallDerivative _ _ ((step n).trans_le toleranceNoise) controls z (hz.trans radiusNoise)).1
  have derivative (n : ℕ) (controls : ℕ → cube (ι := ι) ε)
      (z : EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension))
      (hz : ‖z‖ ≤ radius) :
      ‖fderiv ℝ (maps n controls) z - (expanding n).toContinuousLinearMap.prodMap
        (contracting n).toContinuousLinearMap‖ ≤ 1 / 8 := by
    have noisy := (derivatives ε hp smallDerivative _ _ ((step n).trans_le toleranceNoise)
      controls z (hz.trans radiusNoise)).2
    have deterministicBound := (detEstimates n z (hz.trans radiusDet)).2.2.2
    simp only [LeanShared.DiffeomorphismIterates.coe_pow] at deterministicBound
    change ‖fderiv ℝ (maps n controls) z - fderiv ℝ (deterministicMaps n) z‖ ≤ 1 / 32 at noisy
    change ‖fderiv ℝ (deterministicMaps n) z - (expanding n).toContinuousLinearMap.prodMap
      (contracting n).toContinuousLinearMap‖ ≤ 1 / 32 at deterministicBound
    exact (norm_sub_le_norm_sub_add_norm_sub _ (fderiv ℝ (deterministicMaps n) z) _).trans (by linarith)
  have parameterContinuous (n : ℕ) : ContinuousOn
      (fun p : (ℕ → cube (ι := ι) ε) ×
        (EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension)) => maps n p.1 p.2)
      (univ ×ˢ Metric.closedBall 0 radius) := by
    apply ((continuity ε hp smallContinuous _ _ ((step n).trans_le toleranceContinuous)).2).mono
    intro p hp'
    refine ⟨hp'.1,?_⟩
    have hz : ‖p.2‖ ≤ radius := by simpa only [Metric.mem_closedBall,dist_zero_right] using hp'.2
    simpa only [Metric.mem_closedBall,dist_zero_right] using hz.trans radiusContinuous
  let d : LeanShared.RandomHyperbolicCocyclePlaques.Data (ℕ → cube (ι := ι) ε)
      (EuclideanSpace ℝ (Fin a.unstableDimension)) (EuclideanSpace ℝ (Fin a.stableDimension)) := {
    map := maps
    expanding := expanding
    contracting := fun n => (contracting n).toContinuousLinearMap
    k := ⟨1 / 4,by norm_num⟩
    δ := ⟨1 / 8,by norm_num⟩
    small := by change (1 / 4 : ℝ) + (1 / 8) * 2 < 1; norm_num
    inverse_bound := inverseBound
    stable_bound := stableBound
    radius := radius
    radius_positive := positiveRadius
    differentiable := differentiate
    derivative_bound := derivative
    zero_bound := radius / 4
    map_zero_bound := zeroBound
    forcing := by change (1 / 4 + 1 : ℝ) * (radius / 4) < (1 - (1 / 4 + 1 / 8 * 2)) * radius; nlinarith
    continuous := parameterContinuous }
  exact ⟨d,rfl,(fun _ _ _ => rfl),fun n z hz controls =>
    ((continuity ε hp smallContinuous _ _ ((step n).trans_le toleranceContinuous)).1 z
      (hz.trans radiusContinuous)).2 controls⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
