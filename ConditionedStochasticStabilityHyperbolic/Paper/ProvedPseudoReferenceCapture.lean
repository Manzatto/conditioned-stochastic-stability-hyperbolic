module
public import ConditionedStochasticStabilityHyperbolic.Paper.ProvedPseudoReferenceManifoldPlaques
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseBackwardTailReference
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseFiniteCollarWindow
public import LeanShared.Geometry.PseudoReferenceCoordinateBounds
public import LeanShared.Geometry.PseudoReferenceDecodeBounds
public import LeanShared.Dynamics.ControlledBlockSampling
public import LeanShared.Dynamics.ControlledBlockPathContinuity

/-! Genuine finite capture for constructed random plaques. Approximate core
references are selected from an actual surviving backward orbit, rather than
assuming a deterministic reference or a plaque-capture conclusion. -/
public noncomputable section
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open Set Filter IsManifold Bundle
open scoped Topology Manifold ContDiff Bundle NNReal
open LeanShared.FiniteJetComposition LeanShared.PseudoReferenceCoordinateMaps
open LeanShared.HyperbolicBasicSet LeanShared.ControlledPlaqueClosure
open LeanShared.ControlledBlockUnrolling LeanShared.ControlledBlockSampling

set_option maxHeartbeats 3200000 in
theorem Maps.exists_constructed_capturing_plaques
    {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [Fintype ι]
    [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {r : ℝ} {Λ K G : Set M} {h : HyperbolicData (E := E) T Λ}
    (F : Maps (E := E) (ι := ι) T r) (regularity : 1 ≤ r)
    (deterministic : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (geometry : PseudoReferenceGeometry h) (a : IsometricFraming h)
    (compactK : IsCompact K) (core : LeanShared.isolatedCore T K ⊆ Λ)
    (compactΛ : IsCompact Λ) (invariant : MapsTo (T : M → M) Λ Λ)
    (openG : IsOpen G) (contains : Λ ⊆ G) :
    ∃ window : ℝ≥0, 0 < window ∧ ∀ ε : ℝ≥0, 0 < ε → ε ≤ window →
      ∃ plaque : (ℤ → cube (ι := ι) ε) → Set M,
        (∀ path paths, Tendsto paths atTop (𝓝 path) → ∀ x ∈ plaque path,
          ∃ xn : ℕ → M, Tendsto xn atTop (𝓝 x) ∧ ∀ n, xn n ∈ plaque (paths n)) ∧
        (∀ path x, x ∈ plaque path → ∃ b : ℕ → M, b 0 = x ∧
          (∀ n, b n ∈ G) ∧ ∀ n, F.family ε (backwardNoise path n).val (b (n + 1)) = b n) ∧
        ∀ path (b : ℕ → M), (∀ n, b n ∈ K) →
          (∀ n, F.family ε (backwardNoise path n).val (b (n + 1)) = b n) →
          ∃ j : ℕ, b j ∈ plaque (backwardShift path j) := by
  classical
  obtain ⟨B,positiveB,frameBounds⟩ := a.exists_uniform_bound
  obtain ⟨tube,positiveTube,collarWindow,positiveCollarWindow,collar⟩ :=
    F.exists_finite_collar_window Λ G compactΛ invariant openG contains geometry.blockLength
  obtain ⟨cap,positiveCap,decodeBound⟩ := exists_decode_radius geometry a.whole positiveB frameBounds tube positiveTube
  obtain ⟨radius,positiveRadius,radiusCap,tolerance,positiveTolerance,plaqueWindow,positivePlaqueWindow,produce⟩ :=
    F.exists_pseudo_reference_manifold_plaques regularity deterministic geometry a cap positiveCap
  obtain ⟨coordinateCap,positiveCoordinateCap,coordinatesBound⟩ :=
    exists_ambient_radius geometry a.whole positiveB (fun x => (frameBounds x).2) radius positiveRadius
  obtain ⟨δ,positiveδ,smallδ,J,positiveJ,referenceWindow,positiveReferenceWindow,select⟩ :=
    F.exists_backward_tail_reference compactK core geometry.blockLength tolerance coordinateCap
      positiveTolerance positiveCoordinateCap
  let window := min plaqueWindow (min collarWindow referenceWindow)
  refine ⟨window,lt_min positivePlaqueWindow (lt_min positiveCollarWindow positiveReferenceWindow),
    fun ε hp hw => ?_⟩
  let zero : cube (ι := ι) ε := ⟨0,by intro i; simp⟩
  let Ref := {reference : ℕ → Λ // ∀ n,
    dist ((T : M → M)^[geometry.blockLength] (reference (n + 1)).val) (reference n).val < tolerance}
  have made (reference : Ref) := produce ε hp (hw.trans (min_le_left _ _)) reference.val reference.property
  choose data radiusEq mapEq coordinatesEq using made
  let plaque : (ℤ → cube (ι := ι) ε) → Set M := fun path =>
    ⋃ reference : Ref, (data reference).plaque (blockPath zero geometry.blockLength path)
  refine ⟨plaque,?_,?_,?_⟩
  · intro path paths limit x member
    obtain ⟨reference,member⟩ := mem_iUnion.mp member
    obtain ⟨xn,converges,belongs⟩ := (data reference).lower _ _
      (((continuous_blockPath zero geometry.blockLength).tendsto path).comp limit) x member
    exact ⟨xn,converges,fun n => mem_iUnion.mpr ⟨reference,belongs n⟩⟩
  · intro path x member
    obtain ⟨reference,member⟩ := mem_iUnion.mp member
    obtain ⟨orbit,initial,inside,step⟩ := (data reference).backward _ x member
    have blockStep (n : ℕ) :
        word (fun j y => F.family ε (backwardNoise (blockPath zero geometry.blockLength path) n j).val y)
          geometry.blockLength (orbit (n + 1)) = orbit n := by
      rw [← mapEq reference n]
      exact step n
    obtain ⟨b,initialB,oneStep,_sampled,formula⟩ :=
      exists_one_step_orbit (fun p : M × cube (ι := ι) ε => F.family ε p.2.val p.1)
        zero geometry.blockLength geometry.block_positive path orbit blockStep
    refine ⟨b,initialB.trans initial,fun m => ?_,oneStep⟩
    rw [formula m]
    apply collar ε hp (hw.trans ((min_le_right _ _).trans (min_le_left _ _))) _
      (geometry.blockLength - m % geometry.blockLength) (Nat.sub_le _ _)
    have bound : ‖coordinate geometry a.whole (reference.val (m / geometry.blockLength + 1))
        (orbit (m / geometry.blockLength + 1))‖ ≤ cap := by
      have strict := (inside (m / geometry.blockLength + 1)).2
      rw [coordinatesEq reference, normalizedChart_apply, radiusEq reference] at strict
      exact strict.le.trans radiusCap
    have decodeFacts := decodeBound (reference.val (m / geometry.blockLength + 1)) _ bound
    have original : decode geometry a.whole (reference.val (m / geometry.blockLength + 1))
        (coordinate geometry a.whole (reference.val (m / geometry.blockLength + 1))
          (orbit (m / geometry.blockLength + 1))) = orbit (m / geometry.blockLength + 1) := by
      apply decode_coordinate
      have source := (inside (m / geometry.blockLength + 1)).1
      rw [coordinatesEq reference, normalizedChart_source] at source
      exact source
    rw [original] at decodeFacts
    exact Metric.mem_cthickening_of_dist_le _ _ _ _ (reference.val _).property decodeFacts.2.le
  · intro path b inside step
    obtain ⟨reference,near,pseudo⟩ := select ε hp
      (hw.trans ((min_le_right _ _).trans (min_le_right _ _))) (backwardNoise path) b inside step
    let ref : Ref := ⟨reference,pseudo⟩
    refine ⟨J,mem_iUnion.mpr ⟨ref,?_⟩⟩
    apply (data ref).local_backward (blockPath zero geometry.blockLength (backwardShift path J))
      (fun n => b (J + geometry.blockLength * n))
    · intro n
      have close := coordinatesBound (reference n) (b (J + geometry.blockLength * n))
        ((near n).trans_le smallδ)
      change _ ∧ _
      rw [coordinatesEq ref, normalizedChart_source, normalizedChart_apply, radiusEq ref]
      exact close
    · intro n
      rw [mapEq ref n]
      exact LeanShared.ControlledBlockSampling.sampled_step
        (fun p : M × cube (ι := ι) ε => F.family ε p.2.val p.1) zero
        (backwardShift path J) (fun n => b (J + n))
        (LeanShared.ControlledBlockSampling.shifted_step
          (fun p : M × cube (ι := ι) ε => F.family ε p.2.val p.1) path b step J)
        geometry.blockLength n

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
