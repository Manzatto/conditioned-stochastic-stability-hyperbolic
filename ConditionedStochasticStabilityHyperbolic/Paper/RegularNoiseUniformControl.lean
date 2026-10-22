module

public import ConditionedStochasticStabilityHyperbolic.Paper.RepresentedFixedCubeNoise
public import LeanShared.Topology.UniformControlImage

/-! Actual regular perturbations have a uniform control-image radius at each
positive small scale. Compactness supplies uniformity; only ordinary
rank-chart openness of the joint endpoint map remains a classical source. -/

@[expose] public noncomputable section
open Set Metric IsManifold
open scoped Manifold ContDiff Topology NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M] [Fintype ι]

/-- The zero control lies genuinely inside the positive-radius cube. -/
theorem zero_interior_cube (ε : ℝ≥0) (hε : 0 < ε) :
    (0 : Control (ι := ι)) ∈ interior (LeanShared.NoiseCubeRescaling.cube (ι := ι) (ε : ℝ)) := by
  have hball : ball (0 : Control (ι := ι)) (ε : ℝ) ⊆
      LeanShared.NoiseCubeRescaling.cube (ι := ι) (ε : ℝ) := by
    intro a ha
    have hn : ‖a‖ < (ε : ℝ) := by simpa only [mem_ball, dist_zero_right] using ha
    intro i
    exact (show |a i| ≤ ‖a‖ from by simpa only [Real.norm_eq_abs] using norm_le_pi_norm a i).trans hn.le
  exact (interior_maximal hball isOpen_ball) (mem_ball_self hε)

/-- Ordinary joint submersion openness, independent of laws, spectral data
and any uniform control-radius conclusion. -/
def OpenCubeEndpointContract : Prop :=
  ∀ ε : ℝ≥0, 0 < ε → ∀ H : Control (ι := ι) × M → M,
    (∃ O : Set (Control (ι := ι)), IsOpen O ∧
      (LeanShared.NoiseCubeRescaling.cube (ι := ι) ε : Set (Control (ι := ι))) ⊆ O ∧
      ContMDiffOn ((𝓘(ℝ, Control (ι := ι))).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) 1 H (O ×ˢ univ)) →
    (∀ (a : cube (ι := ι) ε) (x : M),
      Function.Surjective (mfderiv (𝓘(ℝ, Control (ι := ι))) (𝓘(ℝ, E))
        (fun b : Control (ι := ι) => H (b, x)) a.val)) →
    IsOpen ((fun p : M × Control (ι := ι) => (p.1, H (p.2, p.1))) ''
      (univ ×ˢ interior (LeanShared.NoiseCubeRescaling.cube (ι := ι) (ε : ℝ))))

variable [CompactSpace M] {T : M ≃ₜ M} {r : ℝ}

omit [FiniteDimensional ℝ E] in
theorem Maps.exists_uniform_control_radius
    (F : Maps (E := E) (ι := ι) T r)
    (classicalSource : OpenCubeEndpointContract (E := E) (M := M) (ι := ι))
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ F.window) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : M, dist (T x) y < δ →
      ∃ a : cube (ι := ι) ε, F.family ε a.val x = y := by
  have ho := classicalSource ε hε (fun z => F.family ε z.1 z.2)
    (F.joint_C1 ε hε hw) (F.control_surjective ε hε hw)
  obtain ⟨δ, hδ, hcover⟩ := LeanShared.UniformControlImage.exists_uniform_radius T T.continuous
    (fun z : M × Control (ι := ι) => F.family ε z.2 z.1)
    (interior (LeanShared.NoiseCubeRescaling.cube (ι := ι) (ε : ℝ))) 0
    (zero_interior_cube ε hε) (F.zero_control ε hε hw) ho
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  obtain ⟨a, ha, he⟩ := hcover x y hxy
  exact ⟨⟨a, interior_subset ha⟩, he⟩

omit [FiniteDimensional ℝ E] in
/-- The same radius covers targets using the actual fixed control space. -/
theorem Maps.exists_uniform_fixed_control_radius
    (F : Maps (E := E) (ι := ι) T r)
    (classicalSource : OpenCubeEndpointContract (E := E) (M := M) (ι := ι))
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ F.window) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : M, dist (T x) y < δ →
      ∃ z : FixedControl (ι := ι), F.fixedMap ε x z = y := by
  obtain ⟨δ, hδ, hc⟩ := F.exists_uniform_control_radius classicalSource ε hε hw
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  obtain ⟨a, ha⟩ := hc x y hxy
  refine ⟨(LeanShared.NoiseCubeRescaling.rescale (ε : ℝ) hε).symm a, ?_⟩
  simpa only [Maps.fixedMap, dite_eq_left hε, Homeomorph.apply_symm_apply] using ha

variable {Parameters : Type*} [MetricSpace Parameters]
  {F : Maps (E := E) (ι := ι) T r} {evaluate : Parameters → M → M}

omit [FiniteDimensional ℝ E] in
/-- The analytic representation retains the uniform ball in the image. -/
theorem Representation.exists_uniform_fixed_control_radius
    (p : Representation F Parameters evaluate)
    (classicalSource : OpenCubeEndpointContract (E := E) (M := M) (ι := ι))
    (ε : ℝ≥0) (hε : 0 < ε) (hw : ε ≤ p.window) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : M, dist (T x) y < δ →
      ∃ z : FixedControl (ι := ι), evaluate (p.fixedParameters ε z) x = y := by
  obtain ⟨δ, hδ, hc⟩ := F.exists_uniform_fixed_control_radius classicalSource ε hε
    (hw.trans p.window_le)
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  obtain ⟨z, hz⟩ := hc x y hxy
  exact ⟨z, (p.actual_fixedMap ε hε hw x z).trans hz⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
