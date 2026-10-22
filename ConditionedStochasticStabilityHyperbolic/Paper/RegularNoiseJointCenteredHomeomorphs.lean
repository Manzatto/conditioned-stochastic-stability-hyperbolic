module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoiseJointCenteredCutoff
public import LeanShared.Geometry.ParametricNormalizedChartRegularity
public import LeanShared.Analysis.CompactParameterCutoffRegularity
public import LeanShared.Analysis.CompactJointAffineHomeomorphs

/-! Actual joint control/state C1 regularity of a fixed-prototype cutoff
extension on an open neighborhood of the entire legal noise cube. -/
public noncomputable section
open Set IsManifold
open scoped Topology Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.CenteredManifoldCoordinates
variable {E P M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [MetricSpace M] [ChartedSpace E M] [Fintype ι] {T : M ≃ₜ M}

omit [FiniteDimensional ℝ E] in
theorem Maps.joint_centered_homeomorphs {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
    (ε : ℝ≥0) (positive : 0 < ε) (window : ε ≤ F.window)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (L R : P ≃L[ℝ] E) (a b : E) (A : P ≃L[ℝ] P) (β : P)
    (ρ : P → ℝ) (smoothρ : ContDiff ℝ 1 ρ) (compactρ : HasCompactSupport ρ)
    (valid : ∀ control : cube (ι := ι) ε, ∀ z ∈ tsupport ρ,
      a+L z ∈ c.target ∧ F.family ε control.val (c.symm (a+L z)) ∈ d.source)
    (k : ℝ≥0) (positiveK : 0 < k)
    (small : Subsingleton P ∨ k < ‖A.symm.toContinuousLinearMap‖₊⁻¹)
    (margin : ∀ control : cube (ι := ι) ε, ∀ z,
      ‖fderiv ℝ (fun x => A x+β+ρ x •
        (centered L R a b (d ∘ F.family ε control.val ∘ c.symm) x-(A x+β))) z-
          A.toContinuousLinearMap‖ < k) :
    ∃ O : Set (Control (ι := ι)), IsOpen O ∧ (cube (ι := ι) ε : Set _) ⊆ O ∧
      ∃ H : Control (ι := ι) → P ≃ₜ P,
        (∀ control ∈ O, ∀ z, H control z = A z+β+ρ z •
          (centered L R a b (d ∘ F.family ε control ∘ c.symm) z-(A z+β))) ∧
        ContDiffOn ℝ 1 (fun q : Control (ι := ι) × P => H q.1 q.2) (O ×ˢ univ) ∧
        ContDiffOn ℝ 1 (fun q : Control (ι := ι) × P => (H q.1).symm q.2) (O ×ˢ univ) := by
  obtain ⟨O₀,openO₀,contains,joint⟩ := F.joint_centered_cutoff ε positive window
    c d hc hd L R a b A.toContinuousLinearMap β ρ smoothρ compactρ valid
  let f : Control (ι := ι) × P → P := fun q => A q.2+β+ρ q.2 •
    (centered L R a b (d ∘ F.family ε q.1 ∘ c.symm) q.2-(A q.2+β))
  have exterior (control : Control (ι := ι)) (_inside : control ∈ O₀) (z : P)
      (outside : z ∉ tsupport ρ) : f (control,z) = A z+β := by
    dsimp only [f]
    rw [image_eq_zero_of_notMem_tsupport outside, zero_smul, add_zero]
  obtain ⟨O,openO,containsK,_subset,H,actual,forward,inverse⟩ :=
    CompactJointAffineHomeomorphs.exists_family (cube (ι := ι) ε) (NoiseCubeRescaling.cube_compact ε)
      A β f (tsupport ρ) compactρ O₀ openO₀ contains joint exterior k positiveK small
      (fun control member z => margin ⟨control,member⟩ z)
  exact ⟨O,openO,containsK,H,actual,forward,inverse⟩

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
