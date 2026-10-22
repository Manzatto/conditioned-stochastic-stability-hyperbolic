module
public import ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
public import LeanShared.Geometry.ParametricNormalizedChartRegularity
public import LeanShared.Analysis.CompactParameterCutoffRegularity

/-! Actual joint control/state C1 regularity of a fixed-prototype cutoff
extension on an open neighborhood of the entire legal noise cube. -/
public noncomputable section
open Set IsManifold
open scoped Topology Manifold ContDiff NNReal
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared LeanShared.CenteredManifoldCoordinates
variable {E P M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [MetricSpace M] [ChartedSpace E M] [Fintype ι] {T : M ≃ₜ M}

omit [FiniteDimensional ℝ E] in
theorem Maps.joint_centered_cutoff {r : ℝ} (F : Maps (E := E) (ι := ι) T r)
    (ε : ℝ≥0) (positive : 0 < ε) (window : ε ≤ F.window)
    (c d : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M) (hd : d ∈ maximalAtlas (𝓘(ℝ,E)) ∞ M)
    (L R : P ≃L[ℝ] E) (a b : E) (A : P →L[ℝ] P) (β : P)
    (ρ : P → ℝ) (smoothρ : ContDiff ℝ 1 ρ) (compactρ : HasCompactSupport ρ)
    (valid : ∀ control : cube (ι := ι) ε, ∀ z ∈ tsupport ρ,
      a+L z ∈ c.target ∧ F.family ε control.val (c.symm (a+L z)) ∈ d.source) :
    ∃ O : Set (Control (ι := ι)), IsOpen O ∧ (cube (ι := ι) ε : Set _) ⊆ O ∧
      ContDiffOn ℝ 1
        (fun q : Control (ι := ι) × P => A q.2+β+ρ q.2 •
          (centered L R a b (d ∘ F.family ε q.1 ∘ c.symm) q.2-(A q.2+β))) (O ×ˢ univ) := by
  obtain ⟨O,openO,contains,joint⟩ := F.joint_C1 ε positive window
  apply CompactParameterCutoffRegularity.exists_window (cube (ι := ι) ε)
    (NoiseCubeRescaling.cube_compact ε) A β ρ smoothρ compactρ
    (fun q : Control (ι := ι) × P => centered L R a b (d ∘ F.family ε q.1 ∘ c.symm) q.2)
  intro control member z hz
  exact ParametricNormalizedChartRegularity.contDiffAt_centered c d hc hd L R a b
    (fun q : Control (ι := ι) × M => F.family ε q.1 q.2) O openO joint (control,z)
    (contains member) (valid ⟨control,member⟩ z hz).1 (valid ⟨control,member⟩ z hz).2

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
