module

public import ConditionedStochasticStabilityHyperbolic.Paper.RealControlDensity
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.SmoothControlL1Approximation
public import LeanShared.Probability.SubtypeKernel

/-! Smooth ambient control functions approximate the paper's actual control
law density in L1 on its closed cube. The approximants need not be probability
densities: signed smooth functions suffice for the smoothing extension. -/

@[expose] public noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared
variable {ι : Type*} [Fintype ι]

theorem exists_smooth_cube_approximation (ε : ℝ≥0)
    (p : cube (ι := ι) ε → ℝ) (hp : Integrable p (cubeVolume ε)) :
    ∃ pn : ℕ → Control (ι := ι) → ℝ,
      (∀ n, HasCompactSupport (pn n) ∧ ContDiff ℝ ∞ (pn n) ∧
        Integrable (fun z : cube (ι := ι) ε => pn n z.val) (cubeVolume ε)) ∧
      Tendsto (fun n => ∫ z : cube (ι := ι) ε, ‖p z - pn n z.val‖ ∂cubeVolume ε) atTop (𝓝 0) := by
  let S : Set (Control (ι := ι)) := NoiseCubeRescaling.cube (ι := ι) ε
  have hS : MeasurableSet S := (NoiseCubeRescaling.cube_compact (ι := ι) ε).isClosed.measurableSet
  let pe := SubtypeKernel.zeroExtend S p
  have hpe : Integrable pe ((volume : Measure (Control (ι := ι))).restrict S) := by
    apply (integrableOn_iff_comap_subtypeVal hS).mpr
    simpa only [Function.comp_def, pe, SubtypeKernel.zeroExtend_coe, cubeVolume, S] using hp
  obtain ⟨pn, hpn, hlim⟩ := SmoothControlL1Approximation.exists_approximation
    ((volume : Measure (Control (ι := ι))).restrict S) pe hpe
  refine ⟨pn, ?_, ?_⟩
  · intro n
    refine ⟨(hpn n).1, (hpn n).2.1, ?_⟩
    exact (integrableOn_iff_comap_subtypeVal hS).mp (hpn n).2.2
  · have heq (n : ℕ) : (∫ z : cube (ι := ι) ε, ‖p z - pn n z.val‖ ∂cubeVolume ε) =
        ∫ z, ‖pe z - pn n z‖ ∂((volume : Measure (Control (ι := ι))).restrict S) := by
      simpa only [pe, SubtypeKernel.zeroExtend_coe, cubeVolume, S] using
        integral_subtype_comap (μ := (volume : Measure (Control (ι := ι)))) hS (fun z => ‖pe z - pn n z‖)
    simpa only [heq] using hlim

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
