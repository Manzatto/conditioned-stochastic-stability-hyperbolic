module

public import ConditionedStochasticStabilityHyperbolic.Paper.SmoothCubeDensity
public import ConditionedStochasticStabilityHyperbolic.Spectral.WeightedNoiseStrongFeller

/-! The literal paper law, with merely bounded Lebesgue density, inherits
weighted killed-kernel smoothing from the ordinary smooth-control-density
submersion theorem. The density and its approximants are constructed. -/

@[expose] public noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ContDiff
namespace ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
open LeanShared WeightedNoiseL1Approximation
variable {X ι : Type*} [TopologicalSpace X] [MeasurableSpace X] [Fintype ι]

theorem Laws.weighted_killed_smoothing_of_smooth_density_source
    (L : Laws (ι := ι)) (ε : ℝ≥0) (hε : 0 < ε)
    (H : X × cube (ι := ι) ε → X) (hH : Measurable H)
    (W : X × cube (ι := ι) ε → ℝ) (hW : Measurable W) (hW0 : ∀ x z, 0 ≤ W (x, z))
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x z, ‖W (x, z)‖ ≤ B)
    (K : Set X) (hK : MeasurableSet K)
    (smoothSource : ∀ g : Control (ι := ι) → ℝ, HasCompactSupport g → ContDiff ℝ ∞ g →
      ∀ (f : X → ℝ), Measurable f → (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C) →
        Continuous (fun x => ∫ z : cube (ι := ι) ε,
          g z.val * (W (x, z) * f (H (x, z))) ∂cubeVolume ε)) :
    ∀ (f : X → ℝ), Measurable f → (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C) →
      Continuous (fun x => ∫ y, f y ∂WeightedRandomMapKernel.killed (L.law ε) W H K hK x) := by
  obtain ⟨p, hp, hp0, hpi, _hb, hrepr⟩ := L.exists_real_integrable_density ε hε
  obtain ⟨pn, hpn, hlim⟩ := exists_smooth_cube_approximation ε p hpi
  intro f hf hfb
  exact continuous_integral_killed_of_L1_approximation (cubeVolume ε) (L.law ε)
    p hp hp0 hpi hrepr (fun n z => pn n z.val) (fun n => (hpn n).2.2) hlim
    H hH W hW hW0 B hB hbound K hK
    (fun q hq hqb n => smoothSource (pn n) (hpn n).1 (hpn n).2.1 q hq hqb) f hf hfb

end ConditionedStochasticStabilityHyperbolic.Paper.RegularNoise
