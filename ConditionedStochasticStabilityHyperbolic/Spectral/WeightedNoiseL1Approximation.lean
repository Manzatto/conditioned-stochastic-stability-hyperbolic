module

public import LeanShared.Probability.WeightedRandomMapKernel
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-! Arbitrary integrable control-law densities inherit weighted strong-Feller
smoothing from ordinary smooth-density approximants. The uniform error is
bounded by the L1 error of the control density times the actual weight and
observable bounds; no regularity of the limiting density is used. -/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.WeightedNoiseL1Approximation
variable {X Ω : Type*} [TopologicalSpace X] [MeasurableSpace X] [MeasurableSpace Ω]

private theorem integral_error
    (σ : Measure Ω) (p q : Ω → ℝ) (hp : Integrable p σ) (hq : Integrable q σ)
    (v : Ω → ℝ) (hv : AEStronglyMeasurable v σ) (B : ℝ)
    (hb : ∀ z, ‖v z‖ ≤ B) :
    ‖(∫ z, p z * v z ∂σ) - ∫ z, q z * v z ∂σ‖ ≤
      B * ∫ z, ‖p z - q z‖ ∂σ := by
  rw [← integral_sub (hp.mul_bdd hv (ae_of_all _ hb))
    (hq.mul_bdd hv (ae_of_all _ hb))]
  calc
    _ ≤ ∫ z, B * ‖p z - q z‖ ∂σ := by
      apply norm_integral_le_of_norm_le ((hp.sub hq).norm.const_mul B)
      exact ae_of_all _ (fun z => by
        rw [← sub_mul, norm_mul]
        exact (mul_le_mul_of_nonneg_left (hb z) (norm_nonneg _)).trans_eq (mul_comm _ _))
    _ = _ := integral_const_mul _ _

/-- The smooth-control-density rank-theorem statement suffices for ANY L1
control-law density. Approximation and all output continuity are derived. -/
theorem continuous_weighted_integral_of_L1_approximation
    (σ : Measure Ω) (p : Ω → ℝ) (hp : Integrable p σ)
    (pn : ℕ → Ω → ℝ) (hpn : ∀ n, Integrable (pn n) σ)
    (happrox : Tendsto (fun n => ∫ z, ‖p z - pn n z‖ ∂σ) atTop (𝓝 0))
    (F : X × Ω → X) (hF : Measurable F)
    (W : X × Ω → ℝ) (hW : Measurable W)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x z, ‖W (x, z)‖ ≤ B)
    (f : X → ℝ) (hf : Measurable f) (C : ℝ) (_hC : 0 ≤ C)
    (hfb : ∀ x, ‖f x‖ ≤ C)
    (hsmooth : ∀ n, Continuous (fun x => ∫ z, pn n z * (W (x, z) * f (F (x, z))) ∂σ)) :
    Continuous (fun x => ∫ z, p z * (W (x, z) * f (F (x, z))) ∂σ) := by
  have hv (x : X) : Measurable (fun z => W (x, z) * f (F (x, z))) :=
    (hW.comp measurable_prodMk_left).mul (hf.comp (hF.comp measurable_prodMk_left))
  have hvb (x : X) (z : Ω) : ‖W (x, z) * f (F (x, z))‖ ≤ B * C := by
    rw [norm_mul]
    exact mul_le_mul (hbound x z) (hfb _) (norm_nonneg _) hB
  have hh : Tendsto (fun n => (B * C) * ∫ z, ‖p z - pn n z‖ ∂σ) atTop (𝓝 0) := by
    simpa only [mul_zero] using happrox.const_mul (B * C)
  have hu : TendstoUniformly
      (fun n x => ∫ z, pn n z * (W (x, z) * f (F (x, z))) ∂σ)
      (fun x => ∫ z, p z * (W (x, z) * f (F (x, z))) ∂σ) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [hh.eventually (gt_mem_nhds hε)] with n hn x
    rw [Real.dist_eq]
    exact (integral_error σ p (pn n) hp (hpn n) _ (hv x).aestronglyMeasurable
      (B * C) (hvb x)).trans_lt hn
  exact hu.continuous (Eventually.of_forall hsmooth).frequently

end ConditionedStochasticStabilityHyperbolic.WeightedNoiseL1Approximation
