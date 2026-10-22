module

public import ConditionedStochasticStabilityHyperbolic.Spectral.WeightedNoiseL1Approximation

/-! Strong-Feller smoothing for the ACTUAL weighted killed inverse kernel,
with a general bounded/integrable control density. Only the ordinary
smooth-density submersion statement remains a source; the L1-law extension
and passage to the killed kernel are proved here. -/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace ConditionedStochasticStabilityHyperbolic.WeightedNoiseL1Approximation
open LeanShared
variable {X Ω : Type*} [TopologicalSpace X] [MeasurableSpace X] [MeasurableSpace Ω]

theorem continuous_integral_killed_of_L1_approximation
    (σ ρ : Measure Ω) [IsFiniteMeasure ρ]
    (p : Ω → ℝ) (hp : Measurable p) (hp0 : ∀ z, 0 ≤ p z) (hpi : Integrable p σ)
    (hρ : ρ = σ.withDensity (fun z => ENNReal.ofReal (p z)))
    (pn : ℕ → Ω → ℝ) (hpn : ∀ n, Integrable (pn n) σ)
    (happrox : Tendsto (fun n => ∫ z, ‖p z - pn n z‖ ∂σ) atTop (𝓝 0))
    (F : X × Ω → X) (hF : Measurable F)
    (W : X × Ω → ℝ) (hW : Measurable W) (hW0 : ∀ x z, 0 ≤ W (x, z))
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ x z, ‖W (x, z)‖ ≤ B)
    (K : Set X) (hK : MeasurableSet K)
    (hsmooth : ∀ (f : X → ℝ), Measurable f →
      (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C) → ∀ n,
      Continuous (fun x => ∫ z, pn n z * (W (x, z) * f (F (x, z))) ∂σ))
    (f : X → ℝ) (hf : Measurable f)
    (hfb : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C) :
    Continuous (fun x => ∫ y, f y ∂WeightedRandomMapKernel.killed ρ W F K hK x) := by
  obtain ⟨C, hC, hCf⟩ := hfb
  have hif : Measurable (K.indicator f) := hf.indicator hK
  have hib : ∀ x, ‖K.indicator f x‖ ≤ C := by
    intro x
    by_cases hx : x ∈ K
    · simpa only [indicator_of_mem hx] using hCf x
    · simp only [indicator_of_notMem hx, norm_zero]
      exact hC
  have hc := continuous_weighted_integral_of_L1_approximation σ p hpi pn hpn happrox
    F hF W hW B hB hbound (K.indicator f) hif C hC hib
    (hsmooth _ hif ⟨C, hC, hib⟩)
  have heq (x : X) : (∫ y, f y ∂WeightedRandomMapKernel.killed ρ W F K hK x) =
      ∫ z, p z * (W (x, z) * K.indicator f (F (x, z))) ∂σ := by
    rw [WeightedRandomMapKernel.integral_killed ρ W hW F hF hW0 K hK f hf x,
      hρ, integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hp0 _), smul_eq_mul]
  exact hc.congr (fun x => (heq x).symm)

end ConditionedStochasticStabilityHyperbolic.WeightedNoiseL1Approximation
