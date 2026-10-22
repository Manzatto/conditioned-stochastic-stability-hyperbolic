module
public import LeanShared.Analysis.ConeFourierPairingResolution

/-! The actual finite dyadic resolution reconstructs every Schwartz function
pointwise with a uniform spatial bound. No convergence of a completed block
matrix or compact support of its input blocks is presumed. -/
public noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform RealInnerProductSpace Topology
namespace LeanShared.ConeFourierPointwiseResolution
open ConeDyadicSymbols ConeFourierPairingResolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Cp Cm : Set E}

theorem inverse_integral (f : 𝓢(E,ℂ)) (x : E) :
    f x = ∫ ξ,Real.fourierChar (inner ℝ ξ x) • (𝓕 f) ξ := by
  calc
    _ = (𝓕⁻ (𝓕 f) : 𝓢(E,ℂ)) x := by simp
    _ = 𝓕⁻ ((𝓕 f : 𝓢(E,ℂ)) : E → ℂ) x :=
      congrFun (SchwartzMap.fourierInv_coe (𝓕 f)) x
    _ = _ := Real.fourierInv_eq _ _

theorem frequency_norm_bound (χ : RadialCutoff) (Φ : AngularCutoff Cp Cm)
    (f : 𝓢(E,ℂ)) (N : ℕ) (ξ : E) :
    ‖(𝓕 (partialSum χ Φ N f)) ξ‖ ≤ ‖(𝓕 f) ξ‖ := by
  rw [fourier_partialSum,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (χ.nonneg _)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right
    (χ.le_one (((2:ℝ)^N)⁻¹*‖(2*Real.pi) • ξ‖)) (norm_nonneg ((𝓕 f) ξ))

theorem uniform_bound (χ : RadialCutoff) (Φ : AngularCutoff Cp Cm)
    (f : 𝓢(E,ℂ)) (N : ℕ) (x : E) :
    ‖partialSum χ Φ N f x‖ ≤ ∫ ξ,‖(𝓕 f) ξ‖ := by
  rw [inverse_integral]
  have initial := norm_integral_le_integral_norm (μ := volume)
    (fun ξ => Real.fourierChar (inner ℝ ξ x) • (𝓕 (partialSum χ Φ N f)) ξ)
  simp_rw [Circle.norm_smul] at initial
  exact initial.trans (integral_mono (𝓕 (partialSum χ Φ N f)).integrable.norm
    (𝓕 f).integrable.norm (frequency_norm_bound χ Φ f N))

theorem pointwise_converges (χ : RadialCutoff) (Φ : AngularCutoff Cp Cm)
    (f : 𝓢(E,ℂ)) (x : E) :
    Tendsto (fun N => partialSum χ Φ N f x) atTop (𝓝 (f x)) := by
  have actual := tendsto_integral_of_dominated_convergence (μ := volume)
    (fun ξ => ‖(𝓕 f) ξ‖)
    (F := fun N ξ => Real.fourierChar (inner ℝ ξ x) • (𝓕 (partialSum χ Φ N f)) ξ)
    (f := fun ξ => Real.fourierChar (inner ℝ ξ x) • (𝓕 f) ξ)
    (fun N => (by fun_prop : Continuous (fun ξ => Real.fourierChar (inner ℝ ξ x) •
      (𝓕 (partialSum χ Φ N f)) ξ)).aestronglyMeasurable)
    (𝓕 f).integrable.norm
    (fun N => ae_of_all _ (fun ξ => by
      rw [Circle.norm_smul]
      exact frequency_norm_bound χ Φ f N ξ))
    (ae_of_all _ (fun ξ => by
      apply tendsto_const_nhds.congr'
      filter_upwards [ConeDyadicResolution.eventually_finite_sum_eq_one χ Φ ((2*Real.pi) • ξ)]
        with N equal
      rw [ConeDyadicResolution.finite_sum] at equal
      rw [fourier_partialSum,equal,one_mul]))
  simpa only [←inverse_integral] using actual

end LeanShared.ConeFourierPointwiseResolution
