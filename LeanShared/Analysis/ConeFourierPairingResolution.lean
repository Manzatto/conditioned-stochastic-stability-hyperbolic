module
public import LeanShared.Analysis.FourierBlockTestPairing
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The actual physical Fourier blocks reconstruct every Schwartz test
pairing. Convergence follows from the proved finite radial telescope and
dominated convergence, without a reconstruction premise. -/
public noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology
namespace LeanShared.ConeFourierPairingResolution
open ConeDyadicSymbols
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Cplus Cminus : Set E}
@[expose] def partialSum (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus)
    (N : ℕ) (f : 𝓢(E,ℂ)) : 𝓢(E,ℂ) :=
  ∑ n ∈ Finset.range (N+1), ∑ s : Bool, ConeFourierBlocks.block (symbols χ Φ (n,s)) f

theorem fourier_partialSum (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus)
    (N : ℕ) (f : 𝓢(E,ℂ)) (ξ : E) :
    𝓕 (partialSum χ Φ N f) ξ =
      (χ.toFun (((2:ℝ)^N)⁻¹*‖(2*Real.pi) • ξ‖):ℂ)*(𝓕 f) ξ := by
  simp only [partialSum,FourierTransform.fourier_sum,sum_apply,ConeFourierBlocks.fourier_block]
  simp_rw [← Finset.sum_mul]
  rw [ConeDyadicResolution.finite_sum]

theorem pairing_converges (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus)
    (f test : 𝓢(E,ℂ)) :
    Tendsto (fun N=> ∫ x, partialSum χ Φ N f x*test x) atTop (𝓝 (∫ x, f x*test x)) := by
  have major : Integrable (fun ξ=>‖(𝓕 f) ξ‖*‖(𝓕⁻ test) ξ‖) :=
    (𝓕 f).integrable.norm.mul_bdd (𝓕⁻ test).continuous.norm.aestronglyMeasurable
      (ae_of_all _ fun ξ=>by simpa only [norm_norm] using
        SchwartzMap.norm_le_seminorm ℂ (𝓕⁻ test) ξ)
  have converges := tendsto_integral_of_dominated_convergence
    (fun ξ=>‖(𝓕 f) ξ‖*‖(𝓕⁻ test) ξ‖)
    (F:=fun N ξ=> (𝓕 (partialSum χ Φ N f)) ξ*(𝓕⁻ test) ξ)
    (f:=fun ξ=> (𝓕 f) ξ*(𝓕⁻ test) ξ)
    (fun N=>((𝓕 (partialSum χ Φ N f)).continuous.mul (𝓕⁻ test).continuous).aestronglyMeasurable)
    major (fun N=>ae_of_all _ fun ξ=>by
      rw [fourier_partialSum,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (χ.nonneg _)]
      have bound := mul_le_mul_of_nonneg_right (χ.le_one
        (((2:ℝ)^N)⁻¹*‖(2*Real.pi) • ξ‖)) (norm_nonneg ((𝓕 f) ξ))
      exact mul_le_mul_of_nonneg_right (by simpa only [one_mul] using bound) (norm_nonneg _))
    (ae_of_all _ fun ξ=>by
      apply tendsto_const_nhds.congr'
      filter_upwards [ConeDyadicResolution.eventually_finite_sum_eq_one χ Φ ((2*Real.pi) • ξ)]
        with N equal
      rw [ConeDyadicResolution.finite_sum] at equal
      rw [fourier_partialSum,equal,one_mul])
  simpa only [← FourierBlockTestPairing.pairing] using converges
end LeanShared.ConeFourierPairingResolution
