module
public import LeanShared.Analysis.ConeFourierPairingResolution

/-! The dyadic partial sums of an actual Schwartz function converge to it
uniformly (Fourier inversion bounds the sup norm by the L¹ norm of the
transform, and dominated convergence applies to `(χ_N - 1) 𝓕 f`). Hence the
blocks reconstruct the pairing with every integrable bounded test, not only
with Schwartz tests. -/
public noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology
namespace LeanShared.ConeFourierUniformResolution
open ConeDyadicSymbols ConeFourierPairingResolution
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Cplus Cminus : Set E}

/-- The sup norm of a Schwartz function is bounded by the L¹ norm of its transform. -/
theorem norm_le_integral_fourier (g : 𝓢(E, ℂ)) (x : E) : ‖g x‖ ≤ ∫ ξ, ‖(𝓕 g) ξ‖ := by
  have inv : g = 𝓕⁻ (𝓕 g) := (FourierPair.fourierInv_fourier_eq g).symm
  have hx : g x = 𝓕⁻ ((𝓕 g : 𝓢(E, ℂ)) : E → ℂ) x := by
    conv_lhs => rw [inv]
    rw [SchwartzMap.fourierInv_coe]
  rw [hx, Real.fourierInv_eq]
  calc ‖∫ v, 𝐞 (inner ℝ v x) • (𝓕 g) v‖ ≤ ∫ v, ‖𝐞 (inner ℝ v x) • (𝓕 g) v‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ ξ, ‖(𝓕 g) ξ‖ := by
        apply integral_congr_ae
        exact ae_of_all _ fun v => by
          dsimp only
          rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]

/-- Uniform convergence of the dyadic partial sums. -/
theorem uniform (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus) (f : 𝓢(E, ℂ)) :
    Tendsto (fun N => ∫ ξ, ‖(𝓕 (partialSum χ Φ N f - f)) ξ‖) atTop (𝓝 0) := by
  have identity (N : ℕ) (ξ : E) : ‖(𝓕 (partialSum χ Φ N f - f)) ξ‖ =
      |χ.toFun (((2:ℝ)^N)⁻¹ * ‖(2 * Real.pi) • ξ‖) - 1| * ‖(𝓕 f) ξ‖ := by
    rw [sub_eq_add_neg, FourierTransform.fourier_add, FourierTransform.fourier_neg, add_apply,
      neg_apply, fourier_partialSum, ← sub_eq_add_neg, ← sub_one_mul, norm_mul]
    congr 1
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  simp_rw [identity]
  have zero : (0 : ℝ) = ∫ _ξ : E, (0 : ℝ) := by simp
  rw [zero]
  apply tendsto_integral_of_dominated_convergence (fun ξ => ‖(𝓕 f) ξ‖)
  · exact fun N => ((continuous_abs.comp ((χ.smooth.continuous.comp
      (continuous_const.mul (continuous_norm.comp (continuous_const_smul _)))).sub
      continuous_const)).mul (𝓕 f).continuous.norm).aestronglyMeasurable
  · exact (𝓕 f).integrable.norm
  · intro N
    refine ae_of_all _ fun ξ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
    have h1 : |χ.toFun (((2:ℝ)^N)⁻¹ * ‖(2 * Real.pi) • ξ‖) - 1| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [χ.nonneg (((2:ℝ)^N)⁻¹ * ‖(2 * Real.pi) • ξ‖),
        χ.le_one (((2:ℝ)^N)⁻¹ * ‖(2 * Real.pi) • ξ‖)]
    calc |χ.toFun (((2:ℝ)^N)⁻¹ * ‖(2 * Real.pi) • ξ‖) - 1| * ‖(𝓕 f) ξ‖
        ≤ 1 * ‖(𝓕 f) ξ‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖(𝓕 f) ξ‖ := one_mul _
  · refine ae_of_all _ fun ξ => ?_
    apply tendsto_const_nhds.congr'
    filter_upwards [ConeDyadicResolution.eventually_finite_sum_eq_one χ Φ ((2 * Real.pi) • ξ)]
      with N equal
    rw [ConeDyadicResolution.finite_sum] at equal
    have hreal : χ.toFun (((2:ℝ)^N)⁻¹ * ‖(2 * Real.pi) • ξ‖) = 1 := by exact_mod_cast equal
    rw [hreal, sub_self, abs_zero, zero_mul]

/-- The blocks reconstruct the pairing with every integrable bounded test. -/
theorem pairing_converges (χ : RadialCutoff) (Φ : AngularCutoff Cplus Cminus) (f : 𝓢(E, ℂ))
    (φ : E → ℂ) (integrable : Integrable φ) :
    Tendsto (fun N => ∫ x, partialSum χ Φ N f x * φ x) atTop (𝓝 (∫ x, f x * φ x)) := by
  have hφ : 0 ≤ ∫ x, ‖φ x‖ := integral_nonneg fun x => norm_nonneg _
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun N => norm_nonneg _)
    (g := fun N => (∫ ξ, ‖(𝓕 (partialSum χ Φ N f - f)) ξ‖) * ∫ x, ‖φ x‖)
  · intro N
    show ‖(∫ x, partialSum χ Φ N f x * φ x) - ∫ x, f x * φ x‖ ≤
      (∫ ξ, ‖(𝓕 (partialSum χ Φ N f - f)) ξ‖) * ∫ x, ‖φ x‖
    have hd : Integrable (fun x => (partialSum χ Φ N f - f) x * φ x) :=
      integrable.bdd_mul (partialSum χ Φ N f - f).continuous.aestronglyMeasurable
        (ae_of_all _ fun x => norm_le_integral_fourier _ x)
    have eq : (∫ x, partialSum χ Φ N f x * φ x) - ∫ x, f x * φ x =
        ∫ x, (partialSum χ Φ N f - f) x * φ x := by
      rw [← integral_sub]
      · apply integral_congr_ae
        exact ae_of_all _ fun x => by simp only [sub_apply]; ring
      · exact integrable.bdd_mul (partialSum χ Φ N f).continuous.aestronglyMeasurable
          (ae_of_all _ fun x => SchwartzMap.norm_le_seminorm ℂ _ x)
      · exact integrable.bdd_mul f.continuous.aestronglyMeasurable
          (ae_of_all _ fun x => SchwartzMap.norm_le_seminorm ℂ _ x)
    rw [eq]
    calc ‖∫ x, (partialSum χ Φ N f - f) x * φ x‖
        ≤ ∫ x, ‖(partialSum χ Φ N f - f) x * φ x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, (∫ ξ, ‖(𝓕 (partialSum χ Φ N f - f)) ξ‖) * ‖φ x‖ := by
          apply integral_mono_of_nonneg (ae_of_all _ fun x => norm_nonneg _)
            (integrable.norm.const_mul _)
          exact ae_of_all _ fun x => by
            dsimp only
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (norm_le_integral_fourier _ x) (norm_nonneg _)
      _ = (∫ ξ, ‖(𝓕 (partialSum χ Φ N f - f)) ξ‖) * ∫ x, ‖φ x‖ := integral_const_mul _ _
    exact le_rfl
  · simpa only [zero_mul] using (uniform χ Φ f).mul_const (∫ x, ‖φ x‖)

end LeanShared.ConeFourierUniformResolution
