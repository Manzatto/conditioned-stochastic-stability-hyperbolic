module

public import LeanShared.Analysis.PhysicalFiniteAmplitudeRows

/-! Finite physical cylinder aggregation for a genuine local coordinate
map. Only the map on its open source is continuous; no continuity of its
arbitrary total extension is required. Compactly supported amplitudes supply
the exact zero extension used in the integral. -/

public noncomputable section

open Set MeasureTheory
open scoped SchwartzMap ENNReal BigOperators

namespace LeanShared.PhysicalLocalAmplitudeRows

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_weighted (F : OpenPartialHomeomorph E E)
    (g u : E → ℂ) (continuousG : Continuous g) (continuousU : Continuous u)
    (supported : tsupport g ⊆ F.source) :
    Continuous (fun x => g x * u (F x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases inside : x ∈ F.source
  · exact (continuousG.continuousAt).mul
      (continuousU.continuousAt.comp
        (F.continuousOn.continuousAt (F.open_source.mem_nhds inside)))
  · have outside : x ∉ tsupport g := fun hx => inside (supported hx)
    apply (continuousAt_const : ContinuousAt (fun _ : E => (0 : ℂ)) x).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds outside] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]

theorem identity (kernel : 𝓢(E,ℂ)) (F : OpenPartialHomeomorph E E)
    (u : E → ℂ) (continuousU : Continuous u) (g : E → ℂ) (pieces : I → E → ℂ)
    (continuousPieces : ∀ i, Continuous (pieces i))
    (compactPieces : ∀ i, HasCompactSupport (pieces i))
    (supported : ∀ i, tsupport (pieces i) ⊆ F.source)
    (reconstruct : ∀ x, g x = ∑ i, pieces i x) (x : E) :
    (∫ w, kernel (x-w)*g w*u (F w)) =
      ∑ i, ∫ w, kernel (x-w)*pieces i w*u (F w) := by
  have integrable (i : I) : Integrable
      (fun w => kernel (x-w)*pieces i w*u (F w)) := by
    have continuous : Continuous (fun w => kernel (x-w)*(pieces i w*u (F w))) :=
      (kernel.continuous.comp (continuous_const.sub continuous_id)).mul
        (continuous_weighted F (pieces i) u (continuousPieces i) continuousU (supported i))
    have compact : HasCompactSupport (fun w => kernel (x-w)*(pieces i w*u (F w))) := by
      apply HasCompactSupport.intro (compactPieces i)
      intro w hw
      rw [image_eq_zero_of_notMem_tsupport hw, zero_mul, mul_zero]
    simpa only [mul_assoc] using continuous.integrable_of_hasCompactSupport compact
  simp_rw [reconstruct, Finset.mul_sum, Finset.sum_mul]
  exact integral_finsetSum _ (fun i _ => integrable i)

theorem bound (kernel : 𝓢(E,ℂ)) (F : OpenPartialHomeomorph E E)
    (u : E → ℂ) (continuousU : Continuous u) (g : E → ℂ) (pieces : I → E → ℂ)
    (continuousPieces : ∀ i, Continuous (pieces i))
    (compactPieces : ∀ i, HasCompactSupport (pieces i))
    (supported : ∀ i, tsupport (pieces i) ⊆ F.source)
    (reconstruct : ∀ x, g x = ∑ i, pieces i x) (μ : Measure E) (B : I → ℝ≥0∞)
    (rows : ∀ i, (∫⁻ x, ‖∫ w, kernel (x-w)*pieces i w*u (F w)‖ₑ ∂μ) ≤ B i) :
    (∫⁻ x, ‖∫ w, kernel (x-w)*g w*u (F w)‖ₑ ∂μ) ≤ ∑ i, B i := by
  have measurable (i : I) : Measurable
      (fun x => ∫ w, kernel (x-w)*pieces i w*u (F w)) := by
    have joint : Continuous
        (fun p : E × E => kernel (p.1-p.2)*(pieces i p.2*u (F p.2))) :=
      (kernel.continuous.comp (continuous_fst.sub continuous_snd)).mul
        ((continuous_weighted F (pieces i) u (continuousPieces i) continuousU
          (supported i)).comp continuous_snd)
    simpa only [mul_assoc] using joint.stronglyMeasurable.integral_prod_right'.measurable
  calc
    _ = ∫⁻ x, ‖∑ i, ∫ w, kernel (x-w)*pieces i w*u (F w)‖ₑ ∂μ := by
      congr 1
      funext x
      rw [identity kernel F u continuousU g pieces continuousPieces compactPieces supported reconstruct]
    _ ≤ ∫⁻ x, ∑ i, ‖∫ w, kernel (x-w)*pieces i w*u (F w)‖ₑ ∂μ :=
      lintegral_mono (fun _ => enorm_sum_le _ _)
    _ = ∑ i, ∫⁻ x, ‖∫ w, kernel (x-w)*pieces i w*u (F w)‖ₑ ∂μ :=
      lintegral_finsetSum _ (fun i _ => (measurable i).enorm)
    _ ≤ _ := Finset.sum_le_sum (fun i _ => rows i)

/-- The structural prefactor is paid once. The cylinder contribution is
exactly the sum of its joint intrinsic costs, without a counting factor. -/
theorem bound_of_cost (kernel : 𝓢(E,ℂ)) (F : OpenPartialHomeomorph E E)
    (u : E → ℂ) (continuousU : Continuous u) (g : E → ℂ) (pieces : I → E → ℂ)
    (continuousPieces : ∀ i, Continuous (pieces i))
    (compactPieces : ∀ i, HasCompactSupport (pieces i))
    (supported : ∀ i, tsupport (pieces i) ⊆ F.source)
    (reconstruct : ∀ x, g x = ∑ i, pieces i x) (μ : Measure E)
    (A B : ℝ≥0∞) (cost : I → ℝ≥0∞)
    (rows : ∀ i, (∫⁻ x, ‖∫ w, kernel (x-w)*pieces i w*u (F w)‖ₑ ∂μ) ≤
      A * (cost i * B)) :
    (∫⁻ x, ‖∫ w, kernel (x-w)*g w*u (F w)‖ₑ ∂μ) ≤
      A * ((∑ i, cost i) * B) := by
  have estimate := bound kernel F u continuousU g pieces continuousPieces compactPieces
    supported reconstruct μ (fun i => A * (cost i * B)) rows
  simpa only [Finset.mul_sum, Finset.sum_mul] using estimate

end LeanShared.PhysicalLocalAmplitudeRows
