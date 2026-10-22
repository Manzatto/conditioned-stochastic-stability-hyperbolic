module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ComplexRestrictedNoiseIntegral
public import LeanShared.Analysis.AnnealedOperatorBounds

/-! The invariant regular average realizes the actual killed continuous
transfer. Only literal weighted-composition function values are supplied;
no completed physical intertwining or C0-to-regular smoothing is assumed. -/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.RegularAveragePhysicalTransfer

variable {Reg X Ω : Type*} [NormedAddCommGroup Reg] [NormedSpace ℂ Reg] [CompleteSpace Reg]
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

variable (ρ : Measure Ω) [IsProbabilityMeasure ρ]
  (F : X × Ω → X) (hF : Measurable F) (K : Set X) (hK : MeasurableSet K)
  (w : K → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
  (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
  (hSF : HasStrongFellerKernel (RestrictedNoise.chain ρ F hF K hK w hw R hR hwR))
  (view : Reg →ₗ[ℂ] (X → ℂ)) (physical : Reg →L[ℂ] (K →ᵇ ℂ))
  (hphysical : ∀ v (x : K), physical v x = view v x.val)
  (hzero : ∀ v x, x ∉ K → view v x = 0)
  (A : Ω → Reg →L[ℂ] Reg)
  (hmeas : ∀ v, AEStronglyMeasurable (fun ω => A ω v) ρ)
  (C : ℝ) (hbound : ∀ ω, ‖A ω‖ ≤ C)
  (hliteral : ∀ ω v (x : K), view (A ω v) x.val = (w x : ℂ) * view v (F (x.val, ω)))

include hphysical hzero hliteral in
omit [CompleteSpace Reg] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω] in
theorem literal_live_formula (ω : Ω) (v : Reg) (x : K) :
    physical (A ω v) x = (w x : ℂ) * ComplexStrongFeller.zeroExtend K (physical v) (F (x.val, ω)) := by
  rw [hphysical, hliteral]
  congr 1
  by_cases hy : F (x.val, ω) ∈ K
  · rw [ComplexStrongFeller.zeroExtend_coe K (physical v) ⟨F (x.val, ω), hy⟩]
    exact (hphysical v ⟨F (x.val, ω), hy⟩).symm
  · rw [ComplexStrongFeller.zeroExtend_of_not_mem K (physical v) _ hy, hzero v _ hy]

include hphysical hzero hliteral hw0 in
/-- Exact actual averaged physical action, including exit killing. -/
theorem average_intertwining :
    physical.comp (((R⁻¹ : ℝ) : ℂ) •
      LeanShared.AnnealedOperatorBounds.pointwiseAnnealed ρ A hmeas C hbound) =
    (ComplexStrongFeller.transferOperator (𝕜 := ℂ)
      (RestrictedNoise.chain ρ F hF K hK w hw R hR hwR) hSF).comp physical := by
  ext v x
  let ev : Reg →L[ℂ] ℂ := (BoundedContinuousFunction.evalCLM (𝕜 := ℂ) x).comp physical
  have hInt := LeanShared.AnnealedOperatorBounds.random_apply_integrable ρ A hmeas C hbound v
  have hint := ev.integral_comp_comm hInt
  simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul,
    BoundedContinuousFunction.smul_apply, smul_eq_mul,
    LeanShared.AnnealedOperatorBounds.pointwiseAnnealed_apply]
  change ((R⁻¹ : ℝ) : ℂ) * ev (∫ ω, A ω v ∂ρ) = _
  rw [← hint]
  have heq : (∫ ω, ev (A ω v) ∂ρ) = (w x : ℂ) *
      ∫ ω, ComplexStrongFeller.zeroExtend K (physical v) (F (x.val, ω)) ∂ρ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun ω => literal_live_formula F K w view physical hphysical hzero A hliteral ω v x
  rw [heq, ComplexStrongFeller.transferOperator_apply,
    RestrictedNoise.integral_chain_complex ρ F hF K hK w hw hw0 R hR hwR
      (physical v) (physical v).continuous.measurable x]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← div_eq_inv_mul]
  exact Complex.real_smul.symm

end ConditionedStochasticStabilityHyperbolic.RegularAveragePhysicalTransfer
