module

public import ConditionedStochasticStabilityHyperbolic.Spectral.SameCutoffClassicalSources
public import ConditionedStochasticStabilityHyperbolic.Spectral.CanonicalChainGap
public import ConditionedStochasticStabilityHyperbolic.Spectral.LeadingSimplicity

/-! Choice-free rate identification for the universal physical-pair consumer.
Every real gap for the same actual cutoff operator has the rate produced by
KL and the actual retained spectral correspondence. -/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction NNReal
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999

variable {E W Z Zret Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Zret] [NormedSpace ℂ Zret]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {P : ℝ≥0 → E →L[ℂ] E} {i : E →L[ℂ] W}
  {d : DeterministicLeading (P 0)} {q δ : ℝ}

/-- In particular the universal supported-core factory need not assume a
rate equation for the arbitrary physical pair it receives. -/
theorem SameCutoffClassicalSources.normalized_cutoff_rate
    (o : ProjectorOutputs P i d q δ) (hδsub : δ < q - d.subordinate)
    (hδlead : δ < d.rate - q) (hq : 0 < q) (ε : ℝ≥0)
    (C D : AbsorbingMarkovChains.CanonicalChain Y)
    (hC : HasStrongFellerKernel C) (hD : HasStrongFellerKernel D) (R : ℝ) (hR : 0 < R)
    (s : SameCutoffClassicalSources (Z := Z) (Zret := Zret) o ε C D hC hD R)
    (dc : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hC)
      (1 : Y →ᵇ ℝ)) : dc.rate = (o.eigenvalue ε).re := by
  obtain ⟨dr, hr, _⟩ := (s.cutoffInputs o hδsub hδlead hq ε C D hC hD R hR).exists_gap
  let dn := CanonicalChainGap.normalized C hC R hR dr
  have heq : dc.rate = dn.rate := by
    have hh := congrArg ENNReal.toReal (dc.spectralRadius_eq_rate.symm.trans dn.spectralRadius_eq_rate)
    simpa only [ENNReal.toReal_ofReal dc.rate_pos.le, ENNReal.toReal_ofReal dn.rate_pos.le] using hh
  rw [heq, CanonicalChainGap.normalized_rate, hr]
  change R⁻¹ * (R * (o.eigenvalue ε).re) = _
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hR), one_mul]

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
