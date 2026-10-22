module

public import Mathlib.Analysis.Normed.Operator.Completeness
public import ConditionedStochasticStabilityHyperbolic.Spectral.ComplexPowerConvergence

/-! Common actual regular powers identify analytic and physical projectors.
The common distribution identity is needed only on literal smooth functions;
no family-specific projector comparison or high-regularity smoothing is assumed. -/

@[expose] public noncomputable section
open Set Filter
open scoped Topology BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.CommonRegularProjectors

variable {Reg H B Z Core : Type*}
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup B] [NormedSpace ℂ B]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]

/-- The projector identity follows from actual common regular powers and
ordinary norm convergence of the two normalized operator powers. -/
theorem comparison_of_powers
    (smooth : Core → Reg) (dense : DenseRange smooth)
    (i : Reg →L[ℂ] H) (j : Reg →L[ℂ] B)
    (a : H →L[ℂ] Z) (b : B →L[ℂ] Z)
    (T : Reg →L[ℂ] Reg) (P : H →L[ℂ] H) (Q : B →L[ℂ] B)
    (hP : i.comp T = P.comp i) (hQ : j.comp T = Q.comp j)
    (hcommon : ∀ c, b (j (smooth c)) = a (i (smooth c)))
    (Pa : H →L[ℂ] H) (Pb : B →L[ℂ] B)
    (hlimP : ∀ f, Tendsto (fun n : ℕ => (P^n) f) atTop (𝓝 (Pa f)))
    (hlimQ : ∀ f, Tendsto (fun n : ℕ => (Q^n) f) atTop (𝓝 (Pb f)))
    (v : Reg) : b (Pb (j v)) = a (Pa (i v)) := by
  have hc (v : Reg) : b (j v) = a (i v) := by
    exact dense.induction_on (p := fun v => b (j v) = a (i v)) v
      (isClosed_eq (b.continuous.comp j.continuous) (a.continuous.comp i.continuous)) hcommon
  have hi (v : Reg) : i (T v) = P (i v) :=
    congrArg (fun L : Reg →L[ℂ] H => L v) hP
  have hj (v : Reg) : j (T v) = Q (j v) :=
    congrArg (fun L : Reg →L[ℂ] B => L v) hQ
  have hpow (n : ℕ) : i ((T^n) v) = (P^n) (i v) ∧
      j ((T^n) v) = (Q^n) (j v) := by
    induction n with
    | zero => simp
    | succ n ih =>
        simp only [pow_succ', mul_apply_eq_comp, hi, hj]
        exact ⟨congrArg P ih.1, congrArg Q ih.2⟩
  have hp := a.continuous.continuousAt.tendsto.comp
    (hlimP (i v))
  have hq := b.continuous.continuousAt.tendsto.comp
    (hlimQ (j v))
  apply tendsto_nhds_unique hq
  apply hp.congr'
  exact Eventually.of_forall fun n => by
    change a ((P^n) (i v)) = b ((Q^n) (j v))
    rw [← (hpow n).1, ← (hpow n).2]
    exact (hc _).symm

/-- A produced real physical gap supplies the physical power limit. Thus
only the analytic KL power limit and literal common-function identity are
needed; SAME-cutoff Riesz projector comparison is a conclusion. -/
theorem comparison_of_actual_gap
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (smooth : Core → Reg) (dense : DenseRange smooth)
    (i : Reg →L[ℂ] H) (j : Reg →L[ℂ] (X →ᵇ ℂ))
    (a : H →L[ℂ] Z) (b : (X →ᵇ ℂ) →L[ℂ] Z)
    (T : Reg →L[ℂ] Reg) (P : H →L[ℂ] H)
    (C : AbsorbingMarkovChains.CanonicalChain X) (hSF : HasStrongFellerKernel C)
    (d : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hSF)
      (1 : X →ᵇ ℝ))
    (μ : MeasureTheory.Measure X) [MeasureTheory.IsFiniteMeasure μ]
    (hμ : ∀ f : X →ᵇ ℝ, d.mean f = ∫ x, f x ∂μ)
    (hP : i.comp T = P.comp i)
    (hQ : j.comp T = (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF).comp j)
    (hcommon : ∀ c, b (j (smooth c)) = a (i (smooth c)))
    (Pa : H →L[ℂ] H)
    (hlimP : Tendsto (fun n : ℕ => ((d.rate : ℂ)⁻¹ • P)^n) atTop (𝓝 Pa))
    (v : Reg) :
    b (((ComplexLeadingMeasure.integralFunctional μ).smulRight
      (AbsorbingMarkovChains.ComplexKernel.ofReal d.eigenvector)) (j v)) = a (Pa (i v)) := by
  apply comparison_of_powers smooth dense i j a b ((d.rate : ℂ)⁻¹ • T)
    ((d.rate : ℂ)⁻¹ • P)
    ((d.rate : ℂ)⁻¹ • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF)
    ?_ ?_ hcommon Pa _ ?_ ?_ v
  · apply ContinuousLinearMap.ext
    intro u
    simpa only [ContinuousLinearMap.comp_apply, smul_apply, map_smul] using
      congrArg ((d.rate : ℂ)⁻¹ • ·) (congrArg (fun L : Reg →L[ℂ] H => L u) hP)
  · apply ContinuousLinearMap.ext
    intro u
    simpa only [ContinuousLinearMap.comp_apply, smul_apply, map_smul] using
      congrArg ((d.rate : ℂ)⁻¹ • ·) (congrArg (fun L : Reg →L[ℂ] (X →ᵇ ℂ) => L u) hQ)
  · intro f
    exact (ContinuousLinearMap.apply ℂ H f).continuous.continuousAt.tendsto.comp hlimP
  · intro f
    apply ComplexPowerConvergence.tendsto_normalized_apply_of_intertwining
      (ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hSF)
      (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hSF) _ d μ hμ f
    intro f
    rw [CanonicalChainGap.realTransfer_eq]
    exact NoiseSpectralGap.complexTransfer_ofReal C hSF f

end ConditionedStochasticStabilityHyperbolic.CommonRegularProjectors
