module

public import ConditionedStochasticStabilityHyperbolic.Spectral.RetainedProductPairings
public import ConditionedStochasticStabilityHyperbolic.Spectral.NoiseSpectralGap

/-! # Physical product pairing through retained weights and smooth-core projectors

The actual original process and the analytic cutoff process can have different
full right eigenfunctions and different raw left measures. Harmonic restriction
first identifies their normalized product coefficients. Whole-core Riesz
projector compatibility and literal multiplier core realization then identify
the cutoff coefficient with the analytic pairing. No observable probability
pairing or physical measure limit is a premise.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.PhysicalProjectorPairing

open Restriction RetainedProductPairings

variable {X A W Core : Type*}
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

omit [MeasurableSpace X] [BorelSpace X] in
/-- Whole-core projector agreement extends to simultaneous realizations
in the completed analytic and physical spaces. No smoothness of the noisy
right eigenvector is required. -/
theorem coefficient_eq_of_completed_core_projectors
    (Pa : A →L[ℂ] A) (Pp : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ))
    (ma : A →L[ℂ] ℂ) (ℓ : (X →ᵇ ℂ) →L[ℂ] ℂ)
    (γ : A) (g : X →ᵇ ℂ) (hPa : Pa = ma.smulRight γ) (hPp : Pp = ℓ.smulRight g)
    (a : A →L[ℂ] W) (b : (X →ᵇ ℂ) →L[ℂ] W)
    (Ia : Core → A) (Ip : Core → (X →ᵇ ℂ))
    (hprojectors : ∀ u, b (Pp (Ip u)) = a (Pa (Ia u)))
    (c : ℂ) (hc : c ≠ 0) (hvector : b g = c • a γ) (hγ : a γ ≠ 0)
    (fa : A) (fp : X →ᵇ ℂ)
    (u : ℕ → Core) (hIp : Tendsto (fun n => Ip (u n)) atTop (𝓝 fp))
    (hIa : Tendsto (fun n => Ia (u n)) atTop (𝓝 (c • fa))) :
    ℓ fp = ma fa := by
  have hp := b.continuous.continuousAt.tendsto.comp
    (Pp.continuous.continuousAt.tendsto.comp hIp)
  have ha := a.continuous.continuousAt.tendsto.comp
    (Pa.continuous.continuousAt.tendsto.comp hIa)
  have ha' : Tendsto (fun n => b (Pp (Ip (u n)))) atTop (𝓝 (a (Pa (c • fa)))) :=
    ha.congr' (Eventually.of_forall (fun n => (hprojectors (u n)).symm))
  have he := tendsto_nhds_unique hp ha'
  rw [hPa, hPp, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, map_smul, hvector,
    map_smul, map_smul, smul_smul, smul_eq_mul] at he
  have hs := (smul_left_injective ℂ hγ) he
  apply mul_right_cancel₀ hc
  simpa only [mul_comm] using hs

/-- Derive the physical integration representation used by KL measure
stability from actual retained-kernel agreement and common smooth-core Riesz
projectors. Core multiplication is a literal realization condition; the
probability integral itself is proved rather than postulated. -/
theorem integral_eq_analytic_product
    (C D : AbsorbingMarkovChains.CanonicalChain X)
    (hC : HasStrongFellerKernel C) (hD : HasStrongFellerKernel D)
    (V BC BD : Set X) (hV : MeasurableSet V)
    (hreturnC : ∀ x : V, ∀ᵐ y ∂C.killedTransition x.val, y ∉ V → y ∈ BC)
    (hextC : ∀ x ∈ BC, ∃ n : ℕ,
      C.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0)
    (hreturnD : ∀ x : V, ∀ᵐ y ∂D.killedTransition x.val, y ∉ V → y ∈ BD)
    (hextD : ∀ x ∈ BD, ∃ n : ℕ,
      D.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0)
    (hkernel : LeanShared.SubtypeKernel.restrict C.killedTransition V hV =
      LeanShared.SubtypeKernel.restrict D.killedTransition V hV)
    (d : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hC)
      (1 : X →ᵇ ℝ))
    (e : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) D hD)
      (1 : X →ᵇ ℝ))
    (hRate : d.rate = e.rate) (s : ℝ) (hs : s ≠ 0)
    (hmatch : restrictObservable V d.eigenvector = s • restrictObservable V e.eigenvector)
    (hret : restrictObservable V e.eigenvector ≠ 0)
    (μ : Measure X) (hμ : ∀ f : X →ᵇ ℝ, d.mean f = ∫ x, f x ∂μ)
    (ℓ : (X →ᵇ ℂ) →L[ℂ] ℂ)
    (hreal : ∀ f, ℓ (AbsorbingMarkovChains.ComplexKernel.ofReal f) = (e.mean f : ℂ))
    (Pa : A →L[ℂ] A) (Pp : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ))
    (γ : A) (ma : A →L[ℂ] ℂ)
    (hPa : Pa = ma.smulRight γ)
    (hPp : Pp = ℓ.smulRight (AbsorbingMarkovChains.ComplexKernel.ofReal e.eigenvector))
    (a : A →L[ℂ] W) (b : (X →ᵇ ℂ) →L[ℂ] W)
    (Ia : Core → A) (Ip : Core → (X →ᵇ ℂ))
    (hprojectors : ∀ u, b (Pp (Ip u)) = a (Pa (Ia u)))
    (c : ℂ) (hc : c ≠ 0)
    (hvector : b (AbsorbingMarkovChains.ComplexKernel.ofReal e.eigenvector) = c • a γ)
    (hγ : a γ ≠ 0) (h : X →ᵇ ℝ) (M : A →L[ℝ] A)
    (u : ℕ → Core)
    (hIp : Tendsto (fun n => Ip (u n)) atTop
      (𝓝 (AbsorbingMarkovChains.ComplexKernel.ofReal (e.eigenvector * h))))
    (hIa : Tendsto (fun n => Ia (u n)) atTop (𝓝 (c • M γ))) :
    (∫ x, h x ∂LeanShared.eigenvectorMeasure μ d.eigenvector) = (ma (M γ)).re := by
  have hpos : ∀ f : X →ᵇ ℝ, (∀ x, 0 ≤ f x) →
      ∀ x, 0 ≤ ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hC f x := by
    intro f hf x
    rw [ComplexStrongFeller.transferOperator_apply]
    exact integral_nonneg hf
  rw [LeanShared.integral_eigenvectorMeasure μ d.eigenvector
    d.eigenvector.continuous.measurable (d.eigenvector_nonneg_of_positive hpos)]
  have hint : (∫ x, h x * d.eigenvector x ∂μ) = d.mean (d.eigenvector * h) := by
    rw [hμ]
    simp only [BoundedContinuousFunction.mul_apply, mul_comm]
  rw [hint, coefficient_eq_of_two_actual_weights C D hC hD V BC BD hV
    hreturnC hextC hreturnD hextD hkernel d e hRate s hs hmatch hret h]
  have hp := coefficient_eq_of_completed_core_projectors Pa Pp ma ℓ γ
    (AbsorbingMarkovChains.ComplexKernel.ofReal e.eigenvector) hPa hPp a b Ia Ip
    hprojectors c hc hvector hγ (M γ)
    (AbsorbingMarkovChains.ComplexKernel.ofReal (e.eigenvector * h)) u hIp hIa
  rw [hreal] at hp
  exact congrArg Complex.re hp

end ConditionedStochasticStabilityHyperbolic.PhysicalProjectorPairing
