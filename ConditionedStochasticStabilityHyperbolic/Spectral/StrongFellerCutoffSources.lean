module

public import ConditionedStochasticStabilityHyperbolic.Spectral.CutoffEigenvectorLifting
public import ConditionedStochasticStabilityHyperbolic.Spectral.StrongFellerSpectralInputs
public import ConditionedStochasticStabilityHyperbolic.Spectral.CutoffSpectralComparison

/-! # Constructing the spectral source packet from same-cutoff cited facts

Classical forward and reverse spectral comparison is applied only to the
same cutoff operator. Actual equal retained kernels and finite extinction
then construct the original-weight comparisons, separator and nonzero lift.
No density-continuity or higher-noise-regularity assumption is made.
None of those physical comparison conclusions is a supplied packet field.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
open Restriction

variable {E W Z Zret Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Zret] [NormedSpace ℂ Zret]
  [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {P : ℝ≥0 → E →L[ℂ] E} {i : E →L[ℂ] W}
  {d : DeterministicLeading (P 0)} {q δ : ℝ}

/-- The exact original-weight source packet is constructed through the
same-cutoff classical theorem and actual retained geometric certificates. -/
def strongFellerInputsOfSameCutoffSources
    (o : ProjectorOutputs P i d q δ) (hδsub : δ < q - d.subordinate)
    (hδlead : δ < d.rate - q) (hq : 0 < q) (ε : ℝ≥0) (hε : ε ≤ o.window)
    (conjugation : RealOperatorConjugation (P ε)) (scale : ℝ) (hscale : 0 < scale)
    (C D : AbsorbingMarkovChains.CanonicalChain Y)
    (hC : HasStrongFellerKernel C) (hD : HasStrongFellerKernel D)
    (V BC BD : Set Y) (hV : MeasurableSet V)
    (heq : LeanShared.SubtypeKernel.restrict C.killedTransition V hV =
      LeanShared.SubtypeKernel.restrict D.killedTransition V hV)
    (hreturnC : ∀ x : V, ∀ᵐ y ∂C.killedTransition x.val, y ∉ V → y ∈ BC)
    (hextC : ∀ x ∈ BC, ∃ n : ℕ,
      C.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0)
    (hreturnD : ∀ x : V, ∀ᵐ y ∂D.killedTransition x.val, y ∉ V → y ∈ BD)
    (hextD : ∀ x ∈ BD, ∃ n : ℕ,
      D.pathMeasure x (AbsorbingMarkovChains.CanonicalChain.survival n) = 0)
    (NC ND : ℕ)
    (hcompC : ∀ x : ↥(Vᶜ),
      ((LeanShared.SubtypeKernel.restrict C.killedTransition Vᶜ hV.compl) ^ NC) x univ = 0)
    (hcompD : ∀ x : ↥(Vᶜ),
      ((LeanShared.SubtypeKernel.restrict D.killedTransition Vᶜ hV.compl) ^ ND) x univ = 0)
    (R : ℝ) (hR : 0 < R)
    (aSource : E →L[ℂ] Z) (bSource : (Y →ᵇ ℂ) →L[ℂ] Z)
    (restrictSource : Z →L[ℂ] Zret) (ambientRetained : (V →ᵇ ℂ) →L[ℂ] Zret)
    (hRet : Function.Injective ambientRetained)
    (hcompat : restrictSource.comp bSource = ambientRetained.comp (restrictObservable V))
    (hordinary : ComparedSpectralGap.EigenvectorComparison ((scale : ℂ) • P ε)
      ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hC)
      aSource bSource (scale * q))
    (hgeneral : GeneralizedSpectralComparison.Comparison ((scale : ℂ) • P ε)
      ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hC)
      aSource bSource ((scale * (o.eigenvalue ε).re : ℝ) : ℂ))
    (hreverse : CutoffEigenvectorLifting.ClassicalRealization ((scale : ℂ) • P ε)
      ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hC)
      aSource bSource (scale * q))
    (hUltra : StrongFellerSquareCompact.UltraFellerContract (X := Y))
    (hFredholm : PowerCompactGap.SquareCompactFredholm (F := Y →ᵇ ℂ))
    (hRiesz : PowerCompactRealLeadingPair.ClassicalContract (X := Y)) :
    StrongFellerSpectralInputs (E := E) (W := W) (Z := Zret) D hD R := by
  let r := scale * (o.eigenvalue ε).re
  have hr : 0 < r := mul_pos hscale (hq.trans (o.eigenvalue_re_gt hδlead ε hε))
  have hz : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hR)
  have hzNorm : (R : ℂ)⁻¹ * (r : ℂ) ≠ 0 := mul_ne_zero (inv_ne_zero hRc) hz
  have hγ : o.vector ε ≠ 0 := by
    intro hzero
    have hn := o.normalization ε hε
    rw [hzero, map_zero] at hn
    exact zero_ne_one hn
  have hraw : ((scale : ℂ) • P ε) (o.vector ε) = (r : ℂ) • o.vector ε := by
    rw [smul_apply, o.right_equation ε hε, smul_smul,
      o.eigenvalue_eq_real hδsub hδlead ε hε conjugation]
    rw [← Complex.ofReal_mul]
  have hcutoff : scale * q < ‖(r : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hr.le]
    exact mul_lt_mul_of_pos_left (o.eigenvalue_re_gt hδlead ε hε) hscale
  have hlift := CutoffEigenvectorLifting.exists_actual_lift_of_cutoff_realization
    ((scale : ℂ) • P ε) C D hC hD V BC BD hV heq hreturnC hextC hreturnD hextD
    NC ND hcompC hcompD R hR aSource bSource restrictSource ambientRetained hcompat
    (scale * q) hreverse (o.vector ε) hγ (r : ℂ) hz hraw hcutoff
  let f := Classical.choose hlift
  have hf := (Classical.choose_spec hlift).1
  have hfEig := (Classical.choose_spec hlift).2.1
  have hfMatch := (Classical.choose_spec hlift).2.2
  have hmatching := CutoffSpectralComparison.matching_of_actual_kernel_certificates
    D C hD hC V BD BC hV heq.symm hreturnD hextD hreturnC hextC
    ND NC hcompD hcompC (R : ℂ) hRc
  have hphysicalOrd := CutoffSpectralComparison.eigenvector_comparison_of_same_cutoff
    ((scale : ℂ) • P ε) _ _ V hmatching aSource bSource restrictSource ambientRetained
    hcompat (scale * q) (mul_nonneg hscale.le hq.le) hordinary
  have hphysicalGen := CutoffSpectralComparison.generalized_comparison_of_same_cutoff
    ((scale : ℂ) • P ε) _ _ V hmatching aSource bSource restrictSource ambientRetained
    hcompat (r : ℂ) hz hgeneral
  have hseparator := scaled_separator_of_restriction
    (ComplexStrongFeller.transferOperator (𝕜 := ℂ) D hD) V ambientRetained hRet
    (R : ℂ) (r : ℂ) hRc (fun n v hv hzero =>
      generalized_restriction_separates D hD V BD hV hreturnD hextD
        ND hcompD hzNorm n v hv hzero)
  exact {
    rawScale_pos := hR
    analytic := P
    weak := i
    deterministic := d
    cutoff := q
    contour := δ
    outputs := o
    contour_subordinate := hδsub
    contour_leading := hδlead
    cutoff_pos := hq
    noiseParameter := ε
    parameter_small := hε
    conjugation := conjugation
    analyticScale := scale
    analyticScale_pos := hscale
    ultraFeller := hUltra
    squareFredholm := hFredholm
    analyticAmbient := restrictSource.comp aSource
    physicalAmbient := ambientRetained.comp (restrictObservable V)
    compactRiesz := hRiesz
    ordinaryComparison := hphysicalOrd
    generalizedComparison := hphysicalGen
    generalizedSeparator := hseparator
    physicalLift := f
    physicalLift_ne := hf
    physicalLift_match := hfMatch
    physicalLift_eigen := hfEig }

end ConditionedStochasticStabilityHyperbolic.KellerLiverani1999
