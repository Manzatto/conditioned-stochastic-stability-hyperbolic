module

public import ConditionedStochasticStabilityHyperbolic.Spectral.CanonicalChainGap
public import ConditionedStochasticStabilityHyperbolic.Restriction.WeightAgreement

/-! # Actual retained scalar correspondence of produced canonical right vectors

The two weights agree only on the retained kernel. Complement extinction
makes restriction injective on nonzero eigenspaces, and the actual geometric
lifting construction matches the cutoff right vector in the original process.
The produced original gap's simplicity then gives the required scalar.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.RetainedCanonicalVectors
open Restriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem exists_retained_scalar
    (C D : AbsorbingMarkovChains.CanonicalChain X)
    (hC : HasStrongFellerKernel C) (hD : HasStrongFellerKernel D)
    (V BC BD : Set X) (hV : MeasurableSet V)
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
    (d : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hC) (1 : X →ᵇ ℝ))
    (e : RankOneSpectralData (ComplexStrongFeller.transferOperator (𝕜 := ℝ) D hD) (1 : X →ᵇ ℝ))
    (hrate : d.rate = e.rate) :
    restrictObservable V e.eigenvector ≠ 0 ∧ ∃ c : ℝ, c ≠ 0 ∧
      restrictObservable V d.eigenvector = c • restrictObservable V e.eigenvector := by
  have heShift : ((ComplexStrongFeller.transferOperator (𝕜 := ℝ) D hD - e.rate • 1 :
      (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)) ^ 1) e.eigenvector = 0 := by
    simp only [pow_one, sub_apply, smul_apply, one_apply_eq_self, e.right_eigenvector, sub_self]
  have hrestrict : restrictObservable V e.eigenvector ≠ 0 := by
    intro hz
    exact e.eigenvector_ne_zero (generalized_restriction_separates D hD V BD hV
      hreturnD hextD ND hcompD (ne_of_gt e.rate_pos) 1 e.eigenvector heShift hz)
  obtain ⟨f, hf, hfRet, hfShift⟩ := exists_matching_nonzero_generalized_eigenfunction
    D C hD hC V BD BC hV heq.symm hreturnD hextD hreturnC hextC
    ND NC hcompD hcompC (ne_of_gt e.rate_pos) 1 e.eigenvector e.eigenvector_ne_zero heShift
  have hfEigen : ComplexStrongFeller.transferOperator (𝕜 := ℝ) C hC f = d.rate • f := by
    simpa only [pow_one, sub_apply, smul_apply, one_apply_eq_self, sub_eq_zero, ← hrate] using hfShift
  have hfScalar := d.leading_eigenvector_eq f hfEigen
  have hmean : d.mean f ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hfScalar
    exact hf hfScalar
  have hscale : restrictObservable V e.eigenvector =
      d.mean f • restrictObservable V d.eigenvector := by
    calc
      restrictObservable V e.eigenvector = restrictObservable V f := hfRet.symm
      _ = restrictObservable V (d.mean f • d.eigenvector) := congrArg (restrictObservable V) hfScalar
      _ = d.mean f • restrictObservable V d.eigenvector := map_smul _ _ _
  refine ⟨hrestrict, (d.mean f)⁻¹, inv_ne_zero hmean, ?_⟩
  rw [hscale, smul_smul, inv_mul_cancel₀ hmean, one_smul]

end ConditionedStochasticStabilityHyperbolic.RetainedCanonicalVectors
