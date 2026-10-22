module

public import ConditionedStochasticStabilityHyperbolic.Restriction.WeightAgreement
public import ConditionedStochasticStabilityHyperbolic.Spectral.ProducedSpectralInputs

/-! # Analytic eigenvector realization followed by actual retained lifting

Classical cross-space comparison is applied to the same cutoff operator. The
original-weight eigenfunction is then constructed from the actual common
retained kernel and finite complement extinction. Ambient agreement is only
asserted after restriction, so the two full eigenfunctions may differ.
-/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.CutoffEigenvectorLifting

variable {E Z Zret X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]
  [NormedAddCommGroup Zret] [NormedSpace ℂ Zret]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The converse part of ordinary classical common-space spectral
comparison, for the exact same cutoff operator and weights. -/
def ClassicalRealization (P : E →L[ℂ] E) (Q : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ))
    (a : E →L[ℂ] Z) (b : (X →ᵇ ℂ) →L[ℂ] Z) (ρ : ℝ) : Prop :=
  ∀ γ, γ ≠ 0 → ∀ z : ℂ, P γ = z • γ → ρ < ‖z‖ →
    ∃ f : X →ᵇ ℂ, f ≠ 0 ∧ Q f = z • f ∧ b f = a γ

/-- Actual geometry lifts the same-cutoff classical eigenfunction to the
original process. The resulting nonzero physical eigenfunction and retained
ambient matching discharge the corresponding produced-gap packet fields. -/
theorem exists_actual_lift_of_cutoff_realization
    (P : E →L[ℂ] E)
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
    (R : ℝ) (hR : 0 < R)
    (aSource : E →L[ℂ] Z) (bSource : (X →ᵇ ℂ) →L[ℂ] Z)
    (restrictSource : Z →L[ℂ] Zret) (ambientRetained : (V →ᵇ ℂ) →L[ℂ] Zret)
    (hcompat : restrictSource.comp bSource = ambientRetained.comp (Restriction.restrictObservable V))
    (ρ : ℝ)
    (hclassical : ClassicalRealization P
      ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hC) aSource bSource ρ)
    (γ : E) (hγ : γ ≠ 0) (z : ℂ) (hz : z ≠ 0)
    (hγeigen : P γ = z • γ) (hρz : ρ < ‖z‖) :
    ∃ g : X →ᵇ ℂ, g ≠ 0 ∧
      ((R : ℂ) • ComplexStrongFeller.transferOperator (𝕜 := ℂ) D hD) g = z • g ∧
      (ambientRetained.comp (Restriction.restrictObservable V)) g =
        (restrictSource.comp aSource) γ := by
  obtain ⟨f, hf, heigen, hmatch⟩ := hclassical γ hγ z hγeigen hρz
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hR)
  have hz' : (R : ℂ)⁻¹ * z ≠ 0 := mul_ne_zero (inv_ne_zero hRc) hz
  have hnormalized : ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hC f =
      ((R : ℂ)⁻¹ * z) • f := by
    have he := congrArg (fun v : X →ᵇ ℂ => (R : ℂ)⁻¹ • v) heigen
    simpa only [smul_apply, smul_smul, inv_mul_cancel₀ hRc, one_smul] using he
  have hshift : ((ComplexStrongFeller.transferOperator (𝕜 := ℂ) C hC -
      ((R : ℂ)⁻¹ * z) • 1 : (X →ᵇ ℂ) →L[ℂ] (X →ᵇ ℂ)) ^ 1) f = 0 := by
    simp only [pow_one, sub_apply, smul_apply, one_apply_eq_self, hnormalized, sub_self]
  obtain ⟨g, hg, hrestrict, hgeneig⟩ := Restriction.exists_matching_nonzero_generalized_eigenfunction
    C D hC hD V BC BD hV heq hreturnC hextC hreturnD hextD NC ND hcompC hcompD
    hz' 1 f hf hshift
  have hnormalizedD : ComplexStrongFeller.transferOperator (𝕜 := ℂ) D hD g =
      ((R : ℂ)⁻¹ * z) • g := by
    simpa only [pow_one, sub_apply, smul_apply, one_apply_eq_self, sub_eq_zero] using hgeneig
  refine ⟨g, hg, ?_, ?_⟩
  · rw [smul_apply, hnormalizedD, smul_smul, ← mul_assoc, mul_inv_cancel₀ hRc, one_mul]
  · change ambientRetained (Restriction.restrictObservable V g) = restrictSource (aSource γ)
    rw [hrestrict]
    have hcompatf := congrArg (fun A : (X →ᵇ ℂ) →L[ℂ] Zret => A f) hcompat
    simp only [ContinuousLinearMap.comp_apply] at hcompatf
    rw [← hcompatf, hmatch]

end ConditionedStochasticStabilityHyperbolic.CutoffEigenvectorLifting
