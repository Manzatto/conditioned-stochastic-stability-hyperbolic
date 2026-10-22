module

public import ConditionedStochasticStabilityHyperbolic.Restriction.GeometricSpectralRestriction

/-! # Agreement of weights on the retained region

Two full killed processes may have different departure weights outside the
retained region. Equality there gives equality of the actual restricted
kernels and transfers, without equality of the full eigenfunctions.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.Restriction

theorem restricted_weighted_kernel_eq
    {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (F : X × Ω → X) (hF : Measurable F)
    (K : Set X) (hK : MeasurableSet K) (V : Set K) (hV : MeasurableSet V)
    (w v : K → ℝ) (hw : Measurable w) (hv : Measurable v)
    (W : ℝ) (hW : 0 < W) (hwW : ∀ x, w x ≤ W) (hvW : ∀ x, v x ≤ W)
    (heq : ∀ x ∈ V, w x = v x) :
    LeanShared.SubtypeKernel.restrict
      (RestrictedNoise.chain ρ F hF K hK w hw W hW hwW).killedTransition V hV =
    LeanShared.SubtypeKernel.restrict
      (RestrictedNoise.chain ρ F hF K hK v hv W hW hvW).killedTransition V hV := by
  ext x A hA
  rw [LeanShared.SubtypeKernel.restrict_apply_set _ V hV x A hA,
    LeanShared.SubtypeKernel.restrict_apply_set _ V hV x A hA,
    RestrictedNoise.killedTransition, RestrictedNoise.killedTransition]
  simp only [LeanShared.WeightedConditioning.normalizedKernel,
    LeanShared.WeightedConditioning.realWeightedKernel_apply, heq x.val x.property]

theorem smoothedSubtypeTransfer_eq_of_kernel_eq
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type*} [RCLike 𝕜]
    (C D : AbsorbingMarkovChains.CanonicalChain X)
    (hC : HasStrongFellerKernel C) (hD : HasStrongFellerKernel D)
    (V : Set X) (hV : MeasurableSet V)
    (heq : LeanShared.SubtypeKernel.restrict C.killedTransition V hV =
      LeanShared.SubtypeKernel.restrict D.killedTransition V hV) :
    smoothedSubtypeTransfer (𝕜 := 𝕜) C hC V hV =
      smoothedSubtypeTransfer (𝕜 := 𝕜) D hD V hV := by
  ext f x
  rw [smoothedSubtypeTransfer_represents, smoothedSubtypeTransfer_represents, heq]

/-- A common restricted transfer and actual complement extinction compare
nonzero generalized eigenspaces of different full kernels. -/
theorem exists_matching_generalized_eigenfunction
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type*} [RCLike 𝕜]
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
    (N : ℕ) (hcompD : ∀ x : ↥(Vᶜ),
      ((LeanShared.SubtypeKernel.restrict D.killedTransition Vᶜ hV.compl) ^ N) x univ = 0)
    {z : 𝕜} (hz : z ≠ 0) (k : ℕ) (f : X →ᵇ 𝕜)
    (hf : ((ComplexStrongFeller.transferOperator (𝕜 := 𝕜) C hC - z • 1) ^ k) f = 0) :
    ∃ g : X →ᵇ 𝕜, restrictObservable V g = restrictObservable V f ∧
      ((ComplexStrongFeller.transferOperator (𝕜 := 𝕜) D hD - z • 1) ^ k) g = 0 := by
  have hrestricted : ((smoothedSubtypeTransfer (𝕜 := 𝕜) C hC V hV - z • 1) ^ k)
      (restrictObservable V f) = 0 := by
    rw [← restrict_shift_pow_generalized C V BC hV
      (ComplexStrongFeller.transferOperator C hC) (smoothedSubtypeTransfer C hC V hV)
      (ComplexStrongFeller.transferOperator_apply C hC)
      (smoothedSubtypeTransfer_represents C hC V hV) hextC hreturnC hz k f hf k,
      hf, map_zero]
  rw [smoothedSubtypeTransfer_eq_of_kernel_eq C D hC hD V hV heq] at hrestricted
  exact exists_strongFeller_lift_of_complement_extinction D hD V hV BD
    hreturnD hextD N hcompD hz k (restrictObservable V f) hrestricted

theorem exists_matching_nonzero_generalized_eigenfunction
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {𝕜 : Type*} [RCLike 𝕜]
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
    {z : 𝕜} (hz : z ≠ 0) (k : ℕ) (f : X →ᵇ 𝕜) (hne : f ≠ 0)
    (hf : ((ComplexStrongFeller.transferOperator (𝕜 := 𝕜) C hC - z • 1) ^ k) f = 0) :
    ∃ g : X →ᵇ 𝕜, g ≠ 0 ∧ restrictObservable V g = restrictObservable V f ∧
      ((ComplexStrongFeller.transferOperator (𝕜 := 𝕜) D hD - z • 1) ^ k) g = 0 := by
  obtain ⟨g, hRf, hg⟩ := exists_matching_generalized_eigenfunction C D hC hD V BC BD hV
    heq hreturnC hextC hreturnD hextD ND hcompD hz k f hf
  refine ⟨g, ?_, hRf, hg⟩
  intro hzero
  have hRfzero : restrictObservable V f = 0 := by rw [← hRf, hzero, map_zero]
  exact hne (generalized_restriction_separates C hC V BC hV hreturnC hextC
    NC hcompC hz k f hf hRfzero)

end ConditionedStochasticStabilityHyperbolic.Restriction
