module

public import LeanShared.Analysis.SpectralProductConvergence
public import LeanShared.Probability.EigenvectorMeasure
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Conditional convergence of the actual eigenfunction/eigenmeasure product

The measures in this file are actual normalized densities `gₙ μₙ`. Their
products on a uniformly dense observable core agree with intermediate-space
spectral pairings through an explicit representation hypothesis. Dense-core dual
convergence, uniform dual bounds, and convergence of the right vectors then
give weak convergence of these probability measures.

The compact variant derives intermediate convergence from a compact
strong-to-intermediate inclusion and weak convergence through an injective
embedding. Existence of these spaces, the compact embedding, projector
estimates, spectral data and deterministic equilibrium identification are
not proved or assumed implicitly. This is not the local main theorem.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.QuasiErgodicStability

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

/-- The actual normalized spectral product, with no unit-mass assumption on `μ`. -/
def productProbabilityMeasure (μ : Measure X) [IsFiniteMeasure μ]
    (g : X →ᵇ ℝ) (hg0 : ∀ x, 0 ≤ g x) (hnorm : ∫ x, g x ∂μ = 1) :
    ProbabilityMeasure X :=
  ⟨LeanShared.eigenvectorMeasure μ g,
    LeanShared.eigenvectorMeasure_isProbability μ g (g.integrable μ) hg0 hnorm⟩

/-- The ordinary linear integral functional on bounded continuous tests. -/
def probabilityIntegralLinearMap (ν : ProbabilityMeasure X) : (X →ᵇ ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ x, f x ∂(ν : Measure X)
  map_add' f g := by
    simpa only [BoundedContinuousFunction.add_apply] using
      integral_add (f.integrable (ν : Measure X)) (g.integrable (ν : Measure X))
  map_smul' c f := by
    simpa only [BoundedContinuousFunction.smul_apply, smul_eq_mul, RingHom.id_apply] using
      integral_const_mul c (fun x => f x)

/-- Integration against a probability is a bounded functional of norm at most one. -/
def probabilityIntegralFunctional (ν : ProbabilityMeasure X) : (X →ᵇ ℝ) →L[ℝ] ℝ :=
  (probabilityIntegralLinearMap ν).mkContinuous 1 (fun f => by
    change ‖∫ x, f x ∂(ν : Measure X)‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using f.norm_integral_le_norm (ν : Measure X))

theorem probabilityIntegralFunctional_apply (ν : ProbabilityMeasure X) (f : X →ᵇ ℝ) :
    probabilityIntegralFunctional ν f = ∫ x, f x ∂(ν : Measure X) := rfl

theorem norm_probabilityIntegralFunctional_le_one (ν : ProbabilityMeasure X) :
    ‖probabilityIntegralFunctional ν‖ ≤ 1 := by
  apply LinearMap.mkContinuous_norm_le _ zero_le_one

@[simp]
theorem coe_productProbabilityMeasure (μ : Measure X) [IsFiniteMeasure μ]
    (g : X →ᵇ ℝ) (hg0 : ∀ x, 0 ≤ g x) (hnorm : ∫ x, g x ∂μ = 1) :
    (productProbabilityMeasure μ g hg0 hnorm : Measure X) =
      LeanShared.eigenvectorMeasure μ g := rfl

/-- Integration against the product probability is the ordinary density pairing. -/
theorem integral_productProbabilityMeasure (μ : Measure X) [IsFiniteMeasure μ]
    (g : X →ᵇ ℝ) (hg0 : ∀ x, 0 ≤ g x) (hnorm : ∫ x, g x ∂μ = 1) (h : X →ᵇ ℝ) :
    (∫ x, h x ∂(productProbabilityMeasure μ g hg0 hnorm : Measure X)) =
      ∫ x, h x * g x ∂μ := by
  rw [coe_productProbabilityMeasure]
  exact LeanShared.integral_eigenvectorMeasure μ g g.continuous.measurable hg0 h

section SpectralPairings

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} {L : Filter ι}

/-- Uniform density of observable tests suffices for weak convergence of
probabilities. This supplies the smooth-to-continuous approximation step. -/
theorem tendsto_probabilityMeasure_of_dense_tests
    (ν : ι → ProbabilityMeasure X) (ν₀ : ProbabilityMeasure X)
    (A : Set (X →ᵇ ℝ)) (hA : Dense A)
    (htest : ∀ h ∈ A, Tendsto (fun n => ∫ x, h x ∂(ν n : Measure X))
      L (𝓝 (∫ x, h x ∂(ν₀ : Measure X)))) :
    Tendsto ν L (𝓝 ν₀) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro h
  exact LeanShared.SpectralProductConvergence.tendsto_apply_of_dense
    (fun n => probabilityIntegralFunctional (ν n)) (probabilityIntegralFunctional ν₀)
    1 zero_le_one (Eventually.of_forall fun n => norm_probabilityIntegralFunctional_le_one (ν n))
    A hA htest h

/-- Spectral pairings representing actual probabilities imply weak convergence.
The duals need convergence only on a dense vector core. Multiplication and
representation are needed only on a uniformly dense observable core. -/
theorem tendsto_probabilityMeasure_of_spectral_pairings
    (μ : ι → E →L[ℝ] ℝ) (μ₀ : E →L[ℝ] ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ᶠ n in L, ‖μ n‖ ≤ C)
    (D : Set E) (hD : Dense D)
    (hcore : ∀ x ∈ D, Tendsto (fun n => μ n x) L (𝓝 (μ₀ x)))
    (γ : ι → E) (γ₀ : E) (hγ : Tendsto γ L (𝓝 γ₀))
    (A : Set (X →ᵇ ℝ)) (hA : Dense A) (M : A → E →L[ℝ] E)
    (ν : ι → ProbabilityMeasure X) (ν₀ : ProbabilityMeasure X)
    (hν : ∀ n (h : A), (∫ x, h.val x ∂(ν n : Measure X)) = μ n (M h (γ n)))
    (hν₀ : ∀ h : A, (∫ x, h.val x ∂(ν₀ : Measure X)) = μ₀ (M h γ₀)) :
    Tendsto ν L (𝓝 ν₀) := by
  apply tendsto_probabilityMeasure_of_dense_tests ν ν₀ A hA
  intro h hh
  have he := LeanShared.SpectralProductConvergence.tendsto_spectral_product
    μ μ₀ C hC hbound D hD hcore γ γ₀ hγ (M ⟨h, hh⟩)
  simpa only [← hν, ← hν₀] using he

/-- Concrete density-product probabilities converge weakly once their
spectral representations and intermediate-space convergence are supplied. -/
theorem tendsto_productProbabilityMeasure
    (μ : ι → E →L[ℝ] ℝ) (μ₀ : E →L[ℝ] ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ᶠ n in L, ‖μ n‖ ≤ C)
    (D : Set E) (hD : Dense D)
    (hcore : ∀ x ∈ D, Tendsto (fun n => μ n x) L (𝓝 (μ₀ x)))
    (γ : ι → E) (γ₀ : E) (hγ : Tendsto γ L (𝓝 γ₀))
    (A : Set (X →ᵇ ℝ)) (hA : Dense A) (M : A → E →L[ℝ] E)
    (ρ : ι → Measure X) [∀ n, IsFiniteMeasure (ρ n)]
    (g : ι → X →ᵇ ℝ) (hg0 : ∀ n x, 0 ≤ g n x)
    (hnorm : ∀ n, ∫ x, g n x ∂ρ n = 1)
    (hprod : ∀ n (h : A), μ n (M h (γ n)) = ∫ x, h.val x * g n x ∂ρ n)
    (ν₀ : ProbabilityMeasure X)
    (hν₀ : ∀ h : A, μ₀ (M h γ₀) = ∫ x, h.val x ∂(ν₀ : Measure X)) :
    Tendsto (fun n => productProbabilityMeasure (ρ n) (g n) (hg0 n) (hnorm n))
      L (𝓝 ν₀) := by
  apply tendsto_probabilityMeasure_of_spectral_pairings μ μ₀ C hC hbound D hD hcore
    γ γ₀ hγ A hA M _ ν₀
  · intro n h
    rw [integral_productProbabilityMeasure]
    exact (hprod n h).symm
  · intro h
    exact (hν₀ h).symm

omit [OpensMeasurableSpace X] in
/-- Spectral normalization and the constant-one multiplication identity
already imply normalization of the actual density measure. -/
theorem integral_density_eq_one_of_spectral_pairing
    (μ : E →L[ℝ] ℝ) (γ : E) (hpair : μ γ = 1)
    (A : Set (X →ᵇ ℝ)) (hAone : 1 ∈ A)
    (M : A → E →L[ℝ] E) (hMone : M ⟨1, hAone⟩ = 1)
    (ρ : Measure X) (g : X →ᵇ ℝ)
    (hprod : ∀ h : A, μ (M h γ) = ∫ x, h.val x * g x ∂ρ) :
    ∫ x, g x ∂ρ = 1 := by
  have he := hprod ⟨1, hAone⟩
  rw [hMone, one_apply_eq_self, hpair] at he
  simpa only [BoundedContinuousFunction.coe_one, Pi.one_apply, one_mul] using he.symm

section CompactUpgrade

variable {S W : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The compact/intermediate-space version needs only the genuine weak
right-vector convergence; intermediate convergence is derived here. -/
theorem tendsto_productProbabilityMeasure_of_compact
    (i : S →L[ℝ] E) (hi : IsCompactOperator i)
    (j : E →L[ℝ] W) (hj : Function.Injective j)
    (γ : ι → S) (R : ℝ) (hγbound : ∀ᶠ n in L, ‖γ n‖ ≤ R)
    (γ₀ : E) (hweak : Tendsto (fun n => j (i (γ n))) L (𝓝 (j γ₀)))
    (μ : ι → E →L[ℝ] ℝ) (μ₀ : E →L[ℝ] ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ᶠ n in L, ‖μ n‖ ≤ C)
    (D : Set E) (hD : Dense D)
    (hcore : ∀ x ∈ D, Tendsto (fun n => μ n x) L (𝓝 (μ₀ x)))
    (A : Set (X →ᵇ ℝ)) (hA : Dense A) (M : A → E →L[ℝ] E)
    (ρ : ι → Measure X) [∀ n, IsFiniteMeasure (ρ n)]
    (g : ι → X →ᵇ ℝ) (hg0 : ∀ n x, 0 ≤ g n x)
    (hnorm : ∀ n, ∫ x, g n x ∂ρ n = 1)
    (hprod : ∀ n (h : A), μ n (M h (i (γ n))) = ∫ x, h.val x * g n x ∂ρ n)
    (ν₀ : ProbabilityMeasure X)
    (hν₀ : ∀ h : A, μ₀ (M h γ₀) = ∫ x, h.val x ∂(ν₀ : Measure X)) :
    Tendsto (fun n => productProbabilityMeasure (ρ n) (g n) (hg0 n) (hnorm n))
      L (𝓝 ν₀) := by
  have hγ := LeanShared.SpectralProductConvergence.tendsto_intermediate_of_compact
    i hi j hj γ R hγbound γ₀ hweak
  exact tendsto_productProbabilityMeasure μ μ₀ C hC hbound D hD hcore
    (fun n => i (γ n)) γ₀ hγ A hA M ρ g hg0 hnorm hprod ν₀ hν₀

end CompactUpgrade

end SpectralPairings

end ConditionedStochasticStabilityHyperbolic.QuasiErgodicStability
