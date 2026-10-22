module

public import LeanShared.Analysis.RankOneProjectorConvergence
public import ConditionedStochasticStabilityHyperbolic.Spectral.QuasiErgodicStability

/-! # Local probability stability from perturbative projector outputs

This application proves the dual convergence and dual bounds used in the
manuscript's vanishing-weight argument from projector convergence and a
uniform intermediate projector bound. It upgrades weak right-vector
convergence through the actual compact inclusion, then concludes weak
convergence of the actual normalized density products. Spectral perturbation
and the construction of the identified anisotropic spaces remain inputs;
convergence of the left functionals is a conclusion.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.ProjectorStability

variable {X S E W ι : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]
  [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {L : Filter ι}

/-- The actual product-probability limit requires weak projector convergence,
not a separately assumed convergence of left eigenfunctionals. The uniform
dual bound is also deduced from the intermediate projector bound. -/
theorem tendsto_productProbabilityMeasure_of_projectors
    (i : S →L[ℝ] E) (hi : IsCompactOperator i)
    (j : E →L[ℝ] W) (hj : Function.Injective j)
    (γ : ι → S) (R : ℝ) (hγbound : ∀ᶠ n in L, ‖γ n‖ ≤ R)
    (γ₀ : E) (hγ₀ : γ₀ ≠ 0)
    (hweak : Tendsto (fun n => j (i (γ n))) L (𝓝 (j γ₀)))
    (μ : ι → E →L[ℝ] ℝ) (μ₀ : E →L[ℝ] ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hprojbound : ∀ᶠ n in L, ‖(μ n).smulRight (i (γ n))‖ ≤ K)
    (D : Set E) (hD : Dense D)
    (hproj : ∀ x ∈ D, Tendsto (fun n => j ((μ n x) • i (γ n)))
      L (𝓝 (j ((μ₀ x) • γ₀))))
    (A : Set (X →ᵇ ℝ)) (hA : Dense A) (M : A → E →L[ℝ] E)
    (ρ : ι → Measure X) [∀ n, IsFiniteMeasure (ρ n)]
    (g : ι → X →ᵇ ℝ) (hg0 : ∀ n x, 0 ≤ g n x)
    (hnorm : ∀ n, ∫ x, g n x ∂ρ n = 1)
    (hprod : ∀ n (h : A), μ n (M h (i (γ n))) = ∫ x, h.val x * g n x ∂ρ n)
    (ν₀ : ProbabilityMeasure X)
    (hν₀ : ∀ h : A, μ₀ (M h γ₀) = ∫ x, h.val x ∂(ν₀ : Measure X)) :
    Tendsto (fun n => QuasiErgodicStability.productProbabilityMeasure
      (ρ n) (g n) (hg0 n) (hnorm n)) L (𝓝 ν₀) := by
  have hγ := LeanShared.SpectralProductConvergence.tendsto_intermediate_of_compact
    i hi j hj γ R hγbound γ₀ hweak
  have hjγ₀ : j γ₀ ≠ 0 := by
    intro hz
    apply hγ₀
    exact hj (hz.trans (map_zero j).symm)
  have hcore := LeanShared.RankOneProjectorConvergence.tendsto_dual_of_projectors
    j μ μ₀ (fun n => i (γ n)) γ₀ hjγ₀ hweak D hproj
  have hbound := LeanShared.RankOneProjectorConvergence.eventually_norm_dual_le
    μ (fun n => i (γ n)) γ₀ hγ₀ hγ K hK hprojbound
  apply QuasiErgodicStability.tendsto_productProbabilityMeasure
    μ μ₀ (K / (‖γ₀‖ / 2)) (div_nonneg hK (by positivity)) hbound D hD hcore
    (fun n => i (γ n)) γ₀ hγ A hA M ρ g hg0 hnorm hprod ν₀ hν₀

/-- With the perturbation theorem's range-coercivity estimate, the strong
right-vector bound is a conclusion as well. This is the projector-output
interface for the vanishing-weight local weak-stability argument. -/
theorem tendsto_productProbabilityMeasure_of_coercive_projectors
    (i : S →L[ℝ] E) (hi : IsCompactOperator i)
    (j : E →L[ℝ] W) (hj : Function.Injective j)
    (γ : ι → S) (γ₀ : E) (hγ₀ : γ₀ ≠ 0)
    (hweak : Tendsto (fun n => j (i (γ n))) L (𝓝 (j γ₀)))
    (Kstrong : ℝ) (hKstrong : 0 ≤ Kstrong)
    (hcoercive : ∀ᶠ n in L, ‖γ n‖ ≤ Kstrong * ‖j (i (γ n))‖)
    (μ : ι → E →L[ℝ] ℝ) (μ₀ : E →L[ℝ] ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hprojbound : ∀ᶠ n in L, ‖(μ n).smulRight (i (γ n))‖ ≤ K)
    (D : Set E) (hD : Dense D)
    (hproj : ∀ x ∈ D, Tendsto (fun n => j ((μ n x) • i (γ n)))
      L (𝓝 (j ((μ₀ x) • γ₀))))
    (A : Set (X →ᵇ ℝ)) (hA : Dense A) (M : A → E →L[ℝ] E)
    (ρ : ι → Measure X) [∀ n, IsFiniteMeasure (ρ n)]
    (g : ι → X →ᵇ ℝ) (hg0 : ∀ n x, 0 ≤ g n x)
    (hnorm : ∀ n, ∫ x, g n x ∂ρ n = 1)
    (hprod : ∀ n (h : A), μ n (M h (i (γ n))) = ∫ x, h.val x * g n x ∂ρ n)
    (ν₀ : ProbabilityMeasure X)
    (hν₀ : ∀ h : A, μ₀ (M h γ₀) = ∫ x, h.val x ∂(ν₀ : Measure X)) :
    Tendsto (fun n => QuasiErgodicStability.productProbabilityMeasure
      (ρ n) (g n) (hg0 n) (hnorm n)) L (𝓝 ν₀) := by
  have hbound := LeanShared.RankOneProjectorConvergence.eventually_norm_right_le
    (j.comp i) γ (j γ₀) hweak Kstrong hKstrong hcoercive
  exact tendsto_productProbabilityMeasure_of_projectors i hi j hj γ
    (Kstrong * (‖j γ₀‖ + 1)) hbound γ₀ hγ₀ hweak μ μ₀ K hK hprojbound
    D hD hproj A hA M ρ g hg0 hnorm hprod ν₀ hν₀

end ConditionedStochasticStabilityHyperbolic.ProjectorStability
