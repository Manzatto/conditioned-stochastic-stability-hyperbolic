module

public import AbsorbingMarkovChains.StandingHypothesis
public import AbsorbingMarkovChains.SmallTargets

@[expose] public section

/-!
# Uniformly small targets for the killed transition kernel

This is the first assertion of `lem:uniform-small-targets` in the actual
kernel notation: reference-measure-small sets have uniformly small one-step
transition probabilities under (H1). The proof uses the compact L¹ family
argument in `SmallTargets.lean` and the density equation in
`StandingHypothesis.lean`.

The second assertion, involving smallness in the quasi-ergodic measure, is
not proved here.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace AbsorbingMarkovChains

/-- The first small-target assertion requires only (H1): a continuous compact
family of nonnegative L¹ transition densities. No irreducibility, aperiodicity,
spectral data, or probability normalization is assumed in this theorem. -/
theorem uniform_small_targets_of_kernel_density
    {M Y : Type*} [TopologicalSpace M] [CompactSpace M]
    [MeasurableSpace M] [MeasurableSpace Y]
    (ρ : Measure Y) (K : Kernel M Y) (κ : M → Lp ℝ 1 ρ)
    (hκ : Continuous κ) (hκnonneg : ∀ x, ∀ᵐ y ∂ρ, 0 ≤ κ x y)
    (hK : ∀ x (A : Set Y), MeasurableSet A →
      K x A = ENNReal.ofReal (∫ y in A, κ x y ∂ρ))
    (U : ℕ → Set Y) (hUmeas : ∀ n, MeasurableSet (U n))
    (hU : Tendsto (fun n => ρ (U n)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x : M, (K x (U n)).toReal < ε := by
  intro ε hε
  filter_upwards [uniform_small_targets_of_continuous_L1 κ hκ U hU ε hε]
    with n hn x
  rw [hK x (U n) (hUmeas n),
    ENNReal.toReal_ofReal (integral_nonneg_of_ae (ae_restrict_of_ae (hκnonneg x)))]
  exact (le_abs_self _).trans_lt (hn x)

namespace StandingHypothesis

variable {M : Type*} [MeasurableSpace M] [MetricSpace M] [CompactSpace M] [BorelSpace M]
variable {ρ : Measure M} {K : KilledKernel M}

/-- First assertion of `lem:uniform-small-targets`, in epsilon/eventually
form, for the killed kernel supplied with the manuscript's standing data. -/
theorem HypothesisH.uniform_small_targets (h : HypothesisH ρ K)
    (U : ℕ → Set M) (hUmeas : ∀ n, MeasurableSet (U n))
    (hU : Tendsto (fun n => ρ (U n)) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ x : M, (K.kernel x (U n)).toReal < ε := by
  exact uniform_small_targets_of_kernel_density ρ K.kernel h.density
    h.continuous_density h.density_nonneg h.kernel_eq_integral U hUmeas hU

end StandingHypothesis

end AbsorbingMarkovChains
