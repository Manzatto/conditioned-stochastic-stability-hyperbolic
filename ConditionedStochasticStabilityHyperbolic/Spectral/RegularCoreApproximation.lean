module

public import Mathlib.Topology.Sequences
public import Mathlib.Analysis.Normed.Operator.Basic
public import AbsorbingMarkovChains.ComplexKernelOperator

/-! # Simultaneous multiplier approximation from a common regular range

A classical regular-noise range can be realized continuously in both the
physical continuous space and the intermediate anisotropic space. Density of
smooth functions in that regular range supplies simultaneous approximants.
Multiplication compatibility is imposed on the entire regular space, rather
than on the desired probability integral or on one target coefficient.
-/

@[expose] public noncomputable section
open Filter
open scoped Topology BoundedContinuousFunction

namespace ConditionedStochasticStabilityHyperbolic.RegularCoreApproximation

/-- The precise admissible margins for a common `C^u` regular-noise range.
The strict margin `u < r-1` permits smooth approximation of a `C^(r-1)` noisy
right vector in a weaker regular norm; `t < u` permits its isotropic embedding.
The full anisotropic pair also satisfies the manuscript's restriction. -/
structure RegularityMargins (r t s u : ℝ) : Prop where
  r_one : 1 < r
  t_pos : 0 < t
  s_neg : s < 0
  admissible : t - (r - 1) < s
  t_lt_u : t < u
  u_lt_order : u < r - 1

variable {Reg A Core X : Type*}
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  [NormedAddCommGroup A] [NormedSpace ℂ A] [TopologicalSpace X]

/-- The two maps are actual realizations of the same regular functions.
Their compatibility with projectors remains a separate whole-core theorem. -/
structure Realization where
  smooth : Core → Reg
  dense : DenseRange smooth
  analytic : Reg →L[ℂ] A
  physical : Reg →L[ℂ] (X →ᵇ ℂ)

/-- Density in the regular range gives simultaneous analytic and physical
limits; no approximation sequences need to be supplied independently. -/
theorem exists_simultaneous_approximants
    (D : Realization (Reg := Reg) (A := A) (Core := Core) (X := X)) (v : Reg) :
    ∃ u : ℕ → Core,
      Tendsto (fun n => D.physical (D.smooth (u n))) atTop (𝓝 (D.physical v)) ∧
      Tendsto (fun n => D.analytic (D.smooth (u n))) atTop (𝓝 (D.analytic v)) := by
  obtain ⟨z, hz, hlim⟩ := mem_closure_iff_seq_limit.mp (D.dense v)
  choose u hu using hz
  refine ⟨u, ?_, ?_⟩
  · convert D.physical.continuous.continuousAt.tendsto.comp hlim using 1
    ext n
    rw [hu n]
    rfl
  · convert D.analytic.continuous.continuousAt.tendsto.comp hlim using 1
    ext n
    rw [hu n]
    rfl

/-- Applying an actual regular multiplier yields simultaneous approximants
for a noisy harmonic product. The noisy harmonic vector itself need not be
smooth. All multiplier compatibility laws hold on the full regular range. -/
theorem exists_product_approximants
    (D : Realization (Reg := Reg) (A := A) (Core := Core) (X := X))
    (Mt : Reg →L[ℂ] Reg) (Ma : A →L[ℂ] A) (h : X →ᵇ ℝ)
    (hphysical : ∀ v, D.physical (Mt v) =
      D.physical v * AbsorbingMarkovChains.ComplexKernel.ofReal h)
    (hanalytic : D.analytic.comp Mt = Ma.comp D.analytic)
    (v : Reg) (g : X →ᵇ ℝ) (γ : A) (c : ℂ)
    (hg : D.physical v = AbsorbingMarkovChains.ComplexKernel.ofReal g)
    (hγ : D.analytic v = c • γ) :
    ∃ u : ℕ → Core,
      Tendsto (fun n => D.physical (D.smooth (u n))) atTop
        (𝓝 (AbsorbingMarkovChains.ComplexKernel.ofReal (g * h))) ∧
      Tendsto (fun n => D.analytic (D.smooth (u n))) atTop (𝓝 (c • Ma γ)) := by
  obtain ⟨u, hup, hua⟩ := exists_simultaneous_approximants D (Mt v)
  have hp : D.physical (Mt v) = AbsorbingMarkovChains.ComplexKernel.ofReal (g * h) := by
    rw [hphysical, hg]
    ext x
    simp [AbsorbingMarkovChains.ComplexKernel.ofReal_apply]
  have ha : D.analytic (Mt v) = c • Ma γ := by
    have he := congrArg (fun T : Reg →L[ℂ] A => T v) hanalytic
    simp only [ContinuousLinearMap.comp_apply] at he
    rw [he, hγ, map_smul]
  exact ⟨u, hp ▸ hup, ha ▸ hua⟩

end ConditionedStochasticStabilityHyperbolic.RegularCoreApproximation
