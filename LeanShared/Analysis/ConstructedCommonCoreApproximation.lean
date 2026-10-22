module

public import LeanShared.Analysis.CommonFiniteRegularTransferCompatibility
public import Mathlib.Topology.Sequences

/-!
# Simultaneous completed approximants from ordinary core density

One ordinary little-regularity core sequence converges through both
continuous realizations. The simultaneous anisotropic approximation is
therefore constructed from density and exact core identities; it is not
an additional approximation hypothesis about two unrelated spaces.
-/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace LeanShared.ConstructedCommonCoreApproximation

open DyadicCompletion

variable {Core High Low VS VW : Type*} [AddCommGroup Core] [Module ℂ Core]
  [NormedAddCommGroup High] [NormedSpace ℂ High]
  [NormedAddCommGroup Low] [NormedSpace ℂ Low]
  [NormedAddCommGroup VS] [NormedSpace ℂ VS]
  [NormedAddCommGroup VW] [NormedSpace ℂ VW]

/-- Choose smooth approximants in the ordinary little-regularity norm. -/
theorem exists_regular_sequence (regularCore : Core →ₗ[ℂ] High)
    (dense : DenseRange regularCore) (f : High) :
    ∃ c : ℕ → Core, Tendsto (fun n => regularCore (c n)) atTop (𝓝 f) := by
  classical
  obtain ⟨z, hz, hlim⟩ := mem_closure_iff_seq_limit.mp (dense f)
  choose c hc using hz
  refine ⟨c, ?_⟩
  convert hlim using 1
  funext n
  exact hc n

/-- The same ordinary sequence realizes both actual completed core norms. -/
theorem exists_simultaneous
    (qS : Core →ₗ[ℂ] VS) (qW : Core →ₗ[ℂ] VW)
    (regularCore : Core →ₗ[ℂ] High) (dense : DenseRange regularCore)
    (downgrade : High →L[ℂ] Low)
    (realizeStrong : High →L[ℂ] closedCore qS)
    (realizeWeak : Low →L[ℂ] closedCore qW)
    (strong_core : ∀ c, realizeStrong (regularCore c) = coreLift qS c)
    (weak_core : ∀ c, realizeWeak (downgrade (regularCore c)) = coreLift qW c) :
    ∃ approximation : High → ℕ → Core,
      (∀ f, Tendsto (fun n => coreLift qS (approximation f n)) atTop (𝓝 (realizeStrong f))) ∧
      ∀ f, Tendsto (fun n => coreLift qW (approximation f n)) atTop
        (𝓝 (realizeWeak (downgrade f))) := by
  classical
  choose a ha using fun f => exists_regular_sequence regularCore dense f
  refine ⟨a, ?_, ?_⟩
  · intro f
    simpa only [Function.comp_def, strong_core] using
      realizeStrong.continuous.tendsto f |>.comp (ha f)
  · intro f
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, weak_core] using
      (realizeWeak.comp downgrade).continuous.tendsto f |>.comp (ha f)

end LeanShared.ConstructedCommonCoreApproximation
