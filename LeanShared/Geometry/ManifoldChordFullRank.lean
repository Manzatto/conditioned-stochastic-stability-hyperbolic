module
public import LeanShared.Geometry.ManifoldDerivativeChordComparison
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! A chord comparison with an immersion gives full rank for an equal-
dimensional target. This is used by the actual inverse graph construction. -/
public noncomputable section
open Filter
open scoped Topology Manifold ContDiff
namespace LeanShared.ManifoldChordFullRank

theorem bijective_of_chord
    {U E M : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace U M]
    {f : M → E} {g : M → U} {x : M} {C : ℝ}
    (hf : ContMDiffAt (𝓘(ℝ, U)) (𝓘(ℝ, E)) 1 f x)
    (hg : ContMDiffAt (𝓘(ℝ, U)) (𝓘(ℝ, U)) 1 g x)
    (immersion : Function.Injective (mfderiv (𝓘(ℝ, U)) (𝓘(ℝ, E)) f x))
    (chord : ∀ᶠ z in 𝓝 x, ‖f z - f x‖ ≤ C * ‖g z - g x‖) :
    Function.Bijective (mfderiv (𝓘(ℝ, U)) (𝓘(ℝ, U)) g x) := by
  let e := tangentSpaceCastModel (𝓘(ℝ, U)) x
  let d : U →L[ℝ] U := (mvfderiv (𝓘(ℝ, U)) g x).comp e.symm.toContinuousLinearMap
  let j : U →L[ℝ] E := (mvfderiv (𝓘(ℝ, U)) f x).comp e.symm.toContinuousLinearMap
  have ji : Function.Injective j :=
    (NormedSpace.fromTangentSpace (f x)).injective.comp (immersion.comp e.symm.injective)
  have injective : Function.Injective d := by
    apply LinearMap.ker_eq_bot.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro v hv
    have zero : d v = 0 := hv
    have bound := DerivativeChordComparison.norm_mfderiv_apply_le_of_chord hf hg chord v
    change ‖j v‖ ≤ C * ‖d v‖ at bound
    rw [zero, norm_zero, mul_zero] at bound
    apply ji
    simpa only [map_zero] using norm_eq_zero.mp (le_antisymm bound (norm_nonneg _))
  have db : Function.Bijective d :=
    ⟨injective, LinearMap.surjective_of_injective (f := d.toLinearMap) injective⟩
  have equivalent : Function.Bijective
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (g x)).symm ∘ d ∘ e) :=
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (g x)).symm.bijective.comp (db.comp e.bijective)
  convert equivalent using 1
  ext v
  simp only [Function.comp_apply, d, ContinuousLinearMap.comp_apply,
    mvfderiv]
  change _ = (NormedSpace.fromTangentSpace (𝕜 := ℝ) (g x)).symm
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (g x))
      ((mfderiv (𝓘(ℝ, U)) (𝓘(ℝ, U)) g x) (e.symm (e v))))
  rw [e.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]
end LeanShared.ManifoldChordFullRank
