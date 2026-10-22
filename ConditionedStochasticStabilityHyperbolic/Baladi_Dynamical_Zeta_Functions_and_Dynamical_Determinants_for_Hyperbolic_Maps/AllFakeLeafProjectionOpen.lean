module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafBorelGeometry
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafModel
import all LeanShared.Analysis.FakeLeafGraph
public import LeanShared.Geometry.ManifoldDerivativeChordComparison
public import LeanShared.Geometry.ManifoldSubmersionOpen
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! Projection openness is derived from the actual embedded C¹ atlas and
chord slope condition, using the inverse function theorem. -/
public noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem C1Embedded.projection_open {U : Submodule ℝ E} {Γ : Set E}
    (embedded : C1Embedded U Γ) {L : ℝ} (hL : 0 ≤ L)
    (slope : ∀ x ∈ Γ, ∀ y ∈ Γ,
      ‖Uᗮ.starProjection (x-y)‖ ≤ L * ‖U.starProjection (x-y)‖) :
    IsOpen (FakeLeafGraph.parameterDomain U Γ) := by
  obtain ⟨atlas, manifold, smooth, immersion⟩ := embedded
  let : ChartedSpace U Γ := atlas
  let : IsManifold (𝓘(ℝ, U)) 1 Γ := manifold
  let p : Γ → U := fun x => U.orthogonalProjectionOnto (x : E)
  have ps : ContMDiff (𝓘(ℝ, U)) (𝓘(ℝ, U)) 1 p :=
    U.orthogonalProjectionOnto.contDiff.comp_contMDiff smooth
  have rank : ∀ x : Γ, Function.Surjective
      (mfderiv (𝓘(ℝ, U)) (𝓘(ℝ, U)) p x) := by
    intro x
    let e := tangentSpaceCastModel (𝓘(ℝ, U)) x
    let d : U →L[ℝ] U := (mvfderiv (𝓘(ℝ, U)) p x).comp e.symm.toContinuousLinearMap
    let j : U →L[ℝ] E :=
      (mvfderiv (𝓘(ℝ, U)) (Subtype.val : Γ → E) x).comp e.symm.toContinuousLinearMap
    have ji : Function.Injective j :=
      (NormedSpace.fromTangentSpace (x : E)).injective.comp
        ((immersion x).comp e.symm.injective)
    have injective : Function.Injective d := by
      apply (d.toLinearMap.ker_eq_bot).mp
      apply (Submodule.eq_bot_iff _).mpr
      intro v hv
      have zero : d v = 0 := hv
      have bound := DerivativeChordComparison.norm_mfderiv_apply_le_of_chord
        (smooth.contMDiffAt (x := x)) (ps.contMDiffAt (x := x))
        (C := (Real.toNNReal (1 + L) : ℝ))
        (Filter.Eventually.of_forall (fun y : Γ => by
          simpa only [Subtype.dist_eq, dist_eq_norm] using
            (ConeGraphGeometry.leafProjection_antilipschitz U hL slope).le_mul_dist y x)) v
      change ‖j v‖ ≤ (Real.toNNReal (1 + L) : ℝ) * ‖d v‖ at bound
      rw [zero, norm_zero, mul_zero] at bound
      apply ji
      simpa only [map_zero] using norm_eq_zero.mp (le_antisymm bound (norm_nonneg _))
    have surj := LinearMap.surjective_of_injective (f := d.toLinearMap) injective
    intro y
    obtain ⟨v, hv⟩ := surj (NormedSpace.fromTangentSpace (p x) y)
    refine ⟨e.symm v, ?_⟩
    apply (NormedSpace.fromTangentSpace (p x)).injective
    exact hv
  have result := SubmersionOpen.isOpen_image_of_mfderiv_surjective
    (f := p) isOpen_univ (fun x _ => ps.contMDiffAt) (fun x _ => rank x)
  change IsOpen (range p)
  simpa only [image_univ] using result
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
