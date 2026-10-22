module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.AllFakeLeafIntegralControl
public import LeanShared.Analysis.AffineGraphSchwartzIntegrability
public import LeanShared.Analysis.ObliqueLeafPairing
import Mathlib.Tactic.Ring

/-! The actual full fake-leaf norm controls ambient Schwartz pairings by a
finite Schwartz seminorm. Cone geometry, graph measures and Fubini are derived. -/
public noncomputable section
open Set MeasureTheory
open scoped SchwartzMap
namespace ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
open LeanShared
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι]

theorem exists_schwartz_pairing_bound (U : Submodule ℝ E) (C : Set E)
    (cone : ConeData U C) (b : OrthonormalBasis ι ℝ U)
    (m : ℕ) (order : (Module.finrank ℝ Uᗮ:ℝ)<(m:ℝ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f test : 𝓢(E,ℂ)) (A : ℝ),
      (∀ Γ : Index U C, (∫ x, ‖f x‖ ∂inducedVolume U volume Γ.val) ≤ A) →
      ‖∫ x, f x*test x‖ ≤ D*A*ObliqueSchwartzDecay.seminorm m test := by
  obtain ⟨L,positive,_,control⟩ := exists_parallel_integral_control U C cone b
  let J := GraphJacobian.density b L
  let Q := (1+‖L‖)^m*2^m
  let W := ∫ v : Uᗮ, GraphLeafNorm.radialWeight (m:ℝ) v
  have hW : 0 ≤ W := integral_nonneg (fun v => GraphLeafNorm.radialWeight_nonneg (m:ℝ) v)
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  refine ⟨Q/J*W,mul_nonneg (div_nonneg hQ positive.le) hW,fun f test A bounded => ?_⟩
  have product : Integrable (fun x => f x*test x) :=
    f.integrable.mul_bdd test.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (SchwartzMap.norm_le_seminorm ℂ test))
  have leafIntegrable : ∀ v : Uᗮ, Integrable
      (fun u : U => f ((u:E)+(L u:E)+(v:E))) := by
    intro v
    exact AffineGraphParameter.schwartz_integrable U L v f
  have leafBound : ∀ v : Uᗮ, (∫ u : U, ‖f ((u:E)+(L u:E)+(v:E))‖) ≤ A/J :=
    control f A f.continuous bounded
  have result := ObliqueLeafPairing.bound U L f test (A/J)
    (Q*ObliqueSchwartzDecay.seminorm m test) (by dsimp only [Q]; positivity)
    (GraphLeafNorm.radialWeight (m:ℝ)) (GraphLeafNorm.radialWeight_nonneg _)
    (GraphLeafNorm.integrable_radialWeight volume order) product leafIntegrable leafBound
    (ObliqueSchwartzDecay.decay U L m test)
  change ‖∫ x, f x*test x‖ ≤ (Q*ObliqueSchwartzDecay.seminorm m test*(A/J))*W at result
  convert result using 1
  dsimp only [J]
  ring
end ConditionedStochasticStabilityHyperbolic.AllFakeLeafModel
