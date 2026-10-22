module
public import LeanShared.Geometry.ManifoldHolderCanonicalCoordinates
public import LeanShared.Analysis.HolderPowerInterpolation
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-! Explicit power interpolation in the actual manifold little Holder
quotient. The finite chart norm lifting and all cutoff constants are
constructed; the uniform error is measured on the actual manifold function. -/
public noncomputable section
set_option maxHeartbeats 800000
open Set IsManifold
open scoped Manifold ContDiff BoundedContinuousFunction BigOperators
namespace LeanShared.ManifoldHolderPowerInterpolation
open ManifoldHolderCoordinateOperators ManifoldHolderCanonicalCoordinates
variable {E M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  (e : J→OpenPartialHomeomorph M E) {S : Set M}
  (D : ConstructedManifoldLocalization.Data e S)
  (atlas : ∀i,e i∈maximalAtlas (𝓘(ℝ,E)) ∞ M)
  {V : Set M} (openV : IsOpen V) {b : ℝ} (hb : 0<b) (hb1 : b<1)

@[expose] def cutoff (i : D.indices) : M→ᵇℂ :=
  ofCompactSupport (D.cutoff i) (D.smooth i).continuous (D.compact i)
@[expose] def cutoffConstant : ℝ := 1+∑i:D.indices,‖cutoff e D i‖

omit [FiniteDimensional ℝ E] in
theorem cutoffConstant_positive : 0<cutoffConstant e D := by
  have sumNonnegative : 0≤∑i:D.indices,‖cutoff e D i‖ := Finset.sum_nonneg fun i _=>norm_nonneg _
  dsimp only [cutoffConstant]
  linarith

omit [FiniteDimensional ℝ E] in
theorem cutoff_bound (i : D.indices) : ‖cutoff e D i‖≤cutoffConstant e D := by
  have bound : ‖cutoff e D i‖ ≤ ∑j:D.indices,‖cutoff e D j‖ :=
    Finset.single_le_sum (fun j _=>norm_nonneg (cutoff e D j)) (Finset.mem_univ i)
  exact bound.trans (by dsimp only [cutoffConstant];linarith)

theorem coordinate_uniform_bound (v : Regular e D openV hb hb1) {ε:ℝ} (hε:0≤ε)
    (error:∀x,‖ManifoldSmoothHolderCore.physical e D openV hb hb1 v x‖≤ε) (i:D.indices) :
    ‖EuclideanSmoothHolderCore.physical ((regions e D openV).compact_closure i) hb hb1
      (coordinates e D atlas openV hb hb1 v i)‖ ≤ cutoffConstant e D*ε := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (cutoffConstant_positive e D).le hε)).mpr
  intro y
  rw [localization_physical]
  by_cases target:y∈(e i).target
  · rw [ChartLocalization.coordinate,ite_eq_left target,norm_mul]
    have scalar : ‖D.cutoff i ((e i).symm y)‖ ≤ cutoffConstant e D :=
      ((cutoff e D i).norm_coe_le_norm _).trans (cutoff_bound e D i)
    exact mul_le_mul scalar (error _) (norm_nonneg _) (cutoffConstant_positive e D).le
  · rw [ChartLocalization.coordinate,ite_eq_right target,norm_zero]
    exact mul_nonneg (cutoffConstant_positive e D).le hε

theorem exists_power_bound {a:ℝ} (hab:b<a) (B C:D.indices→ℝ)
    (hB:∀i,0≤B i) (hC:∀i,0≤C i) (region:V⊆S) :
    ∃K:ℝ,0≤K ∧ ∀ (v:Regular e D openV hb hb1) (ε:ℝ),0≤ε →
      (∀x,‖ManifoldSmoothHolderCore.physical e D openV hb hb1 v x‖≤ε) →
      (∀i,‖EuclideanSmoothHolderCore.physical ((regions e D openV).compact_closure i) hb hb1
        (coordinates e D atlas openV hb hb1 v i)‖≤B i) →
      (∀i x y,‖EuclideanSmoothHolderCore.physical ((regions e D openV).compact_closure i) hb hb1
        (coordinates e D atlas openV hb hb1 v i) x-
        EuclideanSmoothHolderCore.physical ((regions e D openV).compact_closure i) hb hb1
          (coordinates e D atlas openV hb hb1 v i) y‖≤C i*dist x y^a) →
      ‖v‖≤K*ε^((a-b)/a) := by
  let coefficient (i:D.indices) : ℝ := (C i+3*B i+3)*(cutoffConstant e D)^((a-b)/a)
  have positiveCoefficient : ∀i,0≤coefficient i := fun i=>by
    dsimp only [coefficient]
    exact mul_nonneg (by linarith [hB i,hC i]) (Real.rpow_nonneg (cutoffConstant_positive e D).le _)
  refine ⟨∑i:D.indices,coefficient i,Finset.sum_nonneg (fun i _=>positiveCoefficient i),
    fun v ε hε error uniform increments=>?_⟩
  apply (norm_le_coordinates e D atlas openV hb hb1 region v).trans
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg (fun i _=>positiveCoefficient i))
    (Real.rpow_nonneg hε _))).mpr
  intro i
  have estimate := HolderInterpolation.power_norm_bound hb.le hab (hC i) (hB i)
    (mul_nonneg (cutoffConstant_positive e D).le hε)
    (coordinates e D atlas openV hb hb1 v i).val (uniform i)
    (coordinate_uniform_bound e D atlas openV hb hb1 v hε error i) (increments i)
  rw [Real.mul_rpow (cutoffConstant_positive e D).le hε,←mul_assoc] at estimate
  exact estimate.trans (mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun j _=>positiveCoefficient j) (Finset.mem_univ i))
    (Real.rpow_nonneg hε _))
end LeanShared.ManifoldHolderPowerInterpolation
