module

public import ConditionedStochasticStabilityHyperbolic.Spectral.ComplexStrongFeller
public import LeanShared.Analysis.KernelIntegralSubsequence
public import LeanShared.Analysis.StrongFellerDominatingMeasure
public import LeanShared.Analysis.StrongFellerUniformDominated
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Topology.MetricSpace.ProperSpace

/-! Two actual strong-Feller steps take every bounded continuous sequence
to a uniformly convergent subsequence. No ultra-Feller contract is assumed. -/
public noncomputable section
open Filter Topology Set MeasureTheory ContinuousLinearMap
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.StrongFellerSquareCompact
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

omit [CompactSpace X] [BorelSpace X] in
private theorem continuous_rows (C : AbsorbingMarkovChains.CanonicalChain X)
    (sf : HasStrongFellerKernel C) (B : Set X) (hB : MeasurableSet B) :
    Continuous (fun x => (C.killedTransition x).real B) := by
  have hh := sf (B.indicator (fun _ => (1 : ℝ))) (measurable_const.indicator hB)
    ⟨1,zero_le_one,fun x => by
      by_cases hx : x ∈ B
      · rw [indicator_of_mem hx,norm_one]
      · rw [indicator_of_notMem hx,norm_zero]; exact zero_le_one⟩
  simpa only [integral_indicator_const (1 : ℝ) hB,smul_eq_mul,mul_one] using hh

/-- Actual norm-convergent subsequences of the squared complex transfer on
its unit ball, obtained through a common RN predual and uniform integration. -/
theorem square_subsequence (C : AbsorbingMarkovChains.CanonicalChain X)
    (sf : HasStrongFellerKernel C) (f : ℕ → X →ᵇ ℂ) (bound : ∀ n, ‖f n‖ ≤ 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ h : X →ᵇ ℂ,
      Tendsto (fun n => (ComplexStrongFeller.transferOperator (𝕜 := ℂ) C sf ^ 2) (f (φ n)))
        atTop (𝓝 h) := by
  let T := ComplexStrongFeller.transferOperator (𝕜 := ℂ) C sf
  let : ProbabilityTheory.IsFiniteKernel C.killedTransition := by
    change ProbabilityTheory.IsFiniteKernel C.toKilledKernel.kernel
    infer_instance
  let (x : X) : IsFiniteMeasure (C.killedTransition x) := inferInstance
  obtain ⟨μ,finiteμ,ac⟩ := LeanShared.StrongFellerDominatingMeasure.exists_finite
    C.killedTransition (C.killedTransition_mass_le_one) (continuous_rows C sf)
  let : IsFiniteMeasure μ := finiteμ
  let : Fact ((1 : ENNReal) ≤ 1) := ⟨le_rfl⟩
  let : Fact ((1 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  obtain ⟨φ,mono,g,limits⟩ := LeanShared.KernelIntegralSubsequence.exists_pointwise
    C.killedTransition μ ac (fun n => (f n : X → ℂ))
    (fun n => (f n).continuous.measurable) 1 zero_le_one
    (fun n x => ((f n).norm_coe_le_norm x).trans (bound n))
  have limits' (x : X) : Tendsto (fun n => T (f (φ n)) x) atTop (𝓝 (g x)) := limits x
  have normTf (n : ℕ) (x : X) : ‖T (f (φ n)) x‖ ≤ 1 :=
    ComplexStrongFeller.integral_norm_le C (f (φ n)) zero_le_one
      (fun y => ((f (φ n)).norm_coe_le_norm y).trans (bound _)) x
  have hg : Measurable g := measurable_of_tendsto_metrizable
    (fun n => (T (f (φ n))).continuous.measurable) (tendsto_pi_nhds.mpr limits')
  have gb (x : X) : ‖g x‖ ≤ 1 :=
    le_of_tendsto (limits' x).norm (Eventually.of_forall (fun n => normTf n x))
  let h := ComplexStrongFeller.integralFunction C sf g hg zero_le_one gb
  let difference : ℕ → X → ℂ := fun n x => T (f (φ n)) x-g x
  have measurableDifference (n : ℕ) : Measurable (difference n) :=
    (T (f (φ n))).continuous.measurable.sub hg
  have differenceBound (n : ℕ) (x : X) : ‖difference n x‖ ≤ 2 := by
    exact (norm_sub_le _ _).trans (by linarith [normTf n x,gb x])
  have convergence := LeanShared.StrongFellerUniformRows.uniform_dominated
    C.killedTransition (continuous_rows C sf) (StrongFeller.killedTransition_real_mass_le_one C)
    difference measurableDifference 2 (by norm_num) differenceBound
    (fun x => ae_of_all _ (fun y => by
      simpa only [sub_self] using (limits' y).sub_const (g y)))
  refine ⟨φ,mono,h,?_⟩
  rw [BoundedContinuousFunction.tendsto_iff_tendstoUniformly,Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp convergence ε hε] with n hn
  intro x
  have identity : (∫ y, difference n y ∂C.killedTransition x) =
      (T^2) (f (φ n)) x-h x := by
    rw [integral_sub]
    · rfl
    · exact ComplexStrongFeller.bounded_integrable C _
        (T (f (φ n))).continuous.measurable (normTf n) x
    · exact ComplexStrongFeller.bounded_integrable C g hg gb x
  have hn' := hn x
  rw [identity,dist_zero_left] at hn'
  simpa only [T,dist_eq_norm,norm_sub_rev] using hn'

end ConditionedStochasticStabilityHyperbolic.StrongFellerSquareCompact
