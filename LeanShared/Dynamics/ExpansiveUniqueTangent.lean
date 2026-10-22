module
public import LeanShared.Dynamics.ExpansiveVariationalPrinciple
public import LeanShared.Dynamics.ExpansiveEntropyUpperSemicontinuity
public import LeanShared.Dynamics.CompactInvariantMeasures

/-! A unique equilibrium identifies every pressure tangent. On a compact expansive system, if `φ`
has a unique equilibrium `η` and a real number `ν` satisfies `t ν ≤ P(φ + t f) - P(φ)` for every
real `t`, then `ν = ∫ f dη`. Equilibria `μ_t` of the perturbed potentials satisfy `P(φ + t f) -
P(φ) ≤ t ∫ f dμ_t`; every cluster point of `μ_t` as `t → 0` is an equilibrium of `φ` by upper
semicontinuity of entropy, hence equals `η`. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set Function MeasureTheory Filter
open scoped BoundedContinuousFunction Topology
namespace LeanShared.ThermodynamicDefinitions

variable {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
  [MeasurableSpace X] [BorelSpace X]
  (T : X ≃ₜ X) (c : ℝ) (positive : 0 < c)
  (expansive : ∀ x y, (∀ n : ℕ,
      dist ((T : X → X)^[n] x) ((T : X → X)^[n] y) ≤ c ∧
      dist ((T.symm : X → X)^[n] x) ((T.symm : X → X)^[n] y) ≤ c) → x = y)

include positive expansive in
theorem entropy_eq_coe (μ : ProbabilityMeasure X)
    (invariant : MeasurePreserving T (μ : Measure X) (μ : Measure X)) :
    entropy T (μ : Measure X) = ((entropy T (μ : Measure X)).toReal : EReal) := by
  obtain ⟨k, P, _, mesh, _, _⟩ :=
    exists_expansive_null_boundary_generator T c positive expansive (μ : Measure X)
  rw [P.entropy_eq_generator_rate T c expansive (fun i x y hx hy => (mesh i x y hx hy).le) μ
    invariant, EReal.toReal_coe]

include positive expansive in
theorem free_energy_le (φ : X →ᵇ ℝ) (p : ℝ) (hp : pressure T φ univ = p) (μ : ProbabilityMeasure X)
    (invariant : MeasurePreserving T (μ : Measure X) (μ : Measure X)) :
    (entropy T (μ : Measure X)).toReal + ∫ x, φ x ∂(μ : Measure X) ≤ p := by
  have h := entropy_free_energy_le_pressure T c positive expansive μ invariant φ
  rw [entropy_eq_coe T c positive expansive μ invariant, hp, ← EReal.coe_add] at h
  exact EReal.coe_le_coe_iff.mp h

include positive expansive in
theorem equilibrium_free_energy (φ : X →ᵇ ℝ) (p : ℝ) (hp : pressure T φ univ = p)
    (μ : ProbabilityMeasure X) (hμ : IsEquilibriumState T φ univ μ) :
    (entropy T (μ : Measure X)).toReal + ∫ x, φ x ∂(μ : Measure X) = p := by
  have invariant : MeasurePreserving T (μ : Measure X) (μ : Measure X) := ⟨hμ.1, hμ.2.1⟩
  have h := hμ.2.2.2.2
  rw [entropy_eq_coe T c positive expansive μ invariant, hp, ← EReal.coe_add] at h
  exact EReal.coe_injective h

include positive expansive in
theorem equilibrium_of_free_energy (φ : X →ᵇ ℝ) (p : ℝ) (hp : pressure T φ univ = p)
    (μ : ProbabilityMeasure X) (invariant : MeasurePreserving T (μ : Measure X) (μ : Measure X))
    (energy : p ≤ (entropy T (μ : Measure X)).toReal + ∫ x, φ x ∂(μ : Measure X)) :
    IsEquilibriumState T φ univ μ := by
  refine ⟨invariant.measurable, invariant.map_eq, by simp, (φ.integrable (μ : Measure X)), ?_⟩
  rw [entropy_eq_coe T c positive expansive μ invariant, hp, ← EReal.coe_add]
  exact congrArg _ (le_antisymm (free_energy_le T c positive expansive φ p hp μ invariant) energy)

theorem integral_add_smul (φ f : X →ᵇ ℝ) (t : ℝ) (μ : ProbabilityMeasure X) :
    ∫ x, (φ + t • f) x ∂(μ : Measure X) =
      ∫ x, φ x ∂(μ : Measure X) + t * ∫ x, f x ∂(μ : Measure X) := by
  simp only [BoundedContinuousFunction.coe_add, BoundedContinuousFunction.coe_smul, Pi.add_apply,
    smul_eq_mul]
  rw [integral_add (φ.integrable _) ((f.integrable _).const_mul t), integral_const_mul]

theorem abs_integral_le (f : X →ᵇ ℝ) (μ : ProbabilityMeasure X) :
    |∫ x, f x ∂(μ : Measure X)| ≤ ‖f‖ := by
  rw [← Real.norm_eq_abs]
  exact BoundedContinuousFunction.norm_integral_le_norm (μ : Measure X) f

include positive expansive in
/-- Every cluster point of perturbed equilibria, as the perturbation vanishes, is `η`. -/
theorem cluster_eq (φ f : X →ᵇ ℝ) (η : ProbabilityMeasure X)
    (unique : ∀ μ, IsEquilibriumState T φ univ μ → μ = η)
    (P : ℝ → ℝ) (hP : ∀ t, pressure T (φ + t • f) univ = P t)
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0)) (μ : ℕ → ProbabilityMeasure X)
    (hμ : ∀ k, IsEquilibriumState T (φ + t k • f) univ (μ k))
    (lower : ∀ k, P 0 - |t k| * ‖f‖ ≤ P (t k))
    (ζ : ProbabilityMeasure X) (cluster : MapClusterPt ζ atTop μ) : ζ = η := by
  have hP0 : pressure T φ univ = P 0 := by simpa using hP 0
  have invariantSet := EmpiricalProbability.isClosed_invariant (T : X → X) T.continuous
  have invariantζ : MeasurePreserving T (ζ : Measure X) (ζ : Measure X) := by
    have mem : ζ ∈ closure {ν : ProbabilityMeasure X | MeasurePreserving T (ν : Measure X) (ν : Measure X)} :=
      closure_mono (by
        rintro _ ⟨k, _, rfl⟩
        exact ⟨(hμ k).1, (hμ k).2.1⟩) (mapClusterPt_atTop_iff_forall_mem_closure.mp cluster 0)
    rwa [invariantSet.closure_eq] at mem
  apply unique
  apply equilibrium_of_free_energy T c positive expansive φ (P 0) hP0 ζ invariantζ
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  have usc := entropy_toReal_upperSemicontinuousOn_invariant T c positive expansive ζ invariantζ
  have entropyNear : ∀ᶠ ν : ProbabilityMeasure X in
      𝓝[{ν : ProbabilityMeasure X | MeasurePreserving T (ν : Measure X) (ν : Measure X)}] ζ,
      (entropy T (ν : Measure X)).toReal < (entropy T (ζ : Measure X)).toReal + ε / 3 :=
    usc _ (by linarith)
  have integralNear : ∀ᶠ ν : ProbabilityMeasure X in 𝓝 ζ,
      ∫ x, φ x ∂(ν : Measure X) < ∫ x, φ x ∂(ζ : Measure X) + ε / 3 :=
    ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction φ).continuousAt).eventually
      (gt_mem_nhds (by linarith))
  have small : ∀ᶠ k in atTop, |t k| * ‖f‖ * 2 < ε / 3 := by
    have h : Tendsto (fun k => |t k| * ‖f‖ * 2) atTop (𝓝 0) := by
      simpa using ((ht.abs).mul_const ‖f‖).mul_const 2
    exact h.eventually (gt_mem_nhds (by linarith))
  rw [eventually_nhdsWithin_iff] at entropyNear
  have joint : ∃ᶠ k in atTop, ((μ k ∈ {ν : ProbabilityMeasure X |
      MeasurePreserving T (ν : Measure X) (ν : Measure X)} →
        (entropy T (μ k : Measure X)).toReal < (entropy T (ζ : Measure X)).toReal + ε / 3) ∧
      ∫ x, φ x ∂(μ k : Measure X) < ∫ x, φ x ∂(ζ : Measure X) + ε / 3) ∧
        |t k| * ‖f‖ * 2 < ε / 3 :=
    (cluster.frequently (entropyNear.and integralNear)).and_eventually small
  obtain ⟨k, ⟨hent, hint⟩, hsmall⟩ := joint.exists
  have invk : MeasurePreserving T (μ k : Measure X) (μ k : Measure X) := ⟨(hμ k).1, (hμ k).2.1⟩
  have energy := equilibrium_free_energy T c positive expansive (φ + t k • f) (P (t k)) (hP (t k))
    (μ k) (hμ k)
  rw [integral_add_smul] at energy
  have bound := abs_integral_le f (μ k)
  have hent' := hent invk
  have lowk := lower k
  have tf : t k * ∫ x, f x ∂(μ k : Measure X) ≤ |t k| * ‖f‖ := by
    calc t k * ∫ x, f x ∂(μ k : Measure X) ≤ |t k * ∫ x, f x ∂(μ k : Measure X)| := le_abs_self _
      _ = |t k| * |∫ x, f x ∂(μ k : Measure X)| := abs_mul _ _
      _ ≤ |t k| * ‖f‖ := mul_le_mul_of_nonneg_left bound (abs_nonneg _)
  nlinarith [abs_nonneg (t k), norm_nonneg f]

include positive expansive in
/-- A unique equilibrium identifies every pressure tangent. -/
theorem tangent_eq (φ f : X →ᵇ ℝ) (η : ProbabilityMeasure X)
    (hη : IsEquilibriumState T φ univ η)
    (unique : ∀ μ, IsEquilibriumState T φ univ μ → μ = η)
    (P : ℝ → ℝ) (hP : ∀ t, pressure T (φ + t • f) univ = P t) (ν : ℝ)
    (tangent : ∀ t : ℝ, t * ν ≤ P t - P 0) : ν = ∫ x, f x ∂(η : Measure X) := by
  have hP0 : pressure T φ univ = P 0 := by simpa using hP 0
  choose μ hμ using fun s : ℝ => exists_expansive_equilibrium T c positive expansive (φ + s • f)
  have invariantη : MeasurePreserving T (η : Measure X) (η : Measure X) := ⟨hη.1, hη.2.1⟩
  -- the variational comparisons
  have upper (s : ℝ) : P s - P 0 ≤ s * ∫ x, f x ∂(μ s : Measure X) := by
    have e := equilibrium_free_energy T c positive expansive (φ + s • f) (P s) (hP s) (μ s) (hμ s)
    have le := free_energy_le T c positive expansive φ (P 0) hP0 (μ s) ⟨(hμ s).1, (hμ s).2.1⟩
    rw [integral_add_smul] at e
    linarith
  have lower (s : ℝ) : P 0 - |s| * ‖f‖ ≤ P s := by
    have e := equilibrium_free_energy T c positive expansive φ (P 0) hP0 η hη
    have le := free_energy_le T c positive expansive (φ + s • f) (P s) (hP s) η invariantη
    rw [integral_add_smul] at le
    have bound := abs_integral_le f η
    have : -(|s| * ‖f‖) ≤ s * ∫ x, f x ∂(η : Measure X) := by
      have h := neg_abs_le (s * ∫ x, f x ∂(η : Measure X))
      rw [abs_mul] at h
      nlinarith [abs_nonneg s]
    linarith
  -- convergence of perturbed equilibria along both one-sided sequences
  have converge (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0)) :
      Tendsto (fun k => ∫ x, f x ∂(μ (t k) : Measure X)) atTop (𝓝 (∫ x, f x ∂(η : Measure X))) := by
    have measures : Tendsto (fun k => μ (t k)) atTop (𝓝 η) := by
      apply isCompact_univ.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall fun _ => mem_univ _)
      intro ζ _ cluster
      exact cluster_eq T c positive expansive φ f η unique P hP t ht (fun k => μ (t k))
        (fun k => hμ (t k)) (fun k => lower (t k)) ζ cluster
    exact ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).tendsto η).comp measures
  have plus : Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have minus : Tendsto (fun k : ℕ => -((1 : ℝ) / (k + 1))) atTop (𝓝 0) := by simpa using plus.neg
  have le1 : ν ≤ ∫ x, f x ∂(η : Measure X) := by
    refine ge_of_tendsto' (converge _ plus) fun k => ?_
    have pos : (0 : ℝ) < 1 / (k + 1) := by positivity
    have h := (tangent (1 / (k + 1))).trans (upper (1 / (k + 1)))
    exact le_of_mul_le_mul_left h pos
  have le2 : ∫ x, f x ∂(η : Measure X) ≤ ν := by
    refine le_of_tendsto' (converge _ minus) fun k => ?_
    have pos : (0 : ℝ) < 1 / (k + 1) := by positivity
    have h := (tangent (-(1 / (k + 1)))).trans (upper (-(1 / (k + 1))))
    have h' : (1 / (k + 1)) * ∫ x, f x ∂(μ (-(1 / (k + 1))) : Measure X) ≤ (1 / (k + 1)) * ν := by
      linarith
    exact le_of_mul_le_mul_left h' pos
  exact le_antisymm le1 le2

end LeanShared.ThermodynamicDefinitions
