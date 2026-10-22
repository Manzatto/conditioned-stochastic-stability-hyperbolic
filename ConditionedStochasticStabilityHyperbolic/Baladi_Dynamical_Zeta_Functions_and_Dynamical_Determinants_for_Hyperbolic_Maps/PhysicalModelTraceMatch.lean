module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelTraceIdentity
public import LeanShared.Dynamics.PeriodicWeightDistortion
meta import Lean.LibrarySuggestions.Basic

/-! The carrier trace integrand is the regularized Lefschetz chart integrand. With a real
kernel supported in the `ε`-ball, real chart cutoffs equal to `c_j · wt_j ∘ φ_j` and a bump
cutoff equal to one on the `ε`-neighbourhood of their chart supports, the integrand of the
regularized trace family is the coercion of the Lefschetz chart integrand. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelTraceMatch"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Filter
open scoped Manifold ContDiff SchwartzMap Topology BoundedContinuousFunction
attribute [local instance] Classical.propDecidable
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
open LeanShared DyadicCompletion PhysicalManifoldModel

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

/-- The real regularized Lefschetz chart integrand. -/
abbrev lefschetzIntegrand (T : M → M) (g : M → ℝ) (cR : M → ℝ) (e : OpenPartialHomeomorph M E)
    (κ : E → ℝ) (n : ℕ) (z : E) : ℝ :=
  Set.indicator e.target (fun z =>
    cR (e.symm z) * PeriodicChartChains.weightProduct T g n (e.symm z) *
      Set.indicator e.source (fun y => κ (e y - z)) (T^[n] (e.symm z))) z

theorem integrand_match (a : Ω) (n : ℕ) (j : m.localization.indices) (cut wt : 𝓢(E, ℂ))
    (κ : E → ℝ) (ε : ℝ) (hκ : ∀ t, ε < ‖t‖ → κ t = 0) (cR : M → ℝ)
    (hc : ∀ x ∈ (m.atlas j).source, (cR x : ℂ) = m.localization.cutoff j x * wt (m.atlas j x))
    (hcut : ∀ z ∈ (m.atlas j).target, cR ((m.atlas j).symm z) ≠ 0 →
      ∀ u, ‖u - z‖ ≤ ε → cut u = 1) (z : E) :
    traceIntegrand m a n j cut wt (fun t => (κ t : ℂ)) z =
      (lefschetzIntegrand (m.maps a) m.weight cR (m.atlas j) κ n z : ℂ) := by
  have key : ∀ c w W k u : ℂ, (c * w = 0 ∨ u = 1 ∨ k = 0) → c * W * w * (u * k) = c * w * W * k := by
    rintro c w W k u (h | h | h)
    · linear_combination W * (u - 1) * k * h
    · linear_combination c * w * W * k * h
    · rw [h]; ring
  unfold traceIntegrand lefschetzIntegrand
  by_cases hz : z ∈ (m.atlas j).target
  · rw [ite_eq_left hz, indicator_of_mem hz]
    have hx : (m.atlas j).symm z ∈ (m.atlas j).source := (m.atlas j).map_target hz
    have hcz := hc _ hx
    rw [(m.atlas j).right_inv hz] at hcz
    by_cases hs : (m.maps a)^[n] ((m.atlas j).symm z) ∈ (m.atlas j).source
    · rw [ite_eq_left hs, indicator_of_mem hs]
      simp only [orbitWeight, PeriodicChartChains.weightProduct]
      push_cast
      rw [hcz]
      refine key _ _ _ _ _ ?_
      by_cases hzero : cR ((m.atlas j).symm z) = 0
      · left
        rw [← hcz, hzero, Complex.ofReal_zero]
      · by_cases hfar : ε < ‖m.atlas j ((m.maps a)^[n] ((m.atlas j).symm z)) - z‖
        · exact Or.inr (Or.inr (by rw [hκ _ hfar, Complex.ofReal_zero]))
        · exact Or.inr (Or.inl (hcut z hz hzero _ (not_lt.mp hfar)))
    · rw [ite_eq_right hs, indicator_of_notMem hs]
      simp
  · rw [ite_eq_right hz, indicator_of_notMem hz]
    simp

/-- The chart sum of the carrier trace integrands is the coerced regularized Lefschetz trace of
any chart family indexed through an equivalence with the localization indices. -/
theorem trace_match (a : Ω) (n : ℕ) (tc : TraceCharts m) (ρ ρ' : 𝓢(E, ℂ)) (κ : E → ℝ)
    (hk : ∀ t, MollifierKernel.kernel ρ ρ' t = (κ t : ℂ)) (ε : ℝ) (hκ : ∀ t, ε < ‖t‖ → κ t = 0)
    {ι : Type*} [Fintype ι] (e : ι ≃ m.localization.indices) (chart : ι → OpenPartialHomeomorph M E)
    (hchart : ∀ i, chart i = m.atlas (e i)) (cR : ι → M → ℝ)
    (hc : ∀ i, ∀ x ∈ (m.atlas (e i)).source,
      (cR i x : ℂ) = m.localization.cutoff (e i) x * tc.wt (e i) (m.atlas (e i) x))
    (hcut : ∀ i, ∀ z ∈ (m.atlas (e i)).target, cR i ((m.atlas (e i)).symm z) ≠ 0 →
      ∀ u, ‖u - z‖ ≤ ε → tc.cut (e i) u = 1) :
    ∑ k, ∫ z, traceIntegrand m a n (chartEquiv m k) (tc.cut (chartEquiv m k))
        (tc.wt (chartEquiv m k)) (MollifierKernel.kernel ρ ρ') z =
      ((∑ i, ∫ z, lefschetzIntegrand (m.maps a) m.weight (cR i) (chart i) κ n z : ℝ) : ℂ) := by
  let F : m.localization.indices → ℂ := fun j =>
    ∫ z, traceIntegrand m a n j (tc.cut j) (tc.wt j) (MollifierKernel.kernel ρ ρ') z
  have kernelEq : MollifierKernel.kernel ρ ρ' = fun t => (κ t : ℂ) := funext hk
  calc ∑ k, F (chartEquiv m k) = ∑ j, F j := Equiv.sum_comp _ F
    _ = ∑ i, F (e i) := (Equiv.sum_comp e F).symm
    _ = ∑ i, ((∫ z, lefschetzIntegrand (m.maps a) m.weight (cR i) (chart i) κ n z : ℝ) : ℂ) :=
        Finset.sum_congr rfl fun i _ => by
          simp only [F]
          rw [hchart i, ← integral_complex_ofReal, kernelEq]
          exact integral_congr_ae (ae_of_all _ fun z =>
            integrand_match m a n (e i) _ _ κ ε hκ (cR i) (hc i) (hcut i) z)
    _ = _ := (Complex.ofReal_sum _ _).symm

end ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
