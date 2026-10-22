module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNativeRadiusUpper
public import LeanShared.Geometry.SmoothWeightCutoff
meta import Lean.LibrarySuggestions.Basic

/-! Regular inputs of the positive spectral point. A smooth core cutoff equal to one on the image
`T(tsupport g)` makes the regular action produce a regular element whose view is the weight
itself; a faithful test distribution with a constant-one test gives a strong pairing restricting
to the reference integral on realized regular inputs. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelLeadingInputs"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory
open scoped Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelLeadingInputs
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

/-- The weight is the view of a regular element. -/
theorem seed_exists (a : Ω) (mapCont : Continuous (m.maps a)) (openV : IsOpen V)
    (forwardSupport : m.maps a '' tsupport m.weight ⊆ V) :
    ∃ seed : Reg, ∀ x, m.view seed x = (m.weight x : ℂ) := by
  obtain ⟨ζ, smoothζ, _, supportζ, oneζ⟩ := SmoothWeightCutoff.exists_cutoff (E := E)
    (m.maps a '' tsupport m.weight) V ((isClosed_tsupport _).isCompact.image mapCont) openV
    forwardSupport
  let c : SmoothSupportedManifoldCore.core (E := E) V :=
    ⟨fun x => (ζ x : ℂ), Complex.ofRealCLM.contMDiff.comp smoothζ,
      (tsupport_comp_subset Complex.ofReal_zero ζ).trans supportζ⟩
  obtain ⟨seed, hseed⟩ := m.invariant a (m.regularCore c)
  refine ⟨seed, fun x => ?_⟩
  have value := congrFun hseed x
  rw [value, m.view_core c]
  change (m.weight x : ℂ) * (ζ (m.maps a x) : ℂ) = (m.weight x : ℂ)
  by_cases hx : m.weight x = 0
  · simp [hx]
  · rw [oneζ _ ⟨x, subset_tsupport _ hx, rfl⟩, Complex.ofReal_one, mul_one]

variable (ν : Measure M) [IsFiniteMeasure ν] {Test : Type*} [NormedAddCommGroup Test]
  [NormedSpace ℂ Test]
  (aT : m.StrongSpace →L[ℂ] (Test →L[ℂ] ℂ)) (testView : Test → M →ᵇ ℂ)
  (core : ∀ c t, aT (coreLift m.qa c) t =
    ∫ x, SmoothSupportedManifoldCore.functions V c x * testView t x ∂ν)
  (physReg : Reg →L[ℂ] (M →ᵇ ℂ)) (hphys : ∀ r x, physReg r x = m.view r x)

include core hphys in
/-- A constant-one test gives a strong pairing extending the reference integral. -/
theorem reference_pairing (one : Test) (hone : ∀ x, testView one x = 1) :
    ∃ (pairing : m.StrongSpace →L[ℂ] ℂ) (integral : Reg →L[ℂ] ℂ),
      (∀ r, pairing (m.realize r) = integral r) ∧ (∀ r, integral r = ∫ x, m.view r x ∂ν) := by
  refine ⟨(ContinuousLinearMap.apply ℂ ℂ one).comp aT,
    ((ContinuousLinearMap.apply ℂ ℂ one).comp aT).comp m.realize, fun _ => rfl, fun r => ?_⟩
  change aT (m.realize r) one = _
  rw [PhysicalModelNativeRadiusUpper.realize_coefficient m ν aT testView core physReg hphys r one]
  simp only [hone, one_mul]

end ConditionedStochasticStabilityHyperbolic.PhysicalModelLeadingInputs
