module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNativeCoefficients
public import LeanShared.Analysis.PositiveBoundarySpectrum
public import LeanShared.Analysis.ContinuousLinearMapPowApply
public import LeanShared.Dynamics.BasicHyperbolicShiftedBlockGrowth
meta import Lean.LibrarySuggestions.Basic

/-! The positive cone of the strong space and the positive spectral point. The closure of realized
nonnegative regular functions is a closed cone preserved by every generator; a strong pairing
that restricts to the reference integral is real and nonnegative on it. With the radius upper
bound and the shifted block growth of the weighted-orbit coefficients, `e^P` belongs to the
spectrum of the generator. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelPositiveCone"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold Bundle MeasureTheory
open scoped Manifold ContDiff
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelPositiveCone
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelAnalytic
  PhysicalModelNativeCoefficients

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

/-- Regular functions with nonnegative real values. -/
def positiveRegular : Set Reg := {r | ∀ x, ∃ t : ℝ, 0 ≤ t ∧ m.view r x = t}

/-- The positive cone of the strong space. -/
def cone : Set m.StrongSpace := closure (m.realize '' positiveRegular m)

theorem zero_mem : (0 : m.StrongSpace) ∈ cone m :=
  subset_closure ⟨0, fun x => ⟨0, le_rfl, by rw [map_zero]; rfl⟩, map_zero _⟩

theorem add_mem {u w : m.StrongSpace} (hu : u ∈ cone m) (hw : w ∈ cone m) : u + w ∈ cone m := by
  refine map_mem_closure₂ continuous_add hu hw ?_
  rintro _ ⟨r, hr, rfl⟩ _ ⟨s, hs, rfl⟩
  refine ⟨r + s, fun x => ?_, map_add _ _ _⟩
  obtain ⟨a, ha, ea⟩ := hr x
  obtain ⟨b, hb, eb⟩ := hs x
  refine ⟨a + b, add_nonneg ha hb, ?_⟩
  rw [map_add, Pi.add_apply, ea, eb]
  push_cast
  rfl

theorem smul_mem (c : ℝ) (hc : 0 ≤ c) {u : m.StrongSpace} (hu : u ∈ cone m) :
    (c : ℂ) • u ∈ cone m := by
  refine map_mem_closure (continuous_const_smul (c : ℂ)) hu ?_
  rintro _ ⟨r, hr, rfl⟩
  refine ⟨(c : ℂ) • r, fun x => ?_, map_smul _ _ _⟩
  obtain ⟨a, ha, ea⟩ := hr x
  refine ⟨c * a, mul_nonneg hc ha, ?_⟩
  rw [map_smul, Pi.smul_apply, ea, smul_eq_mul]
  push_cast
  rfl

theorem generator_mapsTo {L : ℝ} (bound : AnalyticBound m L) (a : Ω)
    (nonnegative : ∀ x, 0 ≤ m.weight x) : MapsTo (m.generator a) (cone m) (cone m) := by
  intro u hu
  refine map_mem_closure (m.generator a).continuous hu ?_
  rintro _ ⟨r, hr, rfl⟩
  refine ⟨regularOperator m a r, fun x => ?_,
    DFunLike.congr_fun (regular_intertwining m bound a) r⟩
  obtain ⟨t, ht, et⟩ := hr (m.maps a x)
  refine ⟨m.weight x * t, mul_nonneg (nonnegative x) ht, ?_⟩
  rw [InvariantFiniteRegularTransfer.operator_function, et]
  push_cast
  rfl

set_option maxHeartbeats 1600000 in
/-- A strong pairing restricting to the reference integral is real and nonnegative on the cone. -/
theorem mass_real (ν : Measure M) (pairing : m.StrongSpace →L[ℂ] ℂ)
    (hpair : ∀ r, pairing (m.realize r) = ∫ x, m.view r x ∂ν) :
    ∀ v ∈ cone m, ∃ t : ℝ, 0 ≤ t ∧ pairing v = t := by
  let Z : Set ℂ := (fun t : ℝ => (t : ℂ)) '' Ici 0
  have closedZ : IsClosed Z :=
    Complex.isometry_ofReal.isClosedEmbedding.isClosedMap _ isClosed_Ici
  have sub : cone m ⊆ pairing ⁻¹' Z := by
    refine closure_minimal ?_ (closedZ.preimage pairing.continuous)
    rintro _ ⟨r, hr, rfl⟩
    choose t ht et using hr
    refine ⟨∫ x, t x ∂ν, integral_nonneg ht, ?_⟩
    change ((∫ x, t x ∂ν : ℝ) : ℂ) = pairing (m.realize r)
    rw [hpair, ← integral_complex_ofReal]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => (et x).symm)
  intro v hv
  obtain ⟨t, ht, e⟩ := sub hv
  exact ⟨t, ht, e.symm⟩

section Spectrum
variable [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]

set_option maxHeartbeats 1600000 in
/-- The positive real boundary point `e^P` belongs to the spectrum of the generator. -/
theorem exp_pressure_mem_spectrum {L : ℝ} (bound : AnalyticBound m L)
    (T : M ≃ₜ M) (Λ : Set M) (b : HyperbolicBasicSet.BasicData (E := E) T Λ V)
    {r q : ℝ} (regularity : 1 < r) (weightOrder : 0 < q)
    (forwardRegular : FractionalManifoldRegularity.Regular (E := E) (F := E) r T)
    (inverseRegular : FractionalManifoldRegularity.Regular (E := E) (F := E) r T.symm)
    (mixing : HyperbolicBasicSet.MixingOn T Λ)
    (referenceMeasure : FiniteSmoothReferenceCharts.Data (E := E) (M := M))
    (νE : Measure E) [νE.IsAddHaarMeasure]
    (weightRegular : FractionalManifoldRegularity.Regular (E := E) (F := ℝ) q m.weight)
    (positive : ∀ x ∈ Λ, 0 < m.weight x) (nonnegative : ∀ x, 0 ≤ m.weight x)
    (pressureValue : ℝ)
    (pressure_eq : ThermodynamicDefinitions.pressure T (b.hyperbolic.potential m.weight) Λ =
      (pressureValue : EReal))
    (a : Ω) (map_eq : m.maps a = T)
    (pairing : m.StrongSpace →L[ℂ] ℂ) (integral : Reg →L[ℂ] ℂ)
    (hpair : ∀ r, pairing (m.realize r) = integral r)
    (hint : ∀ r, integral r = ∫ x, m.view r x ∂(referenceMeasure.measure νE))
    (integrableView : ∀ r, Integrable (m.view r) (referenceMeasure.measure νE))
    (seed : Reg) (hseed : ∀ x, m.view seed x = (m.weight x : ℂ))
    (radius : spectralRadius ℂ (m.generator a) ≤ ENNReal.ofReal (Real.exp pressureValue)) :
    ((Real.exp pressureValue : ℝ) : ℂ) ∈ spectrum ℂ (m.generator a) :=
  PositiveBoundarySpectrum.mem_spectrum (cone m) isClosed_closure (zero_mem m)
    (fun hu hw => add_mem m hu hw) (fun c hc _ hu => smul_mem m c hc hu) (m.generator a)
    (generator_mapsTo m bound a nonnegative) pairing
    (mass_real m (referenceMeasure.measure νE) pairing (fun r => (hpair r).trans (hint r)))
    (m.realize seed)
    (subset_closure ⟨seed, fun x => ⟨m.weight x, nonnegative x, hseed x⟩, rfl⟩)
    pressureValue radius
    (b.shifted_block_growth_from_coefficients regularity weightOrder forwardRegular inverseRegular
      mixing referenceMeasure νE m.weight weightRegular positive pressureValue pressure_eq
      (m.generator a) pairing (m.realize seed) fun n =>
        (coefficient m bound (referenceMeasure.measure νE) pairing integral hpair hint
          integrableView a T map_eq seed hseed nonnegative n).trans
          (congrArg (fun z => ENNReal.ofReal ‖pairing z‖)
            (ContinuousLinearMapPowApply.pow_apply (m.generator a) n _).symm))

end Spectrum

end ConditionedStochasticStabilityHyperbolic.PhysicalModelPositiveCone
