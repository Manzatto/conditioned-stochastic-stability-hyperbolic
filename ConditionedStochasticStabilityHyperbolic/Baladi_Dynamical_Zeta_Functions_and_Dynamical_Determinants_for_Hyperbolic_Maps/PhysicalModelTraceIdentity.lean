module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelTraceConvergence
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelNativeCoefficients
public import LeanShared.Geometry.ParametricChartContinuity
meta import Lean.LibrarySuggestions.Basic

/-! The literal regularized trace identity. The chart-`k` test of an iterated generator on a
core function is the chart integral of the weighted orbit product against the test weight;
integrating the bump parameter turns the two mollifiers into the correlation kernel `κ`. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelTraceIdentity"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Filter
open scoped Manifold ContDiff SchwartzMap Topology BoundedContinuousFunction
attribute [local instance] Classical.propDecidable
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelUniformBounds
  PhysicalModelAnalytic SchwartzJetSpace PhysicalModelFullTestPairing PhysicalModelLocalHolderTest
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

/-- The weighted orbit product. -/
abbrev orbitWeight (a : Ω) (n : ℕ) (x : M) : ℂ :=
  ((∏ i ∈ Finset.range n, m.weight ((m.maps a)^[i] x) : ℝ) : ℂ)

theorem view_iterate' (a : Ω) (r : Reg) (n : ℕ) (x : M) :
    m.view ((regularOperator m a)^[n] r) x = orbitWeight m a n x * m.view r ((m.maps a)^[n] x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', InvariantFiniteRegularTransfer.operator_function, ih,
      orbitWeight, orbitWeight, Finset.prod_range_succ' _ n]
    simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
    push_cast
    ring

set_option maxHeartbeats 1600000 in
/-- The chart-`j` Hölder test of an iterated generator on a core function. -/
theorem test_iterate {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1) (localBound : LocalPairing m bt)
    {L : ℝ} (bound : AnalyticBound m L) (a : Ω) (physReg : Reg →L[ℂ] (M →ᵇ ℂ))
    (hphys : ∀ r x, physReg r x = m.view r x) (j : m.localization.indices)
    (v : BoundedHolderSpace.graph E bt) (u : Core (E := E) V) (n : ℕ) :
    test m j v ((m.generator a)^[n] (coreLift m.qa u)) =
      ∫ z, ChartLocalization.coordinate (m.atlas j) (m.localization.cutoff j)
        (fun x => orbitWeight m a n x * SmoothSupportedManifoldCore.functions V u ((m.maps a)^[n] x)) z *
          BoundedHolderSpace.physical E bt v z := by
  have h1 : (m.generator a)^[n] (coreLift m.qa u) =
      m.realize ((regularOperator m a)^[n] (m.regularCore u)) :=
    (congrArg _ (m.realize_core u).symm).trans (iterate_intertwining m bound a n _)
  have h2 : (⇑(physReg ((regularOperator m a)^[n] (m.regularCore u))) : M → ℂ) =
      fun x => orbitWeight m a n x * SmoothSupportedManifoldCore.functions V u ((m.maps a)^[n] x) := by
    funext x
    rw [hphys, view_iterate', m.view_core]
  calc test m j v ((m.generator a)^[n] (coreLift m.qa u))
      = test m j v (m.realize ((regularOperator m a)^[n] (m.regularCore u))) := congrArg _ h1
    _ = chartPairing m j v (physReg ((regularOperator m a)^[n] (m.regularCore u))) :=
        test_realize m hbt hbt1 localBound j v physReg hphys _
    _ = _ := by
        rw [chartPairing, ChartFunctionPairing.pairing_apply, h2]

/-- The bump parameter integral of two mollifiers is the correlation kernel. -/
theorem mollifier_pair_integral (ρ ρ' : 𝓢(E, ℂ)) (z u : E) :
    ∫ y, ρ (z - y) * ρ' (u - y) = MollifierKernel.kernel ρ ρ' (u - z) := by
  unfold MollifierKernel.kernel
  have shift := integral_sub_left_eq_self (μ := volume) (fun s => ρ s * ρ' (u - z + s)) z
  rw [← shift]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  rw [show u - z + (z - y) = u - y by abel]

/-- The pointwise chart integrand after the bump parameter integral. -/
abbrev traceIntegrand (a : Ω) (n : ℕ) (j : m.localization.indices) (cut wt : 𝓢(E, ℂ))
    (κ : E → ℂ) (z : E) : ℂ :=
  if z ∈ (m.atlas j).target then
    m.localization.cutoff j ((m.atlas j).symm z) * orbitWeight m a n ((m.atlas j).symm z) * wt z *
      (if (m.maps a)^[n] ((m.atlas j).symm z) ∈ (m.atlas j).source then
        cut (m.atlas j ((m.maps a)^[n] ((m.atlas j).symm z))) *
          κ (m.atlas j ((m.maps a)^[n] ((m.atlas j).symm z)) - z) else 0)
  else 0

theorem orbitWeight_continuous (a : Ω) (weightCont : Continuous m.weight)
    (mapCont : Continuous (m.maps a)) (n : ℕ) : Continuous (orbitWeight m a n) :=
  Complex.continuous_ofReal.comp (continuous_finsetProd _ fun i _ =>
    weightCont.comp (mapCont.iterate i))

/-- The chart integrand before the bump parameter integral, as a function of `(z, y)`. -/
abbrev chartIntegrand (a : Ω) (n : ℕ) (j : m.localization.indices) (cut wt ρ ρ' : 𝓢(E, ℂ))
    (q : E × E) : ℂ :=
  ChartLocalization.coordinate (m.atlas j) (m.localization.cutoff j)
    (fun x => orbitWeight m a n x * (if (m.maps a)^[n] x ∈ (m.atlas j).source then
      cut (m.atlas j ((m.maps a)^[n] x)) * ρ' (m.atlas j ((m.maps a)^[n] x) - q.2) else 0)) q.1 *
    (wt q.1 * ρ (q.1 - q.2))

theorem chartIntegrand_continuous (a : Ω) (weightCont : Continuous m.weight)
    (mapCont : Continuous (m.maps a)) (n : ℕ) (j : m.localization.indices) (cut wt ρ ρ' : 𝓢(E, ℂ))
    (cutCompact : HasCompactSupport (cut : E → ℂ))
    (cutInside : tsupport (cut : E → ℂ) ⊆ (m.atlas j).target) :
    Continuous (chartIntegrand m a n j cut wt ρ ρ') := by
  have ext := ParametricChartContinuity.extension_continuous (m.atlas j)
    (fun p : E × E => cut p.1 * ρ' (p.1 - p.2))
    ((cut.continuous.comp continuous_fst).mul (ρ'.continuous.comp (continuous_fst.sub continuous_snd)))
    cutCompact cutInside (fun z p hz => by simp [image_eq_zero_of_notMem_tsupport hz])
  have F : Continuous (fun q : M × E => orbitWeight m a n q.1 * (if (m.maps a)^[n] q.1 ∈ (m.atlas j).source then
      cut (m.atlas j ((m.maps a)^[n] q.1)) * ρ' (m.atlas j ((m.maps a)^[n] q.1) - q.2) else 0)) :=
    ((orbitWeight_continuous m a weightCont mapCont n).comp continuous_fst).mul
      (ext.comp (((mapCont.iterate n).comp continuous_fst).prodMk continuous_snd))
  have coord := ParametricChartContinuity.coordinate_continuous (m.atlas j) (m.localization.cutoff j)
    (m.localization.smooth j).continuous (m.localization.compact j) (m.localization.support j) _ F
  exact coord.mul ((wt.continuous.comp continuous_fst).mul
    (ρ.continuous.comp (continuous_fst.sub continuous_snd)))

/-- The bump parameter integral of the chart integrand. -/
theorem chartIntegrand_integral (a : Ω) (n : ℕ) (j : m.localization.indices) (cut wt ρ ρ' : 𝓢(E, ℂ))
    (z : E) :
    ∫ y, chartIntegrand m a n j cut wt ρ ρ' (z, y) =
      traceIntegrand m a n j cut wt (MollifierKernel.kernel ρ ρ') z := by
  unfold chartIntegrand traceIntegrand ChartLocalization.coordinate
  by_cases hz : z ∈ (m.atlas j).target
  · simp only [hz, ↓reduceIte]
    by_cases hs : (m.maps a)^[n] ((m.atlas j).symm z) ∈ (m.atlas j).source
    · simp only [hs, ↓reduceIte]
      set x0 := (m.atlas j).symm z
      set u := m.atlas j ((m.maps a)^[n] x0)
      refine (integral_congr_ae (ae_of_all _ fun y =>
        (show m.localization.cutoff j x0 * (orbitWeight m a n x0 * (cut u * ρ' (u - y))) *
            (wt z * ρ (z - y)) =
          (m.localization.cutoff j x0 * orbitWeight m a n x0 * wt z * cut u) *
            (ρ (z - y) * ρ' (u - y)) by ring))).trans ?_
      rw [integral_const_mul, mollifier_pair_integral]
      ring
    · simp [hs]
  · simp [hz]

set_option maxHeartbeats 1600000 in
/-- The chart-`j` regularized trace integral. -/
theorem chart_trace {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1) (localBound : LocalPairing m bt)
    {L : ℝ} (bound : AnalyticBound m L) (a : Ω) (physReg : Reg →L[ℂ] (M →ᵇ ℂ))
    (hphys : ∀ r x, physReg r x = m.view r x) (weightCont : Continuous m.weight)
    (mapCont : Continuous (m.maps a)) (j : m.localization.indices) (cut : 𝓢(E, ℂ))
    (cutCompact : HasCompactSupport (cut : E → ℂ))
    (cutSupport : tsupport (cut : E → ℂ) ⊆
      ConstructedManifoldLocalization.support m.atlas m.localization j)
    (cutRegion : (m.atlas j).symm '' tsupport (cut : E → ℂ) ⊆ V)
    (wt : 𝓢(E, ℂ)) (wtCompact : HasCompactSupport (wt : E → ℂ)) (ρ ρ' : 𝓢(E, ℂ))
    (ρc : HasCompactSupport (ρ : E → ℂ)) (vf : E → BoundedHolderSpace.graph E bt)
    (hvf : ∀ y z, BoundedHolderSpace.physical E bt (vf y) z = wt z * ρ (z - y)) (n : ℕ) :
    ∫ y, test m j (vf y) ((m.generator a)^[n]
      (coreLift m.qa (bumpCore m j cut cutCompact cutSupport cutRegion ρ' y))) =
      ∫ z, traceIntegrand m a n j cut wt (MollifierKernel.kernel ρ ρ') z := by
  have pointwise (y : E) : test m j (vf y) ((m.generator a)^[n]
      (coreLift m.qa (bumpCore m j cut cutCompact cutSupport cutRegion ρ' y))) =
      ∫ z, chartIntegrand m a n j cut wt ρ ρ' (z, y) := by
    rw [test_iterate m hbt hbt1 localBound bound a physReg hphys j (vf y)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [chartIntegrand]
    rw [hvf]
    congr 2
  have cont := chartIntegrand_continuous m a weightCont mapCont n j cut wt ρ ρ' cutCompact
    (cut_inside m j cut cutSupport)
  have compactY : IsCompact ((fun p : E × E => p.1 - p.2) '' (tsupport (wt : E → ℂ) ×ˢ tsupport (ρ : E → ℂ))) :=
    (wtCompact.prod ρc).image (continuous_fst.sub continuous_snd)
  have product : Integrable (Function.uncurry fun (y z : E) => chartIntegrand m a n j cut wt ρ ρ' (z, y))
      (volume.prod volume) := by
    refine (cont.comp continuous_swap).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (compactY.prod wtCompact) fun q hq => ?_
    simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap, chartIntegrand]
    by_cases hz : q.2 ∈ tsupport (wt : E → ℂ)
    · have hy : q.2 - q.1 ∉ tsupport (ρ : E → ℂ) := fun h => hq ⟨⟨(q.2, q.2 - q.1), ⟨hz, h⟩,
        sub_sub_cancel _ _⟩, hz⟩
      rw [image_eq_zero_of_notMem_tsupport hy, mul_zero, mul_zero]
    · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, mul_zero]
  rw [integral_congr_ae (ae_of_all _ pointwise), integral_integral_swap product]
  exact integral_congr_ae (ae_of_all _ fun z => chartIntegrand_integral m a n j cut wt ρ ρ' z)

set_option maxHeartbeats 1600000 in
/-- The regularized trace of an operator acting as `c L^n` after one step. -/
theorem family_trace (tc : TraceCharts m) {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1)
    (lc : LocalCalculus m) (localBound : LocalPairing m bt) {L : ℝ} (bound : AnalyticBound m L)
    (a : Ω) (strong : ℝ) (remainder : m.localization.indices → m.localization.indices → ℝ)
    (hs : 0 ≤ strong) (hR : ∀ i j, 0 ≤ remainder i j)
    (estimate : PairEstimate m (m.maps a) m.weight strong remainder)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (P : m.StrongSpace →L[ℂ] m.StrongSpace) (ρ : 𝓢(E, ℂ)) (ρc : HasCompactSupport (ρ : E → ℂ))
    (ρ' : 𝓢(E, ℂ)) (ρ'c : HasCompactSupport (ρ' : E → ℂ))
    (physReg : Reg →L[ℂ] (M →ᵇ ℂ)) (hphys : ∀ r x, physReg r x = m.view r x)
    (weightCont : Continuous m.weight) (mapCont : Continuous (m.maps a))
    (X : m.StrongSpace →L[ℂ] m.StrongSpace) (c : ℂ) (n : ℕ)
    (hX : ∀ w, X (P (m.generator a w)) = c • (m.generator a)^[n] w) :
    (family m tc hbt hbt1 ρ ρc lc localBound bound a strong remainder hs hR estimate b P ρ'
      ρ'c).traceL X =
      c * ∑ k, ∫ z, traceIntegrand m a n (chartEquiv m k) (tc.cut (chartEquiv m k))
        (tc.wt (chartEquiv m k)) (MollifierKernel.kernel ρ ρ') z := by
  have expand : (family m tc hbt hbt1 ρ ρc lc localBound bound a strong remainder hs hR estimate b
      P ρ' ρ'c).traceL X = ∑ k, ∫ y, test m (chartEquiv m k)
        (testFamily m tc hbt hbt1 ρ ρc (chartEquiv m k) y)
        (X (vectorFamily m tc a P ρ' (chartEquiv m k) y)) :=
    ChartTraceFamily.traceL_apply' volume _ _ _ _ _ X
  refine expand.trans ((Finset.sum_congr rfl fun k _ => ?_).trans (Finset.mul_sum _ _ _).symm)
  have each (y : E) : test m (chartEquiv m k) (testFamily m tc hbt hbt1 ρ ρc (chartEquiv m k) y)
      (X (vectorFamily m tc a P ρ' (chartEquiv m k) y)) =
      c * test m (chartEquiv m k) (testFamily m tc hbt hbt1 ρ ρc (chartEquiv m k) y)
        ((m.generator a)^[n] (coreLift m.qa (bumpCore m (chartEquiv m k) (tc.cut (chartEquiv m k))
          (tc.cutCompact (chartEquiv m k)) (tc.cutSupport (chartEquiv m k))
          (tc.cutRegion (chartEquiv m k)) ρ' y))) :=
    ((congrArg (test m (chartEquiv m k) (testFamily m tc hbt hbt1 ρ ρc (chartEquiv m k) y))
      (hX _)).trans (map_smul _ _ _)).trans (smul_eq_mul _ _)
  rw [integral_congr_ae (ae_of_all _ each), integral_const_mul]
  congr 1
  exact chart_trace m hbt hbt1 localBound bound a physReg hphys weightCont mapCont (chartEquiv m k)
    (tc.cut (chartEquiv m k)) (tc.cutCompact (chartEquiv m k)) (tc.cutSupport (chartEquiv m k))
    (tc.cutRegion (chartEquiv m k)) (tc.wt (chartEquiv m k)) (tc.wtCompact (chartEquiv m k)) ρ ρ' ρc
    (testFamily m tc hbt hbt1 ρ ρc (chartEquiv m k)) (testFamily_apply m tc hbt hbt1 ρ ρc _) n

end ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
