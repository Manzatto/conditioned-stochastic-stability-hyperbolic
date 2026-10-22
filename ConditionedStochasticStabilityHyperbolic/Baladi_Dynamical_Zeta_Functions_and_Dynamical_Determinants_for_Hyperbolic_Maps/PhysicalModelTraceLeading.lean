module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelTraceMatch
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelTraceConvergence
public import ConditionedStochasticStabilityHyperbolic.Spectral.TraceAsymptoticLeading
public import LeanShared.Dynamics.RegularizedLefschetzTraceFinal
public import LeanShared.Dynamics.LefschetzRatioLimit
public import LeanShared.Analysis.RealMollifierSupply
meta import Lean.LibrarySuggestions.Basic

/-! The deterministic leading record of the carrier transfer operator. The regularized trace
families built from real mollifiers of radius `ε_j → 0` converge to `λ^{-N} L^N`; their traces
of `(λ^{-N} L^N)^k` are `λ^{-N(k+1)}` times the regularized Lefschetz traces, which are
relatively close to the periodic Lefschetz sums, whose normalization by `λ = exp P` tends to
one. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelTraceLeading"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Filter Bundle
open scoped Manifold ContDiff SchwartzMap Topology BoundedContinuousFunction
attribute [local instance] Classical.propDecidable
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelUniformBounds
  PhysicalModelAnalytic SchwartzJetSpace PhysicalModelFullTestPairing PhysicalModelLocalHolderTest
  PhysicalModelNativeCoefficients HyperbolicBasicSet FractionalManifoldRegularity
  ThermodynamicDefinitions

variable {E U M AtlasIndex Reg A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)

/-- The regularized Lefschetz trace of a trace setup in the carrier charts. -/
theorem setup_trace {T : M ≃ₜ M} {Λ V' : Set M} {bd : BasicData (E := E) T Λ V'}
    (s : TraceSetup bd) (a : Ω) (hT : (T : M → M) = m.maps a) (hW : s.weight = m.weight)
    (κ : E → ℝ) (n : ℕ) :
    s.trace volume κ n = @Finset.sum _ _ _ (@Finset.univ _ s.charts.fintype) fun i =>
      ∫ z, lefschetzIntegrand (m.maps a) m.weight (s.cutoff i) (s.charts.chart i) κ n z := by
  unfold TraceSetup.trace TraceSetup.integrand
  rw [hT, hW]

set_option maxHeartbeats 3200000 in
theorem deterministic_leading (tc : TraceCharts m) {bt : ℝ} (hbt : 0 < bt) (hbt1 : bt ≤ 1)
    (lc : LocalCalculus m) (localBound : LocalPairing m bt) {L : ℝ} (bound : AnalyticBound m L)
    (a : Ω) (strong : ℝ) (remainder : m.localization.indices → m.localization.indices → ℝ)
    (hs : 0 ≤ strong) (hR : ∀ i j, 0 ≤ remainder i j)
    (estimate : PairEstimate m (m.maps a) m.weight strong remainder)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (physReg : Reg →L[ℂ] (M →ᵇ ℂ)) (hphys : ∀ r x, physReg r x = m.view r x)
    (weightCont : Continuous m.weight) (mapCont : Continuous (m.maps a))
    (partition : ∀ x, m.weight x ≠ 0 → (∑ j : m.localization.indices,
      if m.maps a x ∈ (m.atlas j).source then
        tc.wt j (m.atlas j (m.maps a x)) * m.localization.cutoff j (m.maps a x) else 0) = 1)
    {T : M ≃ₜ M} {Λ V' : Set M} (bd : BasicData (E := E) T Λ V') (s : TraceSetup bd)
    (hT : (T : M → M) = m.maps a) (hW : s.weight = m.weight)
    (e : s.charts.ι ≃ m.localization.indices) (hchart : ∀ i, s.charts.chart i = m.atlas (e i))
    (hc : ∀ i, ∀ x ∈ (m.atlas (e i)).source,
      (s.cutoff i x : ℂ) = m.localization.cutoff (e i) x * tc.wt (e i) (m.atlas (e i) x))
    (εc : ℝ) (hεc : 0 < εc)
    (hcut : ∀ i, ∀ z ∈ (m.atlas (e i)).target, s.cutoff i ((m.atlas (e i)).symm z) ≠ 0 →
      ∀ u, ‖u - z‖ ≤ εc → tc.cut (e i) u = 1)
    (mixing : MixingOn T Λ) (inverseRegular : Regular (E := E) (F := E) s.r T.symm)
    (P0 : ℝ) (hP0 : pressure T (bd.hyperbolic.potential s.weight) Λ = (P0 : EReal))
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] (i : m.StrongSpace →L[ℂ] W)
    (hi : IsCompactOperator i) (α R C D : ℝ) (hα : 0 ≤ α) (hR' : 0 ≤ R) (hC : 0 ≤ C)
    (hD : 0 ≤ D)
    (twoNorm : ∀ n x, ‖((m.generator a) ^ n) x‖ ≤ C * α ^ n * ‖x‖ + D * R ^ n * ‖i x‖)
    (gap : α < Real.exp P0)
    (radius : spectralRadius ℂ (m.generator a) ≤ ENNReal.ofReal (Real.exp P0))
    (positive : ((Real.exp P0 : ℝ) : ℂ) ∈ spectrum ℂ (m.generator a)) :
    ∃ d : KellerLiverani1999.DeterministicLeading (m.generator a), d.rate = Real.exp P0 := by
  let := s.charts.fintype
  obtain ⟨N, hN, close⟩ := s.trace_close (volume : Measure E)
  obtain ⟨P1, hP1, ratio⟩ := bd.lefschetz_ratio_tendsto s.one_lt_r s.q_pos s.regular
    inverseRegular mixing s.weight (s.weight_regular 0) s.weight_pos s.forward s.inverse
  have same : P1 = P0 := EReal.coe_injective (hP1.symm.trans hP0)
  choose ε0 ε0pos ε0spec using fun j : ℕ => close (1 / ((j : ℝ) + 1)) (by positivity)
  let ε : ℕ → ℝ := fun j => min (min (ε0 j) εc) (1 / ((j : ℝ) + 1)) / 2
  have εpos : ∀ j, 0 < ε j := fun j => by
    have : 0 < min (min (ε0 j) εc) (1 / ((j : ℝ) + 1)) :=
      lt_min (lt_min (ε0pos j) hεc) (by positivity)
    positivity
  have twice : ∀ j, 2 * ε j = min (min (ε0 j) εc) (1 / ((j : ℝ) + 1)) := fun j => by
    simp only [ε]; ring
  have le0 : ∀ j, 2 * ε j ≤ ε0 j := fun j => (twice j).trans_le
    ((min_le_left _ _).trans (min_le_left _ _))
  have leC : ∀ j, 2 * ε j ≤ εc := fun j => (twice j).trans_le
    ((min_le_left _ _).trans (min_le_right _ _))
  have leJ : ∀ j, 2 * ε j ≤ 1 / ((j : ℝ) + 1) := fun j => (twice j).trans_le (min_le_right _ _)
  have ηlim : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have εlim : Tendsto (fun j => ε j + ε j) atTop (𝓝 0) :=
    squeeze_zero (fun j => (add_pos (εpos j) (εpos j)).le)
      (fun j => (two_mul (ε j)).symm.le.trans (leJ j)) ηlim
  have εone : ∀ j, ε j + ε j ≤ 1 := fun j => ((two_mul (ε j)).symm.le.trans (leJ j)).trans
    (div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]) (by positivity))
  choose ρs κs ρc ρout mass l1 kernelEq κcont κnn κcs κout κmass using
    fun j => RealMollifierSupply.supply (E := E) (ε j) (εpos j)
  let lam : ℝ := Real.exp P0
  let c : ℂ := ((lam : ℂ) ^ N)⁻¹
  let Pop : m.StrongSpace →L[ℂ] m.StrongSpace := c • (m.generator a) ^ (N - 1)
  let F : ℕ → RegularizedTraceFunctional.Family m.StrongSpace
      (Fin (Fintype.card m.localization.indices) × E) := fun j =>
    family m tc hbt hbt1 (ρs j) (ρc j) lc localBound bound a strong remainder hs hR estimate b
      Pop (ρs j) (ρc j)
  have weak : ∀ v : m.StrongSpace, ∀ φ : m.StrongSpace →L[ℂ] ℂ,
      Tendsto (fun j => φ ((F j).smoothing v)) atTop (𝓝 (φ (Pop (m.generator a v)))) :=
    fun v φ => (φ.continuous.tendsto _).comp (smoothing_tendsto m tc hbt hbt1 lc localBound
      bound a strong remainder hs hR estimate b Pop partition ρs ρs ρc ρc ε ε ρout ρout εone
      εlim mass mass l1 l1 v)
  have formula : ∀ j k, (F j).traceL ((c • (m.generator a) ^ N) ^ k) =
      c ^ (k + 1) * (s.trace volume (κs j) (N * (k + 1)) : ℂ) := fun j k =>
    (family_trace m tc hbt hbt1 lc localBound bound a strong remainder hs hR estimate b Pop
      (ρs j) (ρc j) (ρs j) (ρc j) physReg hphys weightCont mapCont
      ((c • (m.generator a) ^ N) ^ k) (c ^ (k + 1)) (N * (k + 1))
      (fun w => KellerLiverani1999.power_identity (m.generator a) c N hN k w)).trans
      (congrArg (c ^ (k + 1) * ·) ((trace_match m a (N * (k + 1)) tc (ρs j) (ρs j) (κs j)
        (kernelEq j) (2 * ε j) (κout j) e s.charts.chart hchart s.cutoff hc
        (fun i z hz hne u hu => hcut i z hz hne u (hu.trans (leC j)))).trans
        (congrArg (fun x : ℝ => (x : ℂ)) (setup_trace m s a hT hW (κs j) (N * (k + 1))).symm)))
  have closeness : ∀ j k, |s.trace volume (κs j) (N * (k + 1)) -
      bd.periodicLefschetzSum s.forward s.inverse s.weight (N * (k + 1))| ≤
      1 / ((j : ℝ) + 1) * bd.periodicLefschetzSum s.forward s.inverse s.weight (N * (k + 1)) :=
    fun j k => ε0spec j (2 * ε j) (by linarith [εpos j]) (le0 j) (κs j) (κcont j) (κnn j)
      (κcs j) (κout j) (κmass j) (k + 1) k.succ_pos
  exact KellerLiverani1999.DeterministicLeading.of_trace_asymptotics (m.generator a) i hi α R C D
    hα hR' hC hD twoNorm lam (Real.exp_pos P0) gap radius positive N hN F weak
    (fun j p => s.trace volume (κs j) p)
    (fun p => bd.periodicLefschetzSum s.forward s.inverse s.weight p)
    (fun j => 1 / ((j : ℝ) + 1)) (fun j => by positivity) ηlim formula closeness (by rw [same] at ratio; exact ratio)

end ConditionedStochasticStabilityHyperbolic.PhysicalModelBumpVectors
