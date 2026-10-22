module
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelHorizonIdentities
public import ConditionedStochasticStabilityHyperbolic.Spectral.DeterministicLeadingTangent
public import LeanShared.Analysis.WeightedExponentialJensen
public import LeanShared.Dynamics.BasicHyperbolicOrbitIntegralGrowth
public import LeanShared.Dynamics.BasicHyperbolicShiftedBlockGrowth
public import LeanShared.Geometry.FiniteSmoothReferenceMeasure
public import LeanShared.Analysis.ContinuousLinearMapPowApply
meta import Lean.LibrarySuggestions.Basic

/-! The pressure supporting inequality of the spectral product of a physical model. For the
deterministic leading record of the generator at rate `e^P`, the normalized paired powers of the
realized weight seed are the orbit masses `λ^{-n} ∫ g_{n+1}`, the Birkhoff sums of the strong
multiplier by `ψ` are `λ^{-n} ∫ g_{n+1} S_n ψ`, Jensen compares them with the tilted masses, the
tilted weight `g e^{tψ}` has orbit growth at its own pressure `P_t`, and the shifted block
growth makes the limit mass positive. Hence `t · Re m(M_ψ v) ≤ P_t - P`. -/

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PhysicalModelProductTangent"

@[expose] public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold MeasureTheory Finset Filter Real Bundle
open scoped Manifold ContDiff BoundedContinuousFunction Topology
namespace ConditionedStochasticStabilityHyperbolic.PhysicalModelHorizonIdentities
open LeanShared DyadicCompletion PhysicalManifoldModel PhysicalModelAnalytic
  PhysicalModelNativeCoefficients PhysicalModelNativeRadiusUpper KellerLiverani1999
  HyperbolicBasicSet ThermodynamicDefinitions FractionalManifoldRegularity

/-- Powers of a scaled operator applied to a vector. -/
theorem scaled_pow_apply {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] (L : H →L[ℂ] H)
    (c : ℂ) (n : ℕ) (x : H) : ((c • L) ^ n) x = c ^ n • L^[n] x := by
  rw [smul_pow, smul_apply, ContinuousLinearMapPowApply.pow_apply]

/-- The scalar factor of a paired scaled sandwich `ℓ((cL)^j M (cL)^{n-j} p)`. -/
theorem scaled_sandwich {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] (L Mf : H →L[ℂ] H)
    (ℓ : H →L[ℂ] ℂ) (c : ℂ) (p : H) (n j : ℕ) (hj : j ≤ n) :
    ℓ (((c • L) ^ j) (Mf (((c • L) ^ (n - j)) p))) = c ^ n * ℓ (L^[j] (Mf (L^[n - j] p))) := by
  simp only [smul_pow, smul_apply, map_smul, smul_eq_mul]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hj, ContinuousLinearMapPowApply.pow_apply,
    ContinuousLinearMapPowApply.pow_apply]

/-- The scalar factor of a paired scaled power. -/
theorem scaled_power {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] (L : H →L[ℂ] H)
    (ℓ : H →L[ℂ] ℂ) (c : ℂ) (p : H) (n : ℕ) :
    ℓ (((c • L) ^ n) p) = c ^ n * ℓ (L^[n] p) := by
  rw [scaled_pow_apply, map_smul, smul_eq_mul]

variable {E U M AtlasIndex Reg A Ω Test : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [CompactSpace M]
  [NormedAddCommGroup Reg] [NormedSpace ℂ Reg] [CompleteSpace Reg]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  [NormedAddCommGroup Test] [NormedSpace ℂ Test]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  (m : Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex) (Reg := Reg)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
  (ν : Measure M) [IsFiniteMeasure ν]
  (aT : m.StrongSpace →L[ℂ] (Test →L[ℂ] ℂ)) (testView : Test → M →ᵇ ℂ)
  (core : ∀ c t, aT (coreLift m.qa c) t =
    ∫ x, SmoothSupportedManifoldCore.functions V c x * testView t x ∂ν)
  (physReg : Reg →L[ℂ] (M →ᵇ ℂ)) (hphys : ∀ r x, physReg r x = m.view r x)
  (one : Test) (hone : ∀ x, testView one x = 1)

/-- The orbit product of a continuous weight is continuous. -/
theorem product_continuous (F : M → M) (hF : Continuous F) (g : M → ℝ) (hg : Continuous g)
    (n : ℕ) : Continuous (fun x => ∏ j ∈ range n, g (F^[j] x)) :=
  continuous_finsetProd _ fun j _ => hg.comp (hF.iterate j)

/-- A continuous function is integrable for a finite measure on a compact space. -/
theorem integrable_of_continuous {f : M → ℝ} (hf : Continuous f) : Integrable f ν :=
  (BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩).integrable ν

set_option maxHeartbeats 1600000 in
include core hphys hone in
theorem normalized_mass {L : ℝ} (bound : AnalyticBound m L) (a : Ω) (seed : Reg)
    (hseed : ∀ x, m.view seed x = (m.weight x : ℂ)) (lam : ℝ) (n : ℕ) :
    ((ContinuousLinearMap.apply ℂ ℂ one).comp aT)
      (((((lam : ℂ))⁻¹ • m.generator a) ^ n) (m.realize seed)) =
      (((lam ^ n)⁻¹ * ∫ x, ∏ j ∈ range (n + 1), m.weight ((m.maps a)^[j] x) ∂ν : ℝ) : ℂ) := by
  refine (scaled_power (m.generator a) ((ContinuousLinearMap.apply ℂ ℂ one).comp aT) _
    (m.realize seed) n).trans ?_
  refine (congrArg (fun z => ((lam : ℂ))⁻¹ ^ n * z)
    (orbit_mass m ν aT testView core physReg hphys one hone bound a seed hseed n)).trans ?_
  push_cast
  rw [inv_pow]

section Birkhoff
variable (ψ : M → ℝ) (hψ : ContMDiff (𝓘(ℝ, E)) 𝓘(ℝ) ∞ ψ) (CR CA : ℝ)
  (regularBound : ∀ c, ‖m.regularCore (coreMultiplier ψ hψ c)‖ ≤ CR * ‖m.regularCore c‖)
  (analyticBound : ∀ c, ‖coreLift m.qa (coreMultiplier ψ hψ c)‖ ≤ CA * ‖coreLift m.qa c‖)

set_option maxHeartbeats 3200000 in
include core hphys hone regularBound analyticBound in
theorem normalized_birkhoff {L : ℝ} (bound : AnalyticBound m L) (a : Ω) (seed : Reg)
    (hseed : ∀ x, m.view seed x = (m.weight x : ℂ)) (mapCont : Continuous (m.maps a))
    (weightCont : Continuous m.weight) (lam : ℝ) (n : ℕ) :
    (∑ j ∈ range n, ((ContinuousLinearMap.apply ℂ ℂ one).comp aT)
      (((((lam : ℂ))⁻¹ • m.generator a) ^ j) (strongMultiplier m ψ hψ
        (((((lam : ℂ))⁻¹ • m.generator a) ^ (n - j)) (m.realize seed))))) =
      (((lam ^ n)⁻¹ * ∫ x, (∏ i ∈ range (n + 1), m.weight ((m.maps a)^[i] x)) *
        ∑ j ∈ range n, ψ ((m.maps a)^[j] x) ∂ν : ℝ) : ℂ) := by
  have term : ∀ j ∈ range n, ((ContinuousLinearMap.apply ℂ ℂ one).comp aT)
      (((((lam : ℂ))⁻¹ • m.generator a) ^ j) (strongMultiplier m ψ hψ
        (((((lam : ℂ))⁻¹ • m.generator a) ^ (n - j)) (m.realize seed)))) =
      (((lam ^ n)⁻¹ * ∫ x, (∏ i ∈ range (n + 1), m.weight ((m.maps a)^[i] x)) *
        ψ ((m.maps a)^[j] x) ∂ν : ℝ) : ℂ) := fun j hj => by
    have hjn : j ≤ n := (mem_range.mp hj).le
    have h := horizon_term m ν aT testView core physReg hphys one hone ψ hψ CR CA regularBound
      analyticBound bound a seed hseed n j hjn
    refine (scaled_sandwich (m.generator a) (strongMultiplier m ψ hψ)
      ((ContinuousLinearMap.apply ℂ ℂ one).comp aT) _ (m.realize seed) n j hjn).trans ?_
    refine (congrArg (fun z => ((lam : ℂ))⁻¹ ^ n * z) h).trans ?_
    push_cast
    rw [inv_pow]
  rw [sum_congr rfl term, ← Complex.ofReal_sum, ← mul_sum]
  congr 2
  rw [← integral_finsetSum]
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [mul_sum]
  · intro j _
    exact integrable_of_continuous ν ((product_continuous _ mapCont _ weightCont _).mul
      (hψ.continuous.comp (mapCont.iterate j)))

end Birkhoff

/-- A lintegral bound gives the Bochner bound for a nonnegative integrable function. -/
theorem integral_le_of_lintegral {f : M → ℝ} (hf : Integrable f ν) (nonneg : ∀ x, 0 ≤ f x)
    {C : ℝ} (hC : 0 ≤ C) (bound : (∫⁻ x, ENNReal.ofReal (f x) ∂ν) ≤ ENNReal.ofReal C) :
    ∫ x, f x ∂ν ≤ C := by
  rw [← ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall nonneg)] at bound
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp bound

/-- The tilted orbit product dominates the tilted Birkhoff weight up to a fixed factor. -/
theorem tilted_le (F : M → M) (g ψ : M → ℝ) (hg : ∀ x, 0 ≤ g x) (K : ℝ)
    (hK : ∀ x, |ψ x| ≤ K) (t : ℝ) (n : ℕ) (x : M) :
    (∏ i ∈ range (n + 1), g (F^[i] x)) * exp (t * ∑ j ∈ range n, ψ (F^[j] x)) ≤
      exp (|t| * K) * ∏ i ∈ range (n + 1), (g (F^[i] x) * exp (t * ψ (F^[i] x))) := by
  rw [prod_mul_distrib, ← exp_sum, ← mul_sum, sum_range_succ, mul_add, exp_add]
  have nonneg : 0 ≤ ∏ i ∈ range (n + 1), g (F^[i] x) := prod_nonneg fun i _ => hg _
  have factor : 1 ≤ exp (|t| * K) * exp (t * ψ (F^[n] x)) := by
    rw [← exp_add]
    apply one_le_exp
    have := neg_abs_le (t * ψ (F^[n] x))
    rw [abs_mul] at this
    nlinarith [hK (F^[n] x), abs_nonneg t]
  calc (∏ i ∈ range (n + 1), g (F^[i] x)) * exp (t * ∑ j ∈ range n, ψ (F^[j] x)) =
        (∏ i ∈ range (n + 1), g (F^[i] x)) * exp (t * ∑ j ∈ range n, ψ (F^[j] x)) * 1 := by ring
    _ ≤ (∏ i ∈ range (n + 1), g (F^[i] x)) * exp (t * ∑ j ∈ range n, ψ (F^[j] x)) *
        (exp (|t| * K) * exp (t * ψ (F^[n] x))) :=
        mul_le_mul_of_nonneg_left factor (mul_nonneg nonneg (exp_pos _).le)
    _ = _ := by ring

set_option maxHeartbeats 3200000 in
include core hphys hone in
/-- The weighted orbit masses are the paired powers of the realized seed. -/
theorem coefficient_pow {L : ℝ} (bound : AnalyticBound m L) (a : Ω) (F : M → M)
    (hF : m.maps a = F) (seed : Reg) (hseed : ∀ x, m.view seed x = (m.weight x : ℂ))
    (weightNonneg : ∀ x, 0 ≤ m.weight x) (n : ℕ) :
    (∫⁻ x, ENNReal.ofReal (∏ j ∈ range (n + 1), m.weight (F^[j] x)) ∂ν) =
      ENNReal.ofReal ‖((ContinuousLinearMap.apply ℂ ℂ one).comp aT)
        (((m.generator a) ^ n) (m.realize seed))‖ := by
  have hint : ∀ r, (((ContinuousLinearMap.apply ℂ ℂ one).comp aT).comp m.realize) r =
      ∫ x, m.view r x ∂ν := fun r => by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, realize_coefficient m ν aT testView core physReg hphys r one]
    simp only [hone, one_mul]
  have integrableView : ∀ r, Integrable (m.view r) ν := fun r => by
    have := (physReg r).integrable ν
    have same : (⇑(physReg r) : M → ℂ) = m.view r := funext (hphys r)
    rwa [same] at this
  exact (PhysicalModelNativeCoefficients.coefficient m bound ν
    ((ContinuousLinearMap.apply ℂ ℂ one).comp aT)
    (((ContinuousLinearMap.apply ℂ ℂ one).comp aT).comp m.realize)
    (fun r => (ContinuousLinearMap.comp_apply _ _ r).symm) hint integrableView a F hF seed hseed
    weightNonneg n).trans (congrArg (fun z => ENNReal.ofReal
      ‖((ContinuousLinearMap.apply ℂ ℂ one).comp aT) z‖)
      (ContinuousLinearMapPowApply.pow_apply (m.generator a) n _).symm)

section Tangent
variable [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  (ψ : M → ℝ) (hψ : ContMDiff (𝓘(ℝ, E)) 𝓘(ℝ) ∞ ψ) (CR CA : ℝ)
  (regularBound : ∀ c, ‖m.regularCore (coreMultiplier ψ hψ c)‖ ≤ CR * ‖m.regularCore c‖)
  (analyticBound : ∀ c, ‖coreLift m.qa (coreMultiplier ψ hψ c)‖ ≤ CA * ‖coreLift m.qa c‖)

set_option maxHeartbeats 40000000 in
include core hphys hone regularBound analyticBound in
/-- The pressure supporting inequality of the spectral product. -/
theorem product_tangent {L : ℝ} (bound : AnalyticBound m L) (a : Ω) (seed : Reg)
    (hseed : ∀ x, m.view seed x = (m.weight x : ℂ)) (mapCont : Continuous (m.maps a))
    (weightCont : Continuous m.weight) (weightNonneg : ∀ x, 0 ≤ m.weight x)
    (d : DeterministicLeading (m.generator a)) (P0 : ℝ) (hrate : d.rate = exp P0)
    {T : M ≃ₜ M} {Λ : Set M} (bd : BasicData (E := E) T Λ V) (hT : (T : M → M) = m.maps a)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T)
    (inverse : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 T.symm)
    {r q : ℝ} (regularity : 1 < r) (weightOrder : 0 < q)
    (forwardRegular : Regular (E := E) (F := E) r T)
    (inverseRegular : Regular (E := E) (F := E) r T.symm) (mixing : MixingOn T Λ)
    (weightRegular : Regular (E := E) (F := ℝ) q m.weight)
    (weightPos : ∀ x ∈ Λ, 0 < m.weight x)
    (weightSupport : Function.support m.weight ⊆ closure V)
    (hP0 : pressure T (bd.hyperbolic.potential m.weight) Λ = (P0 : EReal))
    (refData : FiniteSmoothReferenceCharts.Data (E := E) (M := M)) (νE : Measure E)
    [νE.IsAddHaarMeasure] (hν : ν = refData.measure νE) (t : ℝ) :
    ∃ Pt : ℝ, pressure T (bd.hyperbolic.potential (fun x => m.weight x * exp (t * ψ x))) Λ =
      (Pt : EReal) ∧ t * (d.mean (strongMultiplier m ψ hψ d.vector)).re ≤ Pt - P0 := by
  have lamPos : 0 < d.rate := d.rate_pos
  -- the tilted weight and its pressure
  let gt : M → ℝ := fun x => m.weight x * exp (t * ψ x)
  have gtCont : Continuous gt := weightCont.mul (continuous_exp.comp (continuous_const.mul hψ.continuous))
  have gtNonneg : ∀ x, 0 ≤ gt x := fun x => mul_nonneg (weightNonneg x) (exp_pos _).le
  have gtPos : ∀ x ∈ Λ, 0 < gt x := fun x hx => mul_pos (weightPos x hx) (exp_pos _)
  have gtSupport : Function.support gt ⊆ closure V := fun x hx =>
    weightSupport fun h => hx (by simp only [gt, h, zero_mul])
  obtain ⟨Pt, hPt, growthT⟩ := bd.exists_orbit_integral_growth forward inverse gt gtCont gtPos
    gtNonneg gtSupport refData νE
  refine ⟨Pt, hPt, ?_⟩
  let w : ℕ → M → ℝ := fun n x => ∏ i ∈ range (n + 1), m.weight ((m.maps a)^[i] x)
  let S : ℕ → M → ℝ := fun n x => ∑ j ∈ range n, ψ ((m.maps a)^[j] x)
  have wCont : ∀ n, Continuous (w n) := fun n => product_continuous _ mapCont _ weightCont _
  have SCont : ∀ n, Continuous (S n) := fun n =>
    continuous_finsetSum _ fun j _ => hψ.continuous.comp (mapCont.iterate j)
  obtain ⟨K, hK⟩ : ∃ K, ∀ x, |ψ x| ≤ K := by
    obtain ⟨K, hK⟩ := (isCompact_univ.image hψ.continuous).isBounded.exists_norm_le
    exact ⟨K, fun x => by simpa [Real.norm_eq_abs] using hK _ ⟨x, mem_univ _, rfl⟩⟩
  have hS : ∀ n x, |S n x| ≤ n * K := fun n x => by
    calc |S n x| ≤ ∑ j ∈ range n, |ψ ((m.maps a)^[j] x)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range n, K := sum_le_sum fun j _ => hK _
      _ = n * K := by rw [sum_const, card_range, nsmul_eq_mul]
  -- the shifted block lower growth of the paired raw powers
  have coefficient : ∀ n : ℕ, (∫⁻ x, ENNReal.ofReal
      (∏ j ∈ range (n + 1), m.weight ((T : M → M)^[j] x)) ∂(refData.measure νE)) =
      ENNReal.ofReal ‖((ContinuousLinearMap.apply ℂ ℂ one).comp aT)
        (((m.generator a) ^ n) (m.realize seed))‖ := fun n => by
    have := coefficient_pow m ν aT testView core physReg hphys one hone bound a T hT.symm seed
      hseed weightNonneg n
    rwa [hν] at this
  have lower := bd.shifted_block_growth_from_coefficients regularity weightOrder forwardRegular
    inverseRegular mixing refData νE m.weight weightRegular weightPos P0 hP0 (m.generator a)
    ((ContinuousLinearMap.apply ℂ ℂ one).comp aT) (m.realize seed) coefficient
  -- growth of the tilted masses
  have growth : ∀ R, exp (Pt - P0) < R → ∃ C, ∀ n,
      (d.rate ^ n)⁻¹ * ∫ x, w n x * exp (t * S n x) ∂ν ≤ C * R ^ n := by
    intro R hR
    have Rpos : 0 < R := (exp_pos _).trans hR
    set R' := R * d.rate with hR'def
    have hR' : exp Pt < R' := by
      rw [hR'def, hrate]
      have := mul_lt_mul_of_pos_right hR (exp_pos P0)
      rwa [← exp_add, sub_add_cancel] at this
    obtain ⟨C', hC', hbound⟩ := growthT R' hR'
    simp only [hT] at hbound
    refine ⟨exp (|t| * K) * C' * R', fun n => ?_⟩
    have cpos : 0 < (d.rate ^ n)⁻¹ := inv_pos.mpr (pow_pos lamPos n)
    have prodCont : Continuous (fun x => ∏ i ∈ range (n + 1), gt ((m.maps a)^[i] x)) :=
      product_continuous _ mapCont _ gtCont _
    have intBound : ∫ x, ∏ i ∈ range (n + 1), gt ((m.maps a)^[i] x) ∂ν ≤ C' * R' ^ (n + 1) :=
      integral_le_of_lintegral ν (integrable_of_continuous ν prodCont)
        (fun x => prod_nonneg fun _ _ => gtNonneg _) (by positivity) (by rw [hν]; exact hbound (n + 1))
    calc (d.rate ^ n)⁻¹ * ∫ x, w n x * exp (t * S n x) ∂ν
        ≤ (d.rate ^ n)⁻¹ * ∫ x, exp (|t| * K) * ∏ i ∈ range (n + 1), gt ((m.maps a)^[i] x) ∂ν :=
          mul_le_mul_of_nonneg_left (integral_mono (integrable_of_continuous ν
            ((wCont n).mul (continuous_exp.comp (continuous_const.mul (SCont n)))))
            (integrable_of_continuous ν (continuous_const.mul prodCont))
            (fun x => tilted_le (m.maps a) m.weight ψ weightNonneg K hK t n x)) cpos.le
      _ = (d.rate ^ n)⁻¹ * (exp (|t| * K) * ∫ x, ∏ i ∈ range (n + 1), gt ((m.maps a)^[i] x) ∂ν) := by
          rw [integral_const_mul]
      _ ≤ (d.rate ^ n)⁻¹ * (exp (|t| * K) * (C' * R' ^ (n + 1))) := by gcongr
      _ = exp (|t| * K) * C' * R' * R ^ n := by
          have lamNe : d.rate ≠ 0 := lamPos.ne'
          rw [hR'def]
          field_simp
          ring
  exact d.orbit_tangent ((ContinuousLinearMap.apply ℂ ℂ one).comp aT) (strongMultiplier m ψ hψ)
    (m.realize seed) ν w S (fun n x => prod_nonneg fun _ _ => weightNonneg _)
    (fun n => integrable_of_continuous ν (wCont n))
    (fun n t => integrable_of_continuous ν ((wCont n).mul (continuous_const.mul (SCont n))))
    (fun n t => integrable_of_continuous ν ((wCont n).mul
      (continuous_exp.comp (continuous_const.mul (SCont n))))) K hS
    (fun n => normalized_mass m ν aT testView core physReg hphys one hone bound a seed hseed _ n)
    (fun n => normalized_birkhoff m ν aT testView core physReg hphys one hone ψ hψ CR CA
      regularBound analyticBound bound a seed hseed mapCont weightCont _ n)
    P0 hrate lower t (Pt - P0) growth

end Tangent
end ConditionedStochasticStabilityHyperbolic.PhysicalModelHorizonIdentities
