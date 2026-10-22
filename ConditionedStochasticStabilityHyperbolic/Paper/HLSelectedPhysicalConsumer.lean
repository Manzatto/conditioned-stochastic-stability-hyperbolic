module
public import ConditionedStochasticStabilityHyperbolic.Spectral.ActualAnnealedZero
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalHolderCoreTestMetadata
public import ConditionedStochasticStabilityHyperbolic.Paper.HLSelectedPhysicalInputs
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelCarrierLeading
import all ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.PhysicalModelLeadingTrace
public import ConditionedStochasticStabilityHyperbolic.Paper.HLPhysicalLocalStability
import all ConditionedStochasticStabilityHyperbolic.Paper.HLPhysicalLocalStability
public noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 20000
open Set IsManifold MeasureTheory Filter Bundle
open scoped Manifold ContDiff BoundedContinuousFunction Topology NNReal ComplexConjugate
namespace ConditionedStochasticStabilityHyperbolic.Paper.HLSelectedPhysicalInputs
open LeanShared DyadicCompletion SmoothSupportedManifoldCore KellerLiverani1999
open PhysicalHolderClassicalSources.SourceData
universe uX
private theorem consume
  {M : Type uX} {E U AtlasIndex A Ω : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  [MetricSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)] [MetricSpace Ω]
  {LocalReg : AtlasIndex → Type*} [∀ i, NormedAddCommGroup (LocalReg i)]
  [∀ i, NormedSpace ℂ (LocalReg i)] [∀ i, CompleteSpace (LocalReg i)]
  {V S : Set M} {μ : Measure U} [μ.IsAddHaarMeasure]
  {T : M ≃ₜ M} {g : M → ℝ} {Λ : Set M}
  (h : Paper.HL (E := E) T g Λ V)
  (u : ℝ)
  (holder : ∀ c : SmoothSupportedManifoldCore.core (E := E) (univ : Set M),
    ∃ C : ℝ, ∀ x y, ‖c.val x - c.val y‖ ≤ C * dist x y ^ u)
  (ms mh : PhysicalManifoldModel.Data (E := E) (U := U) (M := M) (AtlasIndex := AtlasIndex)
    (Reg := SmoothHolderTestSpaces.space (u) holder V)
    (LocalReg := LocalReg) (A := A) (Ω := Ω) V S μ)
  (K : Set M) [CompactSpace K] (hK : IsCompact K)
  (hΛ : isolatedCore T K = Λ) (hΛK : Λ ⊆ K)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  {ι : Type*} [Fintype ι]
  (N : RegularNoise.Maps (E := E) (ι := ι) T h.r)
  (L : RegularNoise.Laws (ι := ι))
  (representation : RegularNoise.Representation N Ω mh.maps)
  (w : K → ℝ) (R : ℝ) (hR : 0 < R)
  (σ : Measure M) [IsFiniteMeasure σ] [σ.IsOpenPosMeasure]
  (c : Data (Carrier := mh.StrongSpace) (W := W) h u holder ms mh K hK hΛ hΛK N L representation w R hR σ)
  (i : ms.StrongSpace →L[ℂ] mh.StrongSpace) (j : mh.StrongSpace →L[ℂ] W)
  (p : ProducedAnnealedPair.Data i j L.fixedLaw (fun _ => inferInstance)
    (fun ε z => ms.generator (representation.fixedParameters ε z))
    (fun ε z => mh.generator (representation.fixedParameters ε z)) R)
  (principalS : p.strong.principal < Real.exp c.equilibrium.pressure)
  (principalH : p.intermediate.principal < Real.exp c.equilibrium.pressure)
  (weakS : Real.exp c.equilibrium.pressure ≤ p.strong.weakRate)
  (weakH : Real.exp c.equilibrium.pressure ≤ p.intermediate.weakRate) :
  LocalConclusions.Stability N L K Λ hK.measurableSet w c.hw.measurable R hR c.hwR
    (fun x => c.φ x - Real.log (h.basic.hyperbolic.unstableJacobian x)) := by
  have rawS : (R : ℂ) • p.strong.operator 0 = ms.generator representation.reference :=
    p.strong.raw_zero_of_constant_generators hR.ne' _ (fun z =>
      (p.strong_generator 0 z).trans
        (congrArg ms.generator (representation.fixedParameters_zero z)))
  have rawH : (R : ℂ) • p.intermediate.operator 0 = mh.generator representation.reference :=
    p.intermediate.raw_zero_of_constant_generators hR.ne' _ (fun z =>
      (p.intermediate_generator 0 z).trans
        (congrArg mh.generator (representation.fixedParameters_zero z)))
  let ds := c.dsRaw.normalizeOfRaw (P := p.strong.operator 0) R hR rawS
  let dm := c.dmRaw.normalizeOfRaw (P := p.intermediate.operator 0) R hR rawH
  have rateS' :=
    (c.dsRaw.normalizeOfRaw_rate (P := p.strong.operator 0) R hR rawS).trans
      ((congrArg (fun v : ℝ => R⁻¹ * v) c.rateS).trans
        (inv_mul_eq_div R (Real.exp c.equilibrium.pressure)))
  have rateH' :=
    (c.dmRaw.normalizeOfRaw_rate (P := p.intermediate.operator 0) R hR rawH).trans
      ((congrArg (fun v : ℝ => R⁻¹ * v) c.rateH).trans
        (inv_mul_eq_div R (Real.exp c.equilibrium.pressure)))
  have hpS := (div_lt_div_of_pos_right principalS hR).trans_eq rateS'.symm
  have hpH := (div_lt_div_of_pos_right principalH hR).trans_eq rateH'.symm
  have hwS := rateS'.trans_le (div_le_div_of_nonneg_right weakS hR.le)
  have hwH := rateH'.trans_le (div_le_div_of_nonneg_right weakH hR.le)
  have result := HLPhysicalLocalStability.stability_from_classical_physical_sources u holder ms mh
    K c.G c.B hK h hΛ c.equilibrium c.φ c.hφ N L representation c.hF w c.hw c.hwG
    c.wc c.hwc R hR c.hwR c.hwcR c.hweight i j p c.rowsS c.rowsH c.noiseH σ
    c.commonS c.common c.ordinarySource c.submersion c.hBG c.r c.t c.sn c.margins
    c.essential c.essential c.kl c.kl ds dm hpS hwS hpH hwH
    (rateS'.trans rateH'.symm) c.realCutoffS c.realCutoffH c.evenAngleS c.evenAngleH
    (by
      intro Z _ _
      exact c.a2 (H := mh.StrongSpace)
        (P := SupportedPairingClosedCore.space (physicalRealization V K mh.regularCore))
        (Z := Z) (Reg := PhysicalHolderClassicalSources.Regular u holder V)) (by
      intro ψ
      simpa only [PhysicalManifoldModel.Data.GeneratorLeading.multiplierTrace, dm, PhysicalManifoldModel.Data.GeneratorLeading.normalizeOfRaw,
        DeterministicLeading.normalizeOfRaw_mean,
        DeterministicLeading.normalizeOfRaw_vector,
        PhysicalHolderClassicalSources.SourceData.coreData_multiplier] using c.deterministicEquilibrium ψ)
  exact result
end ConditionedStochasticStabilityHyperbolic.Paper.HLSelectedPhysicalInputs
