module
public import ConditionedStochasticStabilityHyperbolic.Spectral.DeterministicPairTrace
public import ConditionedStochasticStabilityHyperbolic.Spectral.DeterministicLeadingUniqueness
public import ConditionedStochasticStabilityHyperbolic.Baladi_Dynamical_Zeta_Functions_and_Dynamical_Determinants_for_Hyperbolic_Maps.SmoothPhysicalTests
public import ConditionedStochasticStabilityHyperbolic.Paper.EquilibriumOnCollar

/-! The equilibrium identification consumed by local stability. The raw product identity on the
intermediate generator is transported to any normalized leading record of the zero-noise
intermediate operator (the product functional is intrinsic), then to the quotient form of the
pair, and the collar integral of a smooth test is the ambient integral of its smooth extension.
-/

public noncomputable section
open Set MeasureTheory Bundle
open scoped Manifold ContDiff BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.LocalEquilibriumIdentification
open KellerLiverani1999 KellerLiveraniMeasureStability

section Spectral
variable {S H : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  {Ps : S →L[ℂ] S} {Ph Qh : H →L[ℂ] H}

/-- The raw product value gives the pair quotient for any normalized leading record. -/
theorem raw_product_to_pair_ratio (ds : DeterministicLeading Ps) (dm : DeterministicLeading Ph)
    (draw : DeterministicLeading Qh) (R : ℝ) (hR : 0 < R) (raw : (R : ℂ) • Ph = Qh)
    (i : S →L[ℂ] H) (hi : Function.Injective i) (commutes : i.comp Ps = Ph.comp i)
    (sameRate : ds.rate = dm.rate) (M : H →L[ℂ] H) (I : ℝ)
    (identifiedRaw : (draw.mean (M draw.vector)).re = I) :
    I = (dm.mean (M (i ds.vector)) / dm.mean (i ds.vector)).re := by
  have ratio := deterministic_multiplier_ratio ds dm i hi commutes sameRate M
  have intrinsic := (draw.normalizeOfRaw R hR raw).product_eq dm M
  rw [DeterministicLeading.normalizeOfRaw_mean, DeterministicLeading.normalizeOfRaw_vector]
    at intrinsic
  rw [ratio, intrinsic]
  exact identifiedRaw.symm

end Spectral

section Collar
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The collar integral of a test is the ambient integral of a continuous extension. -/
theorem integral_on_collar (K : Set X) (νK : ProbabilityMeasure K) (η : ProbabilityMeasure X)
    (pushforward : (νK : Measure K).map Subtype.val = (η : Measure X))
    (f : K →ᵇ ℝ) (ψ : X → ℝ) (hψ : Continuous ψ) (agrees : ∀ x : K, f x = ψ x.val) :
    (∫ x, f x ∂(νK : Measure K)) = ∫ x, ψ x ∂(η : Measure X) := by
  calc (∫ x, f x ∂(νK : Measure K)) = ∫ x : K, ψ x.val ∂(νK : Measure K) :=
        integral_congr_ae (ae_of_all _ agrees)
    _ = ∫ x, ψ x ∂(η : Measure X) := by
        rw [← pushforward]
        exact (integral_map measurable_subtype_coe.aemeasurable
          hψ.aestronglyMeasurable).symm

end Collar

section Consumer
variable {E X S H : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [ChartedSpace E X] [IsManifold (𝓘(ℝ, E)) ∞ X]
  [RiemannianBundle (fun x : X => TangentSpace (𝓘(ℝ, E)) x)]
  [NormedAddCommGroup S] [NormedSpace ℂ S]
  [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  {T : X ≃ₜ X} {g : X → ℝ} {Λ V : Set X}
  {Ps : S →L[ℂ] S} {Ph Qh : H →L[ℂ] H}

omit [CompactSpace X] in
/-- The equilibrium identification of the local consumer from the raw product identities. -/
theorem equilibriumIdentification_from_raw_products
    (hHL : Paper.HL (E := E) T g Λ V)
    (e : LeanShared.HyperbolicBasicSet.EquilibriumPackage hHL.basic.hyperbolic g)
    (K : Set X) [CompactSpace K] (hK : MeasurableSet K) (hΛK : Λ ⊆ K)
    (ds : DeterministicLeading Ps) (dm : DeterministicLeading Ph)
    (draw : DeterministicLeading Qh) (R : ℝ) (hR : 0 < R) (raw : (R : ℂ) • Ph = Qh)
    (i : S →L[ℂ] H) (hi : Function.Injective i) (commutes : i.comp Ps = Ph.comp i)
    (sameRate : ds.rate = dm.rate)
    (M : SmoothPhysicalTests.tests (E := E) K → H →L[ℂ] H)
    (identifiedRaw : ∀ h : SmoothPhysicalTests.tests (E := E) K,
      (draw.mean (M h draw.vector)).re =
        ∫ x, SmoothPhysicalTests.extension K h x ∂(e.state : Measure X)) :
    ∀ h : SmoothPhysicalTests.tests (E := E) K,
      (∫ x, h.val x ∂(hHL.stateOnCollar e K hK hΛK : Measure K)) =
        (dm.mean (M h (i ds.vector)) / dm.mean (i ds.vector)).re := by
  intro h
  have collar := integral_on_collar K (hHL.stateOnCollar e K hK hΛK) e.state
    (hHL.stateOnCollar_map e K hK hΛK) h.val (SmoothPhysicalTests.extension K h)
    (SmoothPhysicalTests.extension_smooth K h).continuous
    (fun x => (SmoothPhysicalTests.extension_live K h x).symm)
  exact collar.trans (raw_product_to_pair_ratio ds dm draw R hR raw i hi commutes sameRate
    (M h) _ (identifiedRaw h))

end Consumer

end ConditionedStochasticStabilityHyperbolic.LocalEquilibriumIdentification
