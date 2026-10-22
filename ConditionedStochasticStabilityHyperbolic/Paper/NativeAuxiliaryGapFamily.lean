module
public import ConditionedStochasticStabilityHyperbolic.Paper.AuxiliaryAnosov
public import ConditionedStochasticStabilityHyperbolic.Paper.NativeLocalOutcomeProducer
public import ConditionedStochasticStabilityHyperbolic.Paper.CompactLocalWeightSetup
public import ConditionedStochasticStabilityHyperbolic.Paper.NormalizedGapRenormalization
public import ConditionedStochasticStabilityHyperbolic.Paper.LocalGapFamilyWindow

/-! The auxiliary Anosov spectral-gap family at normalization one (global step E). The native local
outcome of the auxiliary with weight one, potential zero and live state `univ` gives a family of
literal QEM points with normalized gaps on one positive window; renormalizing the chain from the
outcome scale to one keeps the same probabilities. No source record is used. -/

public noncomputable section
open Set MeasureTheory IsManifold Bundle Filter
open scoped Manifold ContDiff NNReal Topology
namespace ConditionedStochasticStabilityHyperbolic.Paper.NativeAuxiliaryGapFamily
open LeanShared RegularNoise

section Change
variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [ChartedSpace E M] [Fintype ι] [MeasurableSpace M] [BorelSpace M]
  {T : M ≃ₜ M} {r s : ℝ}

omit [FiniteDimensional ℝ E] in
/-- A normalized gap does not depend on the regularity label of the noise. -/
theorem normalizedGapAt_changeRegularity (P : Maps (E := E) (ι := ι) T r) (e : r = s)
    (L : Laws (ι := ι)) (K Λ : Set M) [CompactSpace K] (hK : MeasurableSet K)
    (w : K → ℝ) (hw : Measurable w) (R : ℝ) (hR : 0 < R) (hwR : ∀ x, w x ≤ R)
    (ν : ProbabilityMeasure K) (ε : ℝ≥0) :
    LocalConclusions.NormalizedGapAt (P.changeRegularity e) L K Λ hK w hw R hR hwR ν ε ↔
      LocalConclusions.NormalizedGapAt P L K Λ hK w hw R hR hwR ν ε := by
  subst s
  rfl

end Change

variable {Y F κ : Type}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [MetricSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]
  [ChartedSpace F Y] [IsManifold (𝓘(ℝ, F)) ∞ Y] [CompactSpace Y]
  [RiemannianBundle (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
  [IsContinuousRiemannianBundle F (fun y : Y => TangentSpace (𝓘(ℝ, F)) y)]
  [Fintype κ] {r : ℝ} (a : AuxiliaryAnosov (F := F) (Y := Y) (ι := κ) r)

local instance nativeAuxiliaryCompact : CompactSpace (univ : Set Y) :=
  isCompact_iff_compactSpace.mp isCompact_univ

/-- The auxiliary gap family at normalization one, from the native local outcome. -/
theorem exists_family_native :
    ∃ ν : ℝ≥0 → ProbabilityMeasure (univ : Set Y),
      ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0,
        LocalConclusions.NormalizedGapAt a.noise a.laws univ univ MeasurableSet.univ
          (fun _ => 1) measurable_const 1 zero_lt_one (fun _ => le_rfl) (ν ε) ε := by
  let s : AdaptedLocalWeightSetup.Data a.hl (fun _ => 1) univ :=
    AdaptedLocalWeightSetup.of_supported_product a.hl (fun _ => 1) univ
      isOpen_univ subset_rfl subset_rfl continuous_const (fun _ _ => rfl)
      (fun ζ hs _ => by
        have identity : ζ * (fun _ => (1 : ℝ)) = ζ := by
          funext y
          exact mul_one (ζ y)
        exact identity.symm ▸ FractionalManifoldRegularity.regular_of_smooth hs
          (sub_nonneg.mpr a.hl.regularity_gt_one.le))
  have core : isolatedCore a.map (univ : Set Y) = univ := by
    simpa only [closure_univ] using a.hl.actual_isolated_core.symm
  have e : r = s.fresh.r := (s.regularity_eq.trans a.regularity).symm
  have hφ : ∀ y ∈ (univ : Set Y), (s.cutoff * fun _ : Y => (1 : ℝ)) y = Real.exp ((fun _ : Y => 0) y) :=
    fun y hy => (s.core_agreement hy).trans Real.exp_zero.symm
  obtain ⟨d, hmaps, hlaws, -⟩ := NativeLocalOutcomeProducer.native_local_outcome a.hl
    (fun _ => 1) continuous_const (fun _ => zero_le_one) s univ isCompact_univ core
    (subset_univ _) (fun y _ => by rw [s.hyperbolic_eq]; exact a.stable_positive y)
    (a.noise.changeRegularity e) a.laws (fun _ => 0) hφ 0
  let fd := d.family
  refine ⟨fd.probability, ?_⟩
  have small : ∀ᶠ ε : ℝ≥0 in 𝓝[>] 0, ε ≤ fd.window :=
    mem_nhdsWithin_of_mem_nhds (eventually_le_nhds fd.window_positive)
  filter_upwards [self_mem_nhdsWithin, small] with ε positive window
  have gap := fd.gap ε positive window
  rw [hmaps, hlaws] at gap
  obtain ⟨he, hw, gapY⟩ := (normalizedGapAt_changeRegularity a.noise e a.laws univ univ
    MeasurableSet.univ _ _ d.scale d.scale_positive _ (fd.probability ε) ε).mp gap
  refine ⟨he, hw, ?_⟩
  exact NormalizedGapRenormalization.restrictedNoise (a.laws.law ε)
    (fun z : Y × cube (ι := κ) ε => a.noise.family ε z.2.val z.1)
    (a.noise.raw_measurable ε he hw) univ MeasurableSet.univ
    (fun _ => 1) measurable_const d.scale 1 d.scale_positive zero_lt_one
    fd.weight_bound (fun _ => le_rfl) _ (fd.probability ε) gapY

end ConditionedStochasticStabilityHyperbolic.Paper.NativeAuxiliaryGapFamily
