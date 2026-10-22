module

public import LeanShared.Probability.StationaryTransientLocalization
public import AbsorbingMarkovChains.DoobTransform
import AbsorbingMarkovChains.MarkovPairs

/-!
# Localization of the genuine Doob stationary measure

Only explicit right eigenfunction and left eigenmeasure data are used. Full
extinction makes the bad region have zero eigenfunction; actual no-return
support then makes the retained region absorbing for the Doob kernel.
Complement extinction transfers by absolute continuity of actual finite
kernel powers. Stationarity derives support localization of `g μ`.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace ConditionedStochasticStabilityHyperbolic.Restriction

open AbsorbingMarkovChains

variable {X : Type*} [MeasurableSpace X] {K : Kernel X X} [IsSFiniteKernel K]
  (d : DoobTransform.EigenData K)

/-- Finite extinction in the original killed kernel forces eigenfunction
vanishing, using the checked finite Doob formula and its Markov normalization. -/
theorem doob_weight_zero_of_extinction (x : X) (N : ℕ)
    (hext : (K ^ N) x univ = 0) : d.weight x = 0 := by
  by_contra hx
  let y : d.State := ⟨x, hx⟩
  let : IsMarkovKernel (d.kernel ^ N) := MarkovPairs.isMarkovKernel_pow d.kernel N
  have h := d.kernel_pow_apply N y univ MeasurableSet.univ
  have hzero : (K ^ N) x = 0 := Measure.measure_univ_eq_zero.mp hext
  change (d.kernel ^ N) y univ = _ at h
  rw [measure_univ, hzero, Measure.restrict_zero, lintegral_zero_measure, mul_zero] at h
  exact one_ne_zero h

/-- The actual Doob transition is absolutely continuous with respect to
the original kernel restricted to its positive-eigenfunction live type. -/
theorem doob_absolutelyContinuous_live (x : d.State) : d.kernel x ≪ d.liveKernel x :=
  Kernel.withDensity_absolutelyContinuous (κ := d.liveKernel) d.positiveData.density x

/-- Kernel no-return into a full-extinct bad region makes the retained
region absorbing for positive-eigenfunction Doob states. -/
theorem doob_retained_absorbing (U : Set X) (B : Set X)
    (hbad : ∀ x ∈ B, d.weight x = 0)
    (hreturn : ∀ x ∈ U, ∀ᵐ y ∂K x, y ∉ U → y ∈ B) :
    ∀ x ∈ (Subtype.val ⁻¹' U : Set d.State),
      d.kernel x (Subtype.val ⁻¹' U)ᶜ = 0 := by
  intro x hx
  have hraw : ∀ᵐ y ∂d.liveKernel x, y.val ∉ U → y.val ∈ B :=
    (ae_restrict_iff_subtype d.measurableSet_liveSet).1 (ae_restrict_of_ae (hreturn x.val hx))
  have hdoob := hraw.filter_mono (doob_absolutelyContinuous_live d x).ae_le
  apply measure_eq_zero_iff_ae_notMem.2
  filter_upwards [hdoob] with y hy hout
  exact y.property (hbad y.val (hy hout))

/-- Extra positive-state killing and the Doob density change preserve
finite extinction of the actual original complementary killed kernel. -/
theorem doob_complement_extinction (U : Set X) (hU : MeasurableSet U) (N : ℕ)
    (hext : ∀ x : ↥(Uᶜ), ((LeanShared.SubtypeKernel.restrict K Uᶜ hU.compl) ^ N) x univ = 0) :
    ∀ x : ↥((Subtype.val ⁻¹' U : Set d.State)ᶜ),
      ((LeanShared.SubtypeKernel.restrict d.kernel (Subtype.val ⁻¹' U)ᶜ
        (hU.preimage measurable_subtype_coe).compl) ^ N) x univ = 0 := by
  let V : Set d.State := Subtype.val ⁻¹' U
  have hV : MeasurableSet V := hU.preimage measurable_subtype_coe
  let ι : ↥(Vᶜ) → ↥(Uᶜ) := fun x => ⟨x.val.val, x.property⟩
  have hι : Measurable ι :=
    (measurable_subtype_coe.comp measurable_subtype_coe).subtype_mk
  apply LeanShared.StationaryTransientLocalization.kernel_extinction_of_map_absolutelyContinuous
    (LeanShared.SubtypeKernel.restrict d.kernel Vᶜ hV.compl)
    (LeanShared.SubtypeKernel.restrict K Uᶜ hU.compl) ι hι _ N hext
  intro x
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hz
  rw [Measure.map_apply hι hA, LeanShared.SubtypeKernel.restrict_apply_set]
  · apply doob_absolutelyContinuous_live d x.val
    rw [d.liveKernel_apply]
    · rw [LeanShared.SubtypeKernel.restrict_apply_set K Uᶜ hU.compl (ι x) A hA] at hz
      apply measure_mono_null _ hz
      rintro y ⟨z, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨ι v, hv, rfl⟩
    · exact (MeasurableEmbedding.subtype_coe hV.compl).measurableSet_image' (hA.preimage hι)
  · exact hA.preimage hι

omit [IsSFiniteKernel K] in
/-- The original weighted measure is the pushforward of its positive-state
restriction: its zero-eigenfunction region has weighted mass zero. -/
theorem map_doob_weightedMeasure (μ : Measure X) :
    ((μ.withDensity d.weight).comap (Subtype.val : d.State → X)).map Subtype.val =
      μ.withDensity d.weight := by
  rw [map_comap_subtype_coe d.measurableSet_liveSet]
  apply Measure.restrict_eq_self_of_ae_mem
  exact (ae_withDensity_iff d.measurable_weight).2 (ae_of_all μ fun _ hx => hx)

/-- Localization of `g μ` follows from actual left/right eigenrelations,
no-return support and finite complementary extinction. It is not an input
support condition on a quasi-ergodic measure. -/
theorem doob_weightedMeasure_complement_zero (μ : Measure X)
    (hleft : K ∘ₘ μ = d.rate • μ) (U : Set X) (hU : MeasurableSet U) (B : Set X)
    (hreturn : ∀ x ∈ U, ∀ᵐ y ∂K x, y ∉ U → y ∈ B)
    (hbadext : ∀ x ∈ B, ∃ n : ℕ, (K ^ n) x univ = 0)
    (N : ℕ)
    (hcompext : ∀ x : ↥(Uᶜ), ((LeanShared.SubtypeKernel.restrict K Uᶜ hU.compl) ^ N) x univ = 0) :
    μ.withDensity d.weight Uᶜ = 0 := by
  have hbad : ∀ x ∈ B, d.weight x = 0 := by
    intro x hx
    obtain ⟨n, hn⟩ := hbadext x hx
    exact doob_weight_zero_of_extinction d x n hn
  have hmass := LeanShared.StationaryTransientLocalization.stationary_complement_mass_zero_of_extinction
    d.kernel ((μ.withDensity d.weight).comap (Subtype.val : d.State → X))
    (d.invariant_weightedMeasure μ hleft) (Subtype.val ⁻¹' U)
    (hU.preimage measurable_subtype_coe) (doob_retained_absorbing d U B hbad hreturn)
    N (doob_complement_extinction d U hU N hcompext)
  rw [← map_doob_weightedMeasure d μ, Measure.map_apply measurable_subtype_coe hU.compl]
  exact hmass

section Support

variable [TopologicalSpace X]

theorem doob_weightedMeasure_support_subset_closure (μ : Measure X)
    (hleft : K ∘ₘ μ = d.rate • μ) (U : Set X) (hU : MeasurableSet U) (B : Set X)
    (hreturn : ∀ x ∈ U, ∀ᵐ y ∂K x, y ∉ U → y ∈ B)
    (hbadext : ∀ x ∈ B, ∃ n : ℕ, (K ^ n) x univ = 0) (N : ℕ)
    (hcompext : ∀ x : ↥(Uᶜ), ((LeanShared.SubtypeKernel.restrict K Uᶜ hU.compl) ^ N) x univ = 0) :
    (μ.withDensity d.weight).support ⊆ closure U := by
  apply Measure.support_subset_of_isClosed isClosed_closure
  change μ.withDensity d.weight (closure U)ᶜ = 0
  exact measure_mono_null (compl_subset_compl.mpr subset_closure)
    (doob_weightedMeasure_complement_zero d μ hleft U hU B hreturn hbadext N hcompext)

end Support

end ConditionedStochasticStabilityHyperbolic.Restriction
