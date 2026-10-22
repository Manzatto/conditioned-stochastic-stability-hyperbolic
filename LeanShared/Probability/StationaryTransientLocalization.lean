module

public import LeanShared.Probability.SubtypeKernel
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Stationary measures avoid uniformly transient complements

An absorbing measurable region has an autonomous complementary killed
kernel. Restriction of any measure intertwines the kernels because there is
no return from the absorbing region. Stationarity and finite complement
extinction then force zero mass outside the region.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace LeanShared.StationaryTransientLocalization

variable {X : Type*} [MeasurableSpace X]

/-- Absence of returns into a retained measurable set makes subtype
restriction commute with actual measure/kernel composition. -/
theorem restrict_comp_eq_comap (L : Kernel X X) (V : Set X) (hV : MeasurableSet V)
    (hno : ∀ x ∉ V, L x V = 0) (μ : Measure X) :
    (L ∘ₘ μ).comap (Subtype.val : V → X) =
      SubtypeKernel.restrict L V hV ∘ₘ μ.comap (Subtype.val : V → X) := by
  let e := MeasurableEmbedding.subtype_coe hV
  ext A hA
  have himage : MeasurableSet ((Subtype.val : V → X) '' A) := e.measurableSet_image' hA
  rw [e.comap_apply, Measure.bind_apply himage L.aemeasurable,
    Measure.bind_apply hA (SubtypeKernel.restrict L V hV).aemeasurable]
  simp_rw [SubtypeKernel.restrict_apply_set L V hV _ A hA]
  rw [lintegral_subtype_comap hV (fun x => L x (Subtype.val '' A))]
  symm
  apply setLIntegral_eq_of_support_subset
  intro x hx
  by_contra hnot
  exact hx (measure_mono_null (Subtype.coe_image_subset V A) (hno x hnot))

/-- Stationarity is inherited by the complementary killed kernel when
there is no transition from the absorbing region back into the complement. -/
theorem stationary_complement (L : Kernel X X) (μ : Measure X)
    (hstat : L ∘ₘ μ = μ) (U : Set X) (hU : MeasurableSet U)
    (habs : ∀ x ∈ U, L x Uᶜ = 0) :
    SubtypeKernel.restrict L Uᶜ hU.compl ∘ₘ μ.comap (Subtype.val : ↥(Uᶜ) → X) =
      μ.comap (Subtype.val : ↥(Uᶜ) → X) := by
  rw [← restrict_comp_eq_comap L Uᶜ hU.compl
    (fun x hx => habs x (by simpa only [mem_compl_iff, not_not] using hx)), hstat]

/-- A stationary measure is stationary for every actual kernel power. -/
theorem stationary_pow (L : Kernel X X) (μ : Measure X)
    (hstat : L ∘ₘ μ = μ) (N : ℕ) : (L ^ N) ∘ₘ μ = μ := by
  induction N with
  | zero => exact Measure.bind_dirac
  | succ N ih =>
      rw [pow_succ']
      change (L ∘ₖ (L ^ N)) ∘ₘ μ = μ
      rw [← Measure.comp_assoc, ih, hstat]

/-- A measurable inclusion with one-step absolute continuity preserves
absolute continuity at every actual kernel power. This also permits an
additional destination killing, rather than requiring a full conjugacy. -/
theorem kernel_pow_map_absolutelyContinuous
    {Y : Type*} [MeasurableSpace Y] (L : Kernel X X) (K : Kernel Y Y)
    (ι : X → Y) (hι : Measurable ι)
    (hstep : ∀ x, (L x).map ι ≪ K (ι x)) (N : ℕ) (x : X) :
    ((L ^ N) x).map ι ≪ (K ^ N) (ι x) := by
  have hchange (ν : Measure X) :
      K.comap ι hι ∘ₘ ν = K ∘ₘ ν.map ι := by
    ext A hA
    rw [Measure.bind_apply hA (K.comap ι hι).aemeasurable,
      Measure.bind_apply hA K.aemeasurable, lintegral_map (K.measurable_coe hA) hι]
    rfl
  induction N with
  | zero =>
      change (Measure.dirac x).map ι ≪ Measure.dirac (ι x)
      rw [Measure.map_dirac' hι]
  | succ N ih =>
      rw [pow_succ', pow_succ']
      change (L ∘ₘ (L ^ N) x).map ι ≪ K ∘ₘ (K ^ N) (ι x)
      rw [Measure.map_comp _ _ hι]
      have hstep' (y : X) : (L.map ι) y ≪ K.comap ι hι y := by
        simpa only [Kernel.map_apply _ hι, Kernel.comap_apply] using hstep y
      have hleft : (L.map ι) ∘ₘ (L ^ N) x ≪ (K.comap ι hι) ∘ₘ (L ^ N) x :=
        Measure.AbsolutelyContinuous.comp_left ((L ^ N) x) (ae_of_all _ hstep')
      apply hleft.trans
      rw [hchange]
      exact ih.comp_right K

/-- Finite endpoint extinction transfers through a measurable inclusion
and absolute continuity, including density changes and extra killing. -/
theorem kernel_extinction_of_map_absolutelyContinuous
    {Y : Type*} [MeasurableSpace Y] (L : Kernel X X) (K : Kernel Y Y)
    (ι : X → Y) (hι : Measurable ι)
    (hstep : ∀ x, (L x).map ι ≪ K (ι x)) (N : ℕ)
    (hext : ∀ y, (K ^ N) y univ = 0) : ∀ x, (L ^ N) x univ = 0 := by
  intro x
  have h := kernel_pow_map_absolutelyContinuous L K ι hι hstep N x (hext (ι x))
  simpa only [Measure.map_apply hι MeasurableSet.univ, preimage_univ] using h

/-- Uniform finite extinction of the actual complementary subtype kernel
forces every stationary measure to give the complement mass zero. No
finiteness or normalization assumption on the stationary measure is needed. -/
theorem stationary_complement_mass_zero (L : Kernel X X) (μ : Measure X)
    (hstat : L ∘ₘ μ = μ) (U : Set X) (hU : MeasurableSet U)
    (habs : ∀ x ∈ U, L x Uᶜ = 0) (N : ℕ)
    (hnil : (SubtypeKernel.restrict L Uᶜ hU.compl) ^ N = 0) : μ Uᶜ = 0 := by
  have hp := stationary_pow (SubtypeKernel.restrict L Uᶜ hU.compl)
    (μ.comap (Subtype.val : ↥(Uᶜ) → X)) (stationary_complement L μ hstat U hU habs) N
  rw [hnil] at hp
  have hz : μ.comap (Subtype.val : ↥(Uᶜ) → X) = 0 := by
    change (μ.comap (Subtype.val : ↥(Uᶜ) → X)).bind (fun _ => 0) = _ at hp
    rw [Measure.bind_zero_right'] at hp
    exact hp.symm
  have hu := congrArg (fun ν : Measure ↥(Uᶜ) => ν univ) hz
  rw [(MeasurableEmbedding.subtype_coe hU.compl).comap_apply,
    Set.image_univ, Subtype.range_coe] at hu
  simpa using hu

/-- A pointwise endpoint-mass extinction certificate suffices; kernel
nilpotence is derived rather than added as a spectral assumption. -/
theorem stationary_complement_mass_zero_of_extinction (L : Kernel X X) (μ : Measure X)
    (hstat : L ∘ₘ μ = μ) (U : Set X) (hU : MeasurableSet U)
    (habs : ∀ x ∈ U, L x Uᶜ = 0) (N : ℕ)
    (hext : ∀ x : ↥(Uᶜ), ((SubtypeKernel.restrict L Uᶜ hU.compl) ^ N) x univ = 0) :
    μ Uᶜ = 0 := by
  apply stationary_complement_mass_zero L μ hstat U hU habs N
  ext x A _hA
  have hx := Measure.measure_univ_eq_zero.mp (hext x)
  rw [hx]
  rfl

section Support

variable [TopologicalSpace X]

/-- Topological support is localized in the closure of the absorbing
region, derived from the zero complementary mass. -/
theorem stationary_support_subset_closure (L : Kernel X X) (μ : Measure X)
    (hstat : L ∘ₘ μ = μ) (U : Set X) (hU : MeasurableSet U)
    (habs : ∀ x ∈ U, L x Uᶜ = 0) (N : ℕ)
    (hext : ∀ x : ↥(Uᶜ), ((SubtypeKernel.restrict L Uᶜ hU.compl) ^ N) x univ = 0) :
    μ.support ⊆ closure U := by
  apply Measure.support_subset_of_isClosed isClosed_closure
  change μ (closure U)ᶜ = 0
  exact measure_mono_null (compl_subset_compl.mpr subset_closure)
    (stationary_complement_mass_zero_of_extinction L μ hstat U hU habs N hext)

end Support

end LeanShared.StationaryTransientLocalization
