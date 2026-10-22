module
public import LeanShared.Analysis.ParametricVolumeDomination

/-! State-volume estimates on compact chart patches imply every-state fiber
estimates on their interiors. No almost-everywhere exceptional states remain. -/
public noncomputable section
namespace LeanShared.ParametricVolumeDomination
open MeasureTheory Set
open scoped ENNReal

theorem lowerSemicontinuous_le_on_interior
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [μ.IsOpenPosMeasure] (K : Set X)
    {f : X → ℝ≥0∞} (semicontinuous : LowerSemicontinuous f) {c : ℝ≥0∞}
    (bound : ∀ᵐ x ∂μ.restrict K, f x ≤ c) : ∀ x ∈ interior K, f x ≤ c := by
  have openBad : IsOpen {x | c < f x} := semicontinuous.isOpen_preimage c
  have zero : (μ.restrict K) {x | c < f x} = 0 := by
    simpa only [not_le] using ae_iff.mp bound
  rw [Measure.restrict_apply openBad.measurableSet] at zero
  have empty : {x | c < f x} ∩ interior K = ∅ :=
    (openBad.inter isOpen_interior).eq_empty_of_measure_zero
      (measure_mono_null (inter_subset_inter_right _ interior_subset) zero)
  intro x hx
  by_contra h
  have : x ∈ {y | c < f y} ∩ interior K := ⟨lt_of_not_ge h, hx⟩
  simp only [empty, mem_empty_iff_false] at this

theorem fiber_bound_on_interior
    {X A Y : Type*} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace A] [BorelSpace A]
    [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology A]
    (μ : Measure X) (ρ : Measure A) (σ : Measure Y)
    [SigmaFinite μ] [μ.IsOpenPosMeasure] [ρ.Regular] [SFinite ρ] [SFinite σ]
    [σ.OuterRegular] (K : Set X)
    {f : X × A → Y} (continuousF : Continuous f) (C : ℝ≥0∞) (finiteC : C ≠ ∞)
    (joint : ((μ.restrict K).prod ρ).map (fun z => (z.1, f z)) ≤
      C • (μ.restrict K).prod σ) :
    ∀ x ∈ interior K, ρ.map (fun a => f (x, a)) ≤ C • σ := by
  have openBound (B : Set Y) (openB : IsOpen B) (x : X) (hx : x ∈ interior K) :
      ρ {a | f (x, a) ∈ B} ≤ C * σ B :=
    lowerSemicontinuous_le_on_interior μ K
      (OpenFiberMass.lowerSemicontinuous_pushforward_open ρ continuousF openB)
      (ae_fiber_bound (μ.restrict K) ρ σ continuousF.measurable C joint openB.measurableSet) x hx
  intro x hx
  have : (C • σ).OuterRegular := Measure.OuterRegular.smul σ finiteC
  apply Measure.le_iff.mpr
  intro B _measurableB
  rw [B.measure_eq_iInf_isOpen (C • σ)]
  refine le_iInf fun U => le_iInf fun contained => le_iInf fun openU => ?_
  calc
    (ρ.map (fun a => f (x, a))) B ≤ (ρ.map (fun a => f (x, a))) U := measure_mono contained
    _ = ρ {a | f (x, a) ∈ U} :=
      Measure.map_apply (continuousF.comp (continuous_const.prodMk continuous_id)).measurable
        openU.measurableSet
    _ ≤ C * σ U := openBound U openU x hx
    _ = (C • σ) U := rfl

theorem restrict_joint_endpoint_bound
    {X A Y : Type*} [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace Y]
    (μ : Measure X) (ρ : Measure A) (σ : Measure Y)
    [SFinite μ] [SFinite ρ] [SFinite σ]
    (K : Set X) (measurableK : MeasurableSet K)
    {f : X × A → Y} (measurableF : Measurable f) (C : ℝ≥0∞)
    (joint : ((μ.restrict K).prod ρ).map (fun z => (z.1, f z)) ≤ C • μ.prod σ) :
    ((μ.restrict K).prod ρ).map (fun z => (z.1, f z)) ≤ C • (μ.restrict K).prod σ := by
  let endpoint := fun z : X × A => (z.1, f z)
  have endpointMeasurable : Measurable endpoint := measurable_fst.prodMk measurableF
  have supported : (((μ.restrict K).prod ρ).map endpoint).restrict (K ×ˢ univ) =
      ((μ.restrict K).prod ρ).map endpoint := by
    rw [Measure.restrict_map endpointMeasurable (measurableK.prod MeasurableSet.univ)]
    have preimage : endpoint ⁻¹' (K ×ˢ (univ : Set Y)) = K ×ˢ (univ : Set A) := by
      ext z
      simp only [endpoint, mem_preimage, mem_prod, mem_univ, and_true]
    rw [preimage, ← Measure.restrict_prod_eq_prod_univ,
      Measure.restrict_restrict measurableK, inter_self]
  have restricted := Measure.restrict_mono_measure joint (K ×ˢ univ)
  rw [supported, Measure.restrict_smul, ← Measure.restrict_prod_eq_prod_univ] at restricted
  exact restricted

end LeanShared.ParametricVolumeDomination
