module
public import LeanShared.Analysis.OpenFiberMass
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Measure.Prod

/-! Joint volume domination for a map preserving the state coordinate implies
volume domination at every state. Fubini first gives almost-everywhere bounds;
actual continuity and full-support state volume remove the exceptional states. -/
public noncomputable section
namespace LeanShared.ParametricVolumeDomination
open MeasureTheory Set
open scoped ENNReal

theorem ae_fiber_bound
    {X A Y : Type*} [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace Y]
    (μ : Measure X) (ρ : Measure A) (σ : Measure Y)
    [SigmaFinite μ] [SFinite ρ] [SFinite σ]
    {f : X × A → Y} (measurableF : Measurable f) (C : ℝ≥0∞)
    (joint : (μ.prod ρ).map (fun z => (z.1, f z)) ≤ C • μ.prod σ)
    {B : Set Y} (measurableB : MeasurableSet B) :
    ∀ᵐ x ∂μ, ρ {a | f (x, a) ∈ B} ≤ C * σ B := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite
    (measurable_measure_prodMk_left (measurableF measurableB))
  intro U measurableU _finiteU
  have identity : (∫⁻ x in U, ρ {a | f (x, a) ∈ B} ∂μ) =
      ((μ.prod ρ).map (fun z => (z.1, f z))) (U ×ˢ B) := by
    rw [Measure.map_apply (measurable_fst.prodMk measurableF) (measurableU.prod measurableB),
      Measure.prod_apply ((measurable_fst.prodMk measurableF) (measurableU.prod measurableB)),
      ← lintegral_indicator measurableU]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ U <;> simp [Set.preimage, hx]
  change (∫⁻ x in U, ρ {a | f (x, a) ∈ B} ∂μ) ≤ ∫⁻ _x in U, C * σ B ∂μ
  rw [identity]
  calc
    ((μ.prod ρ).map (fun z => (z.1, f z))) (U ×ˢ B) ≤
        (C • μ.prod σ) (U ×ˢ B) := joint _
    _ = ∫⁻ _x in U, C * σ B ∂μ := by
      simp only [Measure.smul_apply, Measure.prod_prod, smul_eq_mul,
        lintegral_const, Measure.restrict_apply_univ]
      ac_rfl

theorem fiber_bound_everywhere
    {X A Y : Type*} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace A] [BorelSpace A]
    [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology A]
    (μ : Measure X) (ρ : Measure A) (σ : Measure Y)
    [SigmaFinite μ] [μ.IsOpenPosMeasure] [ρ.Regular] [SFinite ρ] [SFinite σ]
    [σ.OuterRegular]
    {f : X × A → Y} (continuousF : Continuous f) (C : ℝ≥0∞) (finiteC : C ≠ ∞)
    (joint : (μ.prod ρ).map (fun z => (z.1, f z)) ≤ C • μ.prod σ) :
    ∀ x, ρ.map (fun a => f (x, a)) ≤ C • σ := by
  have openBound (B : Set Y) (openB : IsOpen B) (x : X) :
      ρ {a | f (x, a) ∈ B} ≤ C * σ B :=
    OpenFiberMass.lowerSemicontinuous_le_of_ae μ
      (OpenFiberMass.lowerSemicontinuous_pushforward_open ρ continuousF openB)
      (ae_fiber_bound μ ρ σ continuousF.measurable C joint openB.measurableSet) x
  intro x
  have : (C • σ).OuterRegular := Measure.OuterRegular.smul σ finiteC
  apply Measure.le_iff.mpr
  intro B _measurableB
  rw [B.measure_eq_iInf_isOpen (C • σ)]
  apply le_iInf
  intro U
  apply le_iInf
  intro contained
  apply le_iInf
  intro openU
  calc
    (ρ.map (fun a => f (x, a))) B ≤ (ρ.map (fun a => f (x, a))) U := measure_mono contained
    _ = ρ {a | f (x, a) ∈ U} :=
      Measure.map_apply (continuousF.comp (continuous_const.prodMk continuous_id)).measurable
        openU.measurableSet
    _ ≤ C * σ U := openBound U openU x
    _ = (C • σ) U := rfl

end LeanShared.ParametricVolumeDomination
