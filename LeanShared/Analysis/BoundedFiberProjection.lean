module
public import Mathlib.MeasureTheory.Measure.Prod

/-! A dominated joint measure supported in a finite-volume cylinder has a
dominated target marginal. This is the excess-control Fubini step in local
submersion volume bounds. -/
public noncomputable section
namespace LeanShared.BoundedFiberProjection
open MeasureTheory Set
open scoped ENNReal

theorem map_snd_le
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (σ : Measure F) [SFinite μ] [SFinite σ]
    (ν : Measure (E × F)) (C : ℝ≥0∞) (B : Set E)
    (dominated : ν ≤ C • μ.prod σ)
    (supported : ∀ᵐ z ∂ν, z.1 ∈ B) :
    ν.map Prod.snd ≤ (C * μ B) • σ := by
  have restricted : ν.restrict (B ×ˢ (univ : Set F)) = ν :=
    Measure.restrict_eq_self_of_ae_mem
      (supported.mono (fun _ h => ⟨h, mem_univ _⟩))
  have bound := Measure.restrict_mono_measure dominated (B ×ˢ (univ : Set F))
  rw [restricted, Measure.restrict_smul,
    ← Measure.restrict_prod_eq_prod_univ] at bound
  have mapped := Measure.map_mono bound measurable_snd
  simpa only [Measure.map_smul C measurable_snd.aemeasurable,
    Measure.map_snd_prod, Measure.restrict_apply_univ, smul_smul] using mapped

end LeanShared.BoundedFiberProjection
