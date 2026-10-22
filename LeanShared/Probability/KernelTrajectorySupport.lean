module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-! A measurable transition relation passes to any joint law represented by
a measure/kernel composition product. No choice of noise parameters is needed. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter

namespace LeanShared.KernelTrajectorySupport

variable {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]

/-- Kernel support gives an almost-sure relation for actual successive
observations whenever their joint law is the corresponding composition product. -/
theorem ae_relation_of_joint_law (μ : Measure Ω) (κ : Kernel A B)
    (a : Ω → A) (b : Ω → B) (ha : Measurable a) (hb : Measurable b)
    (hjoint : μ.map (fun ω => (a ω, b ω)) = μ.map a ⊗ₘ κ)
    (R : A × B → Prop) (hR : MeasurableSet {p | R p})
    (hsupport : ∀ u, ∀ᵐ v ∂κ u, R (u, v)) : ∀ᵐ ω ∂μ, R (a ω, b ω) := by
  have hprod : ∀ᵐ p ∂μ.map a ⊗ₘ κ, R p :=
    Measure.ae_compProd_of_ae_ae hR (ae_of_all _ hsupport)
  rw [← hjoint] at hprod
  exact ae_of_ae_map (ha.prodMk hb).aemeasurable hprod

end LeanShared.KernelTrajectorySupport
