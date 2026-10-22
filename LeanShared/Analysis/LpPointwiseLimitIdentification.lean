module
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! A completed L1 limit agrees with the pointwise limit of its actual
representatives. This closes the physical representation by density. -/
public section
open MeasureTheory Filter
open scoped Topology
namespace LeanShared.LpPointwiseLimitIdentification
variable {X : Type*} [MeasurableSpace X]

theorem identify (μ : Measure X) (z : ℕ→Lp ℂ 1 μ) (limit : Lp ℂ 1 μ)
    (f : ℕ→X→ℂ) (g : X→ℂ) (converges : Tendsto z atTop (𝓝 limit))
    (represents : ∀ n,z n=ᵐ[μ] f n)
    (pointwise : ∀ x,Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    limit=ᵐ[μ] g := by
  obtain ⟨subsequence,strict,aeLimit⟩ :=
    (tendstoInMeasure_of_tendsto_Lp converges).exists_seq_tendsto_ae
  have allRepresent : ∀ᵐ x ∂μ,∀ n,z n x=f n x := ae_all_iff.mpr represents
  filter_upwards [aeLimit,allRepresent] with x hx hr
  have same : Tendsto (fun n => f (subsequence n) x) atTop (𝓝 (limit x)) := by
    simpa only [hr] using hx
  exact tendsto_nhds_unique same ((pointwise x).comp strict.tendsto_atTop)

end LeanShared.LpPointwiseLimitIdentification
