module
public import LeanShared.Analysis.SchwartzConvolutionEvaluation
public import LeanShared.Analysis.LpPointwiseLimitIdentification
public import Mathlib.Topology.Sequences

/-! A completed physical block retains its literal convolution formula.
The formula is proved from dense smooth inputs, bounded C0 realization and
the constructed convolution evaluation, rather than imposed on the completion. -/
public noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap BoundedContinuousFunction Topology
namespace LeanShared.CompletedPhysicalConvolutionIdentity
variable {E R Core : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup R] [NormedSpace ℂ R]

theorem represents (μ ν : Measure E) [μ.IsAddHaarMeasure]
    (physical : R→L[ℂ](E→ᵇℂ)) (realize : R→L[ℂ]Lp ℂ 1 ν)
    (core : Core→R) (dense : DenseRange core) (kernel : 𝓢(E,ℂ)) (weight : ℂ)
    (coreRepresents : ∀ c,realize (core c)=ᵐ[ν]
      (fun x => weight*(∫ y,kernel (x-y)*physical (core c) y ∂μ))) (r : R) :
    realize r=ᵐ[ν](fun x => weight*(∫ y,kernel (x-y)*physical r y ∂μ)) := by
  obtain ⟨sequence,members,converges⟩ := mem_closure_iff_seq_limit.mp (dense r)
  choose inputs inputEq using members
  have approximates : Tendsto (fun n => core (inputs n)) atTop (𝓝 r) := by
    simpa only [inputEq] using converges
  apply LpPointwiseLimitIdentification.identify ν
    (fun n => realize (core (inputs n))) (realize r)
    (fun n x => weight*(∫ y,kernel (x-y)*physical (core (inputs n)) y ∂μ))
    (fun x => weight*(∫ y,kernel (x-y)*physical r y ∂μ))
    (realize.continuous.continuousAt.tendsto.comp approximates)
    (fun n => coreRepresents (inputs n))
  intro x
  have continuous : Continuous (fun v : R =>
      weight*SchwartzConvolutionEvaluation.evaluation μ kernel x (physical v)) :=
    continuous_const.mul ((SchwartzConvolutionEvaluation.evaluation μ kernel x).continuous.comp physical.continuous)
  simpa only [SchwartzConvolutionEvaluation.evaluation_apply,Function.comp_def] using
    continuous.continuousAt.tendsto.comp approximates

end LeanShared.CompletedPhysicalConvolutionIdentity
