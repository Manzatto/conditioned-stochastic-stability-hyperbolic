module
public import LeanShared.Analysis.RieszComplementResolvent

/-! Exact nonzero spectral exclusion after removing an invariant scalar
Riesz projection, including continuous and residual spectrum. -/
public section
open Set Metric
namespace LeanShared.RieszComplementSpectrum
open RieszContourIdempotent
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem inclusion (T : A) (c lam : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (res : sphere c R ⊆ resolventSet ℂ T) (inside : lam ∈ ball c R)
    (idempotent : projector T c R*projector T c R=projector T c R)
    (right : T*projector T c R=lam•projector T c R)
    (left : projector T c R*T=lam•projector T c R)
    (z : ℂ) (hz : z ∈ spectrum ℂ (T-lam•projector T c R)) :
    z=0 ∨ (z ∈ spectrum ℂ T ∧ R ≤ dist z c) := by
  by_cases nonzero : z=0
  · exact Or.inl nonzero
  right
  constructor
  · by_contra notSpec
    have resT : z ∈ resolventSet ℂ T := by
      by_contra hn
      exact notSpec hn
    exact hz (ComplementaryResolvent.mem_resolvent T (projector T c R) lam z
      idempotent right left nonzero resT)
  · apply le_of_not_gt
    intro interior
    exact hz (RieszComplementResolvent.interior T c lam R hR res inside
      idempotent right left z interior nonzero)
end LeanShared.RieszComplementSpectrum
