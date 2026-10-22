module
public import LeanShared.Analysis.CompactSmoothCutoff
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! A genuine Schwartz cutoff equal to one on a compact set, supported
inside any prescribed open neighborhood. -/
public noncomputable section
open Set
open scoped SchwartzMap ContDiff
namespace LeanShared.CompactSchwartzCutoff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_cutoff {K U : Set E} (compact : IsCompact K)
    (openU : IsOpen U) (inside : K ⊆ U) :
    ∃ χ : 𝓢(E,ℂ), HasCompactSupport χ ∧ tsupport χ ⊆ U ∧ ∀ x ∈ K, χ x = 1 := by
  obtain ⟨ψ,smooth,supported,support,_,one⟩ :=
    CompactSmoothCutoff.exists_cutoff compact openU inside
  let f : E → ℂ := fun x => (ψ x : ℂ)
  have compactF : HasCompactSupport f := supported.comp_left Complex.ofReal_zero
  let χ : 𝓢(E,ℂ) := compactF.toSchwartzMap (Complex.ofRealCLM.contDiff.comp smooth)
  refine ⟨χ,compactF,?_,?_⟩
  · apply subset_trans _ support
    apply closure_mono
    intro x hx
    change (ψ x : ℂ) ≠ 0 at hx
    exact fun hz => hx (by rw [hz]; rfl)
  · intro x hx
    change (ψ x : ℂ) = 1
    rw [one hx]
    rfl
end LeanShared.CompactSchwartzCutoff
