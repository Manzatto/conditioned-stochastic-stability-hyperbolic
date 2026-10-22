module
public import LeanShared.Analysis.ParametricCutoffRegularity
public import Mathlib.Topology.Compactness.Compact

/-! Actual joint C1 regularity on a compact parameter set times the cutoff
support yields one open parameter neighborhood and a globally C1 cutoff
family. The totalized chart expression may be arbitrary off its valid set. -/
public noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace LeanShared.CompactParameterCutoffRegularity
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_window (K : Set P) (compactK : IsCompact K)
    (A : E →L[ℝ] F) (b : F) (ρ : E → ℝ) (smoothρ : ContDiff ℝ 1 ρ)
    (compactρ : HasCompactSupport ρ) (h : P × E → F)
    (regular : ∀ p ∈ K, ∀ x ∈ tsupport ρ, ContDiffAt ℝ 1 h (p,x)) :
    ∃ O : Set P, IsOpen O ∧ K ⊆ O ∧ ContDiffOn ℝ 1
      (fun q : P × E => A q.2+b+ρ q.2 • (h q-(A q.2+b))) (O ×ˢ univ) := by
  let U : Set (P × E) := {q | ContDiffAt ℝ 1 h q}
  have openU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro q hq
    change ContDiffAt ℝ 1 h q at hq
    exact hq.eventually (by norm_num)
  have inside : K ×ˢ tsupport ρ ⊆ U := by
    rintro ⟨p,x⟩ ⟨hp,hx⟩
    exact regular p hp x hx
  obtain ⟨O,W,openO,openW,containsK,containsSupport,tube⟩ :=
    generalized_tube_lemma compactK compactρ openU inside
  refine ⟨O,openO,containsK,?_⟩
  exact ParametricCutoffRegularity.contDiffOn_affine_extension A b ρ smoothρ h openU
    (fun q hq => by
      change ContDiffAt ℝ 1 h q at hq
      exact hq.contDiffWithinAt) (fun q hq => tube ⟨hq.1,containsSupport hq.2⟩)

end LeanShared.CompactParameterCutoffRegularity
