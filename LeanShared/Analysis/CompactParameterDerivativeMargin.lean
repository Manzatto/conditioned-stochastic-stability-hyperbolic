module
public import LeanShared.Analysis.PartialDerivativeContinuity
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Topology.Compactness.Compact

/-! A strict global derivative margin on a compact legal parameter set
persists on one open parameter neighborhood when the actual maps have
one fixed compact affine exterior. -/
public noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace LeanShared.CompactParameterDerivativeMargin
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_window (K : Set P) (compactK : IsCompact K)
    (A : E →L[ℝ] F) (b : F) (h : P × E → F) (S : Set E) (compactS : IsCompact S)
    (O₀ : Set P) (openO₀ : IsOpen O₀) (contains : K ⊆ O₀)
    (joint : ContDiffOn ℝ 1 h (O₀ ×ˢ univ))
    (exterior : ∀ p ∈ O₀, ∀ x, x ∉ S → h (p,x) = A x+b)
    (δ : ℝ) (positiveδ : 0 < δ)
    (margin : ∀ p ∈ K, ∀ x, ‖fderiv ℝ (fun z => h (p,z)) x-A‖ < δ) :
    ∃ O : Set P, IsOpen O ∧ K ⊆ O ∧ O ⊆ O₀ ∧
      ∀ p ∈ O, ∀ x, ‖fderiv ℝ (fun z => h (p,z)) x-A‖ < δ := by
  let D : P × E → ℝ := fun q => ‖fderiv ℝ (fun z => h (q.1,z)) q.2-A‖
  have continuousD : ContinuousOn D (O₀ ×ˢ univ) :=
    ((PartialDerivativeContinuity.continuousOn_partial (openO₀.prod isOpen_univ) joint).sub continuousOn_const).norm
  let U := (O₀ ×ˢ univ) ∩ D ⁻¹' Iio δ
  have openU : IsOpen U := continuousD.isOpen_inter_preimage (openO₀.prod isOpen_univ) isOpen_Iio
  have inside : K ×ˢ S ⊆ U := by
    rintro ⟨p,x⟩ ⟨hp,_hx⟩
    exact ⟨⟨contains hp,mem_univ _⟩,margin p hp x⟩
  obtain ⟨O,W,openO,_openW,containsK,containsS,tube⟩ :=
    generalized_tube_lemma compactK compactS openU inside
  refine ⟨O ∩ O₀,openO.inter openO₀,fun p hp => ⟨containsK hp,contains hp⟩,
    inter_subset_right,?_⟩
  intro p hp x
  by_cases member : x ∈ S
  · have memberU : (p,x) ∈ U := tube ⟨hp.1,containsS member⟩
    change (p ∈ O₀ ∧ x ∈ univ) ∧ D (p,x) < δ at memberU
    change D (p,x) < δ
    exact memberU.2
  · have near : (fun z => h (p,z)) =ᶠ[𝓝 x] (fun z => A z+b) := by
      filter_upwards [compactS.isClosed.isOpen_compl.mem_nhds member] with z hz
      exact exterior p hp.2 z hz
    rw [near.fderiv_eq, (A.hasFDerivAt.add_const b).fderiv, sub_self, norm_zero]
    exact positiveδ

end LeanShared.CompactParameterDerivativeMargin
