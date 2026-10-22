module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Support

/-! Joint regularity of a literal compact-cutoff family uses regularity
only on its actual support; no regularity of a totalized chart expression
outside its valid domain is required. -/
public noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace LeanShared.ParametricCutoffRegularity
variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffAt_smul (ρ : E → ℝ) {n : ℕ∞ω} (smoothρ : ContDiff ℝ n ρ)
    (h : P × E → F) (p : P) (x : E)
    (regular : x ∈ tsupport ρ → ContDiffAt ℝ n h (p,x)) :
    ContDiffAt ℝ n (fun q : P × E => ρ q.2 • h q) (p,x) := by
  by_cases inside : x ∈ tsupport ρ
  · exact (smoothρ.contDiffAt.comp (p,x) contDiffAt_snd).smul (regular inside)
  · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    have outside := (continuous_snd.continuousAt (x := (p,x))).eventually
      ((isClosed_tsupport ρ).isOpen_compl.mem_nhds inside)
    filter_upwards [outside] with q hq
    rw [image_eq_zero_of_notMem_tsupport hq, zero_smul]

theorem contDiffOn_smul (ρ : E → ℝ) {n : ℕ∞ω} (smoothρ : ContDiff ℝ n ρ)
    (h : P × E → F) {O : Set P} {U : Set (P × E)} (openU : IsOpen U)
    (regular : ContDiffOn ℝ n h U) (valid : O ×ˢ tsupport ρ ⊆ U) :
    ContDiffOn ℝ n (fun q : P × E => ρ q.2 • h q) (O ×ˢ univ) := by
  intro q hq
  exact (contDiffAt_smul ρ smoothρ h q.1 q.2 (fun hx =>
    (regular q (valid ⟨hq.1,hx⟩)).contDiffAt (openU.mem_nhds (valid ⟨hq.1,hx⟩)))).contDiffWithinAt

theorem contDiffOn_affine_extension (A : E →L[ℝ] F) (b : F) (ρ : E → ℝ)
    {n : ℕ∞ω} (smoothρ : ContDiff ℝ n ρ)
    (h : P × E → F) {O : Set P} {U : Set (P × E)} (openU : IsOpen U)
    (regular : ContDiffOn ℝ n h U) (valid : O ×ˢ tsupport ρ ⊆ U) :
    ContDiffOn ℝ n
      (fun q : P × E => A q.2+b+ρ q.2 • (h q-(A q.2+b))) (O ×ˢ univ) := by
  have affine : ContDiff ℝ n (fun q : P × E => A q.2+b) :=
    (A.contDiff.comp contDiff_snd).add contDiff_const
  exact affine.contDiffOn.add (contDiffOn_smul ρ smoothρ _ openU
    (regular.sub affine.contDiffOn) valid)

end LeanShared.ParametricCutoffRegularity
