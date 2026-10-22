module

public import LeanShared.Geometry.ChartPairTransfer
public import LeanShared.Geometry.IntrinsicWordInverseDifferential
public import LeanShared.Analysis.ContinuousIntrinsicPrincipalDensity
public import LeanShared.Analysis.ActualWordChronology
public import LeanShared.Analysis.LocalInverseWord

/-! Actual endpoint-chart maps for finite manifold words. The backward map
is the true inverse word with reversed time order. It is a local inverse
only on its genuine chart domain, rather than an assumed global Euclidean
conjugacy. The derivative inverse law follows on that open domain. -/

@[expose] public noncomputable section
open Set Filter
open scoped Topology
namespace LeanShared.ActualChartWordFields
variable {E M Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M]
  (out inp : OpenPartialHomeomorph M E) (F : Ω → M ≃ₜ M)

/-- Literal map in the actual localized transfer row. -/
def forward (word : List Ω) (y : E) : E :=
  inp (ActualFiniteRegularWord.orbit (fun a => F a) word (out.symm y))

/-- Literal backward map, with the inverse of the chronological word. -/
def backward (word : List Ω) (y : E) : E :=
  out ((IntrinsicWordDifferential.wordHomeomorph F word).symm (inp.symm y))

def domain (word : List Ω) : Set E :=
  out.target ∩ (fun y => ActualFiniteRegularWord.orbit (fun a => F a) word (out.symm y)) ⁻¹' inp.source

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem word_apply (word : List Ω) (x : M) :
    IntrinsicWordDifferential.wordHomeomorph F word x =
      ActualFiniteRegularWord.orbit (fun a => F a) word x :=
  (IntrinsicWordDifferential.wordHomeomorph_apply F word x).trans
    (ContinuousIntrinsicPrincipalDensity.orbit_eq (fun a => F a) word x)

omit [NormedSpace ℝ E] in
theorem domain_open (word : List Ω) : IsOpen (domain out inp F word) := by
  have hc : Continuous (ActualFiniteRegularWord.orbit (fun a => F a) word) := by
    convert (IntrinsicWordDifferential.wordHomeomorph F word).continuous using 1
    funext x
    exact (word_apply F word x).symm
  exact (hc.comp_continuousOn out.symm.continuousOn).isOpen_inter_preimage
    out.open_target inp.open_source

omit [NormedSpace ℝ E] in
theorem backward_forward (word : List Ω) {y : E} (hy : y ∈ domain out inp F word) :
    backward out inp F word (forward out inp F word y) = y := by
  change out ((IntrinsicWordDifferential.wordHomeomorph F word).symm
    (inp.symm (inp (ActualFiniteRegularWord.orbit (fun a => F a) word (out.symm y))))) = y
  rw [inp.left_inv hy.2]
  change out ((IntrinsicWordDifferential.wordHomeomorph F word).symm
    (ActualFiniteRegularWord.orbit (fun a => F a) word (out.symm y))) = y
  rw [← word_apply F word (out.symm y)]
  rw [(IntrinsicWordDifferential.wordHomeomorph F word).symm_apply_apply]
  exact out.right_inv hy.1

theorem inverse_fderiv_comp (word : List Ω) {y : E}
    (hy : y ∈ domain out inp F word)
    (hf : DifferentiableAt ℝ (forward out inp F word) y)
    (hb : DifferentiableAt ℝ (backward out inp F word) (forward out inp F word y)) :
    (fderiv ℝ (backward out inp F word) (forward out inp F word y)).comp
      (fderiv ℝ (forward out inp F word) y) = ContinuousLinearMap.id ℝ E := by
  apply LocalInverseWord.local_inverse_fderiv_comp _ _ _ hf hb
  filter_upwards [(domain_open out inp F word).mem_nhds hy] with z hz
  exact backward_forward out inp F word hz

theorem forward_derivative_injective (word : List Ω) {y : E}
    (hy : y ∈ domain out inp F word)
    (hf : DifferentiableAt ℝ (forward out inp F word) y)
    (hb : DifferentiableAt ℝ (backward out inp F word) (forward out inp F word y)) :
    Function.Injective (fderiv ℝ (forward out inp F word) y) := by
  apply FiniteDerivativeWord.fderiv_injective_of_local_inverse _ _ _ hf hb
  filter_upwards [(domain_open out inp F word).mem_nhds hy] with z hz
  exact backward_forward out inp F word hz

end LeanShared.ActualChartWordFields
