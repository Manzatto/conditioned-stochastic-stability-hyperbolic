module
public import LeanShared.Geometry.SmallAffineFractionalPerturbation
public import LeanShared.Analysis.CutoffSmallDerivative

/-! A fixed actual compact cutoff produces a global two-sided C^r affine
extension from genuinely local residual regularity and C1 smallness. The
map agrees with the local residual where the cutoff is one and is exactly
affine outside its support. -/
@[expose] public noncomputable section
open Set Filter Function
open scoped NNReal ContDiff Manifold Topology
namespace LeanShared.CutoffAffineDiffeomorphism
open FractionalManifoldRegularity
universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [CompleteSpace E] in
theorem regular_cutoff (ρ : E → ℝ) (smoothρ : ContDiff ℝ ∞ ρ)
    {U : Set E} (openU : IsOpen U) (inside : tsupport ρ ⊆ U)
    {r : ℝ} (hr : 0 ≤ r) (g : E → F) (smooth : ContDiffOn ℝ (⌊r⌋₊ : ℕ) g U)
    (holder : r ≠ (⌊r⌋₊ : ℝ) → ∀ x ∈ U, JetAt ⌊r⌋₊ (r-(⌊r⌋₊ : ℝ)) g x) :
    Regular (E := E) (F := F) r (fun x => ρ x • g x) := by
  have outside (x : E) (hx : x ∉ tsupport ρ) :
      (fun _ : E => (0 : F)) =ᶠ[𝓝 x] (fun y => ρ y • g y) := by
    filter_upwards [(isClosed_tsupport ρ).isOpen_compl.mem_nhds hx] with y hy
    rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
  have globalSmooth : ContDiff ℝ (⌊r⌋₊ : ℕ) (fun x => ρ x • g x) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport ρ
    · exact (smoothρ.of_le (by simp)).contDiffAt.smul
        ((smooth x (inside hx)).contDiffAt (openU.mem_nhds (inside hx)))
    · exact (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq (outside x hx).symm
  refine ⟨hr, globalSmooth.contMDiff, ?_⟩
  intro unequal x
  have nonnegative : 0 ≤ r-(⌊r⌋₊ : ℝ) := sub_nonneg.mpr (Nat.floor_le hr)
  have subunit : r-(⌊r⌋₊ : ℝ) ≤ 1 := by linarith [Nat.lt_floor_add_one r]
  have jet : JetAt ⌊r⌋₊ (r-(⌊r⌋₊ : ℝ)) (fun y => ρ y • g y) x := by
    by_cases hx : x ∈ tsupport ρ
    · have scalarSmooth : ContDiff ℝ ∞ (fun y => ρ y • ContinuousLinearMap.id ℝ F) :=
        smoothρ.smul contDiff_const
      have scalarJet : JetAt ⌊r⌋₊ (r-(⌊r⌋₊ : ℝ))
          (fun y => ρ y • ContinuousLinearMap.id ℝ F) x :=
        JetAt.of_contDiff_succ subunit (scalarSmooth.of_le (by simp)).contDiffAt
      have result := JetAt.bilinear ⌊r⌋₊ nonnegative subunit
        (ContinuousLinearMap.apply ℝ F).flip scalarJet (holder unequal x (inside hx))
      exact result
    · exact (JetAt.of_contDiff_succ subunit (contDiffAt_const (c := (0 : F)))).congr (outside x hx)
  obtain ⟨W, openW, inW, C, hC, bound⟩ := jet.holder
  refine ⟨W, openW, ?_, ?_, C, hC, ?_⟩
  · simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq] using inW
  · simp only [chartDomain, extChartAt_model_space_eq_id, PartialEquiv.refl_source,
      Set.preimage_univ, Set.inter_univ]
    exact subset_univ W
  · have chart : chartMap (E := E) (F := F) (fun y => ρ y • g y) x =
        (fun y => ρ y • g y) := by simp [chartMap, chartAt_self_eq]
    simpa only [chart] using bound

omit [CompleteSpace E] in
theorem small_of_inflated (A : E ≃L[ℝ] F) (k : ℝ≥0)
    (small : (k : ℝ) < (‖A.symm.toContinuousLinearMap‖+1)⁻¹) :
    Subsingleton E ∨ k < ‖A.symm.toContinuousLinearMap‖₊⁻¹ := by
  rcases subsingleton_or_nontrivial E with trivial | nontrivial
  · exact Or.inl trivial
  · let : Nontrivial E := nontrivial
    have positive := A.norm_symm_pos
    have threshold : (‖A.symm.toContinuousLinearMap‖+1)⁻¹ ≤ ‖A.symm.toContinuousLinearMap‖⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le positive
        (show ‖A.symm.toContinuousLinearMap‖ ≤ ‖A.symm.toContinuousLinearMap‖+1 by linarith)
    apply Or.inr
    exact_mod_cast small.trans_le threshold

/-- The fixed cutoff itself determines a positive local tolerance.
No global invertibility or inverse regularity is supplied by the caller. -/
theorem exists_tolerance (A : E ≃L[ℝ] F) (b : F) (ρ : E → ℝ)
    (smoothρ : ContDiff ℝ ∞ ρ) (compactρ : HasCompactSupport ρ)
    {U : Set E} (openU : IsOpen U) (inside : tsupport ρ ⊆ U)
    {r : ℝ} (hr : 1 ≤ r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g : E → F, ContDiffOn ℝ (⌊r⌋₊ : ℕ) g U →
      (r ≠ (⌊r⌋₊ : ℝ) → ∀ x ∈ U, JetAt ⌊r⌋₊ (r-(⌊r⌋₊ : ℝ)) g x) →
      (∀ x ∈ tsupport ρ, ‖g x‖ ≤ δ ∧ ‖fderiv ℝ g x‖ ≤ δ) →
      ∃ H : E ≃ₜ F, (∀ x, H x = A x+b+ρ x • g x) ∧
        Regular (E := E) (F := F) r H ∧ Regular (E := F) (F := E) r H.symm ∧
        (∀ x, ρ x = 1 → H x = A x+b+g x) ∧
        ∀ x, x ∉ tsupport ρ → H x = A x+b := by
  have positive : 0 < (‖A.symm.toContinuousLinearMap‖+1)⁻¹ := by positivity
  obtain ⟨δ, positiveδ, controls⟩ := CutoffSmallDerivative.exists_tolerance (F := F)
    ρ (smoothρ.of_le (by simp)) compactρ openU inside positive
  refine ⟨δ, positiveδ, ?_⟩
  intro g smooth holder control
  have order : (1 : ℕ) ≤ ⌊r⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hr)
  obtain ⟨_cutoffC1, k, small, bound⟩ := controls g (smooth.of_le (by exact_mod_cast order)) control
  have cutoffRegular := regular_cutoff ρ smoothρ openU inside (zero_le_one.trans hr) g smooth holder
  obtain ⟨H, literal, forward, inverse⟩ := SmallAffinePerturbation.exists_regular_homeomorph
    A b hr (fun x => ρ x • g x) cutoffRegular k bound (small_of_inflated A k small)
  refine ⟨H, literal, forward, inverse, ?_, ?_⟩
  · intro x hx
    rw [literal x, hx, one_smul]
  · intro x hx
    rw [literal x, image_eq_zero_of_notMem_tsupport hx, zero_smul, add_zero]

end LeanShared.CutoffAffineDiffeomorphism
