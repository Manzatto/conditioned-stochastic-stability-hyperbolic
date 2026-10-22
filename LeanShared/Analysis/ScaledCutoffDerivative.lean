module
public import LeanShared.Analysis.CutoffSmallDerivative
public import LeanShared.Analysis.CompactSmoothCutoff

/-! A single unit bump gives cutoffs at every positive radius. Its actual
derivative grows like the reciprocal radius. The cutoff residual estimate
keeps the derivative tolerance independent of that radius and only asks
that the displacement of the centre be proportional to the radius. -/
@[expose] public noncomputable section
open Set Filter Function Metric
open scoped NNReal ContDiff Topology
namespace LeanShared.ScaledCutoffDerivative
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def scaled (ψ : E → ℝ) (R : ℝ) (x : E) : ℝ := ψ (R⁻¹ • x)

theorem exists_scaled_cutoffs [FiniteDimensional ℝ E] :
    ∃ L : ℝ, 0 ≤ L ∧ ∃ ρ : ℝ → E → ℝ, ∀ R : ℝ, 0 < R →
      ContDiff ℝ ∞ (ρ R) ∧ HasCompactSupport (ρ R) ∧
      tsupport (ρ R) ⊆ closedBall 0 R ∧
      (∀ x, 0 ≤ ρ R x ∧ ρ R x ≤ 1) ∧
      (∀ x ∈ closedBall 0 (R/2), ρ R x = 1) ∧
      ∀ x, ‖fderiv ℝ (ρ R) x‖ ≤ L/R := by
  obtain ⟨ψ, smoothψ, compactψ, supportψ, rangeψ, oneψ⟩ :=
    CompactSmoothCutoff.exists_cutoff (isCompact_closedBall (0 : E) (1/2 : ℝ))
      isOpen_ball (closedBall_subset_ball (by norm_num : (1/2 : ℝ) < 1))
  obtain ⟨L, lipψ⟩ := CompactC1Lipschitz.exists_lipschitz ψ
    (smoothψ.of_le (by simp)) compactψ
  refine ⟨L, L.coe_nonneg, scaled ψ, ?_⟩
  intro R positiveR
  have continuousScale : Continuous (fun x : E => R⁻¹ • x) := continuous_const.smul continuous_id
  have supportScale : tsupport (scaled ψ R) ⊆
      (fun x : E => R⁻¹ • x) ⁻¹' tsupport ψ := by
    apply closure_minimal
    · intro x hx
      exact subset_closure hx
    · exact (isClosed_tsupport ψ).preimage continuousScale
  have ballScale : tsupport (scaled ψ R) ⊆ closedBall 0 R := by
    intro x hx
    have bound : ‖R⁻¹ • x‖ ≤ 1 := (mem_ball_zero_iff.mp (supportψ (supportScale hx))).le
    have identity : R • (R⁻¹ • x) = x := by simp [smul_smul, ne_of_gt positiveR]
    rw [mem_closedBall_zero_iff, ← identity, norm_smul, Real.norm_eq_abs, abs_of_pos positiveR]
    nlinarith
  have compactScale : HasCompactSupport (scaled ψ R) :=
    (isCompact_closedBall (0 : E) R).of_isClosed_subset (isClosed_tsupport _) ballScale
  refine ⟨smoothψ.comp (contDiff_const.smul contDiff_id), compactScale, ballScale,
    fun x => rangeψ _, ?_, ?_⟩
  · intro x hx
    apply oneψ
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr positiveR)]
    have bound : ‖x‖ ≤ R/2 := mem_closedBall_zero_iff.mp hx
    calc
      R⁻¹ * ‖x‖ ≤ R⁻¹ * (R/2) := mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr positiveR.le)
      _ = 1/2 := by field_simp
  · intro x
    have lip : LipschitzWith (L*‖R⁻¹‖₊) (scaled ψ R) :=
      lipψ.comp (lipschitzWith_smul R⁻¹)
    have bound := norm_fderiv_le_of_lipschitz ℝ lip (x₀ := x)
    simpa only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr positiveR), div_eq_mul_inv] using bound

/-- Weighted product estimate: a residual of size `a*R` and derivative
size `d` gives global derivative size `d+L*a`, independent of `R`. -/
theorem derivative_bound (ρ : E → ℝ) (smoothρ : ContDiff ℝ 1 ρ)
    {R L a d : ℝ} (positiveR : 0 < R) (nonnegativeL : 0 ≤ L)
    (nonnegativeA : 0 ≤ a) (nonnegativeD : 0 ≤ d)
    (rangeρ : ∀ x, ‖ρ x‖ ≤ 1) (derivativeρ : ∀ x, ‖fderiv ℝ ρ x‖ ≤ L/R)
    {U : Set E} (openU : IsOpen U) (inside : tsupport ρ ⊆ U)
    (g : E → F) (regular : ContDiffOn ℝ 1 g U)
    (value : ∀ x ∈ tsupport ρ, ‖g x‖ ≤ a*R)
    (derivative : ∀ x ∈ tsupport ρ, ‖fderiv ℝ g x‖ ≤ d) :
    ContDiff ℝ 1 (fun x => ρ x • g x) ∧
      ∀ x, ‖fderiv ℝ (fun y => ρ y • g y) x‖ ≤ d+L*a := by
  refine ⟨CutoffSmallDerivative.contDiff_cutoff ρ smoothρ openU inside g regular, ?_⟩
  intro x
  by_cases hx : x ∈ tsupport ρ
  · have hdρ := (smoothρ.differentiable (by norm_num) x).hasFDerivAt
    have hdg := (((regular x (inside hx)).contDiffAt
      (openU.mem_nhds (inside hx))).differentiableAt (by norm_num)).hasFDerivAt
    change ‖fderiv ℝ (ρ • g) x‖ ≤ d+L*a
    rw [(hdρ.smul hdg).fderiv]
    calc
      _ ≤ ‖ρ x • fderiv ℝ g x‖+‖(fderiv ℝ ρ x).smulRight (g x)‖ := norm_add_le _ _
      _ = ‖ρ x‖*‖fderiv ℝ g x‖+‖fderiv ℝ ρ x‖*‖g x‖ := by
        rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply]
      _ ≤ 1*d+(L/R)*(a*R) := add_le_add
        (mul_le_mul (rangeρ x) (derivative x hx) (norm_nonneg _) (by norm_num))
        (mul_le_mul (derivativeρ x) (value x hx) (norm_nonneg _) (div_nonneg nonnegativeL positiveR.le))
      _ = d+L*a := by field_simp
  · rw [fderiv_of_notMem_tsupport ℝ
      (fun h => hx (tsupport_smul_subset_left ρ g h)), norm_zero]
    exact add_nonneg nonnegativeD (mul_nonneg nonnegativeL nonnegativeA)

/-- The actual mean value theorem supplies the radius-weighted residual
bound from the displacement at the centre and the actual derivative. -/
theorem norm_le_of_center (g : E → F) {R a d : ℝ} (positiveR : 0 < R)
    (nonnegativeD : 0 ≤ d) {U : Set E} (openU : IsOpen U)
    (inside : closedBall 0 R ⊆ U) (regular : ContDiffOn ℝ 1 g U)
    (center : ‖g 0‖ ≤ a*R)
    (derivative : ∀ x ∈ closedBall 0 R, ‖fderiv ℝ g x‖ ≤ d) :
    ∀ x ∈ closedBall 0 R, ‖g x‖ ≤ (a+d)*R := by
  intro x hx
  have differentiable (y : E) (hy : y ∈ closedBall 0 R) : DifferentiableAt ℝ g y :=
    ((regular y (inside hy)).contDiffAt (openU.mem_nhds (inside hy))).differentiableAt (by norm_num)
  have difference := Convex.norm_image_sub_le_of_norm_fderiv_le differentiable derivative
    (convex_closedBall (0 : E) R) (mem_closedBall_self positiveR.le) hx
  simp only [sub_zero] at difference
  have bound : ‖x‖ ≤ R := mem_closedBall_zero_iff.mp hx
  calc
    ‖g x‖ ≤ ‖g x-g 0‖+‖g 0‖ := norm_le_norm_sub_add _ _
    _ ≤ d*R+a*R := add_le_add
      (difference.trans (mul_le_mul_of_nonneg_left bound nonnegativeD)) center
    _ = (a+d)*R := by ring

/-- A single positive derivative budget is chosen before the radius.
Only the displacement at zero is subsequently scaled by that radius. -/
theorem exists_uniform_budget [FiniteDimensional ℝ E] {κ : ℝ} (positiveκ : 0 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ ρ : ℝ → E → ℝ, ∀ R : ℝ, 0 < R →
      ContDiff ℝ ∞ (ρ R) ∧ HasCompactSupport (ρ R) ∧
      tsupport (ρ R) ⊆ closedBall 0 R ∧
      (∀ x ∈ closedBall 0 (R/2), ρ R x = 1) ∧
      ∀ U : Set E, IsOpen U → closedBall 0 R ⊆ U →
        ∀ g : E → F, ContDiffOn ℝ 1 g U → ‖g 0‖ ≤ δ*R →
          (∀ x ∈ closedBall 0 R, ‖fderiv ℝ g x‖ ≤ δ) →
          ContDiff ℝ 1 (fun x => ρ R x • g x) ∧
            ∃ k : ℝ≥0, (k : ℝ) < κ ∧
              ∀ x, ‖fderiv ℝ (fun y => ρ R y • g y) x‖ ≤ k := by
  obtain ⟨L, nonnegativeL, ρ, cutoffs⟩ := exists_scaled_cutoffs (E := E)
  let δ : ℝ := κ/(4*(L+1))
  have positiveδ : 0 < δ := div_pos positiveκ (by positivity)
  have scale : 4*(L+1)*δ = κ := by dsimp only [δ]; field_simp
  have small : (1+2*L)*δ < κ := by rw [← scale]; nlinarith
  refine ⟨δ, positiveδ, ρ, ?_⟩
  intro R positiveR
  obtain ⟨smoothρ, compactρ, supportρ, rangeρ, oneρ, derivativeρ⟩ := cutoffs R positiveR
  refine ⟨smoothρ, compactρ, supportρ, oneρ, ?_⟩
  intro U openU inside g regular center derivative
  have value := norm_le_of_center g positiveR positiveδ.le openU inside regular center derivative
  obtain ⟨cutoffC1, bound⟩ := derivative_bound (ρ R) (smoothρ.of_le (by simp))
    positiveR nonnegativeL (add_nonneg positiveδ.le positiveδ.le) positiveδ.le
    (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (rangeρ x).1]; exact (rangeρ x).2)
    derivativeρ openU (supportρ.trans inside) g regular
    (fun x hx => value x (supportρ hx)) (fun x hx => derivative x (supportρ hx))
  refine ⟨cutoffC1, ⟨(1+2*L)*δ, by positivity⟩, small, ?_⟩
  intro x
  change ‖fderiv ℝ (fun y => ρ R y • g y) x‖ ≤ (1+2*L)*δ
  convert bound x using 1; ring

end LeanShared.ScaledCutoffDerivative
