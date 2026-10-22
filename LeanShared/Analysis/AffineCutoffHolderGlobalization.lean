module
public import LeanShared.Analysis.CompactOneHolderGlobalization

/-! Actual affine residuals have the same Holder derivative increments as
their original local maps. Their values are controlled by the centre and
the mean value theorem. A fixed cutoff therefore supplies one global
first-derivative Holder constant for the entire family. -/
public noncomputable section
open Set Filter Metric
open scoped ContDiff Topology NNReal
namespace LeanShared.AffineCutoffHolderGlobalization
variable {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_controls (ρ : E → ℝ) (smoothρ : ContDiff ℝ 2 ρ)
    (compactρ : HasCompactSupport ρ) {radius : ℝ} (positiveRadius : 0 < radius)
    {U : Set E} (openU : IsOpen U) (inside : closedBall 0 radius ⊆ U)
    (supportρ : tsupport ρ ⊆ interior (closedBall 0 radius))
    (h : P → E → F) (A : P → E →L[ℝ] F) (b : P → F)
    (regular : ∀ p, ContDiffOn ℝ 1 (h p) U)
    {α B D H : ℝ} (nonnegativeα : 0 ≤ α) (subunitα : α ≤ 1)
    (nonnegativeB : 0 ≤ B) (nonnegativeD : 0 ≤ D) (nonnegativeH : 0 ≤ H)
    (center : ∀ p, ‖h p 0-b p‖ ≤ B)
    (derivative : ∀ p x, x ∈ closedBall 0 radius → ‖fderiv ℝ (h p) x-A p‖ ≤ D)
    (holder : ∀ p x, x ∈ closedBall 0 radius → ∀ y, y ∈ closedBall 0 radius →
      ‖fderiv ℝ (h p) x-fderiv ℝ (h p) y‖ ≤ H*‖x-y‖^α) :
    ∃ L : ℝ≥0, ∃ C : ℝ, 0 ≤ C ∧ ∀ p,
      ContDiff ℝ 1 (fun x => ρ x • (h p x-(A p x+b p))) ∧
      HasCompactSupport (fun x => ρ x • (h p x-(A p x+b p))) ∧
      LipschitzWith L (fun x => ρ x • (h p x-(A p x+b p))) ∧
      (∀ x, ‖fderiv ℝ (fun y => ρ y • (h p y-(A p y+b p))) x‖ ≤ L) ∧
      ∀ x y,
        ‖fderiv ℝ (fun z => ρ z • (h p z-(A p z+b p))) x-
          fderiv ℝ (fun z => ρ z • (h p z-(A p z+b p))) y‖ ≤ C*‖x-y‖^α := by
  let g : P → E → F := fun p x => h p x-(A p x+b p)
  have regularG (p : P) : ContDiffOn ℝ 1 (g p) U :=
    (regular p).sub ((A p).contDiff.add contDiff_const).contDiffOn
  have actual (p : P) (x : E) (hx : x ∈ U) :
      fderiv ℝ (g p) x = fderiv ℝ (h p) x-A p := by
    have derivativeH := (((regular p x hx).contDiffAt (openU.mem_nhds hx)).differentiableAt
      (by norm_num)).hasFDerivAt
    exact (derivativeH.sub ((A p).hasFDerivAt.add_const (b p))).fderiv
  have derivativeG (p : P) (x : E) (hx : x ∈ closedBall 0 radius) :
      ‖fderiv ℝ (g p) x‖ ≤ D := by
    rw [actual p x (inside hx)]
    exact derivative p x hx
  have valueG (p : P) (x : E) (hx : x ∈ closedBall 0 radius) : ‖g p x‖ ≤ B+D*radius := by
    have differentiable (y : E) (hy : y ∈ closedBall 0 radius) : DifferentiableAt ℝ (g p) y :=
      (((regularG p y (inside hy)).contDiffAt
        (openU.mem_nhds (inside hy))).differentiableAt (by norm_num))
    have difference := Convex.norm_image_sub_le_of_norm_fderiv_le differentiable (derivativeG p)
      (convex_closedBall (0 : E) radius) (mem_closedBall_self positiveRadius.le) hx
    simp only [sub_zero] at difference
    have atCenter : ‖g p 0‖ ≤ B := by simpa only [g, map_zero, zero_add] using center p
    calc
      _ ≤ ‖g p x-g p 0‖+‖g p 0‖ := norm_le_norm_sub_add _ _
      _ ≤ D*radius+B := add_le_add
        (difference.trans (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) nonnegativeD)) atCenter
      _ = B+D*radius := add_comm _ _
  have holderG (p : P) (x : E) (hx : x ∈ closedBall 0 radius)
      (y : E) (hy : y ∈ closedBall 0 radius) :
      ‖fderiv ℝ (g p) x-fderiv ℝ (g p) y‖ ≤ H*‖x-y‖^α := by
    rw [actual p x (inside hx), actual p y (inside hy)]
    have cancel : (fderiv ℝ (h p) x-A p)-(fderiv ℝ (h p) y-A p) =
        fderiv ℝ (h p) x-fderiv ℝ (h p) y := by abel
    rw [cancel]
    exact holder p x hx y hy
  exact CompactOneHolderGlobalization.exists_controls ρ smoothρ compactρ
    (convex_closedBall (0 : E) radius) openU inside supportρ g regularG
    nonnegativeα subunitα (add_nonneg nonnegativeB (mul_nonneg nonnegativeD positiveRadius.le))
    nonnegativeD nonnegativeH valueG derivativeG holderG

theorem affine_derivative_holder (A : E →L[ℝ] F) (b : F) {u : E → F}
    (smooth : ContDiff ℝ 1 u) {α C : ℝ}
    (holder : ∀ x y, ‖fderiv ℝ u x-fderiv ℝ u y‖ ≤ C*‖x-y‖^α) :
    ∀ x y, ‖fderiv ℝ (fun z => A z+b+u z) x-
      fderiv ℝ (fun z => A z+b+u z) y‖ ≤ C*‖x-y‖^α := by
  intro x y
  have actual (z : E) : fderiv ℝ (fun v => A v+b+u v) z = A+fderiv ℝ u z :=
    ((A.hasFDerivAt.add_const b).add ((smooth.differentiable (by norm_num) z).hasFDerivAt)).fderiv
  rw [actual x, actual y]
  have cancel : (A+fderiv ℝ u x)-(A+fderiv ℝ u y) = fderiv ℝ u x-fderiv ℝ u y := by abel
  rw [cancel]
  exact holder x y

end LeanShared.AffineCutoffHolderGlobalization
