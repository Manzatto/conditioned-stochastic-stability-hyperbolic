module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

/-!
# Uniform graph volume density bounds

For a graph derivative `D`, the induced Gram matrix is `I + D*D`.
An operator-norm bound gives a uniform bound for its square-root determinant.
The factorial constant is deliberately coarse: uniformity is what the leaf
tail argument needs. No cone-to-slope theorem or graph area identity is assumed
proved by this elementary estimate.
-/

@[expose] public noncomputable section

open Matrix
open scoped RealInnerProductSpace

namespace LeanShared.GraphJacobian

variable {ι E F : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Gram matrix of the derivative `v ↦ (v,Dv)` of a graph. -/
def gram (b : OrthonormalBasis ι ℝ E) (D : E →L[ℝ] F) : Matrix ι ι ℝ :=
  fun i j => (if i = j then 1 else 0) + inner ℝ (D (b i)) (D (b j))

/-- The real density occurring in the classical graph area formula. -/
def density (b : OrthonormalBasis ι ℝ E) (D : E →L[ℝ] F) : ℝ :=
  Real.sqrt (gram b D).det

/-- One bound for all graph derivatives whose norm is at most `L`. -/
def densityBound (L : ℝ) : ℝ :=
  Real.sqrt ((Nat.factorial (Fintype.card ι) : ℝ) * (1 + L ^ 2) ^ Fintype.card ι)

theorem density_nonneg (b : OrthonormalBasis ι ℝ E) (D : E →L[ℝ] F) :
    0 ≤ density b D := Real.sqrt_nonneg _

omit [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
theorem densityBound_nonneg (L : ℝ) : 0 ≤ densityBound (ι := ι) L :=
  Real.sqrt_nonneg _

theorem gram_entry_abs_le (b : OrthonormalBasis ι ℝ E) (D : E →L[ℝ] F)
    {L : ℝ} (hD : ‖D‖ ≤ L) (i j : ι) : |gram b D i j| ≤ 1 + L ^ 2 := by
  have hL : 0 ≤ L := (norm_nonneg D).trans hD
  have hv (k : ι) : ‖D (b k)‖ ≤ L := by
    calc
      ‖D (b k)‖ ≤ ‖D‖ * ‖b k‖ := D.le_opNorm _
      _ = ‖D‖ := by rw [b.norm_eq_one, mul_one]
      _ ≤ L := hD
  have hinner : |inner ℝ (D (b i)) (D (b j))| ≤ L ^ 2 := by
    exact (abs_real_inner_le_norm _ _).trans (by
      simpa only [pow_two] using mul_le_mul (hv i) (hv j) (norm_nonneg _) hL)
  have hid : |(if i = j then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
  exact (abs_add_le _ _).trans (add_le_add hid hinner)

theorem gram_det_abs_le (b : OrthonormalBasis ι ℝ E) (D : E →L[ℝ] F)
    {L : ℝ} (hD : ‖D‖ ≤ L) :
    |(gram b D).det| ≤
      (Nat.factorial (Fintype.card ι) : ℝ) * (1 + L ^ 2) ^ Fintype.card ι := by
  have h := Matrix.det_le (abv := AbsoluteValue.abs) (gram_entry_abs_le b D hD)
  change |(gram b D).det| ≤ Nat.factorial (Fintype.card ι) •
    (1 + L ^ 2) ^ Fintype.card ι at h
  simpa only [nsmul_eq_mul] using h

theorem density_le (b : OrthonormalBasis ι ℝ E) (D : E →L[ℝ] F)
    {L : ℝ} (hD : ‖D‖ ≤ L) : density b D ≤ densityBound (ι := ι) L := by
  apply Real.sqrt_le_sqrt
  exact (le_abs_self _).trans (gram_det_abs_le b D hD)

/-- The Gram area density depends continuously on the graph derivative. -/
theorem continuous_density (b : OrthonormalBasis ι ℝ E) :
    Continuous (density (F := F) b) := by
  change Continuous (fun D : E →L[ℝ] F => Real.sqrt (gram b D).det)
  have hg : Continuous (gram b : (E →L[ℝ] F) → Matrix ι ι ℝ) := by
    apply continuous_matrix
    intro i j
    dsimp [gram]
    fun_prop
  exact Real.continuous_sqrt.comp hg.matrix_det

end LeanShared.GraphJacobian
