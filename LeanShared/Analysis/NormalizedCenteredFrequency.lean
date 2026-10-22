module
public import LeanShared.Analysis.HilbertFrequencyPair
import Mathlib.Tactic

/-! Exact conversion of the nonlinear kernel's center to Mathlib's
Fourier convention. Its structural 2π factors are preserved. -/
public noncomputable section
namespace LeanShared.NormalizedCenteredFrequency
open HilbertFrequencyPair
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem smul_encode (c:ℝ) (x y:E):c • encode x y=encode (c • x) (c • y):=rfl

theorem center (a b:ℝ) (x y:E):
    -(2*Real.pi)⁻¹ • encode (a • x) (b • y)=
      encode ((-(2*Real.pi)⁻¹*a) • x) ((-(2*Real.pi)⁻¹*b) • y):=by
  rw [smul_encode,smul_smul,smul_smul]

theorem envelope_sign (m:ℕ) (a:ℝ) (x:E):
    envelope m ((-(2*Real.pi)⁻¹*a) • x)=
      envelope m (((2*Real.pi)⁻¹*a) • x):=by
  rw [neg_mul,neg_smul,envelope,envelope,norm_neg]
end LeanShared.NormalizedCenteredFrequency
