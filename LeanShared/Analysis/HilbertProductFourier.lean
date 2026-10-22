module
public import LeanShared.Analysis.HilbertFrequencyPair
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Tactic

/-! The Fourier transform of the actual product cutoff on the genuine
Hilbert frequency pair factors into the two physical kernels. Product
volume compatibility is proved by Mathlib's volume-preserving map. -/
public noncomputable section
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace
namespace LeanShared.HilbertProductFourier
open HilbertFrequencyPair
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem fourier_product (f g:E→ℂ) (x y:E):
    𝓕 (fun ζ:Space E=>f (decode ζ).1*g (decode ζ).2) (encode x y)=𝓕 f x*𝓕 g y:=by
  simp only [Real.fourier_eq',smul_eq_mul]
  have changeVolume: (∫uv:E × E,Complex.exp
      ((-2*Real.pi*inner ℝ (WithLp.toLp 2 uv) (encode x y):ℝ)*Complex.I)*
        (f uv.1*g uv.2))=
      ∫ζ:Space E,Complex.exp ((-2*Real.pi*inner ℝ ζ (encode x y):ℝ)*Complex.I)*
        (f (decode ζ).1*g (decode ζ).2):=by
    exact (WithLp.volume_preserving_toLp E E).integral_comp
      (MeasurableEquiv.toLp 2 (E × E)).measurableEmbedding
      (fun ζ:Space E=>Complex.exp ((-2*Real.pi*inner ℝ ζ (encode x y):ℝ)*Complex.I)*
        (f (decode ζ).1*g (decode ζ).2))
  rw [←changeVolume]
  have factor (uv:E × E):Complex.exp
      ((-2*Real.pi*inner ℝ (WithLp.toLp 2 uv) (encode x y):ℝ)*Complex.I)*(f uv.1*g uv.2)=
      (Complex.exp ((-2*Real.pi*inner ℝ uv.1 x:ℝ)*Complex.I)*f uv.1)*
        (Complex.exp ((-2*Real.pi*inner ℝ uv.2 y:ℝ)*Complex.I)*g uv.2):=by
    rw [WithLp.prod_inner_apply]
    change Complex.exp (((-2*Real.pi*(inner ℝ uv.1 x+inner ℝ uv.2 y):ℝ):ℂ)*Complex.I)*
      (f uv.1*g uv.2)=_
    have eqn:((-2*Real.pi*(inner ℝ uv.1 x+inner ℝ uv.2 y):ℝ):ℂ)*Complex.I=
      ((-2*Real.pi*inner ℝ uv.1 x:ℝ):ℂ)*Complex.I+
        ((-2*Real.pi*inner ℝ uv.2 y:ℝ):ℂ)*Complex.I:=by push_cast;ring
    rw [eqn,Complex.exp_add]
    ring
  simp_rw [factor]
  rw [Measure.volume_eq_prod]
  exact integral_prod_mul
    (fun ξ:E=>Complex.exp ((-2*Real.pi*inner ℝ ξ x:ℝ)*Complex.I)*f ξ)
    (fun η:E=>Complex.exp ((-2*Real.pi*inner ℝ η y:ℝ)*Complex.I)*g η)
end LeanShared.HilbertProductFourier
