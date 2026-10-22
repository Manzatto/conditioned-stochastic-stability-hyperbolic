module
public import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Tactic

/-! Genuine Hilbert frequency pairs and the product spatial envelope.
No inner product is imposed on the max-norm Cartesian product. -/
public noncomputable section
namespace LeanShared.HilbertFrequencyPair
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Space (E:Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]:=WithLp 2 (E × E)

@[expose] def decode:Space E→L[ℝ](E × E):=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).toContinuousLinearMap

@[expose] def encode (x y:E):Space E:=WithLp.toLp 2 (x,y)

theorem decode_encode (x y:E):decode (encode x y)=(x,y):=rfl

theorem norm_first (z:Space E):‖(decode z).1‖≤‖z‖:=WithLp.norm_fst_le E z
theorem norm_second (z:Space E):‖(decode z).2‖≤‖z‖:=WithLp.norm_snd_le E z

theorem product_polynomial_le (m:ℕ) (z:Space E):
    (1+‖(decode z).1‖)^m*(1+‖(decode z).2‖)^m≤(1+‖z‖)^(2*m):=by
  calc
    _ = ((1+‖(decode z).1‖)*(1+‖(decode z).2‖))^m:=(mul_pow _ _ _).symm
    _ ≤ ((1+‖z‖)^2)^m:=pow_le_pow_left₀ (by positivity) (by
      rw [pow_two]
      exact mul_le_mul (add_le_add (le_refl 1) (norm_first z)) (add_le_add (le_refl 1) (norm_second z))
        (by positivity) (by positivity)) _
    _ = _:=by rw [←pow_mul]

@[expose] def envelope (m:ℕ) (x:E):ℝ:=((1+‖x‖)^m)⁻¹

theorem product_decay {m:ℕ} {z:Space E} {k:ℂ} {C:ℝ}
    (bound:(1+‖z‖)^(2*m)*‖k‖≤C):
    ‖k‖≤C*envelope m (decode z).1*envelope m (decode z).2:=by
  have hp:0<(1+‖(decode z).1‖)^m*(1+‖(decode z).2‖)^m:=by positivity
  have weighted:‖k‖*((1+‖(decode z).1‖)^m*(1+‖(decode z).2‖)^m)≤C:=by
    exact (mul_le_mul_of_nonneg_left (product_polynomial_le m z) (norm_nonneg k)).trans
      ((mul_comm _ _).trans_le bound)
  have raw:‖k‖≤C/((1+‖(decode z).1‖)^m*(1+‖(decode z).2‖)^m):=
    (le_div_iff₀ hp).mpr weighted
  exact raw.trans_eq (by dsimp [envelope];rw [div_mul_eq_div_div,div_eq_mul_inv,div_eq_mul_inv])
end LeanShared.HilbertFrequencyPair
