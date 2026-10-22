module
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Ring

/-! Actual Laplacian Fourier multipliers in the exact Mathlib 2π convention.
These identities feed elliptic annular test-function reconstruction. -/
public noncomputable section
open scoped SchwartzMap FourierTransform RealInnerProductSpace
open Laplacian LineDeriv
namespace LeanShared.FourierSchwartzLaplacian
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem second_direction (f : 𝓢(E,ℂ)) (v ξ : E) :
    𝓕 (∂_{v} (∂_{v} f)) ξ =
      (2*Real.pi*Complex.I)*(2*Real.pi*Complex.I)*((inner ℝ ξ v:ℂ)^2)*𝓕 f ξ := by
  have growth : (fun x : E => inner ℝ x v).HasTemperateGrowth :=
    ((innerSL ℝ).flip v).hasTemperateGrowth
  rw [SchwartzMap.fourier_lineDerivOp_eq]
  simp only [smul_apply,SchwartzMap.smulLeftCLM_apply_apply growth,
    SchwartzMap.fourier_lineDerivOp_eq,Complex.real_smul,smul_eq_mul]
  ring

theorem laplacian (f : 𝓢(E,ℂ)) (ξ : E) :
    𝓕 (Δ f) ξ = -((2*(Real.pi:ℂ))^2)*((‖ξ‖:ℂ)^2)*𝓕 f ξ := by
  let b := stdOrthonormalBasis ℝ E
  have squareSum : (∑ i, (inner ℝ ξ (b i))^2)=‖ξ‖^2 := by
    calc
      _ = ∑ i, inner ℝ ξ (b i)*inner ℝ (b i) ξ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [real_inner_comm (b i) ξ,pow_two]
      _ = inner ℝ ξ ξ := b.sum_inner_mul_inner ξ ξ
      _ = ‖ξ‖^2 := real_inner_self_eq_norm_sq ξ
  have complexSum : (∑ i, ((inner ℝ ξ (b i):ℂ)^2))=(‖ξ‖:ℂ)^2 := by
    exact_mod_cast squareSum
  have coefficient : (2*(Real.pi:ℂ)*Complex.I)*(2*(Real.pi:ℂ)*Complex.I)=
      -((2*(Real.pi:ℂ))^2) := by
    calc
      _ = (2*(Real.pi:ℂ))^2*Complex.I^2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [SchwartzMap.laplacian_eq_sum b,FourierTransform.fourier_sum,sum_apply]
  simp_rw [second_direction]
  calc
    _ = ((2*(Real.pi:ℂ)*Complex.I)*(2*(Real.pi:ℂ)*Complex.I))*
        (∑ i, ((inner ℝ ξ (b i):ℂ)^2))*𝓕 f ξ := by
      rw [Finset.mul_sum,Finset.sum_mul]
    _ = _ := by rw [complexSum,coefficient]

@[expose] def power (n : ℕ) (f : 𝓢(E,ℂ)) : 𝓢(E,ℂ) :=
  (fun g : 𝓢(E,ℂ) => Δ g)^[n] f

theorem power_fourier (n : ℕ) (f : 𝓢(E,ℂ)) (ξ : E) :
    𝓕 (power n f) ξ = (-((2*(Real.pi:ℂ))^2)*((‖ξ‖:ℂ)^2))^n*𝓕 f ξ := by
  induction n with
  | zero => simp only [power,Function.iterate_zero,Function.id_def,pow_zero,one_mul]
  | succ n ih =>
    rw [power,Function.iterate_succ_apply']
    change 𝓕 (Δ (power n f)) ξ = _
    rw [laplacian,ih,pow_succ]
    ring
end LeanShared.FourierSchwartzLaplacian
