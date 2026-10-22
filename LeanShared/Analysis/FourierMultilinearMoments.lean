module
public import LeanShared.Analysis.FourierWordMomentIntegrability
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Every finite-order multilinear polynomial moment of a genuine inverse
Fourier kernel vanishes for a symbol zero near zero, including order zero. -/
public noncomputable section
open Set MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology BigOperators
namespace LeanShared.FourierWordMoments
variable {E ι:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Fintype ι] [DecidableEq ι] (b:OrthonormalBasis ι ℝ E)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [DecidableEq ι] in
theorem directions_basis {n:ℕ} (r:Fin n→ι) (y:E) :
    directions (List.ofFn (fun i=>b (r i))) y =
      ((∏i:Fin n,inner ℝ (b (r i)) y:ℝ):ℂ) := by
  simp only [directions,List.map_ofFn,List.prod_ofFn]
  have product:((∏i:Fin n,inner ℝ (b (r i)) y:ℝ):ℂ)=
      ∏i:Fin n,(inner ℝ (b (r i)) y:ℂ):=map_prod Complex.ofRealHom _ _
  rw [product]
  apply Finset.prod_congr rfl
  intro i _
  rw [real_inner_comm]
  rfl

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [DecidableEq ι] in
theorem multilinear_expansion {n:ℕ}
    (A:ContinuousMultilinearMap ℝ (fun _:Fin n=>E) ℂ) (y:E) :
    A (fun _=>y)=∑r:Fin n→ι,
      directions (List.ofFn (fun i=>b (r i))) y*A (fun i=>b (r i)) := by
  have expanded:=A.map_sum (fun (_:Fin n) j=>(inner ℝ (b j) y) • b j)
  have same:(fun _:Fin n=>∑j:ι,(inner ℝ (b j) y) • b j)=(fun _=>y):=by
    funext i
    exact b.sum_repr' y
  rw [same] at expanded
  rw [expanded]
  apply Finset.sum_congr rfl
  intro r _
  rw [A.map_smul_univ,RCLike.real_smul_eq_coe_mul,directions_basis b r y]
  rfl

include b in
omit [DecidableEq ι] in
theorem integrable_multilinear_moment (σ:𝓢(E,ℂ))
    {n:ℕ} (A:ContinuousMultilinearMap ℝ (fun _:Fin n=>E) ℂ) :
    Integrable (fun y=>(𝓕⁻ σ) y*A (fun _=>y)) := by
  have expression:(fun y=>(𝓕⁻ σ) y*A (fun _=>y))=
      fun y=>∑r:Fin n→ι,
        (directions (List.ofFn (fun i=>b (r i))) y*(𝓕⁻ σ) y)*A (fun i=>b (r i)):=by
    funext y
    rw [multilinear_expansion b A y,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [expression]
  exact integrable_finsetSum _ fun r _=>
    (integrable_moment σ (List.ofFn (fun i=>b (r i)))).mul_const _

include b in
omit [DecidableEq ι] in
theorem multilinear_moment_zero (σ:𝓢(E,ℂ)) (zero:∀ᶠx in 𝓝 (0:E),σ x=0)
    {n:ℕ} (A:ContinuousMultilinearMap ℝ (fun _:Fin n=>E) ℂ) :
    (∫y,(𝓕⁻ σ) y*A (fun _=>y))=0 := by
  have expression:(fun y=>(𝓕⁻ σ) y*A (fun _=>y))=
      fun y=>∑r:Fin n→ι,
        (directions (List.ofFn (fun i=>b (r i))) y*(𝓕⁻ σ) y)*A (fun i=>b (r i)):=by
    funext y
    rw [multilinear_expansion b A y,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [expression,integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro r _
    rw [integral_mul_const,moment_zero σ zero,zero_mul]
  · intro r _
    exact (integrable_moment σ (List.ofFn (fun i=>b (r i)))).mul_const _
end LeanShared.FourierWordMoments
