module
public import LeanShared.Analysis.SchwartzJetSpace
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Tactic.Ring

/-! Every product of real directional moments of an inverse Fourier kernel
vanishes when the actual symbol is zero near the origin. The Fourier
normalization and arbitrary directional derivative word are retained. -/
public noncomputable section
open Set MeasureTheory Filter
open scoped SchwartzMap FourierTransform Topology
namespace LeanShared.FourierWordMoments
variable {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[expose] def directions (w:List E) (y:E) : ℂ:=
  (w.map (fun v=>(inner ℝ y v:ℂ))).prod

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem word_support (w:List E) (σ:𝓢(E,ℂ)) :
    tsupport (SchwartzJetSpace.wordDerivative w σ)⊆tsupport σ := by
  induction w with
  | nil=>exact subset_rfl
  | cons v w ih=>exact (SchwartzMap.tsupport_lineDerivOp_subset v _).trans ih

theorem fourierInv_word (w:List E) (σ:𝓢(E,ℂ)) (y:E) :
    (𝓕⁻ (SchwartzJetSpace.wordDerivative w σ)) y=
      (-(2*Real.pi*Complex.I))^w.length*directions w y*(𝓕⁻ σ) y := by
  induction w with
  | nil=>simp [directions]
  | cons v w ih=>
    have growth:(fun x:E=>inner ℝ x v).HasTemperateGrowth:=by fun_prop
    rw [SchwartzJetSpace.wordDerivative_cons,SchwartzMap.fourierInv_lineDerivOp_eq]
    simp only [smul_apply,SchwartzMap.smulLeftCLM_apply_apply growth,
      RCLike.real_smul_eq_coe_mul,smul_eq_mul,ih,List.length_cons,directions,List.map_cons,List.prod_cons]
    have algebra (c d r z:ℂ) (k:ℕ) :
        c*(d*(c^k*r*z))=(c^k*c)*(d*r)*z:=by ring
    convert! algebra (-(2*Real.pi*Complex.I)) (inner ℝ y v:ℂ)
      ((w.map (fun v=>(inner ℝ y v:ℂ))).prod) ((𝓕⁻ σ) y) w.length using 1

theorem integral_inverse (σ:𝓢(E,ℂ)) : (∫y,(𝓕⁻ σ) y)=σ 0 := by
  have transform:𝓕 (𝓕⁻ σ)=σ:=by simp
  have evaluated:=congrArg (fun q:𝓢(E,ℂ)=>q 0) transform
  simpa only [SchwartzMap.fourier_coe,Real.fourier_eq,inner_zero_right,neg_zero,
    Real.fourierChar.map_zero_eq_one,one_smul] using evaluated

theorem moment_zero (σ:𝓢(E,ℂ)) (zero:∀ᶠx in 𝓝 (0:E),σ x=0) (w:List E) :
    (∫y,directions w y*(𝓕⁻ σ) y)=0 := by
  have outside:0∉tsupport σ:=notMem_tsupport_iff_eventuallyEq.mpr zero
  have derivativeZero:SchwartzJetSpace.wordDerivative w σ 0=0:=
    image_eq_zero_of_notMem_tsupport (fun h=>outside (word_support w σ h))
  have integralZero:(∫y,(𝓕⁻ (SchwartzJetSpace.wordDerivative w σ)) y)=0:=
    (integral_inverse _).trans derivativeZero
  have expression:(fun y=>(𝓕⁻ (SchwartzJetSpace.wordDerivative w σ)) y)=
      fun y=>(-(2*Real.pi*Complex.I))^w.length*(directions w y*(𝓕⁻ σ) y):=by
    funext y
    rw [fourierInv_word,mul_assoc]
  rw [expression,integral_const_mul] at integralZero
  have nonzero:(-(2*Real.pi*Complex.I):ℂ)^w.length≠0:=by
    apply pow_ne_zero
    simp [Real.pi_ne_zero]
  exact (mul_eq_zero.mp integralZero).resolve_left nonzero
end LeanShared.FourierWordMoments
