module
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! A genuine complete graph norm for bounded Hölder functions with values
in an arbitrary complex Banach space. In particular the target can be a
continuous multilinear derivative space for higher-order Hölder jets. -/
public noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace LeanShared.BanachValuedHolderGraph
variable (X F : Type*) [MetricSpace X] [NormedAddCommGroup F] [NormedSpace ℂ F]

abbrev Pairs := {p : X×X //p.1≠p.2}
abbrev Ambient := (X →ᵇ F) × (Pairs X →ᵇ F)
@[expose] def weight (a : ℝ) (p : Pairs X) : ℂ := (dist p.val.1 p.val.2^a : ℝ)

theorem weight_ne_zero (a : ℝ) (p : Pairs X) : weight X a p≠0 := by
  unfold weight
  exact_mod_cast (Real.rpow_pos_of_pos (dist_pos.mpr p.property) a).ne'

@[expose] def graph (a : ℝ) : Submodule ℂ (Ambient X F) where
  carrier := {v | ∀p,weight X a p • v.2 p = v.1 p.val.1-v.1 p.val.2}
  zero_mem' := by simp
  add_mem' {v w} hv hw := by
    intro p
    change weight X a p • (v.2 p+w.2 p) =
      (v.1 p.val.1+w.1 p.val.1)-(v.1 p.val.2+w.1 p.val.2)
    rw [smul_add,hv,hw]
    abel
  smul_mem' c v hv := by
    intro p
    change weight X a p • (c • v.2 p) = c • v.1 p.val.1-c • v.1 p.val.2
    rw [smul_comm, hv, smul_sub]

theorem graph_closed (a : ℝ) : IsClosed (graph X F a : Set (Ambient X F)) := by
  change IsClosed {v : Ambient X F | ∀p,weight X a p • v.2 p=v.1 p.val.1-v.1 p.val.2}
  have identity : {v : Ambient X F | ∀p,weight X a p • v.2 p=v.1 p.val.1-v.1 p.val.2} =
      ⋂p, {v | weight X a p • v.2 p=v.1 p.val.1-v.1 p.val.2} := by ext v; simp
  rw [identity]
  apply isClosed_iInter
  intro p
  apply isClosed_eq
  · exact continuous_const.smul ((BoundedContinuousFunction.evalCLM ℂ p).continuous.comp continuous_snd)
  · exact ((BoundedContinuousFunction.evalCLM ℂ p.val.1).continuous.comp continuous_fst).sub
      ((BoundedContinuousFunction.evalCLM ℂ p.val.2).continuous.comp continuous_fst)

instance complete [CompleteSpace F] (a : ℝ) : CompleteSpace (graph X F a) :=
  (graph_closed X F a).completeSpace_coe

@[expose] def physical (a : ℝ) : graph X F a →L[ℂ] (X →ᵇ F) :=
  (ContinuousLinearMap.fst ℂ (X →ᵇ F) (Pairs X →ᵇ F)).comp (graph X F a).subtypeL

theorem physical_injective (a : ℝ) : Function.Injective (physical X F a) := by
  intro v w equal
  apply Subtype.ext
  apply Prod.ext
  · exact equal
  · ext p
    have diff : weight X a p • v.val.2 p=weight X a p • w.val.2 p := by
      rw [v.property p,w.property p]
      change physical X F a v p.val.1-physical X F a v p.val.2 =
        physical X F a w p.val.1-physical X F a w p.val.2
      rw [equal]
    calc
      _ = (weight X a p)⁻¹ • (weight X a p • v.val.2 p) :=
        (inv_smul_smul₀ (weight_ne_zero X a p) _).symm
      _ = (weight X a p)⁻¹ • (weight X a p • w.val.2 p) := congrArg (fun z => (weight X a p)⁻¹ • z) diff
      _ = _ := inv_smul_smul₀ (weight_ne_zero X a p) _

theorem physical_norm_le (a : ℝ) (v : graph X F a) : ‖physical X F a v‖≤‖v‖ := norm_fst_le v.val

theorem increment_bound (a : ℝ) (v : graph X F a) (x y : X) :
    ‖physical X F a v x-physical X F a v y‖≤‖v‖*dist x y^a := by
  by_cases same : x=y
  · subst y
    simp only [sub_self,norm_zero]
    positivity
  · let p : Pairs X := ⟨(x,y),same⟩
    have identity := v.property p
    change weight X a p • v.val.2 p=v.val.1 x-v.val.1 y at identity
    change ‖v.val.1 x-v.val.1 y‖≤_
    rw [←identity,norm_smul]
    have normWeight : ‖weight X a p‖=dist x y^a := by
      rw [weight,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg dist_nonneg _)]
    rw [normWeight]
    have value : ‖v.val.2 p‖≤‖v‖ := (v.val.2.norm_coe_le_norm p).trans (norm_snd_le v.val)
    exact (mul_le_mul_of_nonneg_left value (Real.rpow_nonneg dist_nonneg _)).trans_eq (by ring)
@[expose] def quotient (a : ℝ) (f : X →ᵇ F) (p : Pairs X) : F :=
  (weight X a p)⁻¹ • (f p.val.1-f p.val.2)

theorem quotient_continuous (a : ℝ) (f : X →ᵇ F) : Continuous (quotient X F a f) := by
  have first : Continuous (fun p : Pairs X => p.val.1) := continuous_fst.comp continuous_subtype_val
  have second : Continuous (fun p : Pairs X => p.val.2) := continuous_snd.comp continuous_subtype_val
  have weights : Continuous (weight X a) :=
    Complex.continuous_ofReal.comp ((first.dist second).rpow_const
      (fun p => Or.inl (dist_pos.mpr p.property).ne'))
  exact (weights.inv₀ (weight_ne_zero X a)).smul ((f.continuous.comp first).sub (f.continuous.comp second))

theorem quotient_bound (a : ℝ) (f : X →ᵇ F) (C : ℝ)
    (h : ∀x y,‖f x-f y‖≤C*dist x y^a) (p : Pairs X) : ‖quotient X F a f p‖≤C := by
  have positive : 0<dist p.val.1 p.val.2^a := Real.rpow_pos_of_pos (dist_pos.mpr p.property) _
  rw [quotient,norm_smul,norm_inv,weight,Complex.norm_real,Real.norm_eq_abs,abs_of_pos positive]
  rw [mul_comm,←div_eq_mul_inv]
  exact (div_le_iff₀ positive).mpr (h _ _)

@[expose] def ofBound (a : ℝ) (f : X →ᵇ F) (C : ℝ)
    (h : ∀x y,‖f x-f y‖≤C*dist x y^a) : graph X F a :=
  ⟨(f,BoundedContinuousFunction.ofNormedAddCommGroup (quotient X F a f)
    (quotient_continuous X F a f) C (quotient_bound X F a f C h)),by
      intro p
      change weight X a p • ((weight X a p)⁻¹ • (f p.val.1-f p.val.2))=_
      exact smul_inv_smul₀ (weight_ne_zero X a p) _⟩

theorem physical_ofBound (a : ℝ) (f : X →ᵇ F) (C : ℝ)
    (h : ∀x y,‖f x-f y‖≤C*dist x y^a) : physical X F a (ofBound X F a f C h)=f := rfl
end LeanShared.BanachValuedHolderGraph
