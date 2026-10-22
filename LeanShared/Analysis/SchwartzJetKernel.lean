module

public import LeanShared.Analysis.SchwartzJetSpace
public import LeanShared.Analysis.JetLeafComponent

/-!
# Translated cutoff kernels belong to the actual supported derivative-jet space

The Leibniz expansion is constructed for arbitrary finite words of real
directional derivatives. Its terms are fixed Schwartz kernels multiplied by
fixed cutoff derivatives, so the smoothing compactness theorem applies.
-/

@[expose] public noncomputable section

open Set
open scoped SchwartzMap BoundedContinuousFunction LineDeriv BigOperators

namespace LeanShared.SchwartzJetKernel

open SchwartzJetSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def translated (ψ : 𝓢(E, ℂ)) (x : E) : 𝓢(E, ℂ) :=
  SchwartzMap.compSubConstCLM ℂ x
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (LinearIsometryEquiv.neg ℝ (E := E)).toContinuousLinearEquiv ψ)

@[simp] theorem translated_apply (ψ : 𝓢(E, ℂ)) (x y : E) :
    translated ψ x y = ψ (x - y) := by
  simp [translated, SchwartzMap.compSubConstCLM_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, neg_sub]

def multiply (χ ψ : 𝓢(E, ℂ)) : 𝓢(E, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (χ : E → ℂ) ψ

@[simp] theorem multiply_apply (χ ψ : 𝓢(E, ℂ)) (y : E) :
    multiply χ ψ y = χ y * ψ y := by
  exact SchwartzMap.smulLeftCLM_apply_apply χ.hasTemperateGrowth ψ y

def cutoffKernel (χ ψ : 𝓢(E, ℂ)) (x : E) : 𝓢(E, ℂ) :=
  multiply χ (translated ψ x)

@[simp] theorem cutoffKernel_apply (χ ψ : 𝓢(E, ℂ)) (x y : E) :
    cutoffKernel χ ψ x y = χ y * ψ (x - y) := by simp [cutoffKernel]

theorem lineDeriv_multiply (v : E) (χ ψ : 𝓢(E, ℂ)) :
    ∂_{v} (multiply χ ψ) = multiply (∂_{v} χ) ψ + multiply χ (∂_{v} ψ) := by
  ext y
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, add_apply,
    multiply_apply]
  have hfun : (multiply χ ψ : E → ℂ) = fun z => χ z * ψ z := by ext z; simp
  rw [hfun, fderiv_fun_mul χ.differentiableAt ψ.differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem lineDeriv_translated (v : E) (ψ : 𝓢(E, ℂ)) (x : E) :
    ∂_{v} (translated ψ x) = translated (-(∂_{v} ψ)) x := by
  ext y
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, translated_apply,
    neg_apply]
  have hfun : (translated ψ x : E → ℂ) = fun z => ψ (x - z) := by ext z; simp
  rw [hfun]
  have hd := (ψ.hasFDerivAt (x - y)).comp y ((hasFDerivAt_id y).const_sub x)
  change (fderiv ℝ (⇑ψ ∘ HSub.hSub x) y) v = _
  rw [hd.fderiv]
  simp

theorem lineDeriv_cutoffKernel (v : E) (χ ψ : 𝓢(E, ℂ)) (x : E) :
    ∂_{v} (cutoffKernel χ ψ x) =
      cutoffKernel (∂_{v} χ) ψ x + cutoffKernel χ (-(∂_{v} ψ)) x := by
  simp only [cutoffKernel, lineDeriv_multiply, lineDeriv_translated]

/-- A binary choice at each differentiation records the full Leibniz expansion. -/
def Expansion : List E → Type
  | [] => Unit
  | _ :: w => Bool × Expansion w

@[reducible] def expansionFintype : (w : List E) → Fintype (Expansion w)
  | [] => inferInstanceAs (Fintype Unit)
  | _ :: w => by letI := expansionFintype w; exact inferInstanceAs (Fintype (Bool × Expansion w))

instance (w : List E) : Fintype (Expansion w) := expansionFintype w

def coefficient : (w : List E) → Expansion w → 𝓢(E, ℂ) → 𝓢(E, ℂ)
  | [], _, χ => χ
  | v :: w, (b, t), χ => if b then coefficient w t χ else ∂_{v} (coefficient w t χ)

def kernel : (w : List E) → Expansion w → 𝓢(E, ℂ) → 𝓢(E, ℂ)
  | [], _, ψ => ψ
  | v :: w, (b, t), ψ => if b then -(∂_{v} (kernel w t ψ)) else kernel w t ψ

theorem wordDerivative_cutoffKernel (w : List E) (χ ψ : 𝓢(E, ℂ)) (x : E) :
    wordDerivative w (cutoffKernel χ ψ x) =
      ∑ t : Expansion w, cutoffKernel (coefficient w t χ) (kernel w t ψ) x := by
  induction w with
  | nil =>
      change cutoffKernel χ ψ x = ∑ _ : Unit, cutoffKernel χ ψ x
      simp
  | cons v w ih =>
      rw [wordDerivative_cons, ih]
      change (LineDeriv.lineDerivOpCLM ℂ 𝓢(E, ℂ) v) _ = _
      rw [map_sum]
      simp only [LineDeriv.lineDerivOpCLM_apply, lineDeriv_cutoffKernel]
      change _ = ∑ t : Bool × Expansion w,
        cutoffKernel (coefficient (v :: w) t χ) (kernel (v :: w) t ψ) x
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      simp only [coefficient, kernel, Bool.false_eq_true, ↓reduceIte]
      rw [Finset.sum_add_distrib, add_comm]

theorem cutoffKernel_supported {K : Set E} (χ ψ : 𝓢(E, ℂ))
    (hχ : ∀ y ∉ K, χ y = 0) (x : E) : ∀ y ∉ K, cutoffKernel χ ψ x y = 0 := by
  intro y hy
  simp [hχ y hy]

theorem cutoffKernel_jet_mem {I : Type*} {K : Set E} (w : I → List E)
    (χ ψ : 𝓢(E, ℂ)) (hχ : ∀ y ∉ K, χ y = 0) (x : E) :
    jetMap K w (cutoffKernel χ ψ x) ∈ jetSpace K w :=
  jet_mem K w _ (cutoffKernel_supported χ ψ hχ x)

section FiniteJets

variable {I : Type*} [Fintype I] {K : Set E} (w : I → List E)

/-- All fixed-kernel terms of all jet coordinates. -/
abbrev ExpandedIndex := (i : I) × Expansion (w i)

def expandedKernel (ψ : 𝓢(E, ℂ)) (t : ExpandedIndex w) : 𝓢(E, ℂ) :=
  kernel (w t.1) t.2 ψ

def expandedCoefficient (χ : 𝓢(E, ℂ)) (t : ExpandedIndex w) : K →ᵇ ℂ :=
  (coefficient (w t.1) t.2 χ).toBoundedContinuousFunction.domRestrict K

/-- Finite summation reconstructs the actual derivative jet from its Leibniz terms. -/
def sumMap : (ExpandedIndex w → K →ᵇ ℂ) →L[ℂ] (I → K →ᵇ ℂ) :=
  ContinuousLinearMap.pi fun i => ∑ t : Expansion (w i),
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ExpandedIndex w => K →ᵇ ℂ) ⟨i, t⟩

omit [NormedSpace ℝ E] [Fintype I] in
@[simp] theorem sumMap_apply (q : ExpandedIndex w → K →ᵇ ℂ) (i : I) (y : K) :
    sumMap w q i y = ∑ t : Expansion (w i), q ⟨i, t⟩ y := by
  simp [sumMap]

omit [Fintype I] in
theorem sumMap_kernelSection (χ ψ : 𝓢(E, ℂ)) (x : E) :
    sumMap w (SchwartzLeafComponent.kernelSection
      (expandedKernel w ψ) (expandedCoefficient (K := K) w χ) x) =
      jetMap K w (cutoffKernel χ ψ x) := by
  funext i
  ext y
  rw [sumMap_apply, jetMap_apply, wordDerivative_cutoffKernel]
  simp only [sum_apply, cutoffKernel_apply,
    SchwartzLeafComponent.kernelSection, expandedKernel, expandedCoefficient]
  apply Finset.sum_congr rfl
  intro t _
  exact mul_comm _ _

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (hK : IsCompact K) (χ ψ : 𝓢(E, ℂ))
  {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]
  (μ : MeasureTheory.Measure U) [μ.IsAddHaarMeasure] {J : ℝ} (hJ : 0 ≤ J)
  (k : ℕ) (hk : (Module.finrank ℝ U : ℝ) < (k : ℝ))

/-- A dual functional is precomposed by the actual finite Leibniz summation map. -/
def expandFunctional : ((I → K →ᵇ ℂ) →L[ℂ] ℂ) →L[ℂ]
    ((ExpandedIndex w → K →ᵇ ℂ) →L[ℂ] ℂ) :=
  (ContinuousLinearMap.compL ℂ (ExpandedIndex w → K →ᵇ ℂ)
    (I → K →ᵇ ℂ) ℂ).flip (sumMap w)

/-- The actual continuous bounded function obtained by pairing with cutoff jets. -/
def smoothingFunction (f : (I → K →ᵇ ℂ) →L[ℂ] ℂ) : E →ᵇ ℂ :=
  SchwartzLeafComponent.smoothingFunction hK (expandedKernel w ψ)
    (expandedCoefficient w χ) (expandFunctional w f)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem smoothingFunction_apply (f : (I → K →ᵇ ℂ) →L[ℂ] ℂ) (x : E) :
    smoothingFunction w hK χ ψ f x = f (jetMap K w (cutoffKernel χ ψ x)) :=
  congrArg f (sumMap_kernelSection w χ ψ x)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Arbitrary polynomial decay is derived from actual Schwartz derivative kernels. -/
theorem smoothingFunction_decay (f : (I → K →ᵇ ℂ) →L[ℂ] ℂ) (m : ℕ) (x : E) :
    ‖smoothingFunction w hK χ ψ f x‖ ≤
      (‖expandFunctional w f‖ * SchwartzLeafComponent.sectionDecayConstant hK
        (expandedKernel w ψ) (expandedCoefficient w χ) m) *
      GraphLeafNorm.radialWeight (m : ℝ) x :=
  SchwartzLeafComponent.smoothingFunction_decay hK (expandedKernel w ψ)
    (expandedCoefficient w χ) (expandFunctional w f) m x

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Equicontinuity constants come from the actual Schwartz derivative kernels. -/
theorem smoothingFunction_lipschitz (f : (I → K →ᵇ ℂ) →L[ℂ] ℂ) :
    LipschitzWith (‖expandFunctional w f‖₊ * SchwartzLeafComponent.sectionLipschitzConstant
      (expandedKernel w ψ) (expandedCoefficient (K := K) w χ)) (smoothingFunction w hK χ ψ f) :=
  SchwartzLeafComponent.smoothingFunction_lipschitz hK (expandedKernel w ψ)
    (expandedCoefficient w χ) (expandFunctional w f)

/-- The genuine full-tuple dual smoothing component for derivative jets. -/
def fullOperator : ((I → K →ᵇ ℂ) →L[ℂ] ℂ) →L[ℂ]
    GraphLeafNorm.LeafSpace (E := E) μ (J := J) :=
  (SchwartzLeafComponent.operator hK (expandedKernel w ψ)
    (expandedCoefficient w χ) μ hJ k hk).comp (expandFunctional w)

theorem fullOperator_isCompact : IsCompactOperator (fullOperator w hK χ ψ μ hJ k hk) :=
  (SchwartzLeafComponent.operator_isCompact hK (expandedKernel w ψ)
    (expandedCoefficient w χ) μ hJ k hk).comp_clm (expandFunctional w)

theorem fullOperator_ae (f : (I → K →ᵇ ℂ) →L[ℂ] ℂ)
    (L : GraphLeafNorm.GraphLeaf U E J) :
    fullOperator w hK χ ψ μ hJ k hk f L =ᵐ[L.sourceMeasure μ]
      fun y => f (jetMap K w (cutoffKernel χ ψ (L.graph y))) := by
  apply (SchwartzLeafComponent.operator_ae hK (expandedKernel w ψ)
    (expandedCoefficient w χ) μ hJ k hk (expandFunctional w f) L).trans
  exact MeasureTheory.ae_of_all _ fun y => congrArg f (sumMap_kernelSection w χ ψ (L.graph y))

variable (hχ : ∀ y ∉ K, χ y = 0)

include hχ in
theorem fullOperator_restriction_compatible (f g : (I → K →ᵇ ℂ) →L[ℂ] ℂ)
    (hfg : ∀ v : jetSpace K w, f v = g v) :
    fullOperator w hK χ ψ μ hJ k hk f = fullOperator w hK χ ψ μ hJ k hk g := by
  apply lp.ext
  funext L
  apply MeasureTheory.Lp.ext
  filter_upwards [fullOperator_ae w hK χ ψ μ hJ k hk f L,
    fullOperator_ae w hK χ ψ μ hJ k hk g L] with y hf hg
  rw [hf, hg]
  exact hfg ⟨_, cutoffKernel_jet_mem w χ ψ hχ (L.graph y)⟩

/-- Compact smoothing on the dual of the actual supported derivative-jet range. -/
def operator : (jetSpace K w →L[ℂ] ℂ) →L[ℂ]
    GraphLeafNorm.LeafSpace (E := E) μ (J := J) :=
  DualRestrictionCompactness.descend (jetSpace K w) (fullOperator w hK χ ψ μ hJ k hk)
    (fullOperator_restriction_compatible w hK χ ψ μ hJ k hk hχ)

theorem operator_isCompact : IsCompactOperator (operator w hK χ ψ μ hJ k hk hχ) :=
  DualRestrictionCompactness.descend_isCompact (jetSpace K w)
    (fullOperator w hK χ ψ μ hJ k hk)
    (fullOperator_restriction_compatible w hK χ ψ μ hJ k hk hχ)
    (fullOperator_isCompact w hK χ ψ μ hJ k hk)

theorem operator_ae (f : jetSpace K w →L[ℂ] ℂ) (L : GraphLeafNorm.GraphLeaf U E J) :
    operator w hK χ ψ μ hJ k hk hχ f L =ᵐ[L.sourceMeasure μ]
      fun y => f ⟨jetMap K w (cutoffKernel χ ψ (L.graph y)),
        cutoffKernel_jet_mem w χ ψ hχ (L.graph y)⟩ := by
  change fullOperator w hK χ ψ μ hJ k hk
    (DualRestrictionCompactness.extension (jetSpace K w) f) L =ᵐ[_] _
  apply (fullOperator_ae w hK χ ψ μ hJ k hk
    (DualRestrictionCompactness.extension (jetSpace K w) f) L).trans
  exact MeasureTheory.ae_of_all _ fun y =>
    DualRestrictionCompactness.extension_apply (jetSpace K w) f
      ⟨_, cutoffKernel_jet_mem w χ ψ hχ (L.graph y)⟩

end FiniteJets

end LeanShared.SchwartzJetKernel
