module

public import ConditionedStochasticStabilityHyperbolic.Spectral.RankOneRetraction
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import LeanShared.Probability.IndependentNoiseCubes
public import LeanShared.Probability.EigenvectorMeasure
public import Mathlib.MeasureTheory.Measure.Support

/-! Exact change of compact state coordinates for a represented spectral gap.
The transfer is constructed from the actual pushforward kernel identity. -/

@[expose] public noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction
namespace ConditionedStochasticStabilityHyperbolic.HomeomorphicGapTransport

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Pullback is a bounded linear map for arbitrary continuous state maps. -/
def pull (e : C(X, Y)) : (Y →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => f.compContinuous e
      map_add' := by intro f g; ext x; rfl
      map_smul' := by intro c f; ext x; rfl }
    (1 : ℝ) (fun f => by
      change ‖f.compContinuous e‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using BoundedContinuousFunction.norm_compContinuous_le f e)

@[simp] theorem pull_apply (e : C(X, Y)) (f : Y →ᵇ ℝ) (x : X) :
    pull e f x = f (e x) := rfl

/-- Coordinate change preserves the actual rank-one gap, with no new
spectral or positivity input. -/
def transport (e : X ≃ₜ Y)
    (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ))
    (Q : (Y →ᵇ ℝ) →L[ℝ] (Y →ᵇ ℝ))
    (d : RankOneSpectralData Q (1 : Y →ᵇ ℝ))
    (h : Q.comp (pull ⟨e.symm, e.symm.continuous⟩) = (pull ⟨e.symm, e.symm.continuous⟩).comp P) :
    RankOneSpectralData P (1 : X →ᵇ ℝ) := by
  let a := pull ⟨e.symm, e.symm.continuous⟩
  let b := pull ⟨e, e.continuous⟩
  have hba : b.comp a = ContinuousLinearMap.id ℝ (X →ᵇ ℝ) := by
    ext f x
    exact congrArg f (e.symm_apply_apply x)
  have hb : b.comp Q = P.comp b := by
    ext f x
    change Q f (e x) = P (b f) x
    have h' := congrArg (fun L : (X →ᵇ ℝ) →L[ℝ] (Y →ᵇ ℝ) => L (b f) (e x)) h
    have hab : a (b f) = f := by ext y; exact congrArg f (e.apply_symm_apply y)
    change Q (a (b f)) (e x) = P (b f) (e.symm (e x)) at h'
    simpa only [hab, e.symm_apply_apply] using h'
  apply d.retract a b hba h hb
  have hone : a (1 : X →ᵇ ℝ) = 1 := by ext y; rfl
  rw [hone]
  exact d.mean_one_pos

@[simp] theorem transport_eigenvector (e : X ≃ₜ Y)
    (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)) (Q : (Y →ᵇ ℝ) →L[ℝ] (Y →ᵇ ℝ))
    (d : RankOneSpectralData Q (1 : Y →ᵇ ℝ))
    (h : Q.comp (pull ⟨e.symm, e.symm.continuous⟩) =
      (pull ⟨e.symm, e.symm.continuous⟩).comp P) (x : X) :
    (transport e P Q d h).eigenvector x = d.eigenvector (e x) := rfl

@[simp] theorem transport_mean (e : X ≃ₜ Y)
    (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)) (Q : (Y →ᵇ ℝ) →L[ℝ] (Y →ᵇ ℝ))
    (d : RankOneSpectralData Q (1 : Y →ᵇ ℝ))
    (h : Q.comp (pull ⟨e.symm, e.symm.continuous⟩) =
      (pull ⟨e.symm, e.symm.continuous⟩).comp P) (f : X →ᵇ ℝ) :
    (transport e P Q d h).mean f = d.mean (pull ⟨e.symm, e.symm.continuous⟩ f) := rfl

section Kernels
variable [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

/-- Actual kernel pushforward gives the intertwining required above. -/
theorem intertwining (e : X ≃ₜ Y)
    (K : Kernel X X) (L : Kernel Y Y)
    (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ))
    (Q : (Y →ᵇ ℝ) →L[ℝ] (Y →ᵇ ℝ))
    (repP : ∀ f x, P f x = ∫ z, f z ∂K x)
    (repQ : ∀ f y, Q f y = ∫ z, f z ∂L y)
    (hk : ∀ x, (K x).map e = L (e x)) :
    Q.comp (pull ⟨e.symm, e.symm.continuous⟩) =
      (pull ⟨e.symm, e.symm.continuous⟩).comp P := by
  ext f y
  change Q (pull ⟨e.symm, e.symm.continuous⟩ f) y = P f (e.symm y)
  rw [repQ, repP]
  have hmap : L y = (K (e.symm y)).map e := by
    simpa only [e.apply_symm_apply] using (hk (e.symm y)).symm
  rw [hmap, integral_map_of_stronglyMeasurable e.continuous.measurable
    (pull ⟨e.symm, e.symm.continuous⟩ f).continuous.measurable.stronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with z
  exact congrArg f (e.symm_apply_apply z)

/-- The represented left functional changes by the actual inverse state
map, rather than by a separately chosen measure. -/
theorem transport_mean_represents (e : X ≃ₜ Y)
    (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)) (Q : (Y →ᵇ ℝ) →L[ℝ] (Y →ᵇ ℝ))
    (d : RankOneSpectralData Q (1 : Y →ᵇ ℝ))
    (h : Q.comp (pull ⟨e.symm, e.symm.continuous⟩) =
      (pull ⟨e.symm, e.symm.continuous⟩).comp P)
    (μ : Measure Y) (rep : ∀ f, d.mean f = ∫ y, f y ∂μ) (f : X →ᵇ ℝ) :
    (transport e P Q d h).mean f = ∫ x, f x ∂μ.map e.symm := by
  rw [transport_mean, rep, integral_map_of_stronglyMeasurable e.symm.measurable
    f.continuous.measurable.stronglyMeasurable]
  rfl

/-- The eigenproduct is exactly the inverse-coordinate pushforward. -/
theorem transport_product (e : X ≃ₜ Y)
    (P : (X →ᵇ ℝ) →L[ℝ] (X →ᵇ ℝ)) (Q : (Y →ᵇ ℝ) →L[ℝ] (Y →ᵇ ℝ))
    (d : RankOneSpectralData Q (1 : Y →ᵇ ℝ))
    (h : Q.comp (pull ⟨e.symm, e.symm.continuous⟩) =
      (pull ⟨e.symm, e.symm.continuous⟩).comp P) (μ : Measure Y) :
    LeanShared.eigenvectorMeasure (μ.map e.symm) (transport e P Q d h).eigenvector =
      (LeanShared.eigenvectorMeasure μ d.eigenvector).map e.symm := by
  unfold LeanShared.eigenvectorMeasure
  rw [LeanShared.Homeomorph.map_withDensity e.symm μ _
    d.eigenvector.continuous.measurable.ennreal_ofReal]
  rfl

private theorem support_map (e : X ≃ₜ Y) (μ : Measure X) (x : X)
    (hx : x ∈ μ.support) : e x ∈ (μ.map e).support := by
  rw [Measure.support_eq_forall_isOpen]
  intro O hxO hO
  rw [Measure.map_apply e.measurable hO.measurableSet]
  exact ((Measure.mem_support_iff_forall x).mp hx _
    ((hO.preimage e.continuous).mem_nhds hxO))

/-- Support changes in precisely the same coordinates as the eigenproduct. -/
theorem mem_support_inverse_map (e : X ≃ₜ Y) (ν : Measure Y) (x : X) :
    x ∈ (ν.map e.symm).support ↔ e x ∈ ν.support := by
  have hmap : (ν.map e.symm).map e = ν := by
    rw [Measure.map_map e.measurable e.symm.measurable]
    simp only [Function.comp_def, e.apply_symm_apply, Measure.map_id']
  constructor
  · intro hx
    have h := support_map e (ν.map e.symm) x hx
    simpa only [hmap] using h
  · intro hx
    have h := support_map e.symm ν (e x) hx
    simpa only [e.symm_apply_apply] using h

end Kernels

end ConditionedStochasticStabilityHyperbolic.HomeomorphicGapTransport
