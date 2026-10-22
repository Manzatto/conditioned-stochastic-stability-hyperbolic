module

public import LeanShared.Dynamics.HyperbolicFiniteAdaptedEnergy
public import LeanShared.Geometry.BilinearBundleContinuity
public import LeanShared.Dynamics.HyperbolicProjectedBlockBounds
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Continuous positive finite-sum forms. The original Riemannian inner product and the literal
derivative iterates are retained. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators

namespace LeanShared.HyperbolicAdaptedForms
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MetricSpace M] [ChartedSpace E M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]

@[expose] def iterateForm (f : M → M) (a : ℝ) (N : ℕ) (x : M) :
    TangentSpace (𝓘(ℝ, E)) x →L[ℝ] TangentSpace (𝓘(ℝ, E)) x →L[ℝ] ℝ :=
  ∑ j ∈ Finset.range N, ((a ^ 2)⁻¹) ^ j •
    (innerSL ℝ).bilinearComp
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (f^[j]) x)
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (f^[j]) x)

theorem iterateForm_apply (f : M → M) (a : ℝ) (N : ℕ) (x : M)
    (v w : TangentSpace (𝓘(ℝ, E)) x) :
    iterateForm f a N x v w = ∑ j ∈ Finset.range N, ((a ^ 2)⁻¹) ^ j *
      inner ℝ (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (f^[j]) x v)
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (f^[j]) x w) := by
  simp [iterateForm]

theorem self_eq_energy (f : M → M) (a : ℝ) (N : ℕ) (x : M)
    (v : TangentSpace (𝓘(ℝ, E)) x) :
    iterateForm f a N x v v = HyperbolicFiniteAdaptedEnergy.iterateEnergy f a N x v := by
  simp only [iterateForm_apply, real_inner_self_eq_norm_sq,
    HyperbolicFiniteAdaptedEnergy.iterateEnergy, FiniteAdaptedEnergy.energy]

theorem symmetric (f : M → M) (a : ℝ) (N : ℕ) (x : M)
    (v w : TangentSpace (𝓘(ℝ, E)) x) :
    iterateForm f a N x v w = iterateForm f a N x w v := by
  simp only [iterateForm_apply, real_inner_comm]

theorem positive (f : M → M) (a : ℝ) (N : ℕ) (length : 0 < N) (x : M)
    (v : TangentSpace (𝓘(ℝ, E)) x) (nonzero : v ≠ 0) :
    0 < iterateForm f a N x v v := by
  rw [self_eq_energy]
  exact (sq_pos_of_pos (norm_pos_iff.mpr nonzero)).trans_le
    (HyperbolicFiniteAdaptedEnergy.initial_le f a N length x v)

/-- Continuity against arbitrary continuous tangent inputs, including inputs
obtained from the continuous invariant splitting. -/
theorem continuousOn_pairing [IsManifold (𝓘(ℝ, E)) ∞ M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {X : Type*} [TopologicalSpace X] (K : Set X) (b : X → M)
    (v w : ∀ y, TangentSpace (𝓘(ℝ, E)) (b y))
    (cv : ContinuousOn (fun y => (⟨b y, v y⟩ : TangentBundle (𝓘(ℝ, E)) M)) K)
    (cw : ContinuousOn (fun y => (⟨b y, w y⟩ : TangentBundle (𝓘(ℝ, E)) M)) K)
    (f : M → M) (smooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 f)
    (a : ℝ) (N : ℕ) :
    ContinuousOn (fun y => iterateForm f a N (b y) (v y) (w y)) K := by
  simp only [iterateForm_apply]
  apply continuousOn_finsetSum
  intro j _
  have tv := ((smooth.iterate j).continuous_tangentMap le_rfl).comp_continuousOn cv
  have tw := ((smooth.iterate j).continuous_tangentMap le_rfl).comp_continuousOn cw
  exact continuousOn_const.mul (tv.inner_bundle tw)

/-- Continuity as a section of the actual bundle of continuous bilinear forms. -/
theorem continuous_iterateForm [FiniteDimensional ℝ E]
    [IsManifold (𝓘(ℝ, E)) ∞ M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    (f : M → M) (smooth : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 f)
    (a : ℝ) (N : ℕ) :
    Continuous (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun y => TangentSpace (𝓘(ℝ, E)) y →L[ℝ]
        TangentSpace (𝓘(ℝ, E)) y →L[ℝ] ℝ) x (iterateForm f a N x)) := by
  apply BilinearBundleContinuity.of_pairings
  intro U v w cv cw
  exact continuousOn_pairing U id v w cv cw f smooth a N

/-- Orthogonalize the two summands using the actual stable projector. -/
@[expose] def splitForm (f g : M → M) (P : ∀ x : M,
    TangentSpace (𝓘(ℝ, E)) x →L[ℝ] TangentSpace (𝓘(ℝ, E)) x)
    (a : ℝ) (N : ℕ) (x : M) :
    TangentSpace (𝓘(ℝ, E)) x →L[ℝ] TangentSpace (𝓘(ℝ, E)) x →L[ℝ] ℝ :=
  (iterateForm f a N x).bilinearComp
    (E' := TangentSpace (𝓘(ℝ, E)) x) (F' := TangentSpace (𝓘(ℝ, E)) x)
    (E'' := TangentSpace (𝓘(ℝ, E)) x) (F'' := TangentSpace (𝓘(ℝ, E)) x) (P x) (P x) +
    (iterateForm g a N x).bilinearComp
      (E' := TangentSpace (𝓘(ℝ, E)) x) (F' := TangentSpace (𝓘(ℝ, E)) x)
      (E'' := TangentSpace (𝓘(ℝ, E)) x) (F'' := TangentSpace (𝓘(ℝ, E)) x)
      (ContinuousLinearMap.id ℝ (TangentSpace (𝓘(ℝ, E)) x) - P x) (ContinuousLinearMap.id ℝ (TangentSpace (𝓘(ℝ, E)) x) - P x)

theorem splitForm_self (f g : M → M) (P : ∀ x : M,
    TangentSpace (𝓘(ℝ, E)) x →L[ℝ] TangentSpace (𝓘(ℝ, E)) x)
    (a : ℝ) (N : ℕ) (x : M) (v : TangentSpace (𝓘(ℝ, E)) x) :
    splitForm f g P a N x v v =
      HyperbolicFiniteAdaptedEnergy.iterateEnergy f a N x (P x v) +
      HyperbolicFiniteAdaptedEnergy.iterateEnergy g a N x (v - P x v) := by
  simp only [splitForm, add_apply,
    ContinuousLinearMap.bilinearComp_apply, sub_apply,
    ContinuousLinearMap.id_apply, self_eq_energy]

/-- The lower equivalence is universal: no uniform projector bound is needed. -/
theorem splitForm_lower (f g : M → M) (P : ∀ x : M,
    TangentSpace (𝓘(ℝ, E)) x →L[ℝ] TangentSpace (𝓘(ℝ, E)) x)
    (a : ℝ) (N : ℕ) (length : 0 < N) (x : M)
    (v : TangentSpace (𝓘(ℝ, E)) x) :
    ‖v‖ ^ 2 ≤ 2 * splitForm f g P a N x v v := by
  rw [splitForm_self]
  have stable := HyperbolicFiniteAdaptedEnergy.initial_le f a N length x (P x v)
  have unstable := HyperbolicFiniteAdaptedEnergy.initial_le g a N length x (v - P x v)
  have triangle : ‖v‖ ≤ ‖P x v‖ + ‖v - P x v‖ := by
    simpa only [add_sub_cancel] using norm_add_le (P x v) (v - P x v)
  have squares := pow_le_pow_left₀ (norm_nonneg v) triangle 2
  nlinarith [sq_nonneg (‖P x v‖ - ‖v - P x v‖)]

theorem splitForm_positive (f g : M → M) (P : ∀ x : M,
    TangentSpace (𝓘(ℝ, E)) x →L[ℝ] TangentSpace (𝓘(ℝ, E)) x)
    (a : ℝ) (N : ℕ) (length : 0 < N) (x : M)
    (v : TangentSpace (𝓘(ℝ, E)) x) (nonzero : v ≠ 0) :
    0 < splitForm f g P a N x v v := by
  have lower := splitForm_lower f g P a N length x v
  have pos := sq_pos_of_pos (norm_pos_iff.mpr nonzero)
  linarith

theorem splitForm_symmetric (f g : M → M) (P : ∀ x : M,
    TangentSpace (𝓘(ℝ, E)) x →L[ℝ] TangentSpace (𝓘(ℝ, E)) x)
    (a : ℝ) (N : ℕ) (x : M) (v w : TangentSpace (𝓘(ℝ, E)) x) :
    splitForm f g P a N x v w = splitForm f g P a N x w v := by
  simp only [splitForm, add_apply, ContinuousLinearMap.bilinearComp_apply,
    symmetric]

/-- The positive finite-sum metric has exactly the original fiber topology.
Its continuity on the core is proved separately; no ambient continuity of the
hyperbolic splitting is imposed. -/
@[expose] def adaptedMetric (f g : M → M) (P : ∀ x : M,
    TangentSpace (𝓘(ℝ, E)) x →L[ℝ] TangentSpace (𝓘(ℝ, E)) x)
    (a : ℝ) (N : ℕ) (length : 0 < N) :
    RiemannianMetric (fun x : M => TangentSpace (𝓘(ℝ, E)) x) where
  inner := splitForm f g P a N
  symm := splitForm_symmetric f g P a N
  pos := splitForm_positive f g P a N length
  continuousAt x :=
    ((splitForm f g P a N x).continuous.clm_apply continuous_id).continuousAt
  isVonNBounded x := by
    apply (NormedSpace.isVonNBounded_ball ℝ (TangentSpace (𝓘(ℝ, E)) x) 2).subset
    intro v hv
    rw [Metric.mem_ball, dist_zero_right]
    have lower := splitForm_lower f g P a N length x v
    change splitForm f g P a N x v v < 1 at hv
    nlinarith [norm_nonneg v]

/-- The actual hyperbolic splitting yields a continuous positive form on the
core, without requiring any ambient continuous extension of the splitting. -/
theorem HyperbolicData.continuousOn_splitForm [FiniteDimensional ℝ E]
    [IsManifold (𝓘(ℝ, E)) ∞ M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M}
    (h : HyperbolicBasicSet.HyperbolicData (E := E) T Λ)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    (a : ℝ) (N : ℕ) :
    ContinuousOn (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun y => TangentSpace (𝓘(ℝ, E)) y →L[ℝ]
        TangentSpace (𝓘(ℝ, E)) y →L[ℝ] ℝ)
      x (splitForm T T.symm h.projection a N x)) Λ := by
  apply BilinearBundleContinuity.of_pairingsOn
  intro U subset v w cv cw
  have cpv := h.continuous_splitting.comp cv (fun x hx => subset hx)
  have cpw := h.continuous_splitting.comp cw (fun x hx => subset hx)
  have cqv := BilinearBundleContinuity.sub_sections _ U id v
    (fun x => h.projection x (v x)) cv cpv
  have cqw := BilinearBundleContinuity.sub_sections _ U id w
    (fun x => h.projection x (w x)) cw cpw
  have stable := continuousOn_pairing U id (fun x => h.projection x (v x))
    (fun x => h.projection x (w x)) cpv cpw T forward a N
  have unstable := continuousOn_pairing U id (fun x => v x - h.projection x (v x))
    (fun x => w x - h.projection x (w x)) cqv cqw T.symm backward a N
  apply (stable.add unstable).congr
  intro x _
  simp only [splitForm, add_apply, ContinuousLinearMap.bilinearComp_apply,
    sub_apply, ContinuousLinearMap.id_apply]
  rfl

/-- Both uniform comparisons for the actual positive orthogonalized form.
The upper constant is derived from compactness of the actual core. -/
theorem HyperbolicData.exists_adapted_form [FiniteDimensional ℝ E]
    [IsManifold (𝓘(ℝ, E)) ∞ M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
    {T : M ≃ₜ M} {Λ : Set M}
    (h : HyperbolicBasicSet.HyperbolicData (E := E) T Λ)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    (a : ℝ) (slack : h.contraction < a) :
    ∃ N : ℕ, 0 < N ∧ ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Λ,
      ∀ v : TangentSpace (𝓘(ℝ, E)) x,
        ‖v‖ ^ 2 ≤ 2 * splitForm T T.symm h.projection a N x v v ∧
        splitForm T T.symm h.projection a N x v v ≤ B * ‖v‖ ^ 2 := by
  obtain ⟨N, length, Bs, Bu, hBs, hBu, stable, unstable⟩ :=
    HyperbolicFiniteAdaptedEnergy.HyperbolicData.exists_two_sided_energy
      h forward backward a slack
  obtain ⟨C, positiveC, bounds⟩ := h.exists_projection_norm_bound
  refine ⟨N, length, (Bs + Bu) * C ^ 2, mul_pos (by linarith) (sq_pos_of_pos positiveC), ?_⟩
  intro x hx v
  refine ⟨splitForm_lower T T.symm h.projection a N length x v, ?_⟩
  have smem : h.projection x v ∈ h.stable x := by
    rw [← h.projection_range x hx]
    exact LinearMap.mem_range.mpr ⟨v, rfl⟩
  have umem : v - h.projection x v ∈ h.unstable x := by
    rw [← h.projection_kernel x hx]
    change h.projection x (v - h.projection x v) = 0
    rw [map_sub, show h.projection x (h.projection x v) = h.projection x v from
      congrArg (fun L => L v) (h.projection_idempotent x hx), sub_self]
  have sp : ‖h.projection x v‖ ≤ C * ‖v‖ :=
    ((h.projection x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (bounds x hx).1 (norm_nonneg _))
  have up : ‖v - h.projection x v‖ ≤ C * ‖v‖ := by
    exact ((ContinuousLinearMap.id ℝ (TangentSpace (𝓘(ℝ, E)) x) - h.projection x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (bounds x hx).2 (norm_nonneg _))
  rw [splitForm_self]
  calc
    _ ≤ Bs * ‖h.projection x v‖ ^ 2 + Bu * ‖v - h.projection x v‖ ^ 2 :=
      add_le_add (stable x hx _ smem).2.1 (unstable x hx _ umem).2.1
    _ ≤ Bs * (C * ‖v‖) ^ 2 + Bu * (C * ‖v‖) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) sp 2) (by linarith))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) up 2) (by linarith))
    _ = _ := by ring

end LeanShared.HyperbolicAdaptedForms
