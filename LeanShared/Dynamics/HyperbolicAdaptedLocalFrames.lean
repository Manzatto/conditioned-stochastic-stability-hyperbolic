module
public import LeanShared.Dynamics.HyperbolicAdaptedForms
public import LeanShared.Dynamics.HyperbolicContinuousUnstableFrames
public import LeanShared.Dynamics.ReversedHyperbolicBasicSet
import all LeanShared.Dynamics.ReversedHyperbolicBasicSet
public import LeanShared.Geometry.ContinuousSubspaceFrameNormalization

/-! Local frame normalization in the actual adapted form, while retaining
the original tangent topology and the actual invariant subspaces. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators
namespace LeanShared.HyperbolicAdaptedLocalFrames
open HyperbolicAdaptedForms
variable {E M H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [TopologicalSpace X] {T : M ≃ₜ M} {Λ : Set M}

theorem normalized_family (h : HyperbolicBasicSet.HyperbolicData (E := E) T Λ)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    (a : ℝ) (N : ℕ) (length : 0 < N)
    (b : X → M) (cb : Continuous b) (inside : ∀ y, b y ∈ Λ)
    (S : ∀ y, Submodule ℝ (TangentSpace (𝓘(ℝ, E)) (b y)))
    (A : ∀ y, H ≃L[ℝ] S y)
    (sections : ∀ v : H, Continuous
      (fun y => (⟨b y, (A y v).val⟩ : TangentBundle (𝓘(ℝ, E)) M))) :
    ∃ e : ∀ y, Fin (Module.finrank ℝ H) → TangentSpace (𝓘(ℝ, E)) (b y),
      (∀ i, Continuous (fun y => (⟨b y, e y i⟩ : TangentBundle (𝓘(ℝ, E)) M))) ∧
      (∀ y i, e y i ∈ S y) ∧
      (∀ y i j, splitForm T T.symm h.projection a N (b y) (e y i) (e y j) =
        if i = j then 1 else 0) ∧
      (∀ y, ∀ v ∈ S y, ∃ c : Fin (Module.finrank ℝ H) → ℝ,
        v = ∑ i, c i • e y i) := by
  classical
  let g := splitForm T T.symm h.projection a N
  let G := adaptedMetric T T.symm h.projection a N length
  have formContinuous := (HyperbolicAdaptedForms.HyperbolicData.continuousOn_splitForm h forward backward a N).comp_continuous
    cb (fun y => inside y)
  have gramContinuous : Continuous (fun y => fun i j : Fin (Module.finrank ℝ H) =>
      g (b y) (A y (stdOrthonormalBasis ℝ H i)).val
        (A y (stdOrthonormalBasis ℝ H j)).val) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    have total := formContinuous.clm_bundle_apply₂ (𝕜 := ℝ) (F₃ := ℝ)
      (E₃ := Bundle.Trivial M ℝ)
      (sections (stdOrthonormalBasis ℝ H i)) (sections (stdOrthonormalBasis ℝ H j))
    rw [continuous_iff_continuousAt]
    intro y
    have atPoint := total.continuousAt (x := y)
    rw [FiberBundle.continuousAt_totalSpace] at atPoint
    exact atPoint.2
  let : RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x) := ⟨G⟩
  let A' : ∀ y, H ≃L[ℝ] S y := A
  let B := fun y => GramNormalizedBasis.basis (V := S y) (A' y)
  have actualGram : Continuous (fun y => GramNormalizedBasis.gram (A' y)) := by
    exact gramContinuous
  have continuousBasis := ContinuousSubspaceFrameNormalization.continuous_basis_of_gram
    (fun x : M => TangentSpace (𝓘(ℝ, E)) x) b cb S A' sections actualGram
  refine ⟨fun y i => (B y i).val, continuousBasis, fun y i => (B y i).property, ?_, ?_⟩
  · intro y i j
    exact orthonormal_iff_ite.mp (B y).orthonormal i j
  · intro y v hv
    refine ⟨fun i => (B y).toBasis.repr ⟨v, hv⟩ i, ?_⟩
    have identity := (B y).toBasis.sum_repr ⟨v, hv⟩
    simpa using (congrArg Subtype.val identity).symm

/-- The ordinary continuous local unstable frames are normalized in the
actual adapted inner product. These are local families, not a global choice. -/
theorem exists_unstable (h : HyperbolicBasicSet.HyperbolicData (E := E) T Λ)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    (a : ℝ) (N : ℕ) (length : 0 < N) (x : M) (hx : x ∈ Λ) :
    ∃ O : Set M, IsOpen O ∧ x ∈ O ∧
      ∃ e : ∀ y : ↥(Λ ∩ O), Fin (Module.finrank ℝ (h.unstable x)) →
        TangentSpace (𝓘(ℝ, E)) y.val,
        (∀ i, Continuous (fun y => (⟨y.val, e y i⟩ : TangentBundle (𝓘(ℝ, E)) M))) ∧
        (∀ y i, e y i ∈ h.unstable y.val) ∧
        (∀ y i j, splitForm T T.symm h.projection a N y.val (e y i) (e y j) =
          if i = j then 1 else 0) ∧
        (∀ y, ∀ v ∈ h.unstable y.val,
          ∃ c : Fin (Module.finrank ℝ (h.unstable x)) → ℝ, v = ∑ i, c i • e y i) := by
  obtain ⟨O, openO, member, A, sections⟩ := h.exists_continuous_unstable_frames x hx
  obtain ⟨e, ce, belongs, ortho, spans⟩ := normalized_family h forward backward a N length
    (Subtype.val : ↥(Λ ∩ O) → M) continuous_subtype_val (fun y => y.property.1)
    (fun y => h.unstable y.val) A sections
  exact ⟨O, openO, member, e, ce, belongs, ortho, spans⟩

/-- The ordinary continuous local stable frames are normalized in the
actual adapted inner product. These are local families, not a global choice. -/
theorem exists_stable (h : HyperbolicBasicSet.HyperbolicData (E := E) T Λ)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    (a : ℝ) (N : ℕ) (length : 0 < N) (x : M) (hx : x ∈ Λ) :
    ∃ O : Set M, IsOpen O ∧ x ∈ O ∧
      ∃ e : ∀ y : ↥(Λ ∩ O), Fin (Module.finrank ℝ (h.stable x)) →
        TangentSpace (𝓘(ℝ, E)) y.val,
        (∀ i, Continuous (fun y => (⟨y.val, e y i⟩ : TangentBundle (𝓘(ℝ, E)) M))) ∧
        (∀ y i, e y i ∈ h.stable y.val) ∧
        (∀ y i j, splitForm T T.symm h.projection a N y.val (e y i) (e y j) =
          if i = j then 1 else 0) ∧
        (∀ y, ∀ v ∈ h.stable y.val,
          ∃ c : Fin (Module.finrank ℝ (h.stable x)) → ℝ, v = ∑ i, c i • e y i) := by
  let reversed := h.reversed (forward.mdifferentiable one_ne_zero)
    (backward.mdifferentiable one_ne_zero)
  obtain ⟨O, openO, member, A, sections⟩ := reversed.exists_continuous_unstable_frames x hx
  change (∀ y : ↥(Λ ∩ O), h.stable x ≃L[ℝ] h.stable y.val) at A
  change (∀ v : h.stable x, Continuous (fun y : ↥(Λ ∩ O) =>
    (⟨y.val, (A y v).val⟩ : TangentBundle (𝓘(ℝ, E)) M))) at sections
  obtain ⟨e, ce, belongs, ortho, spans⟩ := normalized_family h forward backward a N length
    (Subtype.val : ↥(Λ ∩ O) → M) continuous_subtype_val (fun y => y.property.1)
    (fun y => h.stable y.val) A sections
  exact ⟨O, openO, member, e, ce, belongs, ortho, spans⟩

end LeanShared.HyperbolicAdaptedLocalFrames
