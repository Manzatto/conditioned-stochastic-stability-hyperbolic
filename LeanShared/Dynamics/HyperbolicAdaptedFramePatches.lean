module
public import LeanShared.Dynamics.HyperbolicAdaptedLocalFrames
public import LeanShared.Dynamics.HyperbolicIsometricFraming
public import LeanShared.Topology.FiniteCompactNeighborhoodCover

/-! Local adapted frames with the single stable/unstable dimensions of the
actual basic set, prepared for a finite compact patch cover. -/
public noncomputable section
open Set IsManifold Bundle
open scoped Manifold ContDiff BigOperators
namespace LeanShared.HyperbolicAdaptedFramePatches
open HyperbolicAdaptedForms HyperbolicBasicSet
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M}

structure LocalFrame (h : HyperbolicData (E := E) T Λ)
    (S : ∀ x : M, Submodule ℝ (TangentSpace (𝓘(ℝ, E)) x)) (d : ℕ)
    (a : ℝ) (N : ℕ) (x : Λ) where
  neighborhood : Set M
  open_neighborhood : IsOpen neighborhood
  center_mem : x.val ∈ neighborhood
  vector : ∀ y : ↥(Λ ∩ neighborhood), Fin d → TangentSpace (𝓘(ℝ, E)) y.val
  continuous : ∀ i, Continuous (fun y => (⟨y.val, vector y i⟩ : TangentBundle (𝓘(ℝ, E)) M))
  member : ∀ y i, vector y i ∈ S y.val
  orthonormal : ∀ y i j, splitForm T T.symm h.projection a N y.val (vector y i) (vector y j) =
    if i = j then 1 else 0
  spans : ∀ y, ∀ v ∈ S y.val, ∃ c : Fin d → ℝ, v = ∑ i, c i • vector y i

@[expose] def LocalFrame.reindex {h : HyperbolicData (E := E) T Λ}
    {S : ∀ x : M, Submodule ℝ (TangentSpace (𝓘(ℝ, E)) x)} {d d' : ℕ}
    {a : ℝ} {N : ℕ} {x : Λ} (F : LocalFrame h S d a N x) (equal : d = d') :
    LocalFrame h S d' a N x := by
  classical
  let index : Fin d' ≃ Fin d := finCongr equal.symm
  refine {
    neighborhood := F.neighborhood
    open_neighborhood := F.open_neighborhood
    center_mem := F.center_mem
    vector := fun y i => F.vector y (index i)
    continuous := fun i => F.continuous (index i)
    member := fun y i => F.member y (index i)
    orthonormal := ?_
    spans := ?_ }
  · intro y i j
    simpa only [Equiv.apply_eq_iff_eq] using F.orthonormal y (index i) (index j)
  · intro y v hv
    obtain ⟨c, identity⟩ := F.spans y v hv
    refine ⟨fun i => c (index i), ?_⟩
    rw [identity]
    exact (index.sum_comp (fun i => c i • F.vector y i)).symm

theorem unstable_frame (h : HyperbolicData (E := E) T Λ) (frames : IsometricFraming h)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    (a : ℝ) (N : ℕ) (length : 0 < N) (x : Λ) :
    Nonempty (LocalFrame h h.unstable frames.unstableDimension a N x) := by
  obtain ⟨O, openO, member, e, ce, belongs, ortho, spans⟩ :=
    HyperbolicAdaptedLocalFrames.exists_unstable h forward backward a N length x.val x.property
  let F : LocalFrame h h.unstable (Module.finrank ℝ (h.unstable x.val)) a N x :=
    ⟨O, openO, member, e, ce, belongs, ortho, spans⟩
  have dimensions : Module.finrank ℝ (h.unstable x.val) = frames.unstableDimension := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using (frames.unstable x).toLinearEquiv.finrank_eq.symm
  exact ⟨F.reindex dimensions⟩

theorem stable_frame (h : HyperbolicData (E := E) T Λ) (frames : IsometricFraming h)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    (a : ℝ) (N : ℕ) (length : 0 < N) (x : Λ) :
    Nonempty (LocalFrame h h.stable frames.stableDimension a N x) := by
  obtain ⟨O, openO, member, e, ce, belongs, ortho, spans⟩ :=
    HyperbolicAdaptedLocalFrames.exists_stable h forward backward a N length x.val x.property
  let F : LocalFrame h h.stable (Module.finrank ℝ (h.stable x.val)) a N x :=
    ⟨O, openO, member, e, ce, belongs, ortho, spans⟩
  have dimensions : Module.finrank ℝ (h.stable x.val) = frames.stableDimension := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using (frames.stable x).toLinearEquiv.finrank_eq.symm
  exact ⟨F.reindex dimensions⟩

/-- Finitely many compact smaller patches cover the actual core. Their
stable and unstable local frames use one common pair of dimensions and the
same already selected adapted time. No ambient compactness is required. -/
theorem compact_cover (h : HyperbolicData (E := E) T Λ) (frames : IsometricFraming h)
    (forward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T : M → M))
    (backward : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) 1 (T.symm : M → M))
    (a : ℝ) (N : ℕ) (length : 0 < N) :
    ∃ Fs : ∀ x : Λ, LocalFrame h h.stable frames.stableDimension a N x,
    ∃ Fu : ∀ x : Λ, LocalFrame h h.unstable frames.unstableDimension a N x,
    ∃ centers : Finset Λ, ∃ patch : Λ → Set Λ,
      (∀ x, IsCompact (patch x) ∧
        (∀ y ∈ patch x, y.val ∈ (Fs x).neighborhood ∧ y.val ∈ (Fu x).neighborhood) ∧
        x ∈ interior (patch x)) ∧
      (univ : Set Λ) ⊆ ⋃ x ∈ centers, interior (patch x) := by
  classical
  let Fs := fun x : Λ => Classical.choice (stable_frame h frames forward backward a N length x)
  let Fu := fun x : Λ => Classical.choice (unstable_frame h frames forward backward a N length x)
  let U : Λ → Set Λ := fun x => Subtype.val ⁻¹' ((Fs x).neighborhood ∩ (Fu x).neighborhood)
  have openU : ∀ x, IsOpen (U x) := fun x =>
    ((Fs x).open_neighborhood.inter (Fu x).open_neighborhood).preimage continuous_subtype_val
  have memberU : ∀ x : Λ, x ∈ U x := fun x => ⟨(Fs x).center_mem, (Fu x).center_mem⟩
  let : CompactSpace Λ := isCompact_iff_compactSpace.mp h.compact
  obtain ⟨centers, patch, properties, covers⟩ := FiniteCompactNeighborhoodCover.exists_cover
    (univ : Set Λ) isCompact_univ U openU (fun x _ => memberU x)
  refine ⟨Fs, Fu, centers.image Subtype.val, (fun x => patch ⟨x, mem_univ x⟩),
    (fun x => properties ⟨x, mem_univ x⟩), ?_⟩
  intro y hy
  obtain ⟨x, hx⟩ := mem_iUnion.mp (covers hy)
  obtain ⟨hx, member⟩ := mem_iUnion.mp hx
  refine mem_iUnion.mpr ⟨x.val, mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩⟩
  exact member

end LeanShared.HyperbolicAdaptedFramePatches
