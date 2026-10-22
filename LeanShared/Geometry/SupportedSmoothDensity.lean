module

public import LeanShared.Geometry.SupportedCorePhysicalRealization
public import LeanShared.Geometry.SmoothWeightCutoff
public import Mathlib.Geometry.Manifold.SmoothApprox
public import Mathlib.Topology.TietzeExtension

/-! Supported smooth functions approximate the literal continuous live functions.
The extension and support control are constructed, rather than supplied as a
density axiom to the spectral source packet. -/

@[expose] public noncomputable section
open Set Function
open scoped Manifold ContDiff Topology BoundedContinuousFunction
namespace LeanShared.SmoothSupportedManifoldCore

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  {V K : Set M} [CompactSpace K]

include E in
/-- A literal live function supported inside the open collar has a continuous
ambient extension supported in that same collar. -/
theorem exists_supported_extension (hK : IsClosed K) (hV : IsOpen V)
    (f : K →ᵇ ℂ) (hf : tsupport f ⊆ {x : K | x.val ∈ V}) :
    ∃ F : C(M, ℂ), (∀ x : K, F x.val = f x) ∧ tsupport F ⊆ V := by
  let fr : C(K, ℝ) := ⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩
  let fi : C(K, ℝ) := ⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩
  obtain ⟨gr, hgr⟩ := fr.exists_restrict_eq hK
  obtain ⟨gi, hgi⟩ := fi.exists_restrict_eq hK
  let g : C(M, ℂ) := ⟨fun x => (gr x : ℂ) + (gi x : ℂ) * Complex.I, by fun_prop⟩
  have hg (x : K) : g x.val = f x := by
    have hr := congrArg (fun q : C(K, ℝ) => q x) hgr
    have hi := congrArg (fun q : C(K, ℝ) => q x) hgi
    change gr x.val = (f x).re at hr
    change gi x.val = (f x).im at hi
    change (gr x.val : ℂ) + (gi x.val : ℂ) * Complex.I = f x
    rw [hr, hi, Complex.re_add_im]
  have hS : IsCompact ((Subtype.val : K → M) '' tsupport f) :=
    (isClosed_tsupport f).isCompact.image continuous_subtype_val
  obtain ⟨ζ, hζ, _, hζsupp, hζone⟩ :=
    SmoothWeightCutoff.exists_cutoff (E := E)
      ((Subtype.val : K → M) '' tsupport f) V hS hV (by
        rintro _ ⟨x, hx, rfl⟩
        exact hf hx)
  refine ⟨⟨fun x => (ζ x : ℂ) * g x,
    (Complex.continuous_ofReal.comp hζ.continuous).mul g.continuous⟩, ?_, ?_⟩
  · intro x
    change (ζ x.val : ℂ) * g x.val = f x
    rw [hg]
    by_cases hx : f x = 0
    · simp [hx]
    · rw [hζone x.val ⟨x, subset_tsupport f hx, rfl⟩]
      simp
  · apply tsupport_mul_subset_left.trans
    apply (closure_mono ?_).trans hζsupp
    intro x hx
    change (ζ x : ℂ) ≠ 0 at hx
    exact fun hz => hx (by simp [hz])

/-- The support-qualified C0 density used by the invariant-core construction.
It does not assert density in a big Hölder norm or approximation of arbitrary
boundary values by functions supported strictly inside the collar. -/
theorem physicalCore_supported_dense (hK : IsClosed K) (hV : IsOpen V)
    (f : K →ᵇ ℂ) (hf : tsupport f ⊆ {x : K | x.val ∈ V}) :
    f ∈ closure (range (physicalCore (E := E) V K)) := by
  obtain ⟨F, hF, hFsupp⟩ := exists_supported_extension (E := E) hK hV f hf
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨g, happrox, hgsupp⟩ := F.continuous.exists_contMDiff_approx
    (𝓘(ℝ, E)) (⊤ : ℕ∞) (ε := fun _ => ε / 2) continuous_const (fun _ => half_pos hε)
  let c : core (E := E) V := ⟨g, g.contMDiff, (closure_mono hgsupp).trans hFsupp⟩
  refine ⟨physicalCore V K c, mem_range_self c, ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt ((BoundedContinuousFunction.norm_le (le_of_lt (half_pos hε))).mpr ?_)
    (half_lt_self hε)
  intro x
  change ‖f x - g x.val‖ ≤ ε / 2
  rw [← hF x, ← dist_eq_norm, dist_comm]
  exact (happrox x.val).le

end LeanShared.SmoothSupportedManifoldCore
