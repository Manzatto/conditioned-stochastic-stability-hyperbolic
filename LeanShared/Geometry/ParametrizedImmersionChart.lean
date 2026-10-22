module
public import LeanShared.Geometry.EmbeddedSubmanifoldVolume
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! A genuine open graph coordinate and smooth parametrization/retraction
construct an embedded manifold structure and its injective differential. -/
public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff
namespace LeanShared.ParametrizedImmersionChart
variable {U E : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_chart (Γ : Set E) [Nonempty Γ] (p : Γ → U) (openEmbedding : Topology.IsOpenEmbedding p)
    (g : U → E) (smooth : ContDiffOn ℝ 1 g (range p))
    (parametrization : ∀ x : Γ, g (p x) = x.val)
    (R : E → U) (retraction : ∀ x : Γ, R x.val = p x)
    (regular : ∀ x ∈ Γ, ContDiffAt ℝ 1 R x) :
    ∃ atlas : ChartedSpace U Γ, letI := atlas
      IsManifold (𝓘(ℝ, U)) 1 Γ ∧
      ContMDiff (𝓘(ℝ, U)) (𝓘(ℝ, E)) 1 (Subtype.val : Γ → E) ∧
      ∀ x : Γ, Function.Injective
        (mfderiv (𝓘(ℝ, U)) (𝓘(ℝ, E)) (Subtype.val : Γ → E) x) := by
  let atlas := openEmbedding.singletonChartedSpace
  let : ChartedSpace U Γ := atlas
  let : IsManifold (𝓘(ℝ, U)) 1 Γ := openEmbedding.isManifold_singleton
  have pSmooth : ContMDiff (𝓘(ℝ, U)) (𝓘(ℝ, U)) 1 p :=
    contMDiff_isOpenEmbedding openEmbedding
  have includeSmooth : ContMDiff (𝓘(ℝ, U)) (𝓘(ℝ, E)) 1
      (Subtype.val : Γ → E) := by
    have eq : (Subtype.val : Γ → E) = g ∘ p := funext (fun x => (parametrization x).symm)
    rw [eq]
    intro x
    exact ((smooth.contDiffAt (openEmbedding.isOpen_range.mem_nhds ⟨x, rfl⟩)).contMDiffAt).comp x
      (pSmooth.contMDiffAt (x := x))
  refine ⟨atlas, inferInstance, includeSmooth, fun x => ?_⟩
  have Rregular : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, U)) 1 R x.val :=
    (regular x.val x.property).contMDiffAt
  have chain := mfderiv_comp x (Rregular.mdifferentiableAt (by decide))
    (includeSmooth.mdifferentiable (by decide) x)
  have identity : R ∘ (Subtype.val : Γ → E) = p := funext retraction
  rw [identity] at chain
  let e := openEmbedding.toOpenPartialHomeomorph p
  have mem : e ∈ maximalAtlas (𝓘(ℝ, U)) 1 Γ :=
    subset_maximalAtlas (I := 𝓘(ℝ, U)) (n := 1) (by change e ∈ {e}; simp)
  have invertible := isInvertible_mfderiv_extend mem
    (show x ∈ e.source by simp [e])
  have injective : Function.Injective (mfderiv (𝓘(ℝ, U)) (𝓘(ℝ, U)) p x) := by
    have same : e.extend (𝓘(ℝ, U)) = p := by ext z; rfl
    rw [same] at invertible
    obtain ⟨equiv, sameMap⟩ := invertible
    rw [← sameMap]
    exact equiv.injective
  intro v w equal
  apply injective
  rw [chain]
  exact congrArg (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, U)) R x.val) equal
end LeanShared.ParametrizedImmersionChart
