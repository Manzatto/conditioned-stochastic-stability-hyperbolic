module

public import LeanShared.Geometry.ConstructedManifoldLocalization

/-! Real smooth chart cutoffs can be chosen without an additional geometric assumption. Taking the
real part of any genuine complex partition preserves its support and sum. The reality proof
belongs to this new construction; it is not asserted for an arbitrary chosen partition. -/

@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff ComplexConjugate BigOperators
namespace LeanShared.RealManifoldLocalization

variable {E M J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  {e : J → OpenPartialHomeomorph M E} {S : Set M}

/-- The real-linear projection onto the real axis. -/
def realPart : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM

@[simp] theorem realPart_apply (z : ℂ) : realPart z = (z.re : ℂ) := rfl

/-- A genuine subordinate smooth partition with proved real cutoffs. -/
def realify (d : ConstructedManifoldLocalization.Data e S) :
    ConstructedManifoldLocalization.Data e S where
  indices := d.indices
  cutoff i x := realPart (d.cutoff i x)
  smooth i := realPart.contMDiff.comp (d.smooth i)
  support i := (tsupport_comp_subset (map_zero realPart) (d.cutoff i)).trans (d.support i)
  compact i := HasCompactSupport.of_compactSpace _
  partition x hx := by
    have h := congrArg realPart (d.partition x hx)
    simpa only [map_sum, realPart_apply, Complex.one_re, Complex.ofReal_one] using h

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] in
@[simp] theorem cutoff_real (d : ConstructedManifoldLocalization.Data e S)
    (i : (realify d).indices) (x : M) :
    conj ((realify d).cutoff i x) = (realify d).cutoff i x := by
  change conj ((d.cutoff i x).re : ℂ) = ((d.cutoff i x).re : ℂ)
  simp

/-- Compactness and an adapted genuine chart cover produce a partition
whose conjugation compatibility is a theorem of the chosen construction. -/
def data (hS : IsCompact S) (cover : S ⊆ ⋃ j, (e j).source) :
    ConstructedManifoldLocalization.Data e S :=
  realify (ConstructedManifoldLocalization.data e hS cover)

@[simp] theorem data_cutoff_real (hS : IsCompact S) (cover : S ⊆ ⋃ j, (e j).source)
    (i : (data hS cover).indices) (x : M) :
    conj ((data hS cover).cutoff i x) = (data hS cover).cutoff i x :=
  cutoff_real _ i x

end LeanShared.RealManifoldLocalization
