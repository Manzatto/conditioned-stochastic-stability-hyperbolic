module

public import LeanShared.Geometry.SmoothSupportedManifoldCore
public import LeanShared.Geometry.ConstructedManifoldLocalization
public import LeanShared.Analysis.RealEvenLeafNorm

/-! Complex conjugation on the literal supported manifold core and its
actual chart coordinates. Real cutoffs are an ordinary partition property. -/

@[expose] public noncomputable section
open Set IsManifold
open scoped Manifold ContDiff ComplexConjugate SchwartzMap

namespace LeanShared.SmoothSupportedManifoldCore
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] (V : Set M)

def conjugate : core (E := E) V →ₗ[ℝ] core (E := E) V where
  toFun f := ⟨fun x => conj (f.val x),
    Complex.conjCLE.toContinuousLinearMap.contMDiff.comp f.property.1,
    (tsupport_comp_subset (map_zero Complex.conjCLE) f.val).trans f.property.2⟩
  map_add' f g := by ext x; exact map_add _ _ _
  map_smul' r f := by ext x; exact map_smul Complex.conjCLE r (f.val x)

@[simp] theorem conjugate_apply (f : core (E := E) V) (x : M) :
    (conjugate V f).val x = conj (f.val x) := rfl

theorem conjugate_involutive : Function.Involutive (conjugate (E := E) V) := by
  intro f
  ext x
  exact Complex.conj_conj _

theorem conjugate_smul (z : ℂ) (f : core (E := E) V) :
    conjugate V (z • f) = conj z • conjugate V f := by
  ext x
  exact map_mul _ _ _

end LeanShared.SmoothSupportedManifoldCore

namespace LeanShared.ConstructedManifoldLocalization
variable {E M J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M]
  (e : J → OpenPartialHomeomorph M E) {S : Set M} (D : Data e S)
  (he : ∀ j, e j ∈ maximalAtlas (𝓘(ℝ, E)) ∞ M) (V : Set M)

/-- Taking real parts of the constructed complex partition produces real
cutoffs on the same genuine charts, with the same reconstruction region. -/
def realData : Data e S where
  indices := D.indices
  cutoff i x := Complex.ofRealCLM (Complex.reCLM (D.cutoff i x))
  smooth i := Complex.ofRealCLM.contMDiff.comp (Complex.reCLM.contMDiff.comp (D.smooth i))
  support i := (tsupport_comp_subset
    (map_zero (Complex.ofRealCLM.comp Complex.reCLM)) (D.cutoff i)).trans (D.support i)
  compact i := HasCompactSupport.of_compactSpace _
  partition x hx := by
    have h := congrArg (Complex.ofRealCLM.comp Complex.reCLM) (D.partition x hx)
    simpa only [map_sum, ContinuousLinearMap.comp_apply, Complex.reCLM_apply,
      Complex.ofRealCLM_apply, Complex.one_re, Complex.ofReal_one] using h

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] in
theorem realData_cutoff_real (i : (realData e D).indices) (x : M) :
    conj ((realData e D).cutoff i x) = (realData e D).cutoff i x := by
  exact Complex.conj_ofReal _

omit [FiniteDimensional ℝ E] [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [CompactSpace M] in
theorem localize_conjugate (hreal : ∀ i x, conj (D.cutoff i x) = D.cutoff i x)
    (i : D.indices) (f : SmoothSupportedManifoldCore.core (E := E) V) :
    localize e D he (SmoothSupportedManifoldCore.functions V)
      (SmoothSupportedManifoldCore.smooth V) i
      (SmoothSupportedManifoldCore.conjugate V f) =
    RealEvenFourierBlocks.supportedConjugate
      (localize e D he (SmoothSupportedManifoldCore.functions V)
        (SmoothSupportedManifoldCore.smooth V) i f) := by
  apply Subtype.ext
  apply SchwartzMap.ext
  intro y
  change ChartLocalization.coordinate (e i) (D.cutoff i) (fun x => conj (f.val x)) y =
    conj (ChartLocalization.coordinate (e i) (D.cutoff i) f.val y)
  simp only [ChartLocalization.coordinate]
  split_ifs <;> simp only [map_mul, hreal, map_zero]

end LeanShared.ConstructedManifoldLocalization
