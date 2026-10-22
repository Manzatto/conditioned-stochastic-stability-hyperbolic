module
public import LeanShared.Geometry.ContinuousBundleFiniteSum
public import LeanShared.Geometry.ContinuousBundleScalarMul
public import Mathlib.Topology.VectorBundle.Riemannian
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.FiniteDimension

public noncomputable section
namespace LeanShared.BundleOrthonormalCoordinates
open Set Bundle Filter
open scoped BigOperators Topology
variable {B F X ι : Type*} [TopologicalSpace B] [TopologicalSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (E : B → Type*) [∀ b, NormedAddCommGroup (E b)] [∀ b, InnerProductSpace ℝ (E b)]
  [TopologicalSpace (TotalSpace F E)] [FiberBundle F E] [VectorBundle ℝ F E]

variable [Fintype ι] [∀ b, FiniteDimensional ℝ (E b)] [IsContinuousRiemannianBundle F E]

@[expose] def coordinates (D : Set B) (basis : ∀ b : D, OrthonormalBasis ι ℝ (E b.val))
    (P : ∀ b, E b →L[ℝ] E b) (b : D) : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  (basis b).repr.conjStarAlgEquiv (P b.val)

omit [∀ b, FiniteDimensional ℝ (E b)] [IsContinuousRiemannianBundle F E] in
theorem continuous_section (b : X → B) (basis : ∀ x, OrthonormalBasis ι ℝ (E (b x)))
    (sections : ∀ i, Continuous (fun x => (⟨b x,basis x i⟩ : TotalSpace F E)))
    (coeff : X → EuclideanSpace ℝ ι) (hcoeff : Continuous coeff) (hb : Continuous b) :
    Continuous (fun x => (⟨b x,(basis x).repr.symm (coeff x)⟩ : TotalSpace F E)) := by
  have individual (i : ι) : Continuous
      (fun x => (⟨b x,coeff x i • basis x i⟩ : TotalSpace F E)) :=
    ContinuousBundleScalarMul.continuous E b (fun x => basis x i) (fun x => coeff x i)
      (sections i) ((PiLp.continuous_apply 2 _ i).comp hcoeff)
  have total := ContinuousBundleFiniteSum.continuous E Finset.univ b
    (fun i x => coeff x i • basis x i) hb (fun i _ => individual i)
  apply total.congr
  intro x
  congr 1
  exact (basis x).sum_repr_symm (coeff x)

theorem continuous_coordinates (D : Set B)
    (basis : ∀ b : D, OrthonormalBasis ι ℝ (E b.val))
    (sections : ∀ i, Continuous (fun b : D => (⟨b.val,basis b i⟩ : TotalSpace F E)))
    (P : ∀ b, E b →L[ℝ] E b)
    (action : ContinuousOn
      (fun v : TotalSpace F E => (⟨v.proj,P v.proj v.2⟩ : TotalSpace F E))
      {v | v.proj ∈ D}) : Continuous (coordinates E D basis P) := by
  apply continuous_clm_apply.mpr
  intro v
  have input := continuous_section E (fun b : D => b.val) basis sections
    (fun _ => v) continuous_const continuous_subtype_val
  have output := action.comp_continuous input (fun b => b.property)
  have coefficients : Continuous (fun b : D => fun i : ι => inner ℝ (basis b i) (P b.val ((basis b).repr.symm v))) :=
    continuous_pi (fun i => (sections i).inner_bundle output)
  have actual := (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).comp coefficients
  apply actual.congr
  intro b
  apply PiLp.ext
  intro i
  exact ((basis b).repr_apply_apply _ i).symm
theorem continuous_action_of_coordinates (D : Set B)
    (basis : ∀ b : D, OrthonormalBasis ι ℝ (E b.val))
    (sections : ∀ i, Continuous (fun b : D => (⟨b.val,basis b i⟩ : TotalSpace F E)))
    (P : ∀ b, E b →L[ℝ] E b)
    (hcoords : Continuous (coordinates E D basis P)) :
    ContinuousOn (fun v : TotalSpace F E =>
      (⟨v.proj,P v.proj v.2⟩ : TotalSpace F E)) {v | v.proj ∈ D} := by
  let S := {v : TotalSpace F E | v.proj ∈ D}
  let b : S → D := fun v => ⟨v.val.proj,v.property⟩
  have hb : Continuous b :=
    ((FiberBundle.continuous_proj F E).comp continuous_subtype_val).subtype_mk _
  have hsections (i : ι) : Continuous
      (fun v : S => (⟨v.val.proj,basis (b v) i⟩ : TotalSpace F E)) :=
    (sections i).comp hb
  have hc : Continuous (fun v : S => (basis (b v)).repr v.val.2) := by
    have ci : Continuous (fun v : S => fun i : ι => inner ℝ (basis (b v) i) v.val.2) :=
      continuous_pi (fun i => (hsections i).inner_bundle continuous_subtype_val)
    have actual := (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).comp ci
    apply actual.congr
    intro v
    apply PiLp.ext
    intro i
    exact ((basis (b v)).repr_apply_apply _ i).symm
  have output := continuous_section E (fun v : S => v.val.proj)
    (fun v => basis (b v)) hsections
    (fun v => coordinates E D basis P (b v) ((basis (b v)).repr v.val.2))
    ((hcoords.comp hb).clm_apply hc)
    ((FiberBundle.continuous_proj F E).comp continuous_subtype_val)
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply output.congr
  intro v
  congr 1
  simp only [coordinates,LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_apply_apply]
  rfl

end LeanShared.BundleOrthonormalCoordinates
