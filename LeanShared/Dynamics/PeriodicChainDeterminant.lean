module
public import LeanShared.Dynamics.PeriodicChainDynamics
public import LeanShared.Dynamics.HyperbolicPeriodicDenominatorBounds

/-! The Lefschetz determinant of a periodic chart chain is the literal periodic
denominator. The framed block products telescope to `frame⁻¹ ∘ D(H^m) ∘ frame` at the
periodic point, and the determinant of `1 - P` is invariant under this conjugation. For
`H = T^N` it is the periodic denominator of `T` with period `N m`. -/
public noncomputable section
set_option linter.unusedSectionVars false
open Set IsManifold Bundle Metric
open scoped Manifold ContDiff Topology NNReal
open LeanShared.HyperbolicBasicSet LeanShared.PeriodicChartConstants
namespace LeanShared.PeriodicChartChains

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace M] [CompactSpace M] [ChartedSpace E M] [IsManifold (𝓘(ℝ, E)) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace (𝓘(ℝ, E)) x)]
  {T : M ≃ₜ M} {Λ : Set M} {h : HyperbolicData (E := E) T Λ}
  {a : IsometricFraming h} {F : ChartFamily E M} {H : M → M} {lam : ℝ} {p : Λ} {m : ℕ} {i : F.ι}

namespace PeriodicChain

variable (pc : PeriodicChain a F H lam p m i)

theorem point_val (j : ℕ) : (pc.point j).val = H^[j] p.val := by
  induction j with
  | zero => rw [Nat.cast_zero, pc.point_zero]; rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ← ih, pc.point_step j]
    push_cast
    rfl

theorem prodFrom_framed (Hsmooth : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) H) (j : ℕ) :
    CyclicHyperbolicDeterminant.prodFrom
      (fun k => (pc.chain.A k : EuclideanSpace ℝ (Fin a.unstableDimension) →L[ℝ] _).prodMap
        (pc.chain.B k)) 0 j =
      (a.whole (pc.point j)).symm.toContinuousLinearMap.comp
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (H^[j]) p.val).comp (a.whole p).toContinuousLinearMap) := by
  induction j with
  | zero =>
    rw [CyclicHyperbolicDeterminant.prodFrom_zero]
    have p0 : pc.point ((0 : ℕ) : ℤ) = p := by rw [Nat.cast_zero]; exact pc.point_zero
    rw [p0, Function.iterate_zero, mfderiv_id]
    apply ContinuousLinearMap.ext
    intro v
    simp
  | succ j ih =>
    rw [CyclicHyperbolicDeterminant.prodFrom_succ, ih, zero_add, pc.framed j]
    have chain : mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (H^[j + 1]) p.val =
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H (H^[j] p.val)).comp
          (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (H^[j]) p.val) := by
      rw [Function.iterate_succ']
      exact mfderiv_comp p.val (Hsmooth _) (DiffeomorphismIterates.mdifferentiable_iterate H Hsmooth j _)
    rw [chain, ← pc.point_val j]
    have cast : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
    rw [cast]
    apply ContinuousLinearMap.ext
    intro v
    change (a.whole (pc.point ((j : ℤ) + 1))).symm (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) H (pc.point j).val
      (a.whole (pc.point j) ((a.whole (pc.point j)).symm
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (H^[j]) p.val (a.whole p v))))) = _
    erw [ContinuousLinearEquiv.apply_symm_apply]
    rfl

/-- The base Lefschetz determinant of the chain is that of `D(H^m)` at the periodic point. -/
theorem det_eq (Hsmooth : MDifferentiable (𝓘(ℝ, E)) (𝓘(ℝ, E)) H)
    (X : TangentSpace (𝓘(ℝ, E)) p.val →L[ℝ] TangentSpace (𝓘(ℝ, E)) p.val)
    (hX : ∀ v, X v = mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (H^[m]) p.val v) :
    LinearMap.det ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin a.unstableDimension) ×
        EuclideanSpace ℝ (Fin a.stableDimension)) - CyclicHyperbolicDeterminant.prodFrom
      (fun k => (pc.chain.A k : EuclideanSpace ℝ (Fin a.unstableDimension) →L[ℝ] _).prodMap
        (pc.chain.B k)) 0 m) :
        (EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension)) →ₗ[ℝ] _) =
    LinearMap.det ((ContinuousLinearMap.id ℝ (TangentSpace (𝓘(ℝ, E)) p.val) - X) :
      TangentSpace (𝓘(ℝ, E)) p.val →ₗ[ℝ] TangentSpace (𝓘(ℝ, E)) p.val) := by
  have pm : pc.point (m : ℤ) = p := by
    have := pc.periodic_point 0
    rwa [zero_add, pc.point_zero] at this
  rw [pc.prodFrom_framed Hsmooth m, pm]
  set W := a.whole p
  have conj : ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin a.unstableDimension) ×
      EuclideanSpace ℝ (Fin a.stableDimension)) - W.symm.toContinuousLinearMap.comp
      ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (H^[m]) p.val).comp W.toContinuousLinearMap)) :
        (EuclideanSpace ℝ (Fin a.unstableDimension) × EuclideanSpace ℝ (Fin a.stableDimension)) →ₗ[ℝ] _) =
      W.symm.toLinearEquiv.toLinearMap ∘ₗ
        (((ContinuousLinearMap.id ℝ (TangentSpace (𝓘(ℝ, E)) p.val) - X) :
          TangentSpace (𝓘(ℝ, E)) p.val →ₗ[ℝ] TangentSpace (𝓘(ℝ, E)) p.val) ∘ₗ
          W.symm.toLinearEquiv.symm.toLinearMap) := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    change v - W.symm (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) (H^[m]) p.val (W v)) =
      W.symm (W v - X (W v))
    rw [map_sub, ContinuousLinearEquiv.symm_apply_apply, hX]
  rw [conj, LinearMap.det_conj]

end PeriodicChain
end LeanShared.PeriodicChartChains
