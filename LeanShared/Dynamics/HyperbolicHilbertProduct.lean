module
public import LeanShared.Dynamics.HyperbolicHilbertProductProjection

/-! Uniform hyperbolicity of the actual Hilbert-recharted product map.
The product Riemannian metric is only assumed continuous: the comparison
constants are proved uniformly on the compact product core. -/
public noncomputable section
open Set Function IsManifold Bundle
open scoped Manifold ContDiff Topology
namespace LeanShared.HyperbolicBasicSet.HilbertProduct
open HilbertProductDifferential
variable {E F X Y : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MetricSpace X] [ChartedSpace E X] [IsManifold (𝓘(ℝ,E)) ∞ X]
  [MetricSpace Y] [ChartedSpace F Y] [IsManifold (𝓘(ℝ,F)) ∞ Y]
  [RiemannianBundle (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [RiemannianBundle (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
local instance hyperbolicOldCharts : ChartedSpace (E × F) (X × Y) := prodChartedSpace E X F Y
local instance hyperbolicNewCharts : ChartedSpace (WithLp 2 (E × F)) (X × Y) :=
  LinearRechartedManifold.productCharts
local instance hyperbolicNewManifold : IsManifold (𝓘(ℝ,WithLp 2 (E × F))) ∞ (X × Y) :=
  LinearRechartedManifold.product_manifold
variable [RiemannianBundle (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)]
  {T : X ≃ₜ X} {S : Y ≃ₜ Y} {K : Set X} {L : Set Y}
  (a : HyperbolicData (E := E) T K) (b : HyperbolicData (E := F) S L)


variable
  [IsContinuousRiemannianBundle E (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle F (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
  [IsContinuousRiemannianBundle (WithLp 2 (E×F))
    (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)]

private theorem factor_bound {C D r s u v : ℝ} (hC : 0 ≤ C) (hD : C ≤ D)
    (hr : 0 ≤ r) (hrs : r ≤ s) (hu : 0 ≤ u) (huv : u ≤ v) (n : ℕ) :
    C * r^n * u ≤ D * s^n * v := by
  have hs : 0 ≤ s := hr.trans hrs
  exact mul_le_mul (mul_le_mul hD (pow_le_pow_left₀ hr hrs n) (pow_nonneg hr n)
    (hC.trans hD)) huv hu (mul_nonneg (hC.trans hD) (pow_nonneg hs n))

omit [IsContinuousRiemannianBundle E (fun x:X=>TangentSpace (𝓘(ℝ,E)) x)]
  [IsContinuousRiemannianBundle F (fun y:Y=>TangentSpace (𝓘(ℝ,F)) y)]
  [IsContinuousRiemannianBundle (WithLp 2 (E×F))
    (fun z:X×Y=>TangentSpace (𝓘(ℝ,WithLp 2 (E×F))) z)] in
theorem actual_iterate_bound (f:X→X) (g:Y→Y)
    (hf:MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) f)
    (hg:MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) g)
    (CF CI:ℝ) (posF:0<CF)
    (boundF:∀z∈K×ˢL, ‖(tangentEquiv (E:=E) (F:=F) z).toContinuousLinearMap‖≤CF)
    (boundI:∀z∈K×ˢL, ‖(tangentEquiv (E:=E) (F:=F) z).symm.toContinuousLinearMap‖≤CI)
    (n:ℕ) (z:X×Y) (hz:z∈K×ˢL) (orbit:(f^[n] z.1,g^[n] z.2)∈K×ˢL)
    (u:TangentSpace (𝓘(ℝ,E)) z.1 × TangentSpace (𝓘(ℝ,F)) z.2)
    (hx:‖mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (f^[n]) z.1 u.1‖≤
      a.constant*a.contraction^n*‖u.1‖)
    (hy:‖mfderiv (𝓘(ℝ,F)) (𝓘(ℝ,F)) (g^[n]) z.2 u.2‖≤
      b.constant*b.contraction^n*‖u.2‖) :
    ‖mfderiv (𝓘(ℝ,WithLp 2 (E×F))) (𝓘(ℝ,WithLp 2 (E×F))) ((Prod.map f g)^[n]) z
        (tangentEquiv (E:=E) (F:=F) z u)‖ ≤
      (CF*(a.constant+b.constant)*CI) * (max a.contraction b.contraction)^n *
        ‖tangentEquiv (E:=E) (F:=F) z u‖ := by
  have posC : 0 ≤ a.constant+b.constant := add_nonneg a.constant_pos.le b.constant_pos.le
  have posR : 0 ≤ max a.contraction b.contraction := a.contraction_pos.le.trans (le_max_left _ _)
  have first := hx.trans (factor_bound a.constant_pos.le
    (le_add_of_nonneg_right b.constant_pos.le) a.contraction_pos.le (le_max_left a.contraction b.contraction)
    (norm_nonneg u.1) (norm_fst_le u) n)
  have second := hy.trans (factor_bound b.constant_pos.le
    (le_add_of_nonneg_left a.constant_pos.le) b.contraction_pos.le (le_max_right a.contraction b.contraction)
    (norm_nonneg u.2) (norm_snd_le u) n)
  have pair : ‖(mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (f^[n]) z.1 u.1,
      mfderiv (𝓘(ℝ,F)) (𝓘(ℝ,F)) (g^[n]) z.2 u.2)‖ ≤
      (a.constant+b.constant)*(max a.contraction b.contraction)^n*‖u‖ :=
    max_le first second
  have source : ‖u‖ ≤ CI*‖tangentEquiv (E:=E) (F:=F) z u‖ := by
    calc
      ‖u‖ = ‖(tangentEquiv (E:=E) (F:=F) z).symm (tangentEquiv (E:=E) (F:=F) z u)‖ := by rw [ContinuousLinearEquiv.symm_apply_apply]
      _ ≤ ‖(tangentEquiv (E:=E) (F:=F) z).symm.toContinuousLinearMap‖ * ‖tangentEquiv (E:=E) (F:=F) z u‖ :=
        (tangentEquiv (E:=E) (F:=F) z).symm.toContinuousLinearMap.le_opNorm _
      _ ≤ CI * ‖tangentEquiv (E:=E) (F:=F) z u‖ := mul_le_mul_of_nonneg_right (boundI z hz) (norm_nonneg _)
  have same : (Prod.map f g)^[n] = Prod.map (f^[n]) (g^[n]) := funext (iterate_independent f g n)
  rw [same,derivative_prodMap (f^[n]) (g^[n])
    (DiffeomorphismIterates.mdifferentiable_iterate f hf n)
    (DiffeomorphismIterates.mdifferentiable_iterate g hg n)]
  let w := (mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E)) (f^[n]) z.1 u.1,
    mfderiv (𝓘(ℝ,F)) (𝓘(ℝ,F)) (g^[n]) z.2 u.2)
  have atTarget := (tangentEquiv (E:=E) (F:=F) (f^[n] z.1,g^[n] z.2)).toContinuousLinearMap.le_opNorm w
  have estimated := atTarget.trans
    (mul_le_mul (boundF _ orbit) pair (norm_nonneg w) posF.le)
  have finalBound := estimated.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left source (mul_nonneg posC (pow_nonneg posR n))) posF.le)
  convert finalBound using 1 <;> ac_rfl

/-- The actual product tangent certificate, derived from the two factor
certificates and differentiability in both time directions. -/
@[expose] def of_factors
    (forwardT:MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T)
    (inverseT:MDifferentiable (𝓘(ℝ,E)) (𝓘(ℝ,E)) T.symm)
    (forwardS:MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S)
    (inverseS:MDifferentiable (𝓘(ℝ,F)) (𝓘(ℝ,F)) S.symm) :
    HyperbolicData (E:=WithLp 2 (E×F)) (T.prodCongr S) (K×ˢL) := by
  let forwardBounds := exists_forward_norm_bound (E:=E) (F:=F) (K×ˢL) (a.compact.prod b.compact)
  let inverseBounds := exists_inverse_norm_bound (E:=E) (F:=F) (K×ˢL) (a.compact.prod b.compact)
  let CF := Classical.choose forwardBounds
  let CI := Classical.choose inverseBounds
  have posF : 0 < CF := (Classical.choose_spec forwardBounds).1
  have posI : 0 < CI := (Classical.choose_spec inverseBounds).1
  have boundF := (Classical.choose_spec forwardBounds).2
  have boundI := (Classical.choose_spec inverseBounds).2
  have mapsT : MapsTo T K K := by intro x hx; rw [←a.invariant]; exact mem_image_of_mem T hx
  have mapsS : MapsTo S L L := by intro y hy; rw [←b.invariant]; exact mem_image_of_mem S hy
  have mapsTI : MapsTo T.symm K K := by
    intro x hx
    rw [←a.invariant] at hx
    obtain ⟨w,hw,rfl⟩ := hx
    simpa using hw
  have mapsSI : MapsTo S.symm L L := by
    intro y hy
    rw [←b.invariant] at hy
    obtain ⟨w,hw,rfl⟩ := hy
    simpa using hw
  refine {
    compact := a.compact.prod b.compact
    invariant := ?_
    stable := stable a b
    unstable := unstable a b
    complementary := complementary a b
    projection := projection a b
    projection_range := projection_range a b
    projection_kernel := projection_kernel a b
    projection_idempotent := projection_idempotent a b
    continuous_splitting := continuous_splitting a b
    stable_invariant := stable_invariant a b forwardT forwardS
    unstable_invariant := unstable_invariant a b forwardT forwardS
    constant := CF*(a.constant+b.constant)*CI
    contraction := max a.contraction b.contraction
    constant_pos := mul_pos (mul_pos posF (add_pos a.constant_pos b.constant_pos)) posI
    contraction_pos := a.contraction_pos.trans_le (le_max_left _ _)
    contraction_lt_one := max_lt a.contraction_lt_one b.contraction_lt_one
    stable_bound := ?_
    unstable_bound := ?_ }
  · change (Prod.map T S) '' (K×ˢL) = K×ˢL
    rw [prodMap_image_prod,a.invariant,b.invariant]
  · intro n z hz v hv
    obtain ⟨u,hu,rfl⟩ := hv
    exact actual_iterate_bound a b T S forwardT forwardS CF CI posF boundF boundI n z hz
      ⟨mapsT.iterate n hz.1,mapsS.iterate n hz.2⟩ u
      (a.stable_bound n z.1 hz.1 u.1 hu.1) (b.stable_bound n z.2 hz.2 u.2 hu.2)
  · intro n z hz v hv
    obtain ⟨u,hu,rfl⟩ := hv
    exact actual_iterate_bound a b T.symm S.symm inverseT inverseS CF CI posF boundF boundI n z hz
      ⟨mapsTI.iterate n hz.1,mapsSI.iterate n hz.2⟩ u
      (a.unstable_bound n z.1 hz.1 u.1 hu.1) (b.unstable_bound n z.2 hz.2 u.2 hu.2)

end LeanShared.HyperbolicBasicSet.HilbertProduct
