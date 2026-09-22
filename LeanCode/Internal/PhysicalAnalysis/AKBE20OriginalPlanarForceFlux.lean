import AKBE19ProjectedClassicalAxisConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.ActualCartesianWeakEquations
open Grad.PDEBootstrap Grad.ClosedJets Grad.PhysicalFamily Grad.ActualSmoothPhysicalField
open Grad.RepresentedKernel.SpatialProduct

def originalForceFlux (xi : Spatial → ℂ) (covariant : Spatial → ComplexEuclidean 2)
    (coordinate direction : Fin 2) (point : Spatial) : ℂ :=
  (if direction = coordinate then xi point else 0) -
    angularRotationCoordinate direction point • covariant point coordinate

def originalPlanarGradient (xi : Spatial → ℂ) (point : Spatial) : ComplexEuclidean 2 :=
  WithLp.toLp 2 (fun coordinate => fderiv ℝ xi point (spatialDirection coordinate))

/-- The literal flux Xi delta_ij minus (Jy)_j a_i is smooth on exactly
the same punctured domain as the original fields. -/
theorem originalForceFlux_smooth (domain : Set Spatial) (xi : Spatial → ℂ)
    (covariant : Spatial → ComplexEuclidean 2)
    (xiSmooth : ContDiffOn ℝ ∞ xi domain) (covariantSmooth : ContDiffOn ℝ ∞ covariant domain)
    (coordinate direction : Fin 2) : ContDiffOn ℝ ∞ (originalForceFlux xi covariant coordinate direction) domain := by
  have componentSmooth : ContDiffOn ℝ ∞ (fun point => covariant point coordinate) domain :=
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) coordinate).restrictScalars ℝ).contDiff.comp_contDiffOn covariantSmooth
  have scalarSmooth : ContDiffOn ℝ ∞ (fun point => if direction = coordinate then xi point else 0) domain := by
    by_cases equal : direction = coordinate
    · simpa only [if_pos equal] using xiSmooth
    · simpa only [if_neg equal] using (contDiffOn_const (c := (0 : ℂ)))
  exact scalarSmooth.sub (angularTransportFlux_smooth domain _ componentSmooth direction)

/-- The coefficient Jy has zero divergence, so the actual force flux has
precisely gradient Xi minus R a, with no added axis term. -/
theorem originalForceFlux_divergence (xi : Spatial → ℂ) (covariant : Spatial → ComplexEuclidean 2)
    (point : Spatial) (xiDifferentiable : DifferentiableAt ℝ xi point)
    (covariantDifferentiable : DifferentiableAt ℝ covariant point) :
    originalPlanarDivergence (originalForceFlux xi covariant) point =
      originalPlanarGradient xi point - fderiv ℝ covariant point (planeQuarterTurn point) := by
  apply PiLp.ext
  intro coordinate
  let component : Spatial → ℂ := fun current => covariant current coordinate
  have componentDerivative : HasFDerivAt component
      (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) coordinate).restrictScalars ℝ).comp (fderiv ℝ covariant point)) point :=
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) coordinate).restrictScalars ℝ).hasFDerivAt.comp point covariantDifferentiable.hasFDerivAt
  have componentDiff : DifferentiableAt ℝ component point := componentDerivative.differentiableAt
  have scalarDiff (direction : Fin 2) : DifferentiableAt ℝ (fun current => if direction = coordinate then xi current else 0) point := by
    by_cases equal : direction = coordinate
    · simpa only [if_pos equal] using xiDifferentiable
    · simpa only [if_neg equal] using (differentiableAt_const (c := (0 : ℂ)))
  have difference (direction : Fin 2) :
      directionDerivative direction (originalForceFlux xi covariant coordinate direction) point =
      directionDerivative direction (fun current => if direction = coordinate then xi current else 0) point -
        directionDerivative direction (angularTransportFlux component direction) point := by
    have transportDiff : DifferentiableAt ℝ (angularTransportFlux component direction) point :=
      (angularRotationCoordinate direction).differentiableAt.smul componentDiff
    have actual : HasFDerivAt (originalForceFlux xi covariant coordinate direction)
        (fderiv ℝ (fun current => if direction = coordinate then xi current else 0) point -
          fderiv ℝ (angularTransportFlux component direction) point) point :=
      (scalarDiff direction).hasFDerivAt.sub transportDiff.hasFDerivAt
    exact congrArg (fun derivative : Spatial →L[ℝ] ℂ => derivative (spatialDirection direction)) actual.fderiv
  have scalarDerivative (direction : Fin 2) :
      directionDerivative direction (fun current => if direction = coordinate then xi current else 0) point =
        if direction = coordinate then fderiv ℝ xi point (spatialDirection direction) else 0 := by
    by_cases equal : direction = coordinate
    · simp only [if_pos equal,directionDerivative]
    · simp only [if_neg equal,directionDerivative]
      exact congrArg (fun derivative : Spatial →L[ℝ] ℂ => derivative (spatialDirection direction))
        (hasFDerivAt_const (0 : ℂ) point).fderiv
  change (∑ direction : Fin 2, directionDerivative direction (originalForceFlux xi covariant coordinate direction) point) = _
  simp_rw [difference]
  rw [Finset.sum_sub_distrib,angularTransportFlux_divergence component point componentDiff]
  simp_rw [scalarDerivative]
  rw [componentDerivative.fderiv]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true,originalPlanarGradient,PiLp.sub_apply]
  rfl

end Grad.ActualCartesianWeakEquations
