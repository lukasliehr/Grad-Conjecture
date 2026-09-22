import AKBJ31ActualOriginalDeterminantCell
import AKBJ23ActualScalarDivergenceAxisConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualScalarWeakEquations
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.ActualCartesianFlux
open Grad.ActualCartesianEquations Grad.RepresentedKernel.SpatialProduct

def determinantPlanarCellFlux (length : ℝ) (field : Spatial → ComplexEuclidean 3) (direction : Fin 2) (point : Spatial) : ℂ :=
  determinantFluxProjection length direction.castSucc (field point)

def determinantAxialCellFlux (cell : ℤ) (field : Spatial → ComplexEuclidean 3) (point : Spatial) : ℂ :=
  (Complex.I * (cell : ℂ)) * field point 2

theorem determinantPlanarCellFlux_smooth (length : ℝ) (field : Spatial → ComplexEuclidean 3)
    (domain : Set Spatial) (smooth : ContDiffOn ℝ ∞ field domain) (direction : Fin 2) :
    ContDiffOn ℝ ∞ (determinantPlanarCellFlux length field direction) domain :=
  (determinantFluxProjection length direction.castSucc).contDiff.comp_contDiffOn smooth

theorem determinantAxialCellFlux_smooth (cell : ℤ) (field : Spatial → ComplexEuclidean 3)
    (domain : Set Spatial) (smooth : ContDiffOn ℝ ∞ field domain) :
    ContDiffOn ℝ ∞ (determinantAxialCellFlux cell field) domain :=
  contDiffOn_const.mul (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => ℂ) 2).restrictScalars ℝ).contDiff.comp_contDiffOn smooth)

/-- The scalar divergence consumer uses exactly the original two L factors and the unscaled third cofactor column. -/
theorem determinantCellFlux_divergence (length : ℝ) (cell : ℤ) (field : Spatial → ComplexEuclidean 3)
    (point : Spatial) (differentiable : DifferentiableAt ℝ field point) :
    scalarDivergenceValue (determinantPlanarCellFlux length field) (determinantAxialCellFlux cell field) point 0 =
      sameCellDeterminantDivergence length cell field point := by
  change (∑ direction : Fin 2, directionDerivative direction (determinantPlanarCellFlux length field direction) point) +
    determinantAxialCellFlux cell field point = _
  rw [Fin.sum_univ_two]
  unfold directionDerivative determinantPlanarCellFlux
  rw [determinantFluxProjection_fderiv length _ field point differentiable,
    determinantFluxProjection_fderiv length _ field point differentiable]
  change (length : ℂ) * fderiv ℝ field point (spatialDirection 0) 0 +
    (length : ℂ) * fderiv ℝ field point (spatialDirection 1) 1 +
    (Complex.I * (cell : ℂ)) * field point 2 = _
  have basis (direction : Fin 2) : spatialDirection direction = spatialBasis direction := by
    apply PiLp.ext
    intro coordinate
    fin_cases direction <;> fin_cases coordinate <;> simp [spatialDirection,spatialBasis]
  simp only [basis,sameCellDeterminantDivergence,determinantRowValue,PiLp.smul_apply,smul_eq_mul]
  ring

/-- Continuity needed by the literal circle mean, only on the punctured domain. -/
theorem determinantCellFlux_rawContinuous (length : ℝ) (cell : ℤ) (field : Spatial → ComplexEuclidean 3)
    (smooth : ContDiffOn ℝ ∞ field (openUnitDisk \ {(0 : Spatial)})) :
    ContinuousOn (scalarDivergenceValue (determinantPlanarCellFlux length field) (determinantAxialCellFlux cell field))
      (openUnitDisk \ {(0 : Spatial)}) := by
  have derivativeContinuous : ContinuousOn (fun point => ∑ direction : Fin 2,
      directionDerivative direction (determinantPlanarCellFlux length field direction) point) (openUnitDisk \ {(0 : Spatial)}) :=
    continuousOn_finsetSum _ (fun direction _ => (directionDerivative_smooth (openUnitDisk_isOpen.sdiff isClosed_singleton)
      direction (determinantPlanarCellFlux_smooth length field _ smooth direction)).continuousOn)
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℂ)).comp_continuousOn
  exact continuousOn_pi.mpr (fun _ => derivativeContinuous.add (determinantAxialCellFlux_smooth cell field _ smooth).continuousOn)

end Grad.ActualScalarWeakEquations
