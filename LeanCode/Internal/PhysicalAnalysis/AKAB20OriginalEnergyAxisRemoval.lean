import AKAB19OriginalEnergyCartesianConsumer
import AKAB11FirstOrderAxisRemoval

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace Grad.WeightedAxisRemoval
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularCurrentLow Grad.DiskExtension.Operator Grad.BoundaryTrace Grad.WeakTesting Grad.PDEBootstrap

/-- Original weighted energy and literal physical Fourier fidelity remove
the axis from the actual first-order weak equation. This theorem requires
only the equation on tests away from the axis, not a distributional extension. -/
theorem firstOrder_equation_remove_axis_of_original_energy {dimension : ℕ}
    (parameters : PhaseParameters) (collars : ℕ → ℝ)
    (positive : ∀ index, 0 < collars index) (decreasing : Antitone collars)
    (cofinal : Tendsto collars atTop (𝓝 0))
    (fields : ∀ _direction : Fin 2, ∀ index, DivisionRow dimension (collars index))
    (curve : Fin 2 → ℝ → CellL2 dimension)
    (same : ∀ direction index, ∀ᵐ radius ∂volume.restrict (Icc (collars index) 1), ∀ mode,
      curve direction radius mode = lowRhoPhysicalCoefficient parameters (collars index) (positive index) (fields direction index) radius mode)
    (K : Fin 2 → ℝ) (estimate : ∀ direction index, ‖fields direction index‖ ≤ K direction)
    (curveMeasurable : ∀ direction, AEStronglyMeasurable (curve direction) (volume.restrict (Ioc 0 1)))
    (cell : ℤ) (flux : Fin 2 → SpatialPlane → ComplexEuclidean dimension)
    (measurable : ∀ direction, AEStronglyMeasurable (flux direction) (volume.restrict openUnitDisk))
    (polarMeasurable : ∀ direction, AEStronglyMeasurable
      (fun point : ℝ × ℝ => flux direction (spatialPlaneOfPair (polarCoord.symm point)))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (-Real.pi) Real.pi))))
    (continuousSlices : ∀ direction, ∀ᵐ radius ∂volume.restrict (Ioc (0 : ℝ) 1),
      Continuous (fun angle => flux direction (spatialPlaneOfPair (polarCoord.symm (radius,angle)))))
    (coefficients : ∀ direction, ∀ᵐ radius ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ mode,
      angularCoefficient (fun angle => flux direction (spatialPlaneOfPair (polarCoord.symm (radius,angle)))) mode =
        curve direction radius (mode,cell))
    (source : SpatialPlane → ComplexEuclidean dimension)
    (sourceIntegrable : IntegrableOn source openUnitDisk)
    (punctured : ∀ (test : SpatialPlane → ℝ), ContDiff ℝ ∞ test → HasCompactSupport test →
      tsupport test ⊆ openUnitDisk → (0 : SpatialPlane) ∉ tsupport test →
      (∫ point in openUnitDisk, test point • source point) =
        -(∑ index : Fin 2, ∫ point in openUnitDisk,
          (fderiv ℝ test point (spatialDirection index)) • flux index point)) :
    ∀ (test : SpatialPlane → ℝ), ContDiff ℝ ∞ test → HasCompactSupport test →
      tsupport test ⊆ openUnitDisk →
      (∫ point in openUnitDisk, test point • source point) =
        -(∑ index : Fin 2, ∫ point in openUnitDisk,
          (fderiv ℝ test point (spatialDirection index)) • flux index point) := by
  have integrability (direction : Fin 2) := originalEnergy_cartesian_integrable_pair
    parameters collars positive decreasing cofinal (fields direction) (curve direction)
    (same direction) (K direction) (estimate direction) (curveMeasurable direction)
    cell (flux direction) (measurable direction) (polarMeasurable direction)
    (continuousSlices direction) (coefficients direction)
  exact firstOrder_equation_remove_axis openUnitDisk flux source sourceIntegrable
    (fun direction => (integrability direction).1) (fun direction => (integrability direction).2) punctured

end Grad.WeightedAxisRemoval
