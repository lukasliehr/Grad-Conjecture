import AKAD2PuncturedClassicalWeakEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace Grad.PhysicalAxisEquation
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularCurrentLow Grad.DiskExtension.Operator Grad.BoundaryTrace Grad.WeakTesting Grad.PDEBootstrap
open Grad.RepresentedKernel.SpatialProduct Grad.WeightedAxisRemoval

/-- The original energy and the actual classical PDE away from the axis
imply the ordinary whole-disk weak equation. No punctured distributional
identity is an extra input: the proof derives it by compact integration by parts. -/
theorem originalEnergy_classical_equation_remove_axis {dimension : ℕ}
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
    (smooth : ∀ index, ContDiffOn ℝ ∞ (flux index) (openUnitDisk \ {(0 : Spatial)}))
    (equation : ∀ point ∈ openUnitDisk \ {(0 : Spatial)}, source point =
      ∑ index : Fin 2, directionDerivative index (flux index) point) :
    ∀ (test : SpatialPlane → ℝ), ContDiff ℝ ∞ test → HasCompactSupport test →
      tsupport test ⊆ openUnitDisk →
      (∫ point in openUnitDisk, test point • source point) =
        -(∑ index : Fin 2, ∫ point in openUnitDisk,
          (fderiv ℝ test point (spatialDirection index)) • flux index point) := by
  apply firstOrder_equation_remove_axis_of_original_energy parameters collars positive decreasing cofinal
    fields curve same K estimate curveMeasurable cell flux measurable polarMeasurable continuousSlices coefficients
    source sourceIntegrable
  exact punctured_classical_divergence_weak flux source smooth equation

end Grad.PhysicalAxisEquation
