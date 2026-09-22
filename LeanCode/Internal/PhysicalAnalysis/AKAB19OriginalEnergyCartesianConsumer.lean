import AKAB18CartesianWeightedL1Consumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Grad.WeightedAxisRemoval
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularCurrentLow Grad.DiskExtension.Operator Grad.BoundaryTrace

/-- The actual original low-rho collar energy supplies the two Cartesian
integrability hypotheses of the axis-removal theorem. All Fourier coefficients
belong to the same field; no bound is postulated for the Cartesian field. -/
theorem originalEnergy_cartesian_integrable_pair {dimension : ℕ}
    (parameters : PhaseParameters) (collars : ℕ → ℝ)
    (positive : ∀ index, 0 < collars index) (decreasing : Antitone collars)
    (cofinal : Tendsto collars atTop (𝓝 0))
    (fields : ∀ index, DivisionRow dimension (collars index))
    (curve : ℝ → CellL2 dimension)
    (same : ∀ index, ∀ᵐ radius ∂volume.restrict (Icc (collars index) 1), ∀ mode,
      curve radius mode = lowRhoPhysicalCoefficient parameters (collars index) (positive index) (fields index) radius mode)
    (K : ℝ) (estimate : ∀ index, ‖fields index‖ ≤ K)
    (curveMeasurable : AEStronglyMeasurable curve (volume.restrict (Ioc 0 1)))
    (cell : ℤ) (field : SpatialPlane → ComplexEuclidean dimension)
    (measurable : AEStronglyMeasurable field (volume.restrict openUnitDisk))
    (polarMeasurable : AEStronglyMeasurable
      (fun point : ℝ × ℝ => field (spatialPlaneOfPair (polarCoord.symm point)))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (-Real.pi) Real.pi))))
    (continuousSlices : ∀ᵐ radius ∂volume.restrict (Ioc (0 : ℝ) 1),
      Continuous (fun angle => field (spatialPlaneOfPair (polarCoord.symm (radius,angle)))))
    (coefficients : ∀ᵐ radius ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ mode,
      angularCoefficient (fun angle => field (spatialPlaneOfPair (polarCoord.symm (radius,angle)))) mode =
        curve radius (mode,cell)) :
    IntegrableOn field openUnitDisk ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖field point‖) openUnitDisk := by
  have radial := (physicalHilbertCurve_integrable_pair parameters collars positive decreasing cofinal
    fields curve same K estimate curveMeasurable).1
  have polar := actualPolarField_integrable curve cell _ radial polarMeasurable continuousSlices coefficients
  apply cartesian_integrable_pair_of_polar field measurable
  exact polar.mono_set (Set.prod_mono Ioo_subset_Ioc_self Ioo_subset_Ioc_self)

end Grad.WeightedAxisRemoval
