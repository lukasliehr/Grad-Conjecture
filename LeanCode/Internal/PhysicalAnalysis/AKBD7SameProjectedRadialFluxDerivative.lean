import AKBD6GenuineCorrectedFluxDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualDeterminantEquations
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualBoundaryPrimitives Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)

open Grad.ActualPolarFlux Grad.ActualCartesianEquations

variable {row : DivisionRow 7 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

/-- Genuine radial differentiation of p=P(raw p), preserving the outer
projection and differentiating the same compact angular integral. -/
theorem correctedP_radial_projected (radius : ℝ) (inside : radius ∈ Ioo lower 1) (polar axial : ℝ) :
    scalarDirectionalField (curves.correctedP parameters length compact lower positive bounded state) bounded 0 (1,0,0) (radius,polar,axial) =
      removePolarMean (fun angles =>
        scalarDirectionalField (rawCorrectedPCurves parameters length compact lower positive bounded state curves) bounded 0 (1,0,0) (radius,angles)) (polar,axial) := by
  let raw := rawCorrectedPCurves parameters length compact lower positive bounded state curves
  let corrected := curves.correctedP parameters length compact lower positive bounded state
  have projected := removePolarMean_radial_hasDerivAt
    (fun point => raw.fullField bounded point 0) lower 1 (fullScalarField_smooth raw bounded 0)
    radius inside polar axial (fun angle => scalarDirectionalField raw bounded 0 (1,0,0) (radius,angle,axial))
    (fun angle => scalarRadial_hasDerivAt raw bounded 0 radius inside angle axial)
  have actual : HasDerivAt (fun value => corrected.fullField bounded (value,polar,axial) 0)
      (removePolarMean (fun angles => scalarDirectionalField raw bounded 0 (1,0,0) (radius,angles)) (polar,axial)) radius := by
    apply projected.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds inside] with value member
    exact correctedP_projection_same parameters length compact lower positive bounded state curves value ⟨member.1.le,member.2.le⟩ (polar,axial)
  exact (scalarRadial_hasDerivAt corrected bounded 0 radius inside polar axial).unique actual

end Grad.ActualDeterminantEquations
