import AKAR33ExactRetainedDecayConsumer
import AKV25OriginalRowCurveAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.OriginalKernelGraphRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.AnnularWeightedSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.AnnularOriginalCoreRealization Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.ActualSmoothPhysicalField
open Grad.AnnularCurrentSource Grad.AnnularHighTilt Grad.AnnularOriginalSmoothCore

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (field : ACore parameters 1)

/-- The SAME original Cartesian field placed in the existing low rho storage.
The accepted high storage conversion exactly changes sqrt(r) to r^(-7/4). -/
def originalCoreLowRow : DivisionRow 1 lower :=
  divisionHighWeight lower positive bounded.le (cartesianWeightedRadialRow parameters lower positive bounded field 0 0)

/-- Reuse the accepted all-grade original ACore radial jets, with no additional
regularity or graph-domain premise. -/
def originalCoreLowCurves : SmoothLowPhysicalRow parameters lower positive
    (originalCoreLowRow parameters lower positive bounded field) where
  curve grade := cartesianWeightedRadialCurve parameters lower positive bounded field grade 0
  smooth grade := cartesianWeightedRadialCurve_smooth parameters lower positive bounded field grade 0
  same grade := by
    let curves := cartesianOriginalRowRadialCurves parameters lower positive bounded field
    filter_upwards [curves.same grade,originalF1Coefficient_eq_originalRow parameters lower positive bounded
      (cartesianWeightedRadialRow parameters lower positive bounded field 0 0)] with radius same physical
    intro mode
    change _ = (_ : ℂ)^grade • ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
      originalF1Coefficient parameters lower positive bounded.le
        (cartesianWeightedRadialRow parameters lower positive bounded field 0 0) radius mode)
    rw [physical mode]
    simpa only [curves,cartesianOriginalRowRadialCurves] using same mode

end Grad.OriginalKernelGraphRestriction
