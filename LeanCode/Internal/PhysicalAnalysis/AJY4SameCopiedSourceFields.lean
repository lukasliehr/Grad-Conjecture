import AJY3ExactFinitePhysicalSource

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval ENNReal BigOperators
namespace Grad.AnnularPhysicalFourier
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularStrongOrbit Grad.AnnularCurrentSource
open Grad.AnnularSmoothSources Grad.AnnularCurrentLow Grad.AnnularLowEnergy
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.AnnularClosedJointRegularity Grad.SourceCollarFullSource Grad.SourceCollarAngular

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (core : OriginalSmoothSourceCore parameters)

/-- The copied original F0 graph has a genuine physical smooth field,
using its exact original radial and phase storage. -/
def originalSmoothSourcePhysicalF0 : (ℝ × (ℝ × ℝ)) → ComplexEuclidean 1 :=
  finiteSourcePhysicalField parameters lower bounded ((originalSmoothF0Row parameters lower positive bounded.le core).highWeight positive bounded.le)

theorem originalSmoothSourcePhysicalF0_smooth_closed :
    ContDiffOn ℝ ∞ (originalSmoothSourcePhysicalF0 parameters lower positive bounded core) (annularJointClosed lower) :=
  finiteSourcePhysicalField_smooth_closed parameters lower positive bounded ((originalSmoothF0Row parameters lower positive bounded.le core).highWeight positive bounded.le)

theorem originalSmoothSourcePhysicalF0_angular_periodic (radius axial : ℝ) :
    Function.Periodic
      (fun polar => originalSmoothSourcePhysicalF0 parameters lower positive bounded core (radius, polar, axial)) (2 * Real.pi) :=
  finiteSourcePhysicalField_angular_periodic parameters lower bounded ((originalSmoothF0Row parameters lower positive bounded.le core).highWeight positive bounded.le) radius axial

theorem originalSmoothSourcePhysicalF0_cell_periodic (radius polar : ℝ) :
    Function.Periodic
      (fun axial => originalSmoothSourcePhysicalF0 parameters lower positive bounded core (radius, polar, axial)) (2 * Real.pi) :=
  finiteSourcePhysicalField_cell_periodic parameters lower bounded ((originalSmoothF0Row parameters lower positive bounded.le core).highWeight positive bounded.le) radius polar

/-- Exact coefficient matching to the independently defined AJE55 copied
F0 graph of the SAME original source datum. -/
theorem originalSmoothSourcePhysicalF0_actual :
    ∀ᵐ (radius : ℝ) ∂volume.restrict (Icc lower (1 : ℝ)), ∀ mode,
      angularCoefficient (fun axial => angularCoefficient
        (fun polar => originalSmoothSourcePhysicalF0 parameters lower positive bounded core (radius, polar, axial)) mode.1) mode.2 =
        lowRhoPhysicalCoefficient parameters lower positive
          (divisionHighWeight lower positive bounded.le
            (unweightedSourceF0Bulk parameters lower
              (originalSmoothStrongData parameters lower positive bounded.le core).val.ofLp.1.ofLp.1.ofLp.1)) radius mode :=
  finiteSourcePhysicalField_actual parameters lower positive bounded ((originalSmoothF0Row parameters lower positive bounded.le core).highWeight positive bounded.le)

/-- The copied original F2 graph has a genuine physical smooth field,
using its exact original radial and phase storage. -/
def originalSmoothSourcePhysicalF2 : (ℝ × (ℝ × ℝ)) → ComplexEuclidean 1 :=
  finiteSourcePhysicalField parameters lower bounded ((originalSmoothF2Row parameters lower positive bounded.le core).highWeight positive bounded.le)

theorem originalSmoothSourcePhysicalF2_smooth_closed :
    ContDiffOn ℝ ∞ (originalSmoothSourcePhysicalF2 parameters lower positive bounded core) (annularJointClosed lower) :=
  finiteSourcePhysicalField_smooth_closed parameters lower positive bounded ((originalSmoothF2Row parameters lower positive bounded.le core).highWeight positive bounded.le)

theorem originalSmoothSourcePhysicalF2_angular_periodic (radius axial : ℝ) :
    Function.Periodic
      (fun polar => originalSmoothSourcePhysicalF2 parameters lower positive bounded core (radius, polar, axial)) (2 * Real.pi) :=
  finiteSourcePhysicalField_angular_periodic parameters lower bounded ((originalSmoothF2Row parameters lower positive bounded.le core).highWeight positive bounded.le) radius axial

theorem originalSmoothSourcePhysicalF2_cell_periodic (radius polar : ℝ) :
    Function.Periodic
      (fun axial => originalSmoothSourcePhysicalF2 parameters lower positive bounded core (radius, polar, axial)) (2 * Real.pi) :=
  finiteSourcePhysicalField_cell_periodic parameters lower bounded ((originalSmoothF2Row parameters lower positive bounded.le core).highWeight positive bounded.le) radius polar

/-- Exact coefficient matching to the independently defined AJE55 copied
F2 graph of the SAME original source datum. -/
theorem originalSmoothSourcePhysicalF2_actual :
    ∀ᵐ (radius : ℝ) ∂volume.restrict (Icc lower (1 : ℝ)), ∀ mode,
      angularCoefficient (fun axial => angularCoefficient
        (fun polar => originalSmoothSourcePhysicalF2 parameters lower positive bounded core (radius, polar, axial)) mode.1) mode.2 =
        lowRhoPhysicalCoefficient parameters lower positive
          (divisionHighWeight lower positive bounded.le
            (unweightedSourceF2Bulk parameters lower
              (originalSmoothStrongData parameters lower positive bounded.le core).val.ofLp.1.ofLp.1.ofLp.2)) radius mode :=
  finiteSourcePhysicalField_actual parameters lower positive bounded ((originalSmoothF2Row parameters lower positive bounded.le core).highWeight positive bounded.le)

end Grad.AnnularPhysicalFourier
