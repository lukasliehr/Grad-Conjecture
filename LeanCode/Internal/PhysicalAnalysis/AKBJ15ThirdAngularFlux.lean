import AKBJ12ThirdCellLinearAlgebra
import AKBE4OriginalAngularWeakEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace Grad.ActualScalarWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Ledger Grad.ActualCartesianWeakEquations Grad.PhysicalAxisEquation
open Grad.PhysicalFamily Grad.PDEBootstrap Grad.ActualSmoothPhysicalField

def thirdRotationMap (length : ℝ) : ComplexEuclidean 3 →L[ℝ] ComplexEuclidean 1 :=
  ((length : ℂ) • matrixUnit (0 : Fin 1) (2 : Fin 3)).restrictScalars ℝ

def thirdRotationField (length : ℝ) (field : Spatial → ComplexEuclidean 3) (point : Spatial) : ComplexEuclidean 1 :=
  thirdRotationMap length (field point)

theorem thirdRotationField_smooth (length : ℝ) (field : Spatial → ComplexEuclidean 3) (domain : Set Spatial)
    (smooth : ContDiffOn ℝ ∞ field domain) : ContDiffOn ℝ ∞ (thirdRotationField length field) domain :=
  (thirdRotationMap length).contDiff.comp_contDiffOn smooth

theorem thirdRotationField_fderiv (length : ℝ) (field : Spatial → ComplexEuclidean 3) (point direction : Spatial)
    (differentiable : DifferentiableAt ℝ field point) :
    fderiv ℝ (thirdRotationField length field) point direction =
      (length : ℂ) • matrixUnit (0 : Fin 1) (2 : Fin 3) (fderiv ℝ field point direction) := by
  exact congrArg (fun derivative : Spatial →L[ℝ] ComplexEuclidean 1 => derivative direction)
    ((thirdRotationMap length).hasFDerivAt.comp point differentiable.hasFDerivAt).fderiv

theorem thirdRotationField_integrable_pair (length : ℝ) (field : Spatial → ComplexEuclidean 3)
    (integrable : IntegrableOn field openUnitDisk)
    (weighted : IntegrableOn (fun point => ‖point‖⁻¹ * ‖field point‖) openUnitDisk) :
    IntegrableOn (thirdRotationField length field) openUnitDisk ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖thirdRotationField length field point‖) openUnitDisk :=
  boundedPhysicalFlux_integrable_pair openUnitDisk field integrable weighted
    (fun _ => thirdRotationMap length) aestronglyMeasurable_const ‖thirdRotationMap length‖
    (Eventually.of_forall (fun _ => le_rfl))

theorem quarterTurn_polarPlane (radius polar : ℝ) :
    planeQuarterTurn (polarPlane (radius,polar)) = radius • planeQuarterTurn (radialDirection polar) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [planeQuarterTurn,polarPlane,radialDirection,Grad.BoundaryTrace.collarPlane,PiLp.smul_apply]

end Grad.ActualScalarWeakEquations
