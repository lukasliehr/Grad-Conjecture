import AKBN8RawProjectedForceConsumer
import AKBN9RawAngularFluxPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.RepresentedKernel.SpatialProduct Grad.ActualSmoothPhysicalField
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- Literal scalar compact balance gives the normalized third startup row.
The axial factor is applied only at the chosen cell; its diagonal is not
assumed bounded. Theta is the actual inverse of the SAME mean-free Xi. -/
theorem startupThirdEquation_of_raw (length : ℝ) (nonzero : length ≠ 0) (axial : ℤ → ℂ)
    (psi scalar source correction : StartupL2 1)
    (rawXi rawScalar rawSource rawCorrection : ℤ → Spatial → ComplexEuclidean 1)
    (sameXi : ∀ cell, (fun point => psi point cell) =ᵐ[volume.restrict openUnitDisk] rawXi cell)
    (sameScalar : ∀ cell, (fun point => scalar point cell) =ᵐ[volume.restrict openUnitDisk] rawScalar cell)
    (sameSource : ∀ cell, (fun point => source point cell) =ᵐ[volume.restrict openUnitDisk] rawSource cell)
    (sameCorrection : ∀ cell, (fun point => correction point cell) =ᵐ[volume.restrict openUnitDisk] rawCorrection cell)
    (mean : ∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test) psi = 0)
    (weak : ∀ cell (test : TestFunction openUnitDisk),
      (∫ point in openUnitDisk, test.toFun point •
        (axial cell • rawXi cell point - rawCorrection cell point + rawSource cell point) 0) =
      -(length : ℂ) * (∑ direction : Fin 2, ∫ point in openUnitDisk,
        (directionDerivative direction test.toFun point * angularRotationCoordinate direction point) • rawScalar cell point 0)) :
    StartupWeakThirdEquation (fun cell => axial cell / (length : ℂ))
      (startupTrueAngularInverse 1 0 psi) scalar ((length : ℂ)⁻¹ • (source - correction)) := by
  intro cell test
  let combined := axial cell • psi - correction + source
  have combinedSame : (fun point => combined point cell) =ᵐ[volume.restrict openUnitDisk]
      fun point => axial cell • rawXi cell point - rawCorrection cell point + rawSource cell point := by
    filter_upwards [Lp.coeFn_add (axial cell • psi - correction) source,
      Lp.coeFn_sub (axial cell • psi) correction,Lp.coeFn_smul (axial cell) psi,
      sameXi cell,sameSource cell,sameCorrection cell] with point addition subtraction scaling xi f c
    change (axial cell • psi - correction + source) point cell = _
    rw [addition]
    change (axial cell • psi - correction) point cell + source point cell = _
    rw [subtraction]
    change (axial cell • psi) point cell - correction point cell + source point cell = _
    rw [scaling]
    change axial cell • psi point cell - correction point cell + source point cell = _
    rw [xi,f,c]
  have leftSame := startupCoordinateTestPairing_raw combined cell _ combinedSame 0 test
  have rightSame (direction : Fin 2) :
      (∫ point in openUnitDisk, (directionDerivative direction test.toFun point * angularRotationCoordinate direction point) • rawScalar cell point 0) =
      ∫ point in openUnitDisk, (directionDerivative direction test.toFun point * angularRotationCoordinate direction point) • scalar point cell 0 := by
    apply integral_congr_ae
    filter_upwards [sameScalar cell] with point actual
    rw [actual]
  have equation := weak cell test
  rw [← leftSame] at equation
  simp_rw [rightSame,startupAngularTransport_pairing] at equation
  simp only [combined,map_add,map_sub,map_smul,smul_eq_mul] at equation
  have rotation := startupSame_scalarPrimitive_rotation psi mean cell test
  simp only [map_smul,map_sub,smul_eq_mul]
  rw [show startupCoordinateTestPairing cell 0 (startupRotationTest test) (startupTrueAngularInverse 1 0 psi) =
      -startupCoordinateTestPairing cell 0 test psi by linear_combination -rotation]
  have complexNonzero : (length : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  field_simp [complexNonzero]
  linear_combination equation

end Grad.CartesianStartup
