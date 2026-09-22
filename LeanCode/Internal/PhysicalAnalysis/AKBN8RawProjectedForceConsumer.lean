import AKBN5ScaledProjectionKernels
import AKBN7LiteralForceFluxPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.ActualCartesianWeakEquations
open Grad.RepresentedKernel.SpatialProduct

theorem startupCoordinateTestPairing_raw {dimension : ℕ} (field : StartupL2 dimension)
    (cell : ℤ) (raw : Spatial → ComplexEuclidean dimension)
    (same : (fun point => field point cell) =ᵐ[volume.restrict openUnitDisk] raw)
    (coordinate : Fin dimension) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell coordinate test field =
      ∫ point in openUnitDisk, test.toFun point • raw point coordinate := by
  rw [startupCoordinateTestPairing_apply]
  apply integral_congr_ae
  filter_upwards [same] with point actual
  rw [actual]

/-- The literal compact force law on the SAME raw representatives is precisely
 the rough projected-force interface, with the quarter turn kept on the left. -/
theorem startupProjectedForceEquation_of_raw (psi : StartupL2 1) (vector force correction : StartupL2 2)
    (rawXi : ℤ → Spatial → ComplexEuclidean 1)
    (rawVector rawForce rawCorrection : ℤ → Spatial → ComplexEuclidean 2)
    (sameXi : ∀ cell, (fun point => psi point cell) =ᵐ[volume.restrict openUnitDisk] rawXi cell)
    (sameVector : ∀ cell, (fun point => vector point cell) =ᵐ[volume.restrict openUnitDisk] rawVector cell)
    (sameForce : ∀ cell, (fun point => force point cell) =ᵐ[volume.restrict openUnitDisk] rawForce cell)
    (sameCorrection : ∀ cell, (fun point => correction point cell) =ᵐ[volume.restrict openUnitDisk] rawCorrection cell)
    (weak : ∀ cell output (test : TestFunction openUnitDisk),
      (∑ coordinate : Fin 2, ∫ point in openUnitDisk,
        startupRawQradTest output test.toFun coordinate point •
          (rawForce cell point + quarterValueMap (rawVector cell point) - rawCorrection cell point) coordinate) =
      -(∑ coordinate : Fin 2, ∑ direction : Fin 2, ∫ point in openUnitDisk,
        directionDerivative direction (startupRawQradTest output test.toFun coordinate) point •
          originalForceFlux (fun point => rawXi cell point 0) (rawVector cell) coordinate direction point)) :
    StartupWeakProjectedForceEquation psi vector (startupGenuineQradKernel (force - correction)) := by
  intro cell output test
  let combined := force + originalValueKernel quarterValueMap vector - correction
  have combinedSame : (fun point => combined point cell) =ᵐ[volume.restrict openUnitDisk]
      fun point => rawForce cell point + quarterValueMap (rawVector cell point) - rawCorrection cell point := by
    filter_upwards [Lp.coeFn_sub (force + originalValueKernel quarterValueMap vector) correction,
      Lp.coeFn_add force (originalValueKernel quarterValueMap vector),
      startupPointKernel_field_ae quarterValueMap (LinearIsometryEquiv.refl ℝ _) vector,
      sameForce cell,sameVector cell,sameCorrection cell] with point subtraction addition rotation f a c
    change (force + originalValueKernel quarterValueMap vector - correction) point cell = _
    rw [subtraction]
    change (force + originalValueKernel quarterValueMap vector) point cell - correction point cell = _
    rw [addition]
    change force point cell + (originalValueKernel quarterValueMap vector) point cell - correction point cell = _
    change ∀ cell : ℤ, (originalValueKernel quarterValueMap vector) point cell = quarterValueMap (vector point cell) at rotation
    rw [rotation cell,f,a,c]
  have leftSame (coordinate : Fin 2) := startupCoordinateTestPairing_raw combined cell _ combinedSame
    coordinate (startupQradTestComponent coordinate output test)
  have fluxSame (coordinate direction : Fin 2) :
      (∫ point in openUnitDisk, directionDerivative direction (startupRawQradTest output test.toFun coordinate) point •
        originalForceFlux (fun point => rawXi cell point 0) (rawVector cell) coordinate direction point) =
      ∫ point in openUnitDisk, directionDerivative direction (startupQradTestComponent coordinate output test).toFun point •
        originalForceFlux (fun point => psi point cell 0) (fun point => vector point cell) coordinate direction point := by
    apply integral_congr_ae
    filter_upwards [sameXi cell,sameVector cell] with point xi covariant
    simp only [originalForceFlux,xi,covariant,startupRawQradTest_same]
  have equation := weak cell output test
  rw [show (∑ coordinate : Fin 2, ∫ point in openUnitDisk,
      startupRawQradTest output test.toFun coordinate point •
        (rawForce cell point + quarterValueMap (rawVector cell point) - rawCorrection cell point) coordinate) =
      ∑ coordinate : Fin 2, startupCoordinateTestPairing cell coordinate (startupQradTestComponent coordinate output test) combined by
        apply Finset.sum_congr rfl
        intro coordinate _
        exact (leftSame coordinate).symm] at equation
  simp_rw [fluxSame,startupOriginalForceFlux_pairing] at equation
  rw [startupCoordinateTestPairing_qrad]
  simp only [combined,map_sub,map_add,startupWeakForceVectorPairing,Fin.sum_univ_two] at equation ⊢
  linear_combination equation

end Grad.CartesianStartup
