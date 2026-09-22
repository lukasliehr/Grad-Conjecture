import AKBN16ActualCofactorNativeMoments
import AKBN11ProjectedDeterminantBalance

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.RepresentedKernel.SpatialProduct Grad.ActualSmoothPhysicalField
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.Constraints.Gauges Grad.ActualForceMoments

/-- The literal original L,L,1 cofactor law gives the exact normalized
P0 determinant balance on the same joint fields. -/
theorem startupDeterminantBalance_of_raw (length : ℝ) (nonzero : length ≠ 0) (axial : ℤ → ℂ)
    (cofactor : StartupMoments 3) (source : StartupL2 1)
    (rawCofactor : ℤ → Spatial → ComplexEuclidean 3) (rawSource : ℤ → Spatial → ComplexEuclidean 1)
    (sameCofactor : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, cofactor.field point cell = rawCofactor cell point)
    (sameSource : ∀ cell, (fun point => source point cell) =ᵐ[volume.restrict openUnitDisk] rawSource cell)
    (weak : ∀ cell (test : TestFunction openUnitDisk),
      (∫ point in openUnitDisk, test.toFun point • rawSource cell point 0) -
        (∫ point in openUnitDisk, (startupMeanFreeTest test).toFun point • (axial cell * rawCofactor cell point 2)) =
      -(∑ direction : Fin 2, ∫ point in openUnitDisk,
        directionDerivative direction (startupMeanFreeTest test).toFun point •
          ((length : ℂ) * rawCofactor cell point direction.castSucc))) :
    ∀ cell test, startupCoordinateTestPairing cell 0 test ((length : ℂ)⁻¹ • source) =
      startupWeakDivergencePairing (originalValueKernel planarPartMap cofactor.field) cell (startupMeanFreeTest test) +
        (axial cell / (length : ℂ)) * startupCoordinateTestPairing cell 0 (startupMeanFreeTest test)
          (originalValueKernel toroidalPartMap cofactor.field) := by
  intro cell test
  have planarSame := startupValueMap_same cofactor planarPartMap _ sameCofactor
  have toroidalSame := startupValueMap_same cofactor toroidalPartMap _ sameCofactor
  have scalarPair := startupCoordinateTestPairing_raw (originalValueKernel toroidalPartMap cofactor.field) cell _
    (toroidalSame.mono (fun _ same => same cell)) 0 (startupMeanFreeTest test)
  have planarPair (direction : Fin 2) := startupCoordinateTestPairing_raw
    (originalValueKernel planarPartMap cofactor.field) cell _
    (planarSame.mono (fun _ same => same cell)) direction (startupDerivativeTest direction (startupMeanFreeTest test))
  have planarCoordinate (direction : Fin 2) (value : ComplexEuclidean 3) :
      planarPartMap value direction = value direction.castSucc := by fin_cases direction <;> rfl
  have scalarIntegral :
      (∫ point in openUnitDisk, (startupMeanFreeTest test).toFun point • (axial cell * rawCofactor cell point 2)) =
      axial cell * startupCoordinateTestPairing cell 0 (startupMeanFreeTest test)
        (originalValueKernel toroidalPartMap cofactor.field) := by
    rw [scalarPair,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with point
    change _ • (axial cell * rawCofactor cell point 2) = axial cell * (_ • rawCofactor cell point 2)
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),smul_eq_mul]
    ring
  have planarIntegral (direction : Fin 2) :
      (∫ point in openUnitDisk, directionDerivative direction (startupMeanFreeTest test).toFun point •
        ((length : ℂ) * rawCofactor cell point direction.castSucc)) =
      (length : ℂ) * startupCoordinateTestPairing cell direction
        (startupDerivativeTest direction (startupMeanFreeTest test)) (originalValueKernel planarPartMap cofactor.field) := by
    rw [planarPair,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with point
    rw [planarCoordinate]
    change _ • ((length : ℂ) * rawCofactor cell point direction.castSucc) =
      (length : ℂ) * (_ • rawCofactor cell point direction.castSucc)
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),smul_eq_mul,startupDerivativeTest]
    ring
  have equation := weak cell test
  rw [← startupCoordinateTestPairing_raw source cell _ (sameSource cell) 0 test,scalarIntegral] at equation
  simp_rw [planarIntegral] at equation
  simp only [Fin.sum_univ_two] at equation
  simp only [map_smul,smul_eq_mul,startupWeakDivergencePairing]
  have lengthNonzero : (length : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  field_simp [lengthNonzero]
  linear_combination equation

end Grad.CartesianStartup
