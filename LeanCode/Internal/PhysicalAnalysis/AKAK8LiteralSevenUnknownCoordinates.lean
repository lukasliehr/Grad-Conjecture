import AKAK5ScalarRadialEquationSynthesis

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators

private theorem rawPhysicalSevenVector_firstFour (radius : ℝ) (mode : ℤ × ℤ)
    (x xi : ComplexEuclidean 1) (index : Fin 4) :
    matrixUnit (0 : Fin 1) (index.castLE (by omega : 4 ≤ 7)) (rawPhysicalSevenVector radius mode x xi) =
      if index = 0 then x else if index = 1 then
        (radius : ℂ)⁻¹ • (frequencyNumerator (some false) mode • xi)
      else if index = 2 then frequencyNumerator (some true) mode • xi
      else (radius : ℂ)⁻¹ • xi := by
  apply PiLp.ext
  intro component
  fin_cases component
  fin_cases index <;> simp [rawPhysicalSevenVector,matrixUnit_apply,operatorBasis]

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (field : CoupledSpace lower length positive lengthPositive)

/-- The original seven packet's first four coefficients are exactly
(x,RXi/r,Xi_zeta,Xi/r); prescribed source slots cannot alter them. -/
theorem fullStrongSevenInput_firstFour_physical :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ, ∀ index : Fin 4,
      matrixUnit (0 : Fin 1) (index.castLE (by omega : 4 ≤ 7))
        (lowRhoPhysicalCoefficient parameters lower positive
          (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field) radius mode) =
        if index = 0 then sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0 (radialClamp lower bounded.le radius) mode
        else if index = 1 then (radius : ℂ)⁻¹ • (frequencyNumerator (some false) mode •
          sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0 (radialClamp lower bounded.le radius) mode)
        else if index = 2 then frequencyNumerator (some true) mode •
          sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0 (radialClamp lower bounded.le radius) mode
        else (radius : ℂ)⁻¹ • sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0 (radialClamp lower bounded.le radius) mode := by
  let unknown := homogeneousCoupledSevenInput parameters length lower lengthPositive positive field
  let known := knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded.le data)
  filter_upwards [lowRhoPhysicalCoefficient_add_ae parameters lower positive unknown known,
    homogeneousCoupledSevenInput_sameSections parameters lower length positive bounded lengthPositive field,
    knownLowSevenPacket_ae lower (strongKnownBulk parameters lower positive bounded.le data)] with radius added original sources
  intro mode index
  have unknownSame : lowRhoPhysicalCoefficient parameters lower positive unknown radius mode =
      rawPhysicalSevenVector radius mode
        (sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0 (radialClamp lower bounded.le radius) mode)
        (sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0 (radialClamp lower bounded.le radius) mode) := by
    unfold lowRhoPhysicalCoefficient
    rw [original mode,inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (lowRhoPhysicalWeight_pos parameters lower positive radius mode).ne')]
  have knownZero : matrixUnit (0 : Fin 1) (index.castLE (by omega : 4 ≤ 7))
      (lowRhoPhysicalCoefficient parameters lower positive known radius mode) = 0 := by
    apply PiLp.ext
    intro component
    fin_cases component
    unfold lowRhoPhysicalCoefficient
    rw [sources mode]
    fin_cases index <;> simp [matrixUnit_apply,operatorBasis]
  change matrixUnit (0 : Fin 1) (index.castLE (by omega : 4 ≤ 7))
    (lowRhoPhysicalCoefficient parameters lower positive (unknown+known) radius mode) = _
  rw [added mode,map_add,knownZero,add_zero,unknownSame]
  exact rawPhysicalSevenVector_firstFour radius mode _ _ index

end Grad.ActualPolarEquations
