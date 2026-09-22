import AKAM5SameOriginalFluxFidelity
import AKAJ4ExactCartesianPhysicalForce

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarFlux
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularPhysicalReconstruction Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.AnnularLowEnergy Grad.PhaseAlgebra

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)

 theorem originalBThreeKernel_regular :
    RegularKernelFamily (radialNormalizedBThreeKernel parameters length compact state) :=
  ((radialSignedCofactorRowKernel_regular parameters length compact state 2).comp
    (radialNormalizedCovariantKernel_regular parameters length compact state.val)).add
    ((radialSignedCofactorComponentKernel_regular parameters length compact state 1 2).comp
      (constantMatrixRadialKernel_regular parameters _ _ _))

 theorem originalBThreeKernel_smooth :
    SmoothConjugatedFamily parameters lower positive bounded.le (radialNormalizedBThreeKernel parameters length compact state) :=
  ((actualSignedCofactorRow_conjugated_smooth parameters length compact state lower positive bounded 2).comp
    (radialNormalizedCovariantKernel_conjugated_smooth parameters length compact state.val lower positive bounded)).add
    ((actualSignedCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded 1 2).comp
      (smoothConjugatedFamily_fixed parameters lower positive bounded
        (fun p => sevenInputSlotKernel p 3) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)))

def actualBThreeAction : DivisionRow 7 lower →L[ℂ] DivisionRow 1 lower :=
  regularRadialBulkAction parameters 0 lower positive bounded.le
    (radialNormalizedBThreeKernel parameters length compact state)
    (originalBThreeKernel_regular parameters length compact state)

def _root_.Grad.ActualSmoothPhysicalField.SmoothLowPhysicalRow.bThree {row : DivisionRow 7 lower}
    (seven : SmoothLowPhysicalRow parameters lower positive row) :
    SmoothLowPhysicalRow parameters lower positive (actualBThreeAction parameters length compact lower positive bounded state row) :=
  seven.action parameters lower positive bounded _
    (originalBThreeKernel_regular parameters length compact state)
    (originalBThreeKernel_smooth parameters length compact lower positive bounded state)

def _root_.Grad.ActualSmoothPhysicalField.SmoothLowPhysicalRow.lowPhysicalCurves {row : DivisionRow 7 lower}
    (seven : SmoothLowPhysicalRow parameters lower positive row) (index : Fin 3) :
    SmoothLowPhysicalRow parameters lower positive
      (lowPhysicalRowAction parameters length compact lower positive bounded.le state index row) :=
  seven.action parameters lower positive bounded (lowPhysicalRowKernel parameters length compact state index)
    (lowPhysicalRowKernel_regular parameters length compact state index)
    (sameFullPhysicalRows_conjugated_smooth parameters length compact state lower positive bounded index)

variable (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)

/-- The full physical c coefficient is exactly R of the SAME b3, including the scalar correction. -/
theorem sharedBThree_angularCoefficients :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      lowRhoPhysicalCoefficient parameters lower positive
        (lowPhysicalRowAction parameters length compact lower positive bounded.le state 1
          (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution)) radius mode =
      (Complex.I * (mode.1 : ℂ)) • lowRhoPhysicalCoefficient parameters lower positive
        (actualBThreeAction parameters length compact lower positive bounded state
          (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution)) radius mode := by
  let seven := fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution
  filter_upwards [fullStrongSevenInput_compatible_ae parameters length lower lengthPositive positive bounded.le data solution,
    originalPhysicalSlice_action parameters lower positive bounded.le
      (radialNormalizedBThreeKernel parameters length compact state) (originalBThreeKernel_regular parameters length compact state) seven,
    originalPhysicalSlice_action parameters lower positive bounded.le
      (lowPhysicalRowKernel parameters length compact state 1) (lowPhysicalRowKernel_regular parameters length compact state 1) seven,
    originalPhysicalSlice_coefficient parameters lower positive bounded.le
      (actualBThreeAction parameters length compact lower positive bounded state seven),
    originalPhysicalSlice_coefficient parameters lower positive bounded.le
      (lowPhysicalRowAction parameters length compact lower positive bounded.le state 1 seven)]
      with radius compatible bSame cSame bCoefficient cCoefficient
  let r := collarRadius lower positive bounded.le radius
  let input := (lowStorageWeight lower positive r.val : ℂ)⁻¹ • collectRadial lower seven radius
  have law : BulkSevenCompatibility input := compatible.smul _ _
  have derivative := radialNormalizedBThreeKernel_derivative parameters length compact state r 0 0
    (bulkSevenTrace parameters r input)
    (bulkSevenTrace_meanFree parameters r input 0 law.massMean)
    (bulkSevenTrace_derivative parameters r input 3 1 law.scalarDerivative)
  rw [bulkSevenTrace_flatten] at derivative
  have inputSame : bulkNegativeLift parameters r 7 input = originalPhysicalSlice parameters lower positive bounded.le seven radius := by
    exact map_smul (bulkNegativeLift parameters r 7) _ _
  rw [inputSame] at derivative
  intro mode
  have exactDerivative := derivative mode
  change negativeTraceCoefficient _ 0 0
    (fullNegativeKernelAction _ 0 0 (lowPhysicalRowKernel parameters length compact state 1 r)
      (originalPhysicalSlice parameters lower positive bounded.le seven radius)) mode = _ at exactDerivative
  rw [← cSame,← bSame] at exactDerivative
  dsimp only [r] at exactDerivative
  simp only [lowPhysicalRowAction,actualBThreeAction] at cCoefficient bCoefficient
  rw [cCoefficient mode,bCoefficient mode] at exactDerivative
  exact exactDerivative

/-- Genuine classical angular derivative of the full same-source b3 on the original collar. -/
theorem sharedBThree_classical_angular
    (curves : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution))
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (polar axial : ℝ) :
    HasDerivAt (fun angle => (curves.bThree parameters length compact lower positive bounded state).fullField bounded (radius,angle,axial))
      ((curves.lowPhysicalCurves parameters length compact lower positive bounded state 1).fullField bounded (radius,polar,axial)) polar :=
  samePhysical_angularDerivative _ _ bounded
    (sharedBThree_angularCoefficients parameters length compact lower positive bounded state lengthPositive data solution)
    radius inside polar axial

end Grad.ActualPolarFlux
