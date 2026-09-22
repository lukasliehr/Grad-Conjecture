import AKAO20SameCofactorJetComponentAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualPolarFlux
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceCollarRestriction
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualSmoothPhysicalField Grad.ActualCurrentPrimitives Grad.ActualPolarEquations
open Grad.BoundaryKernelAction Grad.AnnularWeightedSmoothness Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.ActualGaugeSigmaPrimitives

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (cofactorRow : Fin 3) (radial : Fin 2) (direction : Fin 3)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

def _root_.Grad.ActualSmoothPhysicalField.SmoothLowPhysicalRow.cofactorJetRow :
    SmoothLowPhysicalRow parameters lower positive
      (regularRadialBulkAction parameters 0 lower positive bounded.le
        (radialCofactorJetRowKernel parameters length compact state cofactorRow radial direction)
        (radialCofactorJetRowKernel_regular parameters length compact state cofactorRow radial direction) row) :=
  curves.action parameters lower positive bounded _
    (radialCofactorJetRowKernel_regular parameters length compact state cofactorRow radial direction)
    (actualCofactorRow_conjugated_smooth parameters length compact state lower positive bounded cofactorRow radial direction)

/-- The SAME completed original cofactor deviation equals literal polar matrix multiplication. -/
theorem fullField_cofactorJetRowProduct (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.cofactorJetRow parameters length compact lower positive bounded state cofactorRow radial direction).fullField bounded (radius,angles) =
      originalCofactorJetRowProduct parameters length compact state cofactorRow radial direction
        (collarRadius lower positive bounded.le radius) (fun angles => curves.fullField bounded (radius,angles)) angles := by
  let source := fun angles => curves.fullField bounded (radius,angles)
  have sourceContinuous : Continuous source := curves.fullField_continuous_angles bounded radius inside
  let r := collarRadius lower positive bounded.le radius
  apply congrFun ((curves.cofactorJetRow parameters length compact lower positive bounded state cofactorRow radial direction).fullField_eq_of_doubleCoefficient
    bounded radius inside (originalCofactorJetRowProduct parameters length compact state cofactorRow radial direction r source)
    (originalCofactorJetRowProduct_continuous parameters length compact state cofactorRow radial direction r source sourceContinuous) ?_ ?_ ?_) angles
  · intro axial polar
    unfold originalCofactorJetRowProduct
    apply Finset.sum_congr rfl
    intro component _
    rw [(originalCofactorJetSeries_periodic parameters length compact state cofactorRow component radial direction r (polar,axial)).1]
    rw [show source (polar+2*Real.pi,axial)=source (polar,axial) from curves.fullField_angular_shift bounded radius polar axial]
  · intro polar axial
    unfold originalCofactorJetRowProduct
    apply Finset.sum_congr rfl
    intro component _
    rw [(originalCofactorJetSeries_periodic parameters length compact state cofactorRow component radial direction r (polar,axial)).2]
    rw [show source (polar,axial+2*Real.pi)=source (polar,axial) from curves.fullField_cell_shift bounded radius polar axial]
  · intro mode
    symm
    apply curves.physicalCurve_action_eq_of_hasSum parameters lower positive bounded
      (radialCofactorJetRowKernel parameters length compact state cofactorRow radial direction)
      (radialCofactorJetRowKernel_regular parameters length compact state cofactorRow radial direction)
      (actualCofactorRow_conjugated_smooth parameters length compact state lower positive bounded cofactorRow radial direction) radius inside mode
    have series := originalCofactorJetRowProduct_hasSum parameters length compact state cofactorRow radial direction r source sourceContinuous mode
    apply series.congr_fun
    intro shift
    change rowMultiplicationEntry 3
      (fun component => radialCofactorJetScalar parameters length compact state cofactorRow component radial direction
        (collarRadius lower positive bounded.le radius))
      shift (twoFrequencyTranslation shift mode) (curves.physicalCurve 0 radius (twoFrequencyTranslation shift mode)) = _
    rw [curves.fullField_doubleCoefficient bounded radius inside]


end Grad.ActualPolarFlux
