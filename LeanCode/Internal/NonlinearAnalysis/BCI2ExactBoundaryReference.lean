import BCI1PhysicalBoundaryDeviation
import SCS39DoubleCoefficientAlgebra

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff

namespace Grad.ActualBoundaryInverse

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollar
open Grad.SourceCollarDivision Grad.BoundaryTrace Grad.ActualGaugeSigmaPrimitives Grad.ActualCurrentPrimitives
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.SourceCollarFullSource

def boundaryReferenceScalar (component : Fin 3) (mode : ℤ × ℤ) : ℂ :=
  if mode = (0, 0) then (if (0 : Fin 3) = component then 1 else 0) else 0

theorem polarBoundary_axial_continuous (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (component : Fin 3) (polar : ℝ) :
    Continuous (fun axial => polarMatrixEntry 2 component polar
      (familyMatrix family 0 axial (polarClosedPoint 1 polar zero_le_one le_rfl))) := by
  have continuousSeries := continuous_tsum
    (fun cell : ℤ => ((show Continuous (fourierPhase cell) by unfold fourierPhase; fun_prop).mul
      (continuous_const (y := polarEntryCell parameters family coherent 2 component cell (1, polar) 0))))
    (polarEntryCell_norm_summable parameters family coherent 2 component 1 polar zero_le_one le_rfl)
    (fun cell axial => by simp only [Pi.mul_apply, norm_mul, fourierPhase_norm, one_mul]; exact le_rfl)
  convert continuousSeries using 1
  funext axial
  exact (polarEntryCell_fourier parameters family coherent 2 component 1 polar axial zero_le_one le_rfl).tsum_eq.symm

theorem boundaryScalar_eq_deviation_add_reference (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact)
    (component : Fin 3) (mode : ℤ × ℤ) :
    boundaryScalar parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low component mode =
    boundaryDeviationScalar parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low component mode + boundaryReferenceScalar component mode := by
  let family := boundaryPolarDeviation parameters L rho alpha delta parameter epsilon field
  have coherent := boundaryPolarDeviation_coherent parameters L rho alpha delta parameter epsilon compact field
    compactNonnegative alphaSmall deltaSmall parameterSmall low
  let deviation := fun polar axial => polarMatrixEntry 2 component polar
    (familyMatrix family 0 axial (polarClosedPoint 1 polar zero_le_one le_rfl))
  let reference : ℂ := if (0 : Fin 3) = component then 1 else 0
  have inner (polar : ℝ) : angularCoefficient (fun axial =>
      originalBoundaryRow parameters L rho alpha delta parameter epsilon field axial polar
        (polarClosedPoint 1 polar zero_le_one le_rfl) component) mode.2 =
    angularCoefficient (deviation polar) mode.2 + (if mode.2 = 0 then reference else 0) := by
    have equality : (fun axial => originalBoundaryRow parameters L rho alpha delta parameter epsilon field axial polar
        (polarClosedPoint 1 polar zero_le_one le_rfl) component) =
        (fun axial => deviation polar axial + reference) := by
      funext axial
      change _ = polarMatrixEntry 2 component polar
        (familyMatrix (boundaryPolarDeviation parameters L rho alpha delta parameter epsilon field) 0 axial
          (polarClosedPoint 1 polar zero_le_one le_rfl)) + reference
      rw [boundaryPolarDeviation_outer parameters L rho alpha delta parameter epsilon compact field
        compactNonnegative alphaSmall deltaSmall parameterSmall low]
      exact (sub_add_cancel _ _).symm
    rw [equality, angularCoefficient_add_general _ _
      (polarBoundary_axial_continuous parameters family coherent component polar) continuous_const,
      angularCoefficient_constant]
  have polarContinuous : Continuous (fun polar => angularCoefficient (deviation polar) mode.2) := by
    change Continuous (fun polar => angularCoefficient (fun axial => polarMatrixEntry 2 component polar
      (familyMatrix family 0 axial (polarClosedPoint 1 polar zero_le_one le_rfl))) mode.2)
    simp_rw [polarEntry_axialCoefficient parameters family coherent 2 component 1 _ zero_le_one le_rfl mode.2]
    exact (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).continuous.comp
      ((polarEntryCell_smooth parameters family coherent 2 component mode.2).continuous.comp
        (continuous_const.prodMk continuous_id))
  rw [← boundaryScalar_doubleCoefficient parameters L rho alpha delta parameter epsilon compact field
    compactNonnegative alphaSmall deltaSmall parameterSmall low component mode]
  simp_rw [inner]
  rw [angularCoefficient_add_general _ _ polarContinuous continuous_const, angularCoefficient_constant]
  have deviationCoefficient : angularCoefficient (fun polar => angularCoefficient (deviation polar) mode.2) mode.1 =
      boundaryDeviationScalar parameters L rho alpha delta parameter epsilon compact field
        compactNonnegative alphaSmall deltaSmall parameterSmall low component mode :=
    polarEntry_doubleCoefficient parameters family coherent 2 component 1 zero_le_one le_rfl mode
  rw [deviationCoefficient]
  congr 1
  unfold boundaryReferenceScalar
  split_ifs <;> simp_all [Prod.ext_iff, reference]

theorem angularReferenceScalar_zero (component : Fin 3) :
    angularCoefficientSequence (boundaryReferenceScalar component) = 0 := by
  funext mode
  unfold angularCoefficientSequence boundaryReferenceScalar
  by_cases zero : mode = (0, 0)
  · subst mode
    simp
  · simp [zero]

theorem angularBoundaryScalar_eq_deviation (parameters : PhaseParameters)
    (L rho alpha delta parameter epsilon compact : ℝ) (field : ACore parameters 3)
    (compactNonnegative : 0 ≤ compact) (alphaSmall : |alpha| ≤ compact)
    (deltaSmall : |delta| ≤ compact) (parameterSmall : |parameter| ≤ compact)
    (low : physicalBudget parameters field rho epsilon 6 ≤ boundaryCoefficientLowRadius parameters L compact)
    (component : Fin 3) :
    angularCoefficientSequence (boundaryScalar parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low component) =
    angularCoefficientSequence (boundaryDeviationScalar parameters L rho alpha delta parameter epsilon compact field
      compactNonnegative alphaSmall deltaSmall parameterSmall low component) := by
  funext mode
  change Complex.I * (mode.1 : ℂ) * _ = _
  rw [boundaryScalar_eq_deviation_add_reference, mul_add]
  have reference := congrFun (angularReferenceScalar_zero component) mode
  change Complex.I * (mode.1 : ℂ) * boundaryReferenceScalar component mode = 0 at reference
  rw [reference, add_zero]
  rfl

end Grad.ActualBoundaryInverse
