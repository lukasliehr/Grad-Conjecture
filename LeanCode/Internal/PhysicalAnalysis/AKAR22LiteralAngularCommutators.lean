import AKAR21OriginalAngularPrimitive
import AKAR19CircleRepresentationAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceCollarRestriction
open Grad.BoundaryLift Grad.PhaseAlgebra Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.SourceCollarAngular Grad.AnnularGeneralSourceRegularity

variable {parameters : PhaseParameters} {input output : ℕ}

theorem OriginalCircleRotation.unique {field first second : CellL2 input}
    (one : OriginalCircleRotation field first) (two : OriginalCircleRotation field second) : first=second := by
  apply lp.ext
  funext mode
  exact (one mode).trans (two mode).symm

theorem OriginalCircleRotation.add {first second firstR secondR : CellL2 input}
    (one : OriginalCircleRotation first firstR) (two : OriginalCircleRotation second secondR) :
    OriginalCircleRotation (first+second) (firstR+secondR) := by
  intro mode
  change firstR mode+secondR mode = (_ : ℂ) • (first mode+second mode)
  rw [one,two,smul_add]

theorem OriginalCircleRotation.sub {first second firstR secondR : CellL2 input}
    (one : OriginalCircleRotation first firstR) (two : OriginalCircleRotation second secondR) :
    OriginalCircleRotation (first-second) (firstR-secondR) := by
  intro mode
  change firstR mode-secondR mode = (_ : ℂ) • (first mode-second mode)
  rw [one,two,smul_sub]

theorem OriginalCircleRotation.smul {field fieldR : CellL2 input}
    (rotation : OriginalCircleRotation field fieldR) (scalar : ℂ) :
    OriginalCircleRotation (scalar • field) (scalar • fieldR) := by
  intro mode
  change scalar • fieldR mode = (_ : ℂ) • (scalar • field mode)
  rw [rotation,smul_comm]

/-- Literal coefficient Leibniz rule: the derivative kernel acts only on the
coefficient, while the second summand is the actual R of the unknown. -/
theorem OriginalCircleRotation.kernel {field fieldR : CellL2 input}
    (rotation : OriginalCircleRotation field fieldR) (parameters : PhaseParameters) (radius : RadialPoint)
    (kernel : RadialKernel parameters radius input output) :
    OriginalCircleRotation (lambdaCircleAction parameters radius kernel field)
      (lambdaCircleAction parameters radius (angularCoefficientKernel kernel) field +
        lambdaCircleAction parameters radius kernel fieldR) := by
  unfold OriginalCircleRotation at rotation
  intro mode
  have derivative := (lambdaCircleAction_coefficient parameters radius (angularCoefficientKernel kernel) field mode).add
    (lambdaCircleAction_coefficient parameters radius kernel fieldR mode)
  have original := (lambdaCircleAction_coefficient parameters radius kernel field mode).const_smul (Complex.I*(mode.1 : ℂ))
  apply derivative.unique
  apply original.congr_fun
  intro shift
  simp only [angularCoefficientKernel_entry,smul_apply,rotation,map_smul,smul_smul]
  rw [← add_smul]
  congr 1
  change (lambdaPhaseRatio parameters radius.val shift mode : ℂ)*(Complex.I*(shift.1 : ℂ)) +
    (lambdaPhaseRatio parameters radius.val shift mode : ℂ)*(Complex.I*((mode.1-shift.1 : ℤ) : ℂ)) =
      (Complex.I*(mode.1 : ℂ))*(lambdaPhaseRatio parameters radius.val shift mode : ℂ)
  push_cast
  ring

theorem OriginalCircleRotation.valueMap {field fieldR : CellL2 input}
    (rotation : OriginalCircleRotation field fieldR) (parameters : PhaseParameters)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) :
    OriginalCircleRotation (originalCircleMatrix parameters mapping field) (originalCircleMatrix parameters mapping fieldR) := by
  intro mode
  change mapping (fieldR mode)=(_ : ℂ) • mapping (field mode)
  rw [rotation,map_smul]

theorem originalSineScalar : (2*Complex.I : ℂ)⁻¹ = -(Complex.I/2) := by
  apply (inv_eq_iff_eq_inv).mpr
  field_simp
  linear_combination Complex.I_sq

theorem OriginalCircleRotation.cosine {field fieldR : CellL2 input}
    (rotation : OriginalCircleRotation field fieldR) (parameters : PhaseParameters) :
    OriginalCircleRotation (weightedHilbertCosine parameters input 0 field)
      (weightedHilbertCosine parameters input 0 fieldR-weightedHilbertSine parameters input 0 field) := by
  unfold OriginalCircleRotation at rotation
  intro mode
  change (2 : ℂ)⁻¹ • (annularShiftScalar 0 1 mode • fieldR (mode.1-1,mode.2)+annularShiftScalar 0 (-1) mode • fieldR (mode.1-(-1),mode.2)) -
    (2*Complex.I : ℂ)⁻¹ • (annularShiftScalar 0 1 mode • field (mode.1-1,mode.2)-annularShiftScalar 0 (-1) mode • field (mode.1-(-1),mode.2)) =
    (_ : ℂ) • ((2 : ℂ)⁻¹ • (annularShiftScalar 0 1 mode • field (mode.1-1,mode.2)+annularShiftScalar 0 (-1) mode • field (mode.1-(-1),mode.2)))
  simp only [annularShiftScalar,pow_zero,Complex.ofReal_one,one_smul,rotation,originalSineScalar]
  push_cast
  module

theorem OriginalCircleRotation.sine {field fieldR : CellL2 input}
    (rotation : OriginalCircleRotation field fieldR) (parameters : PhaseParameters) :
    OriginalCircleRotation (weightedHilbertSine parameters input 0 field)
      (weightedHilbertSine parameters input 0 fieldR+weightedHilbertCosine parameters input 0 field) := by
  unfold OriginalCircleRotation at rotation
  intro mode
  change (2*Complex.I : ℂ)⁻¹ • (annularShiftScalar 0 1 mode • fieldR (mode.1-1,mode.2)-annularShiftScalar 0 (-1) mode • fieldR (mode.1-(-1),mode.2)) +
    (2 : ℂ)⁻¹ • (annularShiftScalar 0 1 mode • field (mode.1-1,mode.2)+annularShiftScalar 0 (-1) mode • field (mode.1-(-1),mode.2)) =
    (_ : ℂ) • ((2*Complex.I : ℂ)⁻¹ • (annularShiftScalar 0 1 mode • field (mode.1-1,mode.2)-annularShiftScalar 0 (-1) mode • field (mode.1-(-1),mode.2)))
  simp only [annularShiftScalar,pow_zero,Complex.ofReal_one,one_smul,rotation,originalSineScalar]
  push_cast
  apply PiLp.ext
  intro slot
  simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
  ring_nf
  simp only [Complex.I_sq]
  ring

end Grad.OriginalKernelRetainedDecay
