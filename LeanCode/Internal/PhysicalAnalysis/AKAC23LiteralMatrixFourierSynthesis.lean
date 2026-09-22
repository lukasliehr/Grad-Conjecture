import AKAC22ExactRotatedPhysicalVector

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceCollarRestriction
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryLift Grad.PhaseAlgebra Grad.ActualPhysicalField
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation

local instance matrixAngularPeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

theorem periodicScalar_fourier_hasSum (field : ℝ → ℂ) (continuousField : Continuous field)
    (periodic : Function.Periodic field (2 * Real.pi))
    (summable : Summable (angularCoefficient field)) (angle : ℝ) :
    HasSum (fun mode => cellExponential mode angle * angularCoefficient field mode) (field angle) := by
  let circle : C(CellCircle,ℂ) := ⟨periodic.lift,periodicLift_continuous field continuousField periodic⟩
  have coefficients (mode : ℤ) : fourierCoeff circle mode = angularCoefficient field mode := by
    rw [← angularCoefficient_circle]
    rfl
  have actualSummable : Summable (fourierCoeff circle) := summable.congr (fun mode => (coefficients mode).symm)
  have series := has_pointwise_sum_fourier_series_of_summable actualSummable (angle : CellCircle)
  apply series.congr_fun
  intro mode
  rw [coefficients]
  change _ = angularCoefficient field mode * cellCharacter mode (angle : CellCircle)
  rw [cellCharacter_coe,mul_comm]

variable {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (row : Fin output) (column : Fin input)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
include nonnegative bounded

theorem physicalMatrixScalar_norm_summable :
    Summable (fun mode : ℤ × ℤ => ‖physicalMatrixScalar parameters family coherent row column 0 radius mode‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (physicalMatrixScalar_moment_summable parameters family coherent row column 0 0 radius nonnegative bounded)
  intro mode
  change ‖_‖ ≤ coefficientRadialEnvelope parameters mode.2 radius * _ ^ 0 * ‖_‖
  simpa only [pow_zero,mul_one,one_mul] using mul_le_mul_of_nonneg_right
    (coefficientRadialEnvelope_one_le parameters radius nonnegative bounded mode.2)
    (norm_nonneg (physicalMatrixScalar parameters family coherent row column 0 radius mode))

theorem physicalMatrixScalar_angular_hasSum (cell : ℤ) (angle : ℝ) :
    HasSum (fun mode : ℤ => cellExponential mode angle *
      physicalMatrixScalar parameters family coherent row column 0 radius (mode,cell))
      (originalPolarValue (coefficientColumnJet parameters family coherent cell (operatorBasis column)) (radius,angle) row) := by
  let value := fun angle => originalPolarValue
    (coefficientColumnJet parameters family coherent cell (operatorBasis column)) (radius,angle) row
  have continuousValue : Continuous value :=
    (PiLp.continuous_apply (p := 2) _ row).comp
      ((originalPolarValue_smooth _).continuous.comp (continuous_const.prodMk continuous_id))
  have periodic : Function.Periodic value (2*Real.pi) := by
    intro angle
    simpa only [Prod.add_def, add_zero] using congrArg (fun vector : ComplexEuclidean output => vector row)
      (originalPolarValue_periodic _ (radius,angle))
  have coefficients (mode : ℤ) : angularCoefficient value mode =
      physicalMatrixScalar parameters family coherent row column 0 radius (mode,cell) := by
    exact (angularCoefficient_component _
      ((originalPolarValue_smooth _).continuous.comp (continuous_const.prodMk continuous_id)) row mode).symm
  have norms := (physicalMatrixScalar_norm_summable parameters family coherent row column radius nonnegative bounded).comp_injective
    (fun a b equality => congrArg Prod.fst equality : Function.Injective (fun mode : ℤ => (mode,cell)))
  have result := periodicScalar_fourier_hasSum value continuousValue periodic
    (norms.of_norm.congr (fun mode => (coefficients mode).symm)) angle
  simpa only [coefficients] using result

/-- Literal full matrix multiplication kernel: its complete two-frequency
series sums to the existing physical Cartesian matrix at the same point. -/
theorem physicalMatrixScalar_double_hasSum (polar axial : ℝ) :
    HasSum (fun mode : ℤ × ℤ => cellExponential mode.2 axial *
      (cellExponential mode.1 polar * physicalMatrixScalar parameters family coherent row column 0 radius mode))
      (familyMatrix family 0 axial (polarClosedPoint radius polar nonnegative bounded) row column) := by
  let term : ℤ × ℤ → ℂ := fun mode => cellExponential mode.2 axial *
    (cellExponential mode.1 polar * physicalMatrixScalar parameters family coherent row column 0 radius mode)
  have norms : Summable (fun mode => ‖term mode‖) := by
    simpa only [term,norm_mul,cellExponential_norm,one_mul] using
      physicalMatrixScalar_norm_summable parameters family coherent row column radius nonnegative bounded
  have rotated : Summable (fun pair : ℤ × ℤ => term (pair.2,pair.1)) :=
    (Equiv.prodComm ℤ ℤ).summable_iff.mpr norms.of_norm
  have equality : (∑' mode,term mode) =
      familyMatrix family 0 axial (polarClosedPoint radius polar nonnegative bounded) row column := by
    calc
      _ = ∑' pair : ℤ × ℤ,term (pair.2,pair.1) := ((Equiv.prodComm ℤ ℤ).tsum_eq term).symm
      _ = ∑' cell : ℤ,∑' mode : ℤ,term (mode,cell) := rotated.tsum_prod
      _ = ∑' cell : ℤ,cellExponential cell axial *
          originalPolarValue (coefficientColumnJet parameters family coherent cell (operatorBasis column)) (radius,polar) row := by
        apply tsum_congr
        intro cell
        rw [show (fun mode => term (mode,cell)) = (fun mode => cellExponential cell axial *
          (cellExponential mode polar * physicalMatrixScalar parameters family coherent row column 0 radius (mode,cell))) from rfl,
          tsum_mul_left,(physicalMatrixScalar_angular_hasSum parameters family coherent row column radius nonnegative bounded cell polar).tsum_eq]
      _ = _ := by
        exact ((PiLp.proj 2 (fun _ : Fin output => ℂ) row : ComplexEuclidean output →L[ℂ] ℂ).hasSum
          (coefficientColumnJet_polarFourier parameters family coherent (operatorBasis column) radius polar axial nonnegative bounded)).tsum_eq
  exact equality ▸ norms.of_norm.hasSum

end Grad.ActualSmoothPhysicalField
