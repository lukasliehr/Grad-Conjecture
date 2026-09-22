import AKAF12ActualSourcePointwiseForceConsumer
import GPA5ForceAngularCells

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualForceMatrixFidelity
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceCollarRestriction
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualSmoothPhysicalField Grad.ActualCurrentPrimitives Grad.ActualPhysicalAngular

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (low : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (kind : Fin 2) (component : Fin 3) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
include nonnegative bounded

theorem forceScalar_norm_summable :
    Summable (fun mode => ‖forceScalar parameters length rho epsilon base kind low component 0 radius mode‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (forceScalarMoment_summable parameters length rho epsilon base kind low component 0 0 radius nonnegative bounded)
  intro mode
  change ‖_‖ ≤ coefficientRadialEnvelope parameters mode.2 radius * _^0 * ‖_‖
  simpa only [pow_zero,mul_one,one_mul] using mul_le_mul_of_nonneg_right
    (coefficientRadialEnvelope_one_le parameters radius nonnegative bounded mode.2)
    (norm_nonneg (forceScalar parameters length rho epsilon base kind low component 0 radius mode))

theorem forceScalar_angular_hasSum (cell : ℤ) (angle : ℝ) :
    HasSum (fun mode => cellExponential mode angle * forceScalar parameters length rho epsilon base kind low component 0 radius (mode,cell))
      (forcePolarCell parameters length rho epsilon base kind low component cell (radius,angle) 0) := by
  let value := fun angle => forcePolarCell parameters length rho epsilon base kind low component cell (radius,angle) 0
  have continuousValue : Continuous value := (PiLp.continuous_apply (p := 2) _ 0).comp
    ((forcePolarCell_smooth parameters length rho epsilon base kind low component cell).continuous.comp
      (continuous_const.prodMk continuous_id))
  have periodic : Function.Periodic value (2*Real.pi) := by
    intro angle
    simpa only [Prod.add_def,add_zero] using congrArg (fun vector : ComplexEuclidean 1 => vector 0)
      (forceAngularCell_periodic parameters length rho epsilon base low kind component cell (radius,angle))
  have coefficients (mode : ℤ) : angularCoefficient value mode =
      forceScalar parameters length rho epsilon base kind low component 0 radius (mode,cell) := by
    have projected := angularCoefficient_component
      (fun angle => forcePolarCell parameters length rho epsilon base kind low component cell (radius,angle))
      ((forcePolarCell_smooth parameters length rho epsilon base kind low component cell).continuous.comp
        (continuous_const.prodMk continuous_id)) 0 mode
    exact projected.symm.trans (congrArg (fun vector : ComplexEuclidean 1 => vector 0)
      (forcePolarCell_coefficient parameters length rho epsilon base kind low component cell mode 0 radius))
  have norms := (forceScalar_norm_summable parameters length rho epsilon base low kind component radius nonnegative bounded).comp_injective
    (fun a b equality => congrArg Prod.fst equality : Function.Injective (fun mode : ℤ => (mode,cell)))
  have result := periodicScalar_fourier_hasSum value continuousValue periodic
    (norms.of_norm.congr (fun mode => (coefficients mode).symm)) angle
  simpa only [coefficients] using result

/-- The actual completed force coefficient series sums to the literal
original force-matrix contraction at the same radius and both angles. -/
theorem forceScalar_double_hasSum (polar axial : ℝ) :
    HasSum (fun mode : ℤ × ℤ => cellExponential mode.2 axial *
      (cellExponential mode.1 polar * forceScalar parameters length rho epsilon base kind low component 0 radius mode))
      (forcePolarComponent kind polar (originalForceMatrix parameters length epsilon base axial
        (polarClosedPoint radius polar nonnegative bounded)) component) := by
  let term : ℤ × ℤ → ℂ := fun mode => cellExponential mode.2 axial *
    (cellExponential mode.1 polar * forceScalar parameters length rho epsilon base kind low component 0 radius mode)
  have norms : Summable (fun mode => ‖term mode‖) := by
    simpa only [term,norm_mul,cellExponential_norm,one_mul] using
      forceScalar_norm_summable parameters length rho epsilon base low kind component radius nonnegative bounded
  have rotated : Summable (fun pair : ℤ × ℤ => term (pair.2,pair.1)) :=
    (Equiv.prodComm ℤ ℤ).summable_iff.mpr norms.of_norm
  have equality : (∑' mode,term mode) =
      forcePolarComponent kind polar (originalForceMatrix parameters length epsilon base axial
        (polarClosedPoint radius polar nonnegative bounded)) component := by
    calc
      _ = ∑' pair : ℤ × ℤ,term (pair.2,pair.1) := ((Equiv.prodComm ℤ ℤ).tsum_eq term).symm
      _ = ∑' cell : ℤ,∑' mode : ℤ,term (mode,cell) := rotated.tsum_prod
      _ = ∑' cell : ℤ,cellExponential cell axial * forcePolarCell parameters length rho epsilon base kind low component cell (radius,polar) 0 := by
        apply tsum_congr
        intro cell
        rw [show (fun mode => term (mode,cell)) = (fun mode => cellExponential cell axial *
          (cellExponential mode polar * forceScalar parameters length rho epsilon base kind low component 0 radius (mode,cell))) from rfl,
          tsum_mul_left,(forceScalar_angular_hasSum parameters length rho epsilon base low kind component radius nonnegative bounded cell polar).tsum_eq]
      _ = _ := (forcePolarCell_actual_fourier parameters length rho epsilon base kind low component radius polar axial nonnegative bounded).tsum_eq
  exact equality ▸ norms.of_norm.hasSum

end Grad.ActualForceMatrixFidelity
