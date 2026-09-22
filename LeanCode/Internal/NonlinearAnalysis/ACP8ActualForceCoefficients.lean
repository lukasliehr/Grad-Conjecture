import ACP7ForcePhysicalSeries
import SCC33ActualCoefficientRecovery

noncomputable section
open scoped BigOperators
namespace Grad.ActualCurrentPrimitives
open Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.BoundaryTrace
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.SourceCollarDivision Grad.SourceCollarRestriction

theorem forcePolarCellTerm_norm_summable (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (slot : Fin 2 × Fin 2) (radius angle : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (fun cell => ‖forcePolarCellTerm parameters L rho epsilon field kind low component slot cell (radius, angle)‖) := by
  simp only [forcePolarCellTerm, angularCharacterField, norm_smul, cellExponential_norm, one_mul,
    originalPolarValue_closed _ radius angle nonnegative bounded]
  exact coefficientColumnJet_norm_summable parameters _
    (mappedForceFamily_coherent parameters L rho epsilon field _ low) _ _

theorem forcePolarCell_norm_summable (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (fun cell => ‖forcePolarCell parameters L rho epsilon field kind low component cell (radius, angle) 0‖) := by
  have norms : Summable (fun cell => ∑ slot : Fin 2 × Fin 2,
      ‖forcePolarCellTerm parameters L rho epsilon field kind low component slot cell (radius, angle)‖) :=
    summable_sum (fun slot _ => forcePolarCellTerm_norm_summable parameters L rho epsilon field kind low component slot radius angle nonnegative bounded)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ norms
  intro cell
  apply (PiLp.norm_apply_le _ 0).trans
  simpa only [forcePolarCell, Finset.sum_apply] using norm_sum_le (Finset.univ)
    (fun slot => forcePolarCellTerm parameters L rho epsilon field kind low component slot cell (radius, angle))

theorem actualForce_axialCoefficient (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (cell : ℤ) :
    angularCoefficient (fun axialAngle => forcePolarComponent kind angle
      (originalForceMatrix parameters L epsilon field axialAngle
        (polarClosedPoint radius angle nonnegative bounded)) component) cell =
      forcePolarCell parameters L rho epsilon field kind low component cell (radius, angle) 0 :=
  angularCoefficient_of_axialSeries _
    (forcePolarCell_norm_summable parameters L rho epsilon field kind low component radius angle nonnegative bounded) _
    (forcePolarCell_actual_fourier parameters L rho epsilon field kind low component radius angle · nonnegative bounded) cell

/-- The coefficients estimated by AD24 are the literal iterated Fourier
integrals of the actual physical force rows, with both original periods. -/
theorem actualForce_doubleCoefficient (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (mode : ℤ × ℤ) :
    angularCoefficient (fun angle => angularCoefficient (fun axialAngle => forcePolarComponent kind angle
      (originalForceMatrix parameters L epsilon field axialAngle
        (polarClosedPoint radius angle nonnegative bounded)) component) mode.2) mode.1 =
      (forceFourier parameters L rho epsilon field kind low component 0 radius mode) 0 := by
  simp_rw [actualForce_axialCoefficient parameters L rho epsilon field kind low component radius _ nonnegative bounded mode.2]
  have projected := angularCoefficient_component
    (fun angle => forcePolarCell parameters L rho epsilon field kind low component mode.2 (radius, angle))
    ((forcePolarCell_smooth parameters L rho epsilon field kind low component mode.2).continuous.comp
      (continuous_const.prodMk continuous_id)) 0 mode.1
  exact projected.symm.trans (congrArg (fun value : ComplexEuclidean 1 => value 0)
    (forcePolarCell_coefficient parameters L rho epsilon field kind low component mode.2 mode.1 0 radius))

end Grad.ActualCurrentPrimitives

