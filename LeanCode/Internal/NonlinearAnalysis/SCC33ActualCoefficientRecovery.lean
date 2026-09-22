import SCC32ActualKappaProduct
import GC14SeedFourierRecovery

noncomputable section
open Set MeasureTheory
open scoped BigOperators Topology

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.BoundaryTrace
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.SourceCollarDivision Grad.SourceCollarRestriction

theorem coefficientColumnJet_norm_summable {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (column : PhysicalValue input) (point : ClosedDisk) :
    Summable (fun cell => ‖(coefficientColumnJet parameters family coherent cell column).value point‖) := by
  simp only [coefficientColumnJet_value]
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun cell => (coefficientValue (family 0) cell point).le_opNorm column)
    ((coefficientValue_point_norm_summable (unitDiskAdmissible parameters) (family 0) point).mul_right ‖column‖)

theorem kappaPolarCellTerm_norm_summable (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (slot : Fin 2 × Fin 2) (radius angle : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (fun cell => ‖kappaPolarCellTerm parameters L rho epsilon field low component slot cell (radius, angle)‖) := by
  simp only [kappaPolarCellTerm, angularCharacterField, norm_smul, cellExponential_norm, one_mul,
    originalPolarValue_closed _ radius angle nonnegative bounded]
  exact coefficientColumnJet_norm_summable parameters _
    (mappedCofactorFamily_coherent parameters L rho epsilon field _ low) _ _

theorem kappaPolarCell_norm_summable (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (fun cell => ‖kappaPolarCell parameters L rho epsilon field low component cell (radius, angle) 0‖) := by
  have norms : Summable (fun cell => ∑ slot : Fin 2 × Fin 2,
      ‖kappaPolarCellTerm parameters L rho epsilon field low component slot cell (radius, angle)‖) :=
    summable_sum (fun slot _ => kappaPolarCellTerm_norm_summable parameters L rho epsilon field low component slot radius angle nonnegative bounded)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ norms
  intro cell
  apply (PiLp.norm_apply_le _ 0).trans
  simpa only [kappaPolarCell, Finset.sum_apply] using norm_sum_le (Finset.univ)
    (fun slot => kappaPolarCellTerm parameters L rho epsilon field low component slot cell (radius, angle))

theorem angularCoefficient_of_axialSeries {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] [CompleteSpace Value] (coefficients : ℤ → Value)
    (norms : Summable (fun cell => ‖coefficients cell‖)) (field : ℝ → Value)
    (series : ∀ angle : ℝ, HasSum (fun cell => fourierPhase cell angle • coefficients cell) (field angle))
    (cell : ℤ) : angularCoefficient field cell = coefficients cell := by
  have equality : field = (fun angle : ℝ => ∑' source, cellCharacter source (angle : CellCircle) • coefficients source) := by
    funext angle
    rw [← (series angle).tsum_eq]
    apply tsum_congr
    intro source
    rw [cellCharacter_coe]
    rfl
  rw [equality]
  exact (angularCoefficient_circle
    (fun circle : CellCircle => ∑' source, cellCharacter source circle • coefficients source) cell).trans
    (seedCircleSeries_coefficient coefficients norms cell)

theorem actualKappa_axialCoefficient (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (cell : ℤ) :
    angularCoefficient (fun axialAngle => Grad.SourceCollar.physicalKappa angle
      (Grad.SourceCollar.originalPhysicalSignedCofactor parameters L epsilon field axialAngle
        (polarClosedPoint radius angle nonnegative bounded)) component - (![0, -1, 0] : Fin 3 → ℂ) component) cell =
      kappaPolarCell parameters L rho epsilon field low component cell (radius, angle) 0 :=
  angularCoefficient_of_axialSeries _
    (kappaPolarCell_norm_summable parameters L rho epsilon field low component radius angle nonnegative bounded) _
    (kappaPolarCell_actual_fourier parameters L rho epsilon field low component radius angle · nonnegative bounded) cell

/-- The coefficients estimated by BS40 are the literal iterated Fourier
integrals of the actual physical signed cofactor, with both original periods. -/
theorem actualKappa_doubleCoefficient (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (mode : ℤ × ℤ) :
    angularCoefficient (fun angle => angularCoefficient (fun axialAngle => Grad.SourceCollar.physicalKappa angle
      (Grad.SourceCollar.originalPhysicalSignedCofactor parameters L epsilon field axialAngle
        (polarClosedPoint radius angle nonnegative bounded)) component - (![0, -1, 0] : Fin 3 → ℂ) component) mode.2) mode.1 =
      kappaScalar parameters L rho epsilon field low component 0 radius mode := by
  simp_rw [actualKappa_axialCoefficient parameters L rho epsilon field low component radius _ nonnegative bounded mode.2]
  have projected := angularCoefficient_component
    (fun angle => kappaPolarCell parameters L rho epsilon field low component mode.2 (radius, angle))
    ((kappaPolarCell_smooth parameters L rho epsilon field low component mode.2).continuous.comp
      (continuous_const.prodMk continuous_id)) 0 mode.1
  exact projected.symm.trans (congrArg (fun value : ComplexEuclidean 1 => value 0)
    (kappaPolarCell_coefficient parameters L rho epsilon field low component mode.2 mode.1 0 radius))

end Grad.SourceCollarCoefficients
