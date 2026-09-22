import AKAF4ActualSourceCovariantAngularConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.AnnularPhysicalReconstruction Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.ActualSmoothPhysicalField Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.Ledger

/-- A genuine stored angular relation gives the classical derivative of the
same normalized scalar physical coordinates, with the actual rho factor. -/
theorem samePhysical_projectedAngularDerivative {dimension : ℕ} {parameters : PhaseParameters}
    {lower : ℝ} {positive : 0 < lower} {row : DivisionRow dimension lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower < 1)
    (input output : Fin dimension)
    (same : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      row mode radius output = (Complex.I * (mode.1 : ℂ)) * row mode radius input)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (polar axial : ℝ) :
    HasDerivAt (fun angle => (curves.bulkUnit (0 : Fin 1) input).fullField bounded (radius,angle,axial))
      ((curves.bulkUnit (0 : Fin 1) output).fullField bounded (radius,polar,axial)) polar := by
  apply samePhysical_angularDerivative _ _ bounded _ radius inside polar axial
  filter_upwards [same,
    lowRhoPhysicalCoefficient_bulkUnit parameters lower positive (0 : Fin 1) input row,
    lowRhoPhysicalCoefficient_bulkUnit parameters lower positive (0 : Fin 1) output row]
      with location law first second
  intro mode
  rw [first mode,second mode]
  apply PiLp.ext
  intro component
  fin_cases component
  simp only [matrixUnit_apply,lowRhoPhysicalCoefficient,PiLp.smul_apply,smul_eq_mul]
  rw [law mode]
  ring

variable (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)

/-- The SAME full seven input has both genuine scalar and source angular
relations; these are consequences of the actual datum, not PDE premises. -/
theorem sharedSeven_storedAngularLaws :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution) mode radius 1 =
        (Complex.I * (mode.1 : ℂ)) * (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution) mode radius 3 ∧
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution) mode radius 5 =
        (Complex.I * (mode.1 : ℂ)) * (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution) mode radius 4 := by
  filter_upwards [fullStrongSevenInput_compatible_ae parameters length lower lengthPositive positive bounded.le data solution,
    collectRadial_ae lower (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution)]
      with radius laws actual
  intro mode
  have scalar := laws.scalarDerivative mode
  have source := laws.sourceDerivative mode
  rw [actual mode] at scalar source
  exact ⟨scalar,source⟩

/-- Genuine classical R(Xi/r) and R(F0) for the same complete input fields. -/
theorem sharedSeven_classical_angular
    (curves : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution))
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (polar axial : ℝ) :
    HasDerivAt (fun angle => (curves.bulkUnit (0 : Fin 1) 3).fullField bounded (radius,angle,axial))
      ((curves.bulkUnit (0 : Fin 1) 1).fullField bounded (radius,polar,axial)) polar ∧
    HasDerivAt (fun angle => (curves.bulkUnit (0 : Fin 1) 4).fullField bounded (radius,angle,axial))
      ((curves.bulkUnit (0 : Fin 1) 5).fullField bounded (radius,polar,axial)) polar := by
  have laws := sharedSeven_storedAngularLaws parameters length lower positive bounded lengthPositive data solution
  exact ⟨samePhysical_projectedAngularDerivative curves bounded 3 1
    (laws.mono (fun _ law mode => (law mode).1)) radius inside polar axial,
    samePhysical_projectedAngularDerivative curves bounded 4 5
    (laws.mono (fun _ law mode => (law mode).2)) radius inside polar axial⟩

end Grad.ActualPolarEquations
