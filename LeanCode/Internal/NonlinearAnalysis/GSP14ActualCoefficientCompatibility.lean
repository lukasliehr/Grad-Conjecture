import GSP13PhysicalGaugeCovectors

noncomputable section
namespace Grad.ActualGaugeSigmaPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.Allocation Grad.ActualCurrentPrimitives

/-- The two independently constructed actual coefficient families satisfy AF2 exactly. -/
theorem sigmaScalar_eq_kappaScalar (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (mode : ℤ × ℤ) :
    sigmaScalar parameters L rho epsilon field low 1 0 radius mode =
      kappaScalar parameters L rho epsilon field low 0 0 radius mode := by
  rw [← sigmaScalar_doubleCoefficient parameters L rho epsilon field low 1 radius nonnegative bounded,
    ← actualKappa_doubleCoefficient parameters L rho epsilon field low 0 radius nonnegative bounded]
  simp only [originalSigma_kappa, Matrix.cons_val_zero, zero_ne_one, if_false, add_zero, sub_zero]

theorem gaugeAngularCoefficient_exact (parameters : PhaseParameters) (L rho alpha delta parameter epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (kind : Fin 2) (component : Fin 3) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (mode : ℤ × ℤ) :
    angularCoefficientSequence (gaugeScalar parameters L rho alpha delta parameter epsilon field low kind component 0 radius) mode =
      (Complex.I * (mode.1 : ℂ)) * angularCoefficient (fun angle => angularCoefficient (fun axialAngle =>
        originalGaugeRow parameters L rho alpha delta parameter epsilon field kind axialAngle angle
          (polarClosedPoint radius angle nonnegative bounded) component -
          (if (if kind = 0 then (1 : Fin 3) else 2) = component then 1 else 0)) mode.2) mode.1 := by
  rw [gaugeScalar_doubleCoefficient parameters L rho alpha delta parameter epsilon field low]
  rfl

theorem sigmaAngularCoefficient_exact (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (mode : ℤ × ℤ) :
    angularCoefficientSequence (sigmaScalar parameters L rho epsilon field low component 0 radius) mode =
      (Complex.I * (mode.1 : ℂ)) * angularCoefficient (fun angle => angularCoefficient (fun axialAngle =>
        originalSigmaRow parameters L epsilon field axialAngle angle
          (polarClosedPoint radius angle nonnegative bounded) component +
          (if (0 : Fin 3) = component then 1 else 0)) mode.2) mode.1 := by
  rw [sigmaScalar_doubleCoefficient parameters L rho epsilon field low]
  rfl

end Grad.ActualGaugeSigmaPrimitives
