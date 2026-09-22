import ACP15PhysicalFrameRotation

noncomputable section
open scoped BigOperators
namespace Grad.ActualCurrentPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Allocation

/-- The R slot needed by the coefficientwise AE/AF reconstruction is the
Fourier angular derivative of the literal AD10 row. It is not supplied as
an independent coefficient family. Classical physical AF16 correspondence
is retained as a later consumer obligation. -/
theorem forceAngularCoefficient_exact (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (mode : ℤ × ℤ) :
    angularCoefficientSequence (forceScalar parameters L rho epsilon field kind low component 0 radius) mode =
      (Complex.I * (mode.1 : ℂ)) * angularCoefficient (fun angle => angularCoefficient (fun axialAngle =>
        originalPolarForceRow parameters L epsilon field kind axialAngle angle
          (polarClosedPoint radius angle nonnegative bounded) component - forceReferenceRow kind component) mode.2) mode.1 := by
  rw [originalPolarForceRow_doubleCoefficient parameters L rho epsilon field kind low]
  rfl

/-- Universal original-width full-cell force coefficient consumer. A single
B6 neighborhood is chosen before both grades; later AE inversion may use
its fixed B7 sub-neighborhood, but no high-grade smallness is introduced. -/
theorem originalForceCoefficientConsumer (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (tangential radial : ℕ) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (productMoment parameters tangential radius
      (forceScalar parameters L rho epsilon field kind low component radial radius)) ∧
    (∑' mode, productMoment parameters tangential radius
      (forceScalar parameters L rho epsilon field kind low component radial radius) mode) ≤
        forceFourierConstant parameters L kind tangential radial *
          physicalBudget parameters field rho epsilon (tangential + radial + 6) ∧
    Summable (productMoment parameters tangential radius
      (angularCoefficientSequence (forceScalar parameters L rho epsilon field kind low component radial radius))) ∧
    (∑' mode, productMoment parameters tangential radius
      (angularCoefficientSequence (forceScalar parameters L rho epsilon field kind low component radial radius)) mode) ≤
        forceFourierConstant parameters L kind (tangential + 1) radial *
          physicalBudget parameters field rho epsilon (tangential + radial + 7) :=
  ⟨forceScalarMoment_summable parameters L rho epsilon field kind low component tangential radial radius nonnegative bounded,
   forceScalarMoment_bound parameters L rho epsilon field kind low component tangential radial radius nonnegative bounded,
   rotatedForceScalarMoment_bound parameters L rho epsilon field kind low component tangential radial radius nonnegative bounded⟩

end Grad.ActualCurrentPrimitives
