import GSP15OriginalGaugeSigmaConsumer

noncomputable section
namespace Grad.ActualPhysicalAngular
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Allocation Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives

def actualForceSlice (parameters : PhaseParameters) (L epsilon : ℝ) (field : ACore parameters 3)
    (kind : Fin 2) (component : Fin 3) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (axialAngle angle : ℝ) : ℂ :=
  originalPolarForceRow parameters L epsilon field kind axialAngle angle
    (polarClosedPoint radius angle nonnegative bounded) component - forceReferenceRow kind component

def actualSigmaSlice (parameters : PhaseParameters) (L epsilon : ℝ) (field : ACore parameters 3)
    (component : Fin 3) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (axialAngle angle : ℝ) : ℂ :=
  originalSigmaRow parameters L epsilon field axialAngle angle
    (polarClosedPoint radius angle nonnegative bounded) component + if (0 : Fin 3) = component then 1 else 0

/-- Genuine classical R of the actual AD10 force row; not just a new name for i*m. -/
def ActualForceAngularGoal : Prop :=
  ∀ (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (kind : Fin 2) (component : Fin 3) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1),
    (∀ axialAngle, Differentiable ℝ (actualForceSlice parameters L epsilon field kind component radius nonnegative bounded axialAngle)) ∧
    ∀ mode : ℤ × ℤ,
      angularCoefficient (fun angle => angularCoefficient (fun axialAngle =>
        deriv (actualForceSlice parameters L epsilon field kind component radius nonnegative bounded axialAngle) angle) mode.2) mode.1 =
        angularCoefficientSequence (forceScalar parameters L rho epsilon field kind low component 0 radius) mode

/-- Genuine classical R of the actual AF1 signed flux row. -/
def ActualSigmaAngularGoal : Prop :=
  ∀ (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1),
    (∀ axialAngle, Differentiable ℝ (actualSigmaSlice parameters L epsilon field component radius nonnegative bounded axialAngle)) ∧
    ∀ mode : ℤ × ℤ,
      angularCoefficient (fun angle => angularCoefficient (fun axialAngle =>
        deriv (actualSigmaSlice parameters L epsilon field component radius nonnegative bounded axialAngle) angle) mode.2) mode.1 =
        angularCoefficientSequence (sigmaScalar parameters L rho epsilon field low component 0 radius) mode

def ActualPhysicalAngularGoal : Prop := ActualForceAngularGoal ∧ ActualSigmaAngularGoal

#check ActualPhysicalAngularGoal
#print ActualForceAngularGoal
#print ActualSigmaAngularGoal

end Grad.ActualPhysicalAngular

