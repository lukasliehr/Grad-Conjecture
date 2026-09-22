import GSP9OneHighPolarMoments

noncomputable section
open scoped BigOperators
namespace Grad.ActualGaugeSigmaPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision
open Grad.ActualCurrentPrimitives Grad.GaugeCoefficients.Physical.Allocation

def sigmaScalar (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radial : ℕ) (radius : ℝ) : ℤ × ℤ → ℂ :=
  polarEntryScalar parameters (originalCofactorDeviation parameters L epsilon field) (originalCofactorDeviation_coherent parameters L rho epsilon field low) 0 component radial radius

def sigmaScalarConstant (parameters : PhaseParameters) (L : ℝ) 
    (component : Fin 3) (tangential radial : ℕ) : ℝ :=
  physicalPolarEntryConstant (originalCofactorProfile parameters L).deviation 0 component tangential radial

theorem sigmaScalarConstant_nonnegative (parameters : PhaseParameters) (L : ℝ) 
    (component : Fin 3) (tangential radial : ℕ) :
    0 ≤ sigmaScalarConstant parameters L component tangential radial :=
  physicalPolarEntryConstant_nonnegative _ _ _ _ _

theorem sigmaScalar_hasDerivAt (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radial : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    HasDerivAt (fun radius => sigmaScalar parameters L rho epsilon field low component radial radius mode)
      (sigmaScalar parameters L rho epsilon field low component (radial + 1) radius mode) radius :=
  polarEntryScalar_hasDerivAt parameters _ (originalCofactorDeviation_coherent parameters L rho epsilon field low) 0 component radial radius mode

theorem sigmaScalarMoment_summable (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (tangential radial : ℕ) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (productMoment parameters tangential radius (sigmaScalar parameters L rho epsilon field low component radial radius)) :=
  polarEntryScalarMoment_summable parameters _ (originalCofactorDeviation_coherent parameters L rho epsilon field low) 0 component tangential radial radius nonnegative bounded

/-- Full original-width (m,n) moment with one B_(t+k+5), on the original B6 ball. -/
theorem sigmaScalarMoment_bound (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (tangential radial : ℕ) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    (∑' mode, productMoment parameters tangential radius (sigmaScalar parameters L rho epsilon field low component radial radius) mode) ≤
      sigmaScalarConstant parameters L component tangential radial *
        physicalBudget parameters field rho epsilon (tangential + radial + 5) :=
  physicalPolarEntryScalarMoment_bound parameters _ (originalCofactorDeviation_coherent parameters L rho epsilon field low) field rho epsilon (originalCofactorProfile parameters L).deviation
    (originalCofactorDeviation_bound parameters L rho epsilon field low) 0 component tangential radial radius nonnegative bounded

/-- The literal R multiplier is i*m; its full moment costs exactly one further grade. -/
theorem sigmaAngularScalarMoment_bound (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (tangential radial : ℕ) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (productMoment parameters tangential radius (angularCoefficientSequence (sigmaScalar parameters L rho epsilon field low component radial radius))) ∧
    (∑' mode, productMoment parameters tangential radius (angularCoefficientSequence (sigmaScalar parameters L rho epsilon field low component radial radius)) mode) ≤
      sigmaScalarConstant parameters L component (tangential + 1) radial *
        physicalBudget parameters field rho epsilon (tangential + radial + 6) :=
  physicalRotatedPolarEntryScalarMoment_bound parameters _ (originalCofactorDeviation_coherent parameters L rho epsilon field low) field rho epsilon (originalCofactorProfile parameters L).deviation
    (originalCofactorDeviation_bound parameters L rho epsilon field low) 0 component tangential radial radius nonnegative bounded

end Grad.ActualGaugeSigmaPrimitives

