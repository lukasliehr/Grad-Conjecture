import GSP9OneHighPolarMoments

noncomputable section
open scoped BigOperators
namespace Grad.ActualGaugeSigmaPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision
open Grad.ActualCurrentPrimitives Grad.GaugeCoefficients.Physical.Allocation

def gaugeScalar (parameters : PhaseParameters) (L rho alpha delta parameter epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (kind : Fin 2) (component : Fin 3) (radial : ℕ) (radius : ℝ) : ℤ × ℤ → ℂ :=
  polarEntryScalar parameters (originalGaugeDeviation parameters L rho alpha delta parameter epsilon field) (originalGaugeDeviation_coherent parameters L rho alpha delta parameter epsilon field low) (if kind = 0 then 1 else 2) component radial radius

def gaugeScalarConstant (parameters : PhaseParameters) (L : ℝ) (compactRadius : ℝ) 
    (kind : Fin 2) (component : Fin 3) (tangential radial : ℕ) : ℝ :=
  physicalPolarEntryConstant (originalGaugeProfile parameters L compactRadius).deviation (if kind = 0 then 1 else 2) component tangential radial

theorem gaugeScalarConstant_nonnegative (parameters : PhaseParameters) (L : ℝ) (compactRadius : ℝ) 
    (kind : Fin 2) (component : Fin 3) (tangential radial : ℕ) :
    0 ≤ gaugeScalarConstant parameters L compactRadius kind component tangential radial :=
  physicalPolarEntryConstant_nonnegative _ _ _ _ _

theorem gaugeScalar_hasDerivAt (parameters : PhaseParameters) (L rho alpha delta parameter epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (kind : Fin 2) (component : Fin 3) (radial : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    HasDerivAt (fun radius => gaugeScalar parameters L rho alpha delta parameter epsilon field low kind component radial radius mode)
      (gaugeScalar parameters L rho alpha delta parameter epsilon field low kind component (radial + 1) radius mode) radius :=
  polarEntryScalar_hasDerivAt parameters _ (originalGaugeDeviation_coherent parameters L rho alpha delta parameter epsilon field low) (if kind = 0 then 1 else 2) component radial radius mode

theorem gaugeScalarMoment_summable (parameters : PhaseParameters) (L rho alpha delta parameter epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (kind : Fin 2) (component : Fin 3) (tangential radial : ℕ) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (productMoment parameters tangential radius (gaugeScalar parameters L rho alpha delta parameter epsilon field low kind component radial radius)) :=
  polarEntryScalarMoment_summable parameters _ (originalGaugeDeviation_coherent parameters L rho alpha delta parameter epsilon field low) (if kind = 0 then 1 else 2) component tangential radial radius nonnegative bounded

/-- Full original-width (m,n) moment with one B_(t+k+5), on the original B6 ball. -/
theorem gaugeScalarMoment_bound (parameters : PhaseParameters) (L rho alpha delta parameter epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (compactRadius : ℝ) (kind : Fin 2) (component : Fin 3) (tangential radial : ℕ) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius) (deltaSmall : |delta| ≤ compactRadius) (parameterSmall : |parameter| ≤ compactRadius) :
    (∑' mode, productMoment parameters tangential radius (gaugeScalar parameters L rho alpha delta parameter epsilon field low kind component radial radius) mode) ≤
      gaugeScalarConstant parameters L compactRadius kind component tangential radial *
        physicalBudget parameters field rho epsilon (tangential + radial + 5) :=
  physicalPolarEntryScalarMoment_bound parameters _ (originalGaugeDeviation_coherent parameters L rho alpha delta parameter epsilon field low) field rho epsilon (originalGaugeProfile parameters L compactRadius).deviation
    (originalGaugeDeviation_bound parameters L rho alpha delta parameter epsilon compactRadius field compactNonnegative alphaSmall deltaSmall parameterSmall low) (if kind = 0 then 1 else 2) component tangential radial radius nonnegative bounded

/-- The literal R multiplier is i*m; its full moment costs exactly one further grade. -/
theorem gaugeAngularScalarMoment_bound (parameters : PhaseParameters) (L rho alpha delta parameter epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (compactRadius : ℝ) (kind : Fin 2) (component : Fin 3) (tangential radial : ℕ) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius) (deltaSmall : |delta| ≤ compactRadius) (parameterSmall : |parameter| ≤ compactRadius) :
    Summable (productMoment parameters tangential radius (angularCoefficientSequence (gaugeScalar parameters L rho alpha delta parameter epsilon field low kind component radial radius))) ∧
    (∑' mode, productMoment parameters tangential radius (angularCoefficientSequence (gaugeScalar parameters L rho alpha delta parameter epsilon field low kind component radial radius)) mode) ≤
      gaugeScalarConstant parameters L compactRadius kind component (tangential + 1) radial *
        physicalBudget parameters field rho epsilon (tangential + radial + 6) :=
  physicalRotatedPolarEntryScalarMoment_bound parameters _ (originalGaugeDeviation_coherent parameters L rho alpha delta parameter epsilon field low) field rho epsilon (originalGaugeProfile parameters L compactRadius).deviation
    (originalGaugeDeviation_bound parameters L rho alpha delta parameter epsilon compactRadius field compactNonnegative alphaSmall deltaSmall parameterSmall low) (if kind = 0 then 1 else 2) component tangential radial radius nonnegative bounded

end Grad.ActualGaugeSigmaPrimitives

