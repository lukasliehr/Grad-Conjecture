import GSP14ActualCoefficientCompatibility

noncomputable section
open scoped BigOperators
namespace Grad.ActualGaugeSigmaPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollarDivision
open Grad.GaugeCoefficients.Physical.Allocation Grad.ActualCurrentPrimitives

/-- Actual original physical coefficient consumer, retaining full cells and the single B6 ball.
The angular sequence is derived by i*m, not supplied as an independent row. -/
theorem originalGaugeCoefficientConsumer (parameters : PhaseParameters) (L rho alpha delta parameter epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (compactRadius : ℝ) (kind : Fin 2) (component : Fin 3) (tangential radial : ℕ) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (compactNonnegative : 0 ≤ compactRadius)
    (alphaSmall : |alpha| ≤ compactRadius) (deltaSmall : |delta| ≤ compactRadius) (parameterSmall : |parameter| ≤ compactRadius) :
    Summable (productMoment parameters tangential radius (gaugeScalar parameters L rho alpha delta parameter epsilon field low kind component radial radius)) ∧
    (∑' mode, productMoment parameters tangential radius (gaugeScalar parameters L rho alpha delta parameter epsilon field low kind component radial radius) mode) ≤
      gaugeScalarConstant parameters L compactRadius kind component tangential radial *
        physicalBudget parameters field rho epsilon (tangential + radial + 5) ∧
    Summable (productMoment parameters tangential radius (angularCoefficientSequence (gaugeScalar parameters L rho alpha delta parameter epsilon field low kind component radial radius))) ∧
    (∑' mode, productMoment parameters tangential radius (angularCoefficientSequence (gaugeScalar parameters L rho alpha delta parameter epsilon field low kind component radial radius)) mode) ≤
      gaugeScalarConstant parameters L compactRadius kind component (tangential + 1) radial *
        physicalBudget parameters field rho epsilon (tangential + radial + 6) :=
  ⟨gaugeScalarMoment_summable parameters L rho alpha delta parameter epsilon field low kind component tangential radial radius nonnegative bounded,
   gaugeScalarMoment_bound parameters L rho alpha delta parameter epsilon field low compactRadius kind component tangential radial radius nonnegative bounded compactNonnegative alphaSmall deltaSmall parameterSmall,
   gaugeAngularScalarMoment_bound parameters L rho alpha delta parameter epsilon field low compactRadius kind component tangential radial radius nonnegative bounded compactNonnegative alphaSmall deltaSmall parameterSmall⟩

/-- Actual original physical coefficient consumer, retaining full cells and the single B6 ball.
The angular sequence is derived by i*m, not supplied as an independent row. -/
theorem originalSigmaCoefficientConsumer (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (tangential radial : ℕ) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (productMoment parameters tangential radius (sigmaScalar parameters L rho epsilon field low component radial radius)) ∧
    (∑' mode, productMoment parameters tangential radius (sigmaScalar parameters L rho epsilon field low component radial radius) mode) ≤
      sigmaScalarConstant parameters L component tangential radial *
        physicalBudget parameters field rho epsilon (tangential + radial + 5) ∧
    Summable (productMoment parameters tangential radius (angularCoefficientSequence (sigmaScalar parameters L rho epsilon field low component radial radius))) ∧
    (∑' mode, productMoment parameters tangential radius (angularCoefficientSequence (sigmaScalar parameters L rho epsilon field low component radial radius)) mode) ≤
      sigmaScalarConstant parameters L component (tangential + 1) radial *
        physicalBudget parameters field rho epsilon (tangential + radial + 6) :=
  ⟨sigmaScalarMoment_summable parameters L rho epsilon field low component tangential radial radius nonnegative bounded,
   sigmaScalarMoment_bound parameters L rho epsilon field low component tangential radial radius nonnegative bounded,
   sigmaAngularScalarMoment_bound parameters L rho epsilon field low component tangential radial radius nonnegative bounded⟩

end Grad.ActualGaugeSigmaPrimitives

