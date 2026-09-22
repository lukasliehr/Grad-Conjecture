import GQD5PolynomialDifference

noncomputable section
set_option maxHeartbeats 800000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation

/-- AP29–30 on the specified closures, not on a maximal PDE domain.
All norms are the inherited original five-slot Hilbert norm. -/
structure CompletedCompensatedIsomorphism {L sigma gamma ell : ℝ}
    {admissible : Admissible L sigma gamma ell} {gauge : CoefficientFamily L sigma gamma ell 3 3}
    (smooth : SmoothCompensatedCoreIsomorphism admissible gauge) (grade : ℕ) where
  equivalence : circularCompensatedClosure admissible grade ≃L[ℂ]
    currentCompensatedClosure admissible gauge smooth.coherent grade
  forwardCore : ∀ core, equivalence (compensatedIntoClosure admissible grade _ core) =
    compensatedIntoClosure admissible grade _ (smooth.equivalence core)
  backwardCore : ∀ core, equivalence.symm (compensatedIntoClosure admissible grade _ core) =
    compensatedIntoClosure admissible grade _ (smooth.equivalence.symm core)
  forwardBound : ‖equivalence.toContinuousLinearMap‖ ≤ completedTransferConstant gauge grade
  inverseBound : ‖equivalence.symm.toContinuousLinearMap‖ ≤ backwardDifferenceConstant grade + 1
  differenceBound : ‖(currentCompensatedClosure admissible gauge smooth.coherent grade).subtypeL.comp
    equivalence.toContinuousLinearMap - (circularCompensatedClosure admissible grade).subtypeL‖ ≤
      (transferPolynomial L sigma gamma grade).eval (gaugeEpsilon (gauge (grade + 3)))

def completedCompensatedIsomorphism {L sigma gamma ell : ℝ}
    {admissible : Admissible L sigma gamma ell} {gauge : CoefficientFamily L sigma gamma ell 3 3}
    (smooth : SmoothCompensatedCoreIsomorphism admissible gauge) (grade : ℕ) (large : 3 ≤ grade) :
    CompletedCompensatedIsomorphism smooth grade where
  equivalence := completedCompensatedEquivalence smooth grade large
  forwardCore := completedCompensatedEquivalence_core smooth grade large
  backwardCore := completedCompensatedEquivalence_symm_core smooth grade large
  forwardBound := completedTransfer_bound smooth grade large
  inverseBound := completedInverse_bound smooth grade
  differenceBound := completedTransferDifference_bound smooth grade large

end Grad.GaugeCoefficients.Physical.Compensated
