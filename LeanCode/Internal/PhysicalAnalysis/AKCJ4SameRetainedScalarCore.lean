import AKCJ3OriginalTangentialCovariantCore
import AKBM9ActualProjectedPolarDivergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.NonlinearRange Grad.QuotientProjection Grad.FinitePhysicalJetLift
open Grad.OriginalKernelRetainedDecay Grad.OriginalKernelCovariantRecovery
open Grad.GaugeCoefficients.Physical.Ledger Grad.SourceCollarDivision Grad.SourceCollarFullSource
open Grad.OriginalKernelHomogeneousGraph

/-- Literal scalar reconstruction and its genuine zero-mean constraint identify
the SAME retained Xi core. No differential equation is added as a premise. -/
theorem originalKernelXi_sameRecoveredScalar (parameters : PhaseParameters) (length epsilon : ℝ)
    (base vector : ACore parameters 3) (scalar : ACore parameters 1)
    (zeroMean : angularCore parameters 0 scalar=0)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (radius : Icc lower (1:ℝ))
    (covariant : ℝ×ℝ→ComplexEuclidean 3) (xi : ℝ×ℝ→ComplexEuclidean 1)
    (sameCovariant : ∀ query, coreValue (originalCovariantCore parameters length epsilon base vector false)
      (polarClosedPoint radius.val query.1 (positive.le.trans radius.property.1) radius.property.2) query.2=covariant query)
    (sameScalar : ∀ query, coreValue scalar
      (polarClosedPoint radius.val query.1 (positive.le.trans radius.property.1) radius.property.2) query.2=
      xi query+removePolarMean (fun angle => scalarTangentialPolynomial
        (polarClosedPoint radius.val angle.1 (positive.le.trans radius.property.1) radius.property.2).val (covariant angle)) query)
    (angles : ℝ×ℝ) :
    coreValue (originalKernelXi (planarReferenceCore parameters+base) vector scalar)
      (polarClosedPoint radius.val angles.1 (positive.le.trans radius.property.1) radius.property.2) angles.2=xi angles := by
  have literal : (fun query : ℝ×ℝ => coreValue
      (dotOperation parameters (rotationCore parameters (planarReferenceCore parameters+base)) vector)
      (polarClosedPoint radius.val query.1 (positive.le.trans radius.property.1) radius.property.2) query.2)=
      (fun query => scalarTangentialPolynomial
        (polarClosedPoint radius.val query.1 (positive.le.trans radius.property.1) radius.property.2).val (covariant query)) := by
    funext query
    exact (originalTangentialCovariant_value parameters length epsilon base vector _ query.2).trans
      (congrArg (scalarTangentialPolynomial _) (sameCovariant query))
  have keep : removeAngularCore parameters scalar=scalar := by
    change scalar-angularCore parameters 0 scalar=scalar
    rw [zeroMean,sub_zero]
  rw [originalKernelXi,map_sub,keep,Grad.GaugeCoefficients.Physical.RadialLedger.coreValue_subtract,
    ← originalCoreCircle_meanFree parameters lower positive bounded _ radius angles]
  rw [literal,sameScalar,add_sub_cancel_right]

end Grad.OriginalCoreRealization
