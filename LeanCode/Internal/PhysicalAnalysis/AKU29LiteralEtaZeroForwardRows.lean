import AKU26AxisPolynomialFourierAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 3000
open scoped BigOperators
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.FlatSourceProjection Grad.QuotientProjection Grad.AxisSplit

def physicalVariationAffine {parameters : PhaseParameters} (epsilon : ℂ)
    (direction : ACore parameters 3) : ACore parameters 3 :=
  timeDerivativeCore parameters direction + epsilon • valueMapCore parameters tangentGeneratorMap direction

def physicalVariationRadialCorrection {parameters : PhaseParameters}
    (field direction : ACore parameters 3) : ACore parameters 1 :=
  quotientDotCurried parameters direction field + quotientDotCurried parameters field direction

/-- The literal first variation at eta=0, retaining the original radial
correction, angular projections, full determinant, and axial current. -/
def physicalEtaZeroRows (parameters : PhaseParameters) (length : ℝ)
    (base : QuotientState parameters) (vector : ACore parameters 3) (scalar : ACore parameters 1) :
    QuotientRows parameters :=
  ![partialPlusCore parameters scalar -
      dotOperation parameters (partialPlusCore parameters vector) (rotationCore parameters base.2.1) -
      dotOperation parameters (partialPlusCore parameters base.2.1) (rotationCore parameters vector) +
      zMulCore parameters (physicalVariationRadialCorrection base.2.1 vector),
    partialMinusCore parameters scalar -
      dotOperation parameters (partialMinusCore parameters vector) (rotationCore parameters base.2.1) -
      dotOperation parameters (partialMinusCore parameters base.2.1) (rotationCore parameters vector) +
      starZMulCore parameters (physicalVariationRadialCorrection base.2.1 vector),
    removeAngularCore parameters
      (determinantOperation parameters (partialCore parameters 0 vector) (partialCore parameters 1 base.2.1)
          (affineStateCore parameters length base) +
        determinantOperation parameters (partialCore parameters 0 base.2.1) (partialCore parameters 1 vector)
          (affineStateCore parameters length base) +
        determinantOperation parameters (partialCore parameters 0 base.2.1) (partialCore parameters 1 base.2.1)
          (physicalVariationAffine base.1 vector)),
    removeAngularCore parameters
      (dotOperation parameters (rotationCore parameters vector) (affineStateCore parameters length base) +
        dotOperation parameters (rotationCore parameters base.2.1) (physicalVariationAffine base.1 vector) -
        timeDerivativeCore parameters scalar)]

/-- This is the actual accepted polynomial derivative, not a replacement
operator whose jet formulas are assumed. -/
theorem quotientRowsDerivative_etaZero (parameters : PhaseParameters) (length : ℝ)
    (base : QuotientState parameters) (vector : ACore parameters 3) (scalar : ACore parameters 1) :
    quotientRowsDerivative parameters length 1 base ![(0,vector,scalar)] =
      physicalEtaZeroRows parameters length base vector scalar := by
  unfold quotientRowsDerivative
  simp only [diagonalDerivative_one]
  funext row
  fin_cases row
  all_goals simp [quotientDegreeZeroPart,quotientDegreeOnePart,quotientDegreeTwoPart,
    quotientDegreeThreePart,quotientDegreeFourPart,Fin.sum_univ_two,Fin.sum_univ_three,Fin.sum_univ_four,
    physicalEtaZeroRows,physicalVariationRadialCorrection,physicalVariationAffine,affineStateCore,
    Function.update,LinearMap.compr₂_apply,map_add,map_sub,map_smul]
  all_goals abel_nf
  all_goals rw [coe_smul_core length ((removeAngularCore parameters)
    ((dotOperation parameters (rotationCore parameters vector)) (eTConstantCore parameters)))]
  all_goals abel

end Grad.FinitePhysicalJetLift
