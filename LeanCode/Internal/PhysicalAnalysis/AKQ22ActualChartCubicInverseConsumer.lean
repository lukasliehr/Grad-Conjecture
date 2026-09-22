import AKQ21ActualCubicInverseTwoSided

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.SourceCollarCoefficients
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.AxisSplit
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.NonlinearDivision

/-- Every grade and every disk evaluation point gives one and the same
actual circle inverse; grade regularity never changes the solved matrix. -/
theorem originalCubicInverseFamily_same_value (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (firstGrade secondGrade : ℕ) (angle : ℝ) (firstPoint secondPoint : ClosedDisk) :
    coefficientPhysicalValue (originalCubicInverseFamily parameters length epsilon field firstGrade) angle firstPoint =
      coefficientPhysicalValue (originalCubicInverseFamily parameters length epsilon field secondGrade) angle secondPoint := by
  have first := originalCubicInverseFamily_two_sided parameters length rho epsilon field vanishes low firstGrade angle firstPoint
  have second := originalCubicInverseFamily_two_sided parameters length rho epsilon field vanishes low secondGrade angle secondPoint
  let matrix := cubicDeterminantOperator (matrixOperator (originalAxisInverseGram parameters length epsilon field angle))
  have injective : Function.Injective matrix := by
    intro x y same
    have mapped := congrArg (coefficientPhysicalValue (originalCubicInverseFamily parameters length epsilon field firstGrade) angle firstPoint) same
    have left (value : ComplexEuclidean 2) := congrArg (fun mapping : OperatorValue 2 2 => mapping value) first.2
    exact (left x).symm.trans (mapped.trans (left y))
  apply ContinuousLinearMap.ext
  intro value
  apply injective
  exact (congrArg (fun mapping : OperatorValue 2 2 => mapping value) first.1).trans
    (congrArg (fun mapping : OperatorValue 2 2 => mapping value) second.1).symm

/-- Exact current normalized-chart specialization: A0=aM, K0=(A0ᵀA0)^-1,
and the same accepted physical budget. No substituted circular matrix. -/
theorem normalizedChartCubicInverse_two_sided (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) (state : ChartState parameters)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (state.2.1.val cell))
    (low : physicalBudget parameters (normalizedChartDisplacement parameters seed inside state) rho epsilon 6 ≤
      originalCubicLowRadius parameters length) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    let inverse := coefficientPhysicalValue (originalCubicInverseFamily parameters length epsilon
      (normalizedChartDisplacement parameters seed inside state) grade) angle point
    (normalizedAxisCubicOperator seed state angle).comp inverse = ContinuousLinearMap.id ℂ (ComplexEuclidean 2) ∧
      inverse.comp (normalizedAxisCubicOperator seed state angle) = ContinuousLinearMap.id ℂ (ComplexEuclidean 2) := by
  have laws := originalCubicInverseFamily_two_sided parameters length rho epsilon
    (normalizedChartDisplacement parameters seed inside state)
    (normalizedChartDisplacement_axis_zero parameters seed inside state zeroJets) low grade angle point
  simpa only [originalAxisInverseGram,normalizedAxisPlanarMatrix_actual parameters length epsilon seed inside state zeroJets,
    normalizedAxisCubicOperator] using laws

/-- Final boundary consumer on the actual original constrained smooth
chart carrier; its vanishing remainder jets come from accepted membership. -/
theorem actualSmoothChartCubicInverse_two_sided (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (state : Grad.RealFixedRanges.stateSmoothRange parameters seed inside)
    (low : physicalBudget parameters (normalizedChartDisplacement parameters seed inside (Grad.Q24Realization.smoothingChartCore parameters state.val)) rho epsilon 6 ≤
      originalCubicLowRadius parameters length) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    let inverse := coefficientPhysicalValue (originalCubicInverseFamily parameters length epsilon
      (normalizedChartDisplacement parameters seed inside (Grad.Q24Realization.smoothingChartCore parameters state.val)) grade) angle point
    (normalizedAxisCubicOperator seed (Grad.Q24Realization.smoothingChartCore parameters state.val) angle).comp inverse = ContinuousLinearMap.id ℂ (ComplexEuclidean 2) ∧
      inverse.comp (normalizedAxisCubicOperator seed (Grad.Q24Realization.smoothingChartCore parameters state.val) angle) = ContinuousLinearMap.id ℂ (ComplexEuclidean 2) :=
  normalizedChartCubicInverse_two_sided parameters length rho epsilon seed inside (Grad.Q24Realization.smoothingChartCore parameters state.val)
    (Grad.ConstrainedTransfer.smoothState_constraints parameters seed inside state).1.1 low grade angle point

end Grad.FinitePhysicalJetLift
