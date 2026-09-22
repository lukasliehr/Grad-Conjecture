import AIT4CompleteNeumannFixedPoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCoupledInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularCrossMaps Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularKernelL2 Grad.AnnularKernelContinuity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

variable (parameters : PhaseParameters) (lower length compact : ℝ)
  (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
  (state : RetainedInverseState parameters length compact)

/-- The actual low weak derivative obeys the literal normalized BE equation. -/
theorem actualLowOffDiagonal_normalizedEquation
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters length compact)
    (field : CrossHighSpace lower length positive lengthPositive) (index : LowAnnularIndex) :
    collarScalar 1 lower (lowMuInverseCurve lower length positive index.2.val.2)
      (lowEnergyDerivative lower length positive index
        (actualLowOffDiagonal parameters lower length compact lengthPositive positive bounded state field).val) =
      lowCurrentGeneratorValue parameters length compact lower lengthPositive positive bounded.le state
        (actualLowOffDiagonal parameters lower length compact lengthPositive positive bounded state field) index +
      lowDataResidual lower positive
        (highToLowCross parameters lower length compact lengthPositive positive bounded.le state field) index :=
  lowCurrentInverse_normalizedEquation parameters length compact lower lengthPositive positive bounded state small _ index

/-- The original rho factor cancels in the decoded source, leaving exactly
exp(Phi) times the two physical BF18 flux combinations. -/
theorem actualHighCrossSource_physical
    (field : CrossHighSpace lower length positive lengthPositive) (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowDataResidual lower positive
        (highToLowCross parameters lower length compact lengthPositive positive bounded.le state field) index radius =
      Real.exp (radialPhase parameters radius index.2.val.2) •
        crossLowSourceSymbol parameters length radius index
          (highCrossOriginalRow parameters lower length compact positive bounded.le lengthPositive state field 0 radius index.2.val)
          (highCrossOriginalRow parameters lower length compact positive bounded.le lengthPositive state field 1 radius index.2.val)
          (highCrossOriginalRow parameters lower length compact positive bounded.le lengthPositive state field 2 radius index.2.val) := by
  filter_upwards [collarScalar_ae 1 lower (lowStorageInverse lower positive)
      (highToLowBulkCross parameters lower length compact lengthPositive positive bounded.le state field index),
    highToLowBulkCross_physical parameters lower length compact positive bounded.le lengthPositive state field index]
    with radius decoded physical
  change collarScalar 1 lower (lowStorageInverse lower positive)
    (highToLowBulkCross parameters lower length compact lengthPositive positive bounded.le state field index) radius = _
  rw [decoded, physical]
  rw [Complex.coe_smul (lowRhoPhysicalWeight parameters lower positive radius index.2.val), smul_smul]
  congr 1
  unfold lowRhoPhysicalWeight
  calc
    lowStorageInverse lower positive radius *
        (lowStorageWeight lower positive radius * Real.exp (radialPhase parameters radius index.2.val.2)) =
      (lowStorageWeight lower positive radius * lowStorageInverse lower positive radius) *
        Real.exp (radialPhase parameters radius index.2.val.2) := by ring
    _ = Real.exp (radialPhase parameters radius index.2.val.2) := by rw [lowStorage_inverse, one_mul]

/-- Zero incoming means zero actual canonical inner endpoint, not a free
trace coordinate attached to the output. -/
theorem actualLowOffDiagonal_endpoint
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ lowCurrentNeighborhood parameters length compact)
    (field : CrossHighSpace lower length positive lengthPositive) (index : LowAnnularIndex) :
    lowEnergyEndpoint lower length positive bounded 0
      (actualLowOffDiagonal parameters lower length compact lengthPositive positive bounded state field) index = 0 := by
  have endpoint := lowCurrentInverse_endpoint parameters length compact lower lengthPositive positive bounded state small
    (highToLowCross parameters lower length compact lengthPositive positive bounded.le state field) index
  change lowEnergyEndpoint lower length positive bounded 0
    (actualLowOffDiagonal parameters lower length compact lengthPositive positive bounded state field) index = _ at endpoint
  rw [endpoint]
  change _ • ((0 : LowEnergyBoundary) index) = 0
  simp

end Grad.AnnularCoupledInverse
