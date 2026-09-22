import AKF1ExactConjugatedUnknownInput
import AKD5ActualConjugatedKernelFidelity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.AnnularWeightedSystem
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularHighGenerators Grad.AnnularCurrentLow Grad.AnnularStrongSolution
open Grad.AnnularWeightedSmoothness Grad.AnnularKernelL2

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

/-- The actual original j, c and rV on the SAME inverse unknown packet,
represented with the original exponential phase and polynomial grade. -/
def conjugatedUnknownPhysicalRowCurve (row : Fin 3) (grade : ℕ) (radius : ℝ) : CellL2 1 :=
  radialConjugatedAction parameters lower positive (lowerHalf.trans (by norm_num))
    (lowPhysicalRowKernel parameters length compact state row) (grade + 1) 0 radius
    (conjugatedUnknownSevenCurve parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core grade radius)

theorem conjugatedUnknownPhysicalRowCurve_actual (row : Fin 3) (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      conjugatedUnknownPhysicalRowCurve parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core row grade radius mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ (grade + 1) : ℂ) •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
            lowRhoPhysicalCoefficient parameters lower positive
              (lowPhysicalRowAction parameters length compact lower positive (lowerHalf.trans (by norm_num)) state row
                (homogeneousCoupledSevenInput parameters length lower lengthPositive positive
                  (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive
                    widthHalf widthLength state small core))) radius mode) :=
  radialConjugatedAction_actual parameters lower positive (lowerHalf.trans (by norm_num))
    (lowPhysicalRowKernel parameters length compact state row)
    (lowPhysicalRowKernel_regular parameters length compact state row)
    (homogeneousCoupledSevenInput parameters length lower lengthPositive positive
      (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core)) (grade + 1)
    (conjugatedUnknownSevenCurve parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core grade)
    (conjugatedUnknownSevenCurve_actual parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core grade)

end Grad.AnnularWeightedSystem
