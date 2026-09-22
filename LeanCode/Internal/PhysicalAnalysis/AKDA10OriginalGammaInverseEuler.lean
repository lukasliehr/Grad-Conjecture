import AKDA9SameInverseAllEulerFidelity
import AJH11ActualGammaRadialJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularRadialSmoothness Grad.ActualGaugeSigmaPrimitives
open Grad.GaugeCoefficients.Physical.Allocation

theorem originalGammaOperator_hasDerivWithinAt (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (order : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt (radialPolynomialAction parameters lower positive bounded.le (gammaJetKernel parameters L compact state order) 0)
      (radialPolynomialAction parameters lower positive bounded.le (gammaJetKernel parameters L compact state (order+1)) 0 radius)
      (Icc lower 1) radius := by
  apply actualMatrixKernelAction_hasDerivWithinAt parameters lower positive bounded
    (gammaJetKernel parameters L compact state)
    (fun order radius shift => matrixMultiplicationEntry 2 2
      (fun row column mode => if mode.1 = 0 then gaugeScalar parameters L state.data.rho state.data.alpha state.data.delta
        state.data.parameter state.data.epsilon state.data.field state.low row column.succ order radius mode else 0) shift (0,0))
    (fun _ _ _ _ => rfl) _ (gammaJetKernel_regular parameters L compact state) order radius inside
  intro order shift radius
  exact matrixMultiplicationEntry_hasDerivAt 2 2
    (fun row column point mode => if mode.1 = 0 then gaugeScalar parameters L state.data.rho state.data.alpha state.data.delta
      state.data.parameter state.data.epsilon state.data.field state.low row column.succ order point mode else 0)
    (fun row column point mode => if mode.1 = 0 then gaugeScalar parameters L state.data.rho state.data.alpha state.data.delta
      state.data.parameter state.data.epsilon state.data.field state.low row column.succ (order+1) point mode else 0)
    (fun row column point mode => by
      by_cases zero : mode.1 = 0
      · simp only [if_pos zero]
        exact gaugeScalar_hasDerivAt parameters L state.data.rho state.data.alpha state.data.delta
          state.data.parameter state.data.epsilon state.data.field state.low row column.succ order point mode
      · simp only [if_neg zero]
        exact hasDerivAt_const point 0) radius shift (0,0)

theorem originalNegativeGammaOperator_hasDerivWithinAt (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (order : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt
      (radialPolynomialAction parameters lower positive bounded.le (fun point => fullKernelNeg (gammaJetKernel parameters L compact state order point)) 0)
      (radialPolynomialAction parameters lower positive bounded.le (fun point => fullKernelNeg (gammaJetKernel parameters L compact state (order+1) point)) 0 radius)
      (Icc lower 1) radius := by
  have same (raw : ℕ) : radialPolynomialAction parameters lower positive bounded.le
      (fun point => fullKernelNeg (gammaJetKernel parameters L compact state raw point)) 0 =
      -radialPolynomialAction parameters lower positive bounded.le (gammaJetKernel parameters L compact state raw) 0 := by
    funext point
    exact polynomialKernelAction_neg _ 0 _
  rw [same,same]
  exact (originalGammaOperator_hasDerivWithinAt parameters L compact state lower positive bounded order radius inside).neg

/-- Concrete Euler kernel of the original inverse of minus identity minus
the actual angular-mean gauge matrix. No surrogate inverse is introduced. -/
def originalGammaInverseEulerKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤ radialGaugeLowRadius parameters L compact)
    (radius : RadialPoint) (rank : ℕ) : RadialKernel parameters radius 2 2 :=
  actualNegativeInverseEulerKernel parameters radius
    (fun raw => fullKernelNeg (gammaJetKernel parameters L compact state raw radius)) (1/2) (by norm_num)
    (radialGammaDeviationKernel_small parameters L compact state radius small) rank

theorem originalGammaInverseEulerKernel_zero (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤ radialGaugeLowRadius parameters L compact)
    (radius : RadialPoint) :
    originalGammaInverseEulerKernel parameters L compact state small radius 0 =
      radialNegativeGammaInverseKernel parameters L compact state radius small := rfl

/-- All Euler ranks of the SAME gauge inverse at every full Fourier cell,
including the original outer boundary through its one-sided derivative. -/
theorem originalGammaInverseEulerKernel_fidelity (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤ radialGaugeLowRadius parameters L compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (rank : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (shift input : ℤ × ℤ) :
    vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (fun point => (radialNegativeGammaInverseKernel parameters L compact state
        (collarRadius lower positive bounded.le point) small).entry shift input) radius =
      (originalGammaInverseEulerKernel parameters L compact state small
        (collarRadius lower positive bounded.le radius) rank).entry shift input :=
  actualNegativeInverseEulerKernel_fidelity parameters lower positive bounded
    (fun raw point => fullKernelNeg (gammaJetKernel parameters L compact state raw point))
    (radialGammaDeviationKernel_smooth parameters L compact state lower positive bounded).neg
    (originalNegativeGammaOperator_hasDerivWithinAt parameters L compact state lower positive bounded)
    (1/2) (by norm_num) (fun radius => radialGammaDeviationKernel_small parameters L compact state radius small)
    rank radius inside shift input

end Grad.OriginalCartesianTameEstimate
