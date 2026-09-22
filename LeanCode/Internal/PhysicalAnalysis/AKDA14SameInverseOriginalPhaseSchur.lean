import AKDA13ClosedEulerSchurAllocation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.CartesianState Grad.BoundaryKernelAction Grad.AnnularReconstruction Grad.AnnularRadialSmoothness
open Grad.AnnularKernelL2 Grad.GaugeCoefficients.Physical.Allocation

theorem originalGammaInverseEulerKernel_hasDerivWithinAt (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤ radialGaugeLowRadius parameters L compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (rank : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (shift input : ℤ × ℤ) :
    HasDerivWithinAt (fun point => (originalGammaInverseEulerKernel parameters L compact state small
      (collarRadius lower positive bounded.le point) rank).entry shift input)
      (radius⁻¹ • (originalGammaInverseEulerKernel parameters L compact state small
        (collarRadius lower positive bounded.le radius) (rank+1)).entry shift input) (Icc lower 1) radius :=
  actualNegativeInverseEulerKernel_hasDerivWithinAt parameters lower positive bounded
    (fun raw point => fullKernelNeg (gammaJetKernel parameters L compact state raw point))
    (radialGammaDeviationKernel_smooth parameters L compact state lower positive bounded).neg
    (originalNegativeGammaOperator_hasDerivWithinAt parameters L compact state lower positive bounded)
    (1/2) (by norm_num) (fun radius => radialGammaDeviationKernel_small parameters L compact state radius small)
    rank radius inside shift input

def gammaInverseConjugatedEulerConstant (parameters : PhaseParameters) (L compact : ℝ) (rank moment : ℕ) : ℝ :=
  eulerAllocationSum (fun first second => positiveEulerRatioConstant parameters first *
    gammaInverseEulerMomentConstant parameters L compact second (moment+first)) (eulerLeibnizTerms rank)

theorem gammaInverseConjugatedEulerConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) (rank moment : ℕ) :
    0 ≤ gammaInverseConjugatedEulerConstant parameters L compact rank moment :=
  eulerAllocationSum_nonnegative _ (fun first second => mul_nonneg
    (zero_le_one.trans (positiveEulerRatioConstant_one_le parameters first))
    (gammaInverseEulerMomentConstant_nonnegative parameters L compact second (moment+first))) _

/-- Uniform original-width all-cell Schur bound for every genuine Euler
derivative of the SAME phase-conjugated original gauge inverse. Constants
are fixed before state, radius, collar and row/column input selector. -/
theorem originalGammaInverseConjugatedEuler_oneHigh (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact)
    (low : physicalBudget parameters state.val.field state.val.rho state.val.epsilon 7 ≤ 1)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (radius : RadialPoint) (inside : radius.val ∈ Icc lower 1) (rank moment : ℕ)
    (inputs : (ℤ × ℤ) → (ℤ × ℤ)) :
    let coefficient := fun point => (radialNegativeGammaInverseKernel parameters L compact state.val
      (collarRadius lower positive bounded.le point) state.gaugeSmall).entry
    Summable (fun shift : ℤ × ℤ => Grad.AnnularVariational.annularFrequency shift.1 shift.2^moment *
      ‖actualClosedConjugatedEulerEntry parameters (Icc lower 1) coefficient rank radius.val shift (inputs shift)‖) ∧
    (∑' shift : ℤ × ℤ, Grad.AnnularVariational.annularFrequency shift.1 shift.2^moment *
      ‖actualClosedConjugatedEulerEntry parameters (Icc lower 1) coefficient rank radius.val shift (inputs shift)‖) ≤
      gammaInverseConjugatedEulerConstant parameters L compact rank moment *
        (1+physicalBudget parameters state.val.field state.val.rho state.val.epsilon (7+(rank+moment))) := by
  have allocated := actualClosedEulerDisplacementMoment_allocated parameters lower positive bounded
    (fun rank radius => originalGammaInverseEulerKernel parameters L compact state.val state.gaugeSmall radius rank)
    (originalGammaInverseEulerKernel_hasDerivWithinAt parameters L compact state.val state.gaugeSmall lower positive bounded)
    radius inside rank moment inputs
  refine ⟨allocated.1,allocated.2.trans ?_⟩
  let size := 1+physicalBudget parameters state.val.field state.val.rho state.val.epsilon (7+(rank+moment))
  have paid : eulerAllocationSum (fun first second => positiveEulerRatioConstant parameters first *
        fullKernelMoment (radialKernelParameters parameters radius) (moment+first)
          (originalGammaInverseEulerKernel parameters L compact state.val state.gaugeSmall radius second)) (eulerLeibnizTerms rank) ≤
      eulerAllocationSum (fun first second => size * (positiveEulerRatioConstant parameters first *
        gammaInverseEulerMomentConstant parameters L compact second (moment+first))) (eulerLeibnizTerms rank) := by
    apply eulerAllocationSum_mono
    intro term member
    have degree := eulerLeibnizTerms_rank rank term member
    have actual := originalGammaInverseEulerKernel_oneHigh parameters L compact state low radius term.2 (moment+term.1)
    rw [show 7+(term.2+(moment+term.1)) = 7+(rank+moment) by omega] at actual
    have multiplied := mul_le_mul_of_nonneg_left actual
      (zero_le_one.trans (positiveEulerRatioConstant_one_le parameters term.1))
    exact multiplied.trans_eq (by dsimp only [size]; ring)
  apply paid.trans_eq
  rw [← eulerAllocationSum_mul_left]
  exact mul_comm _ _

end Grad.OriginalCartesianTameEstimate
