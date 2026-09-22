import AKBZ30ActualFullDerivativeOneHigh

noncomputable section
set_option maxHeartbeats 1400000
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate.Consumer
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Frame
open Grad.CartesianState Grad.NonlinearProduct Grad.GenericCarriers

/-- Actual original full frame, with every phase/coefficient Leibniz term
included and all signed cells retained. Constants are chosen before the
state and unknown; the original B12 ball suffices and the high grade is
exactly 12+the total derivative order. -/
theorem originalPhysicalFrame_fullDerivative_oneHigh (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (inputRank : ℕ) {grade : ℕ} (index : DerivativeIndex grade)
    (positive : 0<derivativeOrder index) (inputWord : CartesianWord inputRank)
    (epsilon : ℝ) (epsilonPositive : 0<epsilon) :
    ∃ remainder : ℝ,0≤remainder ∧
      ∀ (base : ACore parameters 3) (rho curvature : ℝ) (curvatureSmall : |curvature|≤1)
        (field : ACore parameters 3),
      physicalBudget parameters base rho curvature 12≤1 →
      ‖startupDerivativeKernel admissible (fullFrameFamily parameters L ell curvature base)
        (fullFrameFamily_estimate parameters admissible rho curvature curvatureSmall base).actualCoherent index
        (originalMixedDerivativeCarrier parameters admissible field inputRank (derivativeOrder index-1) inputWord)‖≤
      epsilon*originalGradeNorm (derivativeOrder index+inputRank) field+
        remainder*((1+physicalBudget parameters base rho curvature (12+(derivativeOrder index+inputRank)))*
          originalGradeNorm 0 field) := by
  obtain ⟨remainder,nonnegative,payment⟩ := actualFullDerivative_oneHigh parameters admissible 12 inputRank index positive inputWord
    (frameProfile parameters L) (fixedFamilyConstant_nonnegative referenceFrame)
    (frameConstant_nonnegative parameters admissible.1) epsilon epsilonPositive
  refine ⟨remainder,nonnegative,?_⟩
  intro base rho curvature curvatureSmall field low
  exact payment 3 3 base rho curvature (fullFrameFamily parameters L ell curvature base)
    (constantFamily L parameters.sigma0 parameters.gamma ell referenceFrame)
    ((fullFrameFamily_estimate parameters admissible rho curvature curvatureSmall base).offset_mono (by norm_num : 4≤12)) field low

end Grad.OriginalCartesianTameEstimate.Consumer
