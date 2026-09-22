import AKBZ19SharpKernelOneHighPayment

noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Frame
open Grad.CartesianState Grad.NonlinearProduct Grad.GenericCarriers

/-- Exact original physical full frame, all signed cells and every
rotation/reflection: the positive phase allocation has the CT9 bound with
fixed offset twelve and complementary unknown order, uniformly in both cores. -/
theorem actualFullFrame_sharpOneHigh (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (phaseRank displacement inputRank : ℕ) (phasePositive : 0<phaseRank)
    (displacementPositive : 0<displacement) (displacementLe : displacement≤phaseRank)
    (phaseWord : Fin phaseRank → Fin 2) (index : CartesianMultiIndex)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (inputWord : CartesianWord inputRank)
    (epsilon : ℝ) (epsilonPositive : 0<epsilon) :
    ∃ remainder : ℝ,0≤remainder ∧
      ∀ (base : ACore parameters 3) (rho curvature : ℝ) (curvatureSmall : |curvature|≤1)
        (field : ACore parameters 3),
      physicalBudget parameters base rho curvature 12≤1 →
      ‖sharpOrthogonalKernel admissible (fullFrameFamily parameters L ell curvature base)
        (fullFrameFamily_estimate parameters admissible rho curvature curvatureSmall base).actualCoherent
        phaseRank displacement phasePositive phaseWord index orthogonal
        (originalMixedDerivativeCarrier parameters admissible field inputRank (phaseRank-displacement) inputWord)‖≤
      epsilon*originalGradeNorm (phaseRank+cartesianOrder index+inputRank) field+
        remainder*((1+physicalBudget parameters base rho curvature (12+(phaseRank+cartesianOrder index+inputRank)))*
          originalGradeNorm 0 field) := by
  obtain ⟨remainder,nonnegative,payment⟩ := sharpKernel_oneHigh parameters admissible 12
    phaseRank displacement inputRank phasePositive displacementPositive displacementLe phaseWord index orthogonal inputWord
    (frameProfile parameters L) (fixedFamilyConstant_nonnegative referenceFrame)
    (frameConstant_nonnegative parameters admissible.1) epsilon epsilonPositive
  refine ⟨remainder,nonnegative,?_⟩
  intro base rho curvature curvatureSmall field low
  exact payment 3 3 base rho curvature (fullFrameFamily parameters L ell curvature base)
    (constantFamily L parameters.sigma0 parameters.gamma ell referenceFrame)
    ((fullFrameFamily_estimate parameters admissible rho curvature curvatureSmall base).offset_mono (by norm_num : 4≤12)) field low

end Grad.OriginalCartesianTameEstimate
