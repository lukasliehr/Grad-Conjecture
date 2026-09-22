import AKAL3OperatorNormAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 3000

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

def startupComplementBound : ℝ := ‖originalComplementKernel‖ + ‖originalComplementFirstGraph‖
def startupRadialBound : ℝ := ‖originalRadialProjectionKernel‖ + ‖originalRadialProjectionFirstGraph‖
def startupScalarMeanBound : ℝ := ‖originalScalarMeanFreeKernel‖ + ‖originalScalarMeanFreeFirstGraph‖
def startupPlanarMeanBound : ℝ := ‖originalPlanarMeanFreeKernel‖ + ‖originalPlanarMeanFreeFirstGraph‖
def startupAverageBound : ℝ := ‖originalAverageKernel‖ + ‖originalAverageFirstGraph‖
def startupPlanarPartBound : ℝ := ‖originalValueKernel planarPartMap‖ + ‖originalValueFirstGraph planarPartMap‖
def startupQuarterBound : ℝ := ‖originalValueKernel quarterValueMap‖ + ‖originalValueFirstGraph quarterValueMap‖

def startupCurrentBound (L sigma gamma : ℝ) (four : ℕ → ℝ) : ℝ :=
  1 + startupExtensionMatrixConstant L sigma gamma four *
    (startupComplementBound * startupGaugeMatrixConstant L sigma gamma four)

def startupForceBound (L sigma gamma : ℝ) (four five : ℕ → ℝ) : ℝ :=
  2 * (startupRadialBound * (startupDeviationMatrixConstant L sigma gamma five * startupCurrentBound L sigma gamma four))

def startupThirdBound (L sigma gamma : ℝ) (four five : ℕ → ℝ) : ℝ :=
  2 * (startupScalarMeanBound * (startupDeviationMatrixConstant L sigma gamma five * startupCurrentBound L sigma gamma four))

def startupFluxBound (L sigma gamma : ℝ) (four : ℕ → ℝ) : ℝ :=
  startupDeviationMatrixConstant L sigma gamma four * startupCurrentBound L sigma gamma four

def startupPrincipalFluxBound (L sigma gamma : ℝ) (four five : ℕ → ℝ) : ℝ :=
  startupPlanarMeanBound * (startupPlanarPartBound * startupFluxBound L sigma gamma four) +
    startupQuarterBound * (startupAverageBound * startupForceBound L sigma gamma four five)

variable {L ell : ℝ} {parameters : PhaseParameters}
  {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
  {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}

/-- Actual full-current coefficients a,c,h,s, with their original signs and
 both gauges, have a fixed linear B10 norm payment on the Kernel carrier. -/
theorem startupActualRows_Kernel_bounds
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (four five : ℕ → ℝ) (fourNonnegative : ∀ grade, 0 ≤ four grade)
    (fiveNonnegative : ∀ grade, 0 ≤ five grade)
    (bounds : ∀ grade, ledgerSizeFour ledger grade ≤ four grade * physicalBudget parameters base rho epsilon (grade + 4) ∧
      ledgerSizeFive ledger grade ≤ five grade * physicalBudget parameters base rho epsilon (grade + 5))
    (unit : physicalBudget parameters base rho epsilon 10 ≤ 1)
    (small : physicalBudget parameters base rho epsilon 6 ≤ determinantLowRadius four)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation)) :
    ‖originalCurrentKernel admissible ledger.val.gaugeDeviation ledger.property.1.2.2.2.1 inverseCoherent‖ ≤
      startupCurrentBound L parameters.sigma0 parameters.gamma four ∧
    ‖originalForceCorrectionKernel admissible ledger.val ledger.property.1 inverseCoherent‖ ≤
      startupForceBound L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10 ∧
    ‖originalThirdCorrectionKernel admissible ledger.val ledger.property.1 inverseCoherent‖ ≤
      startupThirdBound L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10 ∧
    ‖originalFluxKernel admissible ledger.val ledger.property.1 inverseCoherent‖ ≤
      startupFluxBound L parameters.sigma0 parameters.gamma four * physicalBudget parameters base rho epsilon 10 ∧
    ‖originalPrincipalFluxKernel admissible ledger.val ledger.property.1 inverseCoherent‖ ≤
      startupPrincipalFluxBound L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10 := by
  have matrices := startupActual_gauge_extension_bounds ledger four fourNonnegative
    (fun grade => (bounds grade).1) unit small inverseCoherent
  have d0 := startupActual_deviation_coefficients ledger four five fourNonnegative fiveNonnegative bounds 0 (by norm_num)
  have d1 := startupActual_deviation_coefficients ledger four five fourNonnegative fiveNonnegative bounds 1 le_rfl
  have aBound := (startupDeviationMatrix_bounds admissible ledger.val.rotatedPlanarProduct
    ledger.property.1.2.2.2.2.2.2.2.1 five (physicalBudget parameters base rho epsilon 10) d0.2.2.1 d1.2.2.1).1
  have cBound := (startupDeviationMatrix_bounds admissible ledger.val.rotatedThirdProduct
    ledger.property.1.2.2.2.2.2.2.2.2 five (physicalBudget parameters base rho epsilon 10) d0.2.2.2 d1.2.2.2).1
  have hBound := (startupDeviationMatrix_bounds admissible ledger.val.fluxDeviation
    ledger.property.1.2.2.2.2.1 four (physicalBudget parameters base rho epsilon 10) d0.2.1 d1.2.1).1
  have fixedComplement : ‖originalComplementKernel‖ ≤ startupComplementBound := le_add_of_nonneg_right (norm_nonneg originalComplementFirstGraph)
  have fixedRadial : ‖originalRadialProjectionKernel‖ ≤ startupRadialBound := le_add_of_nonneg_right (norm_nonneg originalRadialProjectionFirstGraph)
  have fixedScalarMean : ‖originalScalarMeanFreeKernel‖ ≤ startupScalarMeanBound := le_add_of_nonneg_right (norm_nonneg originalScalarMeanFreeFirstGraph)
  have fixedPlanarMean : ‖originalPlanarMeanFreeKernel‖ ≤ startupPlanarMeanBound := le_add_of_nonneg_right (norm_nonneg originalPlanarMeanFreeFirstGraph)
  have fixedAverage : ‖originalAverageKernel‖ ≤ startupAverageBound := le_add_of_nonneg_right (norm_nonneg originalAverageFirstGraph)
  have fixedPlanarPart : ‖originalValueKernel planarPartMap‖ ≤ startupPlanarPartBound := le_add_of_nonneg_right (norm_nonneg (originalValueFirstGraph planarPartMap))
  have fixedQuarter : ‖originalValueKernel quarterValueMap‖ ≤ startupQuarterBound := le_add_of_nonneg_right (norm_nonneg (originalValueFirstGraph quarterValueMap))
  have qBound : ‖originalCurrentKernel admissible ledger.val.gaugeDeviation ledger.property.1.2.2.2.1 inverseCoherent‖ ≤
      startupCurrentBound L parameters.sigma0 parameters.gamma four :=
    startupCurrent_norm _ _ _ matrices.2.1 fixedComplement matrices.1.1
  have forceBound : ‖originalForceCorrectionKernel admissible ledger.val ledger.property.1 inverseCoherent‖ ≤
      startupForceBound L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10 := by
    exact (startupTwiceComposition_norm _ _ _ fixedRadial aBound qBound).trans_eq (by
      unfold startupForceBound
      ring)
  have thirdBound : ‖originalThirdCorrectionKernel admissible ledger.val ledger.property.1 inverseCoherent‖ ≤
      startupThirdBound L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10 := by
    exact (startupTwiceComposition_norm _ _ _ fixedScalarMean cBound qBound).trans_eq (by
      unfold startupThirdBound
      ring)
  have fluxBound : ‖originalFluxKernel admissible ledger.val ledger.property.1 inverseCoherent‖ ≤
      startupFluxBound L parameters.sigma0 parameters.gamma four * physicalBudget parameters base rho epsilon 10 := by
    exact (startupComposition_norm _ _ hBound qBound).trans_eq (by
      unfold startupFluxBound
      ring)
  refine ⟨qBound, forceBound, thirdBound, fluxBound, ?_⟩
  have planar := startupComposition_norm _ _ fixedPlanarMean
    (startupComposition_norm _ _ fixedPlanarPart fluxBound)
  have correction := startupHalfComposition_norm _ _ _ fixedQuarter fixedAverage forceBound
  have arithmetic : startupPlanarMeanBound * (startupPlanarPartBound *
      (startupFluxBound L parameters.sigma0 parameters.gamma four * physicalBudget parameters base rho epsilon 10)) +
      startupQuarterBound * (startupAverageBound *
        (startupForceBound L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10)) =
      startupPrincipalFluxBound L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10 := by
    unfold startupPrincipalFluxBound
    ring
  have triangle := norm_sub_le (originalPlanarFluxKernel admissible ledger.val ledger.property.1 inverseCoherent)
    ((1 / 2 : ℂ) • (originalValueKernel quarterValueMap).comp
      (originalAverageKernel.comp (originalForceCorrectionKernel admissible ledger.val ledger.property.1 inverseCoherent)))
  exact triangle.trans ((add_le_add planar correction).trans_eq arithmetic)

/-- Actual full-current coefficients a,c,h,s, with their original signs and
 both gauges, have a fixed linear B10 norm payment on the FirstGraph carrier. -/
theorem startupActualRows_FirstGraph_bounds
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)
    (four five : ℕ → ℝ) (fourNonnegative : ∀ grade, 0 ≤ four grade)
    (fiveNonnegative : ∀ grade, 0 ≤ five grade)
    (bounds : ∀ grade, ledgerSizeFour ledger grade ≤ four grade * physicalBudget parameters base rho epsilon (grade + 4) ∧
      ledgerSizeFive ledger grade ≤ five grade * physicalBudget parameters base rho epsilon (grade + 5))
    (unit : physicalBudget parameters base rho epsilon 10 ≤ 1)
    (small : physicalBudget parameters base rho epsilon 6 ≤ determinantLowRadius four)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation)) :
    ‖originalCurrentFirstGraph admissible ledger.val.gaugeDeviation ledger.property.1.2.2.2.1 inverseCoherent‖ ≤
      startupCurrentBound L parameters.sigma0 parameters.gamma four ∧
    ‖originalForceCorrectionFirstGraph admissible ledger.val ledger.property.1 inverseCoherent‖ ≤
      startupForceBound L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10 ∧
    ‖originalThirdCorrectionFirstGraph admissible ledger.val ledger.property.1 inverseCoherent‖ ≤
      startupThirdBound L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10 ∧
    ‖originalFluxFirstGraph admissible ledger.val ledger.property.1 inverseCoherent‖ ≤
      startupFluxBound L parameters.sigma0 parameters.gamma four * physicalBudget parameters base rho epsilon 10 ∧
    ‖originalPrincipalFluxFirstGraph admissible ledger.val ledger.property.1 inverseCoherent‖ ≤
      startupPrincipalFluxBound L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10 := by
  have matrices := startupActual_gauge_extension_bounds ledger four fourNonnegative
    (fun grade => (bounds grade).1) unit small inverseCoherent
  have d0 := startupActual_deviation_coefficients ledger four five fourNonnegative fiveNonnegative bounds 0 (by norm_num)
  have d1 := startupActual_deviation_coefficients ledger four five fourNonnegative fiveNonnegative bounds 1 le_rfl
  have aBound := (startupDeviationMatrix_bounds admissible ledger.val.rotatedPlanarProduct
    ledger.property.1.2.2.2.2.2.2.2.1 five (physicalBudget parameters base rho epsilon 10) d0.2.2.1 d1.2.2.1).2
  have cBound := (startupDeviationMatrix_bounds admissible ledger.val.rotatedThirdProduct
    ledger.property.1.2.2.2.2.2.2.2.2 five (physicalBudget parameters base rho epsilon 10) d0.2.2.2 d1.2.2.2).2
  have hBound := (startupDeviationMatrix_bounds admissible ledger.val.fluxDeviation
    ledger.property.1.2.2.2.2.1 four (physicalBudget parameters base rho epsilon 10) d0.2.1 d1.2.1).2
  have fixedComplement : ‖originalComplementFirstGraph‖ ≤ startupComplementBound := le_add_of_nonneg_left (norm_nonneg originalComplementKernel)
  have fixedRadial : ‖originalRadialProjectionFirstGraph‖ ≤ startupRadialBound := le_add_of_nonneg_left (norm_nonneg originalRadialProjectionKernel)
  have fixedScalarMean : ‖originalScalarMeanFreeFirstGraph‖ ≤ startupScalarMeanBound := le_add_of_nonneg_left (norm_nonneg originalScalarMeanFreeKernel)
  have fixedPlanarMean : ‖originalPlanarMeanFreeFirstGraph‖ ≤ startupPlanarMeanBound := le_add_of_nonneg_left (norm_nonneg originalPlanarMeanFreeKernel)
  have fixedAverage : ‖originalAverageFirstGraph‖ ≤ startupAverageBound := le_add_of_nonneg_left (norm_nonneg originalAverageKernel)
  have fixedPlanarPart : ‖originalValueFirstGraph planarPartMap‖ ≤ startupPlanarPartBound := le_add_of_nonneg_left (norm_nonneg (originalValueKernel planarPartMap))
  have fixedQuarter : ‖originalValueFirstGraph quarterValueMap‖ ≤ startupQuarterBound := le_add_of_nonneg_left (norm_nonneg (originalValueKernel quarterValueMap))
  have qBound : ‖originalCurrentFirstGraph admissible ledger.val.gaugeDeviation ledger.property.1.2.2.2.1 inverseCoherent‖ ≤
      startupCurrentBound L parameters.sigma0 parameters.gamma four :=
    startupCurrent_norm _ _ _ matrices.2.2 fixedComplement matrices.1.2
  have forceBound : ‖originalForceCorrectionFirstGraph admissible ledger.val ledger.property.1 inverseCoherent‖ ≤
      startupForceBound L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10 := by
    exact (startupTwiceComposition_norm _ _ _ fixedRadial aBound qBound).trans_eq (by
      unfold startupForceBound
      ring)
  have thirdBound : ‖originalThirdCorrectionFirstGraph admissible ledger.val ledger.property.1 inverseCoherent‖ ≤
      startupThirdBound L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10 := by
    exact (startupTwiceComposition_norm _ _ _ fixedScalarMean cBound qBound).trans_eq (by
      unfold startupThirdBound
      ring)
  have fluxBound : ‖originalFluxFirstGraph admissible ledger.val ledger.property.1 inverseCoherent‖ ≤
      startupFluxBound L parameters.sigma0 parameters.gamma four * physicalBudget parameters base rho epsilon 10 := by
    exact (startupComposition_norm _ _ hBound qBound).trans_eq (by
      unfold startupFluxBound
      ring)
  refine ⟨qBound, forceBound, thirdBound, fluxBound, ?_⟩
  have planar := startupComposition_norm _ _ fixedPlanarMean
    (startupComposition_norm _ _ fixedPlanarPart fluxBound)
  have correction := startupHalfComposition_norm _ _ _ fixedQuarter fixedAverage forceBound
  have arithmetic : startupPlanarMeanBound * (startupPlanarPartBound *
      (startupFluxBound L parameters.sigma0 parameters.gamma four * physicalBudget parameters base rho epsilon 10)) +
      startupQuarterBound * (startupAverageBound *
        (startupForceBound L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10)) =
      startupPrincipalFluxBound L parameters.sigma0 parameters.gamma four five * physicalBudget parameters base rho epsilon 10 := by
    unfold startupPrincipalFluxBound
    ring
  have triangle := norm_sub_le (originalPlanarFluxFirstGraph admissible ledger.val ledger.property.1 inverseCoherent)
    ((1 / 2 : ℂ) • (originalValueFirstGraph quarterValueMap).comp
      (originalAverageFirstGraph.comp (originalForceCorrectionFirstGraph admissible ledger.val ledger.property.1 inverseCoherent)))
  exact triangle.trans ((add_le_add planar correction).trans_eq arithmetic)

end Grad.CartesianStartup
