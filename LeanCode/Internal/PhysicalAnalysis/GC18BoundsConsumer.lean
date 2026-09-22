import GC18ExtensionEstimate
import GC18NumeratorConsumer

noncomputable section

set_option maxHeartbeats 1800000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

def fullLedgerConstant (gauge : ℕ → ℝ) (grade : ℕ) : ℝ :=
  muConstant gauge grade + etaConstant gauge grade + nuConstant gauge grade + deltaConstant gauge grade +
    determinantConstant gauge grade + determinantInverseConstant gauge grade + complementExtensionConstant gauge grade

theorem fullLedgerConstant_nonnegative {gauge : ℕ → ℝ} (nonnegative : ∀ grade, 0 ≤ gauge grade) (grade : ℕ) :
    0 ≤ fullLedgerConstant gauge grade := by
  unfold fullLedgerConstant complementExtensionConstant
  positivity [muConstant_nonnegative nonnegative grade, etaConstant_nonnegative nonnegative grade,
    nuConstant_nonnegative nonnegative grade, deltaConstant_nonnegative nonnegative grade,
    determinantConstant_nonnegative gauge grade, determinantInverseConstant_nonnegative gauge grade]

theorem radialLedgerSize_bound {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (field : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters field rho epsilon 6 ≤ 1)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters field rho epsilon (grade + 4))
    (small : physicalBudget parameters field rho epsilon 6 ≤ determinantLowRadius constants) (grade : ℕ) :
    radialLedgerSize admissible gauge grade ≤
      fullLedgerConstant constants grade * physicalBudget parameters field rho epsilon (grade + 6) := by
  have first := muDeviation_bound parameters admissible field rho epsilon gauge constants bound grade
  have second := etaCoefficient_bound parameters admissible field rho epsilon gauge constants bound grade
  have third := nuCoefficient_bound parameters admissible field rho epsilon gauge constants bound grade
  have fourth := deltaDeviation_bound parameters admissible field rho epsilon gauge constants nonnegative bound grade
  have fifth := determinant_deviation_bound parameters admissible field rho epsilon gauge coherent constants nonnegative low bound grade
  have sixth : ‖determinantInverseFamily admissible gauge grade - identityFamily L parameters.sigma0 parameters.gamma ell 1 grade‖ ≤
      determinantInverseConstant constants grade * physicalBudget parameters field rho epsilon (grade + 6) := by
    simpa only [unitProfile, Nat.add_comm] using
      (determinantInverse_estimate parameters admissible field rho epsilon gauge coherent constants nonnegative low bound small).deviationBound grade
  have seventh := complementExtension_deviation_bound parameters admissible field rho epsilon gauge coherent constants nonnegative low bound small grade
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add first second) third) fourth) fifth) sixth) seventh).trans_eq (by
    unfold fullLedgerConstant
    ring)

/-- Bounds-and-determinant consumer on the actual physical ledger. The
remaining GC03 radial-division and complement G/E correspondence are not
asserted by this theorem; the exact seven families are explicitly constructed. -/
theorem actualRadialInverseCoefficientBounds (parameters : PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold) :
    ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
      ∃ constants : ℕ → ℝ, (∀ grade, 0 ≤ constants grade) ∧
        ∀ (ell rho alpha delta parameter epsilon : ℝ)
          (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
          |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius →
          ∀ field : ACore parameters 3,
            physicalBudget parameters field rho epsilon 10 < lowRadius →
            physicalBudget parameters field rho epsilon 12 ≤ 1 →
            ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon field,
              primitiveSize parameters admissible rho alpha delta parameter epsilon field 2 ≤ threshold ∧
              ‖determinantInverseInput admissible ledger.val.gaugeDeviation 0‖ ≤ 1 / 2 ∧
              (∀ grade, radialLedgerSize admissible ledger.val.gaugeDeviation grade ≤
                constants grade * physicalBudget parameters field rho epsilon (grade + 6)) ∧
              ∀ grade angle point,
                familyMatrix (determinantFamily admissible ledger.val.gaugeDeviation) grade angle point *
                  familyMatrix (determinantInverseFamily admissible ledger.val.gaugeDeviation) grade angle point = 1 ∧
                familyMatrix (determinantInverseFamily admissible ledger.val.gaugeDeviation) grade angle point *
                  familyMatrix (determinantFamily admissible ledger.val.gaugeDeviation) grade angle point = 1 := by
  obtain ⟨ledgerRadius, ledgerRadiusPositive, ledgerRadiusOne, gaugeConstants, higherConstants,
    gaugeConstantsNonnegative, _, supplied⟩ := actualLedger parameters L radius threshold positive radiusNonnegative thresholdPositive
  refine ⟨min ledgerRadius (determinantLowRadius gaugeConstants),
    lt_min ledgerRadiusPositive (determinantLowRadius_positive gaugeConstants),
    (min_le_left _ _).trans ledgerRadiusOne, fullLedgerConstant gaugeConstants,
    fullLedgerConstant_nonnegative gaugeConstantsNonnegative, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall field low _bounded
  have lowSix := (physicalBudget_monotone parameters field rho epsilon (by norm_num : 6 ≤ 10)).trans low.le
  have ledgerSmall := lowSix.trans (min_le_left _ _)
  have determinantSmall := lowSix.trans (min_le_right _ _)
  have unitSmall := ledgerSmall.trans ledgerRadiusOne
  have rhoSmall : |rho| ≤ 1 := by
    unfold physicalBudget at unitSmall
    have := Grad.NonlinearProduct.originalGradeNorm_nonnegative 6 field
    linarith [abs_nonneg epsilon]
  have epsilonSmall : |epsilon| ≤ 1 := by
    unfold physicalBudget at unitSmall
    have := Grad.NonlinearProduct.originalGradeNorm_nonnegative 6 field
    linarith [abs_nonneg rho]
  obtain ⟨ledger, primitiveMargin, ledgerBounds⟩ := supplied ell rho alpha delta parameter epsilon admissible
    rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall field ledgerSmall
  have gaugeBound (grade : ℕ) : ‖ledger.val.gaugeDeviation grade‖ ≤
      gaugeConstants grade * physicalBudget parameters field rho epsilon (grade + 4) :=
    (actualGaugeDeviation_bound ledger grade).trans (ledgerBounds grade).1
  have gaugeCoherent : FamilyCoherent ledger.val.gaugeDeviation := ledger.property.1.2.2.2.1
  refine ⟨ledger, primitiveMargin,
    determinant_base_margin parameters admissible field rho epsilon _ gaugeCoherent gaugeConstants gaugeConstantsNonnegative unitSmall gaugeBound determinantSmall,
    fun grade => radialLedgerSize_bound parameters admissible field rho epsilon _ gaugeCoherent gaugeConstants gaugeConstantsNonnegative unitSmall gaugeBound determinantSmall grade,
    ?_⟩
  intro grade angle point
  exact determinantInverse_two_sided parameters admissible field rho epsilon _ gaugeCoherent gaugeConstants gaugeConstantsNonnegative
    unitSmall gaugeBound determinantSmall grade angle point

end Grad.GaugeCoefficients.Physical.RadialLedger
