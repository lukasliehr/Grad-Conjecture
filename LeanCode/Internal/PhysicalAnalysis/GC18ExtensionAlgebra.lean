import GC18Inverse

noncomputable section

set_option maxHeartbeats 1400000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

def liftedEntryProfile (offset : ℕ) (row column : Fin 3) (profile : EstimateProfile) : EstimateProfile :=
  (constantProfile (matrixUnit (input := 1) row 0)).comp offset
    (profile.comp offset (constantProfile (matrixUnit (output := 1) 0 column)))

theorem liftedEntry_estimate {L ell : ℝ} {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {offset : ℕ} {profile : EstimateProfile}
    {actual reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell 1 1}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (low : physicalBudget parameters field rho epsilon offset ≤ 1) (row column : Fin 3)
    (estimate : FamilyEstimate parameters field rho epsilon offset profile actual reference) :
    FamilyEstimate parameters field rho epsilon offset (liftedEntryProfile offset row column profile)
      (liftedEntry admissible row column actual) (liftedEntry admissible row column reference) :=
  (constantFamily_estimate parameters admissible field rho epsilon offset (matrixUnit (input := 1) row 0)).comp
    admissible low (estimate.comp admissible low
      (constantFamily_estimate parameters admissible field rho epsilon offset (matrixUnit (output := 1) 0 column)))

theorem liftedEntry_identity {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (row column : Fin 3) : liftedEntry admissible row column (identityFamily L sigma gamma ell 1) =
      constantFamily L sigma gamma ell (matrixUnit row column) := by
  unfold liftedEntry
  rw [← constantFamily_identity L sigma gamma ell 1, constantFamily_comp, constantFamily_comp]
  congr 1
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro coordinate
  simp [ContinuousLinearMap.comp_apply, matrixUnit_apply, operatorBasis]

theorem liftedEntry_zero {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (row column : Fin 3) : liftedEntry admissible row column (zeroFamily L sigma gamma ell 1 1) =
      zeroFamily L sigma gamma ell 3 3 := by
  unfold liftedEntry
  rw [composeFamily_zero_left, composeFamily_zero_right]

theorem threeDiagonalUnits :
    matrixUnit (input := 3) (output := 3) 0 0 + matrixUnit 1 1 + matrixUnit 2 2 =
      ContinuousLinearMap.id ℂ (PhysicalValue 3) := by
  apply operatorMatrix_injective
  rw [operatorMatrix_add, operatorMatrix_add, operatorMatrix_matrixUnit, operatorMatrix_matrixUnit,
    operatorMatrix_matrixUnit, operatorMatrix_one]
  ext row column
  fin_cases row <;> fin_cases column <;> simp

theorem liftedDiagonal_identity {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) :
    (fun grade => liftedEntry admissible 0 0 (identityFamily L sigma gamma ell 1) grade +
      liftedEntry admissible 1 1 (identityFamily L sigma gamma ell 1) grade +
      liftedEntry admissible 2 2 (identityFamily L sigma gamma ell 1) grade) = identityFamily L sigma gamma ell 3 := by
  simp_rw [liftedEntry_identity]
  rw [show (fun grade => constantFamily L sigma gamma ell (matrixUnit (input := 3) (output := 3) 0 0) grade +
      constantFamily L sigma gamma ell (matrixUnit 1 1) grade + constantFamily L sigma gamma ell (matrixUnit 2 2) grade) =
      constantFamily L sigma gamma ell (matrixUnit 0 0 + matrixUnit 1 1 + matrixUnit 2 2) by
    funext grade
    rw [← congrFun (constantFamily_add L sigma gamma ell _ _) grade,
      ← congrFun (constantFamily_add L sigma gamma ell _ _) grade]]
  rw [threeDiagonalUnits, constantFamily_identity]

theorem scalarLift_three_identity {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) :
    scalarLiftFamily admissible 3 (identityFamily L sigma gamma ell 1) = identityFamily L sigma gamma ell 3 := by
  change (fun grade => ∑ row : Fin 3, liftedEntry admissible row row (identityFamily L sigma gamma ell 1) grade) = _
  simp only [Fin.sum_univ_three]
  exact liftedDiagonal_identity admissible

def fixedProfile (constants : ℕ → ℝ) : EstimateProfile := ⟨constants, fun _ => 0⟩

theorem fixedFamily_estimate {L ell : ℝ} (parameters : PhaseParameters)
    (field : ACore parameters 3) (rho epsilon : ℝ) (offset : ℕ) {input output : ℕ}
    (family : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output)
    (coherent : FamilyCoherent family) (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (bound : ∀ grade, ‖family grade‖ ≤ constants grade) :
    FamilyEstimate parameters field rho epsilon offset (fixedProfile constants) family family where
  actualCoherent := coherent
  referenceCoherent := coherent
  fixedNonnegative := nonnegative
  deviationNonnegative _ := le_rfl
  referenceBound := bound
  deviationBound grade := by rw [sub_self, norm_zero]; change (0 : ℝ) ≤ 0 * _; rw [zero_mul]

def scalarLiftThreeProfile (offset : ℕ) (profile : EstimateProfile) : EstimateProfile :=
  ((liftedEntryProfile offset 0 0 profile).add (liftedEntryProfile offset 1 1 profile)).add
    (liftedEntryProfile offset 2 2 profile)

theorem scalarLiftThree_estimate {L ell : ℝ} {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {offset : ℕ} {profile : EstimateProfile}
    {actual reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell 1 1}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (low : physicalBudget parameters field rho epsilon offset ≤ 1)
    (estimate : FamilyEstimate parameters field rho epsilon offset profile actual reference) :
    FamilyEstimate parameters field rho epsilon offset (scalarLiftThreeProfile offset profile)
      (scalarLiftFamily admissible 3 actual) (scalarLiftFamily admissible 3 reference) := by
  have result := ((liftedEntry_estimate admissible low 0 0 estimate).add
    (liftedEntry_estimate admissible low 1 1 estimate)).add (liftedEntry_estimate admissible low 2 2 estimate)
  change FamilyEstimate parameters field rho epsilon offset (scalarLiftThreeProfile offset profile)
    (fun grade => ∑ row : Fin 3, liftedEntry admissible row row actual grade)
    (fun grade => ∑ row : Fin 3, liftedEntry admissible row row reference grade)
  simpa only [Fin.sum_univ_three, scalarLiftThreeProfile] using result

end Grad.GaugeCoefficients.Physical.RadialLedger
