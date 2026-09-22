import GC17MatrixOperators
import GC17PolynomialFamily

noncomputable section

set_option maxHeartbeats 1200000

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

/-- Grade profiles are numerical recipes independent of ell and of the
physical state. The actual coefficients are separate parameters below. -/
structure EstimateProfile where
  fixed : ℕ → ℝ
  deviation : ℕ → ℝ

def EstimateProfile.add (first second : EstimateProfile) : EstimateProfile :=
  ⟨fun grade => first.fixed grade + second.fixed grade,
    fun grade => first.deviation grade + second.deviation grade⟩

def EstimateProfile.smul (scalar : ℂ) (profile : EstimateProfile) : EstimateProfile :=
  ⟨fun grade => ‖scalar‖ * profile.fixed grade, fun grade => ‖scalar‖ * profile.deviation grade⟩

def EstimateProfile.comp (offset : ℕ) (outer inner : EstimateProfile) : EstimateProfile :=
  ⟨productReferenceConstant outer.fixed inner.fixed,
    productDeviationConstant offset 1 outer.fixed inner.fixed outer.deviation inner.deviation⟩

structure FamilyEstimate {L ell : ℝ} (parameters : PhaseParameters) (field : ACore parameters 3)
    (rho epsilon : ℝ) (offset : ℕ) {input output : ℕ} (profile : EstimateProfile)
    (actual reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output) : Prop where
  actualCoherent : FamilyCoherent actual
  referenceCoherent : FamilyCoherent reference
  fixedNonnegative : ∀ grade, 0 ≤ profile.fixed grade
  deviationNonnegative : ∀ grade, 0 ≤ profile.deviation grade
  referenceBound : ∀ grade, ‖reference grade‖ ≤ profile.fixed grade
  deviationBound : ∀ grade, ‖actual grade - reference grade‖ ≤
    profile.deviation grade * physicalBudget parameters field rho epsilon (offset + grade)

theorem FamilyEstimate.add {L ell : ℝ} {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {offset input output : ℕ} {firstProfile secondProfile : EstimateProfile}
    {first firstReference second secondReference : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output}
    (firstEstimate : FamilyEstimate parameters field rho epsilon offset firstProfile first firstReference)
    (secondEstimate : FamilyEstimate parameters field rho epsilon offset secondProfile second secondReference) :
    FamilyEstimate parameters field rho epsilon offset (firstProfile.add secondProfile)
      (fun grade => first grade + second grade) (fun grade => firstReference grade + secondReference grade) where
  actualCoherent := firstEstimate.actualCoherent.add secondEstimate.actualCoherent
  referenceCoherent := firstEstimate.referenceCoherent.add secondEstimate.referenceCoherent
  fixedNonnegative grade := add_nonneg (firstEstimate.fixedNonnegative grade) (secondEstimate.fixedNonnegative grade)
  deviationNonnegative grade := add_nonneg (firstEstimate.deviationNonnegative grade) (secondEstimate.deviationNonnegative grade)
  referenceBound grade := (norm_add_le (firstReference grade) (secondReference grade)).trans
    (add_le_add (firstEstimate.referenceBound grade) (secondEstimate.referenceBound grade))
  deviationBound grade := by
    rw [show (first grade + second grade) - (firstReference grade + secondReference grade) =
      (first grade - firstReference grade) + (second grade - secondReference grade) by abel]
    exact (norm_add_le _ _).trans ((add_le_add (firstEstimate.deviationBound grade)
      (secondEstimate.deviationBound grade)).trans_eq (by simp only [EstimateProfile.add, add_mul]))

theorem FamilyEstimate.smul {L ell : ℝ} {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {offset input output : ℕ} {profile : EstimateProfile}
    {actual reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output}
    (estimate : FamilyEstimate parameters field rho epsilon offset profile actual reference) (scalar : ℂ) :
    FamilyEstimate parameters field rho epsilon offset (profile.smul scalar)
      (fun grade => scalar • actual grade) (fun grade => scalar • reference grade) where
  actualCoherent := estimate.actualCoherent.smul scalar
  referenceCoherent := estimate.referenceCoherent.smul scalar
  fixedNonnegative grade := mul_nonneg (norm_nonneg scalar) (estimate.fixedNonnegative grade)
  deviationNonnegative grade := mul_nonneg (norm_nonneg scalar) (estimate.deviationNonnegative grade)
  referenceBound grade := (coefficientScalarNorm_le scalar _).trans
    (mul_le_mul_of_nonneg_left (estimate.referenceBound grade) (norm_nonneg scalar))
  deviationBound grade := by
    rw [← smul_sub]
    exact ((coefficientScalarNorm_le scalar _).trans
      (mul_le_mul_of_nonneg_left (estimate.deviationBound grade) (norm_nonneg scalar))).trans_eq (by
        simp only [EstimateProfile.smul, mul_assoc])

theorem FamilyEstimate.comp {L ell : ℝ} {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {offset input middle output : ℕ} {outerProfile innerProfile : EstimateProfile}
    {outer referenceOuter : CoefficientFamily L parameters.sigma0 parameters.gamma ell middle output}
    {inner referenceInner : CoefficientFamily L parameters.sigma0 parameters.gamma ell input middle}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (low : physicalBudget parameters field rho epsilon offset ≤ 1)
    (outerEstimate : FamilyEstimate parameters field rho epsilon offset outerProfile outer referenceOuter)
    (innerEstimate : FamilyEstimate parameters field rho epsilon offset innerProfile inner referenceInner) :
    FamilyEstimate parameters field rho epsilon offset (outerProfile.comp offset innerProfile)
      (fun grade => coefficientComposition admissible grade (outer grade) (inner grade))
      (fun grade => coefficientComposition admissible grade (referenceOuter grade) (referenceInner grade)) where
  actualCoherent := outerEstimate.actualCoherent.comp admissible innerEstimate.actualCoherent
  referenceCoherent := outerEstimate.referenceCoherent.comp admissible innerEstimate.referenceCoherent
  fixedNonnegative := productReferenceConstant_nonnegative _ _ outerEstimate.fixedNonnegative innerEstimate.fixedNonnegative
  deviationNonnegative := productDeviationConstant_nonnegative offset 1 (by norm_num) _ _ _ _
    outerEstimate.fixedNonnegative innerEstimate.fixedNonnegative outerEstimate.deviationNonnegative innerEstimate.deviationNonnegative
  referenceBound := composition_reference_bound admissible _ _ outerEstimate.referenceCoherent innerEstimate.referenceCoherent
    _ _ outerEstimate.fixedNonnegative outerEstimate.referenceBound innerEstimate.referenceBound
  deviationBound := composition_deviation_bound parameters admissible offset 1 (by norm_num) field rho epsilon low
    _ _ _ _ outerEstimate.actualCoherent outerEstimate.referenceCoherent innerEstimate.actualCoherent innerEstimate.referenceCoherent
    _ _ _ _ outerEstimate.fixedNonnegative innerEstimate.fixedNonnegative outerEstimate.deviationNonnegative
    innerEstimate.deviationNonnegative outerEstimate.referenceBound innerEstimate.referenceBound
    outerEstimate.deviationBound innerEstimate.deviationBound

theorem FamilyEstimate.offset_mono {L ell : ℝ} {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {offset larger input output : ℕ} {profile : EstimateProfile}
    {actual reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output}
    (estimate : FamilyEstimate parameters field rho epsilon offset profile actual reference) (increase : offset ≤ larger) :
    FamilyEstimate parameters field rho epsilon larger profile actual reference where
  actualCoherent := estimate.actualCoherent
  referenceCoherent := estimate.referenceCoherent
  fixedNonnegative := estimate.fixedNonnegative
  deviationNonnegative := estimate.deviationNonnegative
  referenceBound := estimate.referenceBound
  deviationBound grade := (estimate.deviationBound grade).trans (mul_le_mul_of_nonneg_left
    (physicalBudget_monotone parameters field rho epsilon (by omega)) (estimate.deviationNonnegative grade))

def constantProfile {input output : ℕ} (value : OperatorValue input output) : EstimateProfile :=
  ⟨fixedFamilyConstant value, fun _ => 0⟩

theorem constantFamily_estimate {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell) (field : ACore parameters 3)
    (rho epsilon : ℝ) (offset : ℕ) {input output : ℕ} (value : OperatorValue input output) :
    FamilyEstimate parameters field rho epsilon offset (constantProfile value)
      (constantFamily L parameters.sigma0 parameters.gamma ell value)
      (constantFamily L parameters.sigma0 parameters.gamma ell value) where
  actualCoherent := constantFamily_coherent L parameters.sigma0 parameters.gamma ell value
  referenceCoherent := constantFamily_coherent L parameters.sigma0 parameters.gamma ell value
  fixedNonnegative := fixedFamilyConstant_nonnegative value
  deviationNonnegative _ := le_rfl
  referenceBound := constantFamily_norm_le admissible value
  deviationBound grade := by
    rw [sub_self, norm_zero]
    change (0 : ℝ) ≤ 0 * physicalBudget parameters field rho epsilon (offset + grade)
    rw [zero_mul]

def fixedJetProfile {input output : ℕ} (jet : SmoothOperatorJet input output) : EstimateProfile :=
  ⟨fixedJetConstant jet, fun _ => 0⟩

theorem fixedJetFamily_estimate {L ell : ℝ} (parameters : PhaseParameters)
    (field : ACore parameters 3) (rho epsilon : ℝ) (offset : ℕ) {input output : ℕ}
    (jet : SmoothOperatorJet input output) :
    FamilyEstimate parameters field rho epsilon offset (fixedJetProfile jet)
      (fixedJetFamily L parameters.sigma0 parameters.gamma ell jet)
      (fixedJetFamily L parameters.sigma0 parameters.gamma ell jet) where
  actualCoherent := fixedJetFamily_coherent L parameters.sigma0 parameters.gamma ell jet
  referenceCoherent := fixedJetFamily_coherent L parameters.sigma0 parameters.gamma ell jet
  fixedNonnegative := fixedJetConstant_nonnegative jet
  deviationNonnegative _ := le_rfl
  referenceBound := fixedJetFamily_norm_le L parameters.sigma0 parameters.gamma ell jet
  deviationBound grade := by
    rw [sub_self, norm_zero]
    change (0 : ℝ) ≤ 0 * physicalBudget parameters field rho epsilon (offset + grade)
    rw [zero_mul]

end Grad.GaugeCoefficients.Physical.Ledger
