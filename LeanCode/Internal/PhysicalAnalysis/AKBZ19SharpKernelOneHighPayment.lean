import AKBZ18SharpOrthogonalKernelAction
import GC17Bounds

noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger
open Grad.CartesianState Grad.NonlinearProduct Grad.GenericCarriers

theorem estimatedFamily_norm_le {L ell : ℝ} {parameters : PhaseParameters} {base : ACore parameters 3}
    {rho curvature : ℝ} {offset inputDimension outputDimension : ℕ} {profile : EstimateProfile}
    {family reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell inputDimension outputDimension}
    (estimate : FamilyEstimate parameters base rho curvature offset profile family reference) (grade : ℕ) :
    ‖family grade‖≤(profile.fixed grade+profile.deviation grade)*
      (1+physicalBudget parameters base rho curvature (offset+grade)) := by
  have difference := estimate.deviationBound grade
  have original := estimate.referenceBound grade
  have triangle := norm_add_le (family grade-reference grade) (reference grade)
  rw [sub_add_cancel] at triangle
  have fixed := estimate.fixedNonnegative grade
  have deviation := estimate.deviationNonnegative grade
  have budget := physicalBudget_nonnegative parameters base rho curvature (offset+grade)
  nlinarith [mul_nonneg fixed budget]

/-- The genuine sharp matrix/orthogonal kernel has the adjustable one-high
estimate. The coefficient profile is numerical and fixed before either field. -/
theorem sharpKernel_oneHigh (parameters : PhaseParameters) {L ell : ℝ}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (offset phaseRank displacement inputRank : ℕ) (phasePositive : 0<phaseRank)
    (displacementPositive : 0<displacement) (displacementLe : displacement≤phaseRank)
    (phaseWord : Fin phaseRank → Fin 2) (index : CartesianMultiIndex)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (inputWord : CartesianWord inputRank)
    (profile : EstimateProfile) (fixedNonnegative : ∀ grade,0≤profile.fixed grade)
    (deviationNonnegative : ∀ grade,0≤profile.deviation grade)
    (epsilon : ℝ) (epsilonPositive : 0<epsilon) :
    ∃ remainder : ℝ,0≤remainder ∧
      ∀ (inputDimension outputDimension : ℕ) (base : ACore parameters 3) (rho curvature : ℝ)
        (family reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell inputDimension outputDimension)
        (estimate : FamilyEstimate parameters base rho curvature offset profile family reference)
        (field : ACore parameters inputDimension),
      physicalBudget parameters base rho curvature offset≤1 →
      ‖sharpOrthogonalKernel admissible family estimate.actualCoherent phaseRank displacement phasePositive phaseWord index orthogonal
        (originalMixedDerivativeCarrier parameters admissible field inputRank (phaseRank-displacement) inputWord)‖≤
      epsilon*originalGradeNorm (phaseRank+cartesianOrder index+inputRank) field+
        remainder*((1+physicalBudget parameters base rho curvature (offset+(phaseRank+cartesianOrder index+inputRank)))*
          originalGradeNorm 0 field) := by
  let grade := phaseRank+cartesianOrder index+inputRank
  let order := cartesianOrder index+displacement
  let constant := sharpPhaseConstant L parameters.sigma0 parameters.gamma phaseRank*
    (profile.fixed order+profile.deviation order)
  have constantNonnegative : 0≤constant := mul_nonneg (sharpPhaseConstant_nonnegative admissible phaseRank)
    (add_nonneg (fixedNonnegative order) (deviationNonnegative order))
  have totalPositive : 0<grade := by dsimp [grade]; omega
  have orderPositive : 0<order := by dsimp [order]; omega
  have orderLe : order≤grade := by dsimp [order,grade]; omega
  have allocated : inputRank+(phaseRank-displacement)=grade-order := by dsimp [grade,order]; omega
  have adjustedPositive : 0<epsilon/(constant+1) := div_pos epsilonPositive (by linarith)
  obtain ⟨payment,paymentNonnegative,pays⟩ := originalPositiveOrder_oneHigh offset grade order totalPositive
    orderPositive orderLe (epsilon/(constant+1)) adjustedPositive
  refine ⟨constant*payment,mul_nonneg constantNonnegative paymentNonnegative,?_⟩
  intro inputDimension outputDimension base rho curvature family reference estimate field low
  have kernel := sharpOrthogonalKernel_originalDerivative_bound admissible family estimate.actualCoherent
    phaseRank displacement inputRank phasePositive phaseWord index orthogonal parameters field inputWord
  have coefficient := estimatedFamily_norm_le estimate order
  have paid := pays inputDimension parameters base rho curvature field low
  have less : constant*(epsilon/(constant+1))≤epsilon := by
    have ratio : constant/(constant+1)≤1 := (div_le_one (by linarith : 0<constant+1)).mpr (by linarith)
    calc
      _ = epsilon*(constant/(constant+1)) := by ring
      _ ≤ epsilon*1 := mul_le_mul_of_nonneg_left ratio epsilonPositive.le
      _ = _ := mul_one _
  have inputNonnegative := originalGradeNorm_nonnegative (grade-order) field
  have paymentBound := mul_le_mul_of_nonneg_left paid constantNonnegative
  have leading := mul_le_mul_of_nonneg_right less (originalGradeNorm_nonnegative grade field)
  rw [allocated] at kernel
  have coefficientBound := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left coefficient (sharpPhaseConstant_nonnegative admissible phaseRank)) inputNonnegative
  change ‖sharpOrthogonalKernel admissible family estimate.actualCoherent phaseRank displacement phasePositive phaseWord index orthogonal
      (originalMixedDerivativeCarrier parameters admissible field inputRank (phaseRank-displacement) inputWord)‖≤
    epsilon*originalGradeNorm grade field+(constant*payment)*
      ((1+physicalBudget parameters base rho curvature (offset+grade))*originalGradeNorm 0 field)
  dsimp only [constant] at paymentBound leading
  nlinarith only [kernel,coefficientBound,paymentBound,leading]

end Grad.OriginalCartesianTameEstimate
