import AKU67OriginalSourceAxisBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Algebra
open Grad.ExhaustionSourceAllocation

theorem familyEstimate_norm_one_high {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {input output : ℕ} {profile : EstimateProfile}
    {actual reference : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output}
    (estimate : FamilyEstimate parameters field rho epsilon 4 profile actual reference) (grade : ℕ) :
    ‖actual grade‖ ≤ (profile.fixed grade+profile.deviation grade) *
      (1+physicalBudget parameters field rho epsilon (grade+4)) := by
  have triangle := (norm_le_norm_sub_add (actual grade) (reference grade)).trans
    (add_le_add (estimate.deviationBound grade) (estimate.referenceBound grade))
  have budget := physicalBudget_nonnegative parameters field rho epsilon (grade+4)
  have extra := mul_nonneg (estimate.fixedNonnegative grade) budget
  rw [Nat.add_comm 4 grade] at triangle
  nlinarith only [triangle,extra,estimate.deviationNonnegative grade]

def axisCoefficientActionConstant (parameters : PhaseParameters) (coefficientBound : ℕ → ℝ) (grade : ℕ) : ℝ :=
  (2 : ℝ)^grade * Real.exp parameters.sigma0 * ((2 : ℝ)^grade*coefficientBound grade+2*coefficientBound 0)

theorem axisCoefficientActionConstant_nonnegative (parameters : PhaseParameters) (coefficientBound : ℕ → ℝ)
    (nonnegative : ∀ grade, 0 ≤ coefficientBound grade) (grade : ℕ) :
    0 ≤ axisCoefficientActionConstant parameters coefficientBound grade := by
  unfold axisCoefficientActionConstant
  have hq := nonnegative grade
  have h0 := nonnegative 0
  positivity

/-- A literal original-width coefficient action spends the high grade in
one factor. The low coefficient is paid only on the fixed B4 neighborhood. -/
theorem axisFamilyAction_actual_one_high {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output) (coherent : FamilyCoherent family)
    (coefficientBound : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ coefficientBound grade)
    (bound : ∀ grade, ‖family grade‖ ≤ coefficientBound grade * (1+physicalBudget parameters field rho epsilon (grade+4)))
    (low : physicalBudget parameters field rho epsilon 4 ≤ 1)
    (data : Grad.AxisCore.AxisSmoothCore parameters input) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters output grade (axisFamilyAction family coherent data)‖ ≤
      axisCoefficientActionConstant parameters coefficientBound grade *
        (‖Grad.AxisCore.axisEta parameters input grade data‖ +
          (1+physicalBudget parameters field rho epsilon (grade+4)) * ‖Grad.AxisCore.axisEta parameters input 0 data‖) := by
  have lowBound : ‖family 0‖ ≤ 2*coefficientBound 0 := by
    have lowNorm := bound 0
    have scaled := mul_le_mul_of_nonneg_left (by linarith : 1+physicalBudget parameters field rho epsilon 4 ≤ 2) (nonnegative 0)
    exact lowNorm.trans (by simpa only [Nat.zero_add,mul_comm] using scaled)
  have budget := physicalBudget_nonnegative parameters field rho epsilon (grade+4)
  have hq := nonnegative grade
  have h0 := nonnegative 0
  have first := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (bound grade)
    (by positivity : 0 ≤ Real.exp parameters.sigma0*2^grade)) (norm_nonneg (Grad.AxisCore.axisEta parameters input 0 data))
  have second := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left lowBound (Real.exp_pos parameters.sigma0).le)
    (norm_nonneg (Grad.AxisCore.axisEta parameters input grade data))
  have result := (axisFamilyAction_one_high family coherent data grade).trans
    (mul_le_mul_of_nonneg_left (add_le_add first second) (by positivity : 0 ≤ (2 : ℝ)^grade))
  have cross0 : 0 ≤ (2 : ℝ)^grade * Real.exp parameters.sigma0 * (2^grade*coefficientBound grade) *
      ‖Grad.AxisCore.axisEta parameters input grade data‖ := by positivity
  have cross1 : 0 ≤ (2 : ℝ)^grade * Real.exp parameters.sigma0 * (2*coefficientBound 0) *
      ((1+physicalBudget parameters field rho epsilon (grade+4)) * ‖Grad.AxisCore.axisEta parameters input 0 data‖) := by positivity
  unfold axisCoefficientActionConstant
  nlinarith only [result,cross0,cross1]

/-- The original source payment used throughout the finite construction.
The small fixed F4 factor will later be enlarged to the requested F6. -/
def finiteLiftAxisPayment (parameters : PhaseParameters) (field : ACore parameters 3) (rho epsilon : ℝ)
    (source : SmoothQuotient parameters) (grade : ℕ) : ℝ :=
  ‖quotientEta parameters (grade+4) source‖ + physicalBudget parameters field rho epsilon (grade+4) *
    ‖quotientEta parameters 4 source‖

theorem finiteLiftAxisPayment_nonnegative (parameters : PhaseParameters) (field : ACore parameters 3) (rho epsilon : ℝ)
    (source : SmoothQuotient parameters) (grade : ℕ) : 0 ≤ finiteLiftAxisPayment parameters field rho epsilon source grade :=
  add_nonneg (norm_nonneg _) (mul_nonneg (physicalBudget_nonnegative parameters field rho epsilon _) (norm_nonneg _))

theorem axisFamilyAction_source_payment {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output) (coherent : FamilyCoherent family)
    (coefficientBound dataBound : ℕ → ℝ) (coefficientNonnegative : ∀ grade, 0 ≤ coefficientBound grade)
    (dataNonnegative : ∀ grade, 0 ≤ dataBound grade)
    (bound : ∀ grade, ‖family grade‖ ≤ coefficientBound grade * (1+physicalBudget parameters field rho epsilon (grade+4)))
    (low : physicalBudget parameters field rho epsilon 4 ≤ 1)
    (source : SmoothQuotient parameters) (data : Grad.AxisCore.AxisSmoothCore parameters input)
    (controlled : ∀ grade, ‖Grad.AxisCore.axisEta parameters input grade data‖ ≤
      dataBound grade * finiteLiftAxisPayment parameters field rho epsilon source grade) (grade : ℕ) :
    ‖Grad.AxisCore.axisEta parameters output grade (axisFamilyAction family coherent data)‖ ≤
      (axisCoefficientActionConstant parameters coefficientBound grade * (dataBound grade+2*dataBound 0)) *
        finiteLiftAxisPayment parameters field rho epsilon source grade := by
  have paymentLow : finiteLiftAxisPayment parameters field rho epsilon source 0 ≤ 2*‖quotientEta parameters 4 source‖ := by
    unfold finiteLiftAxisPayment
    have scaled := mul_le_mul_of_nonneg_right low (norm_nonneg (quotientEta parameters 4 source))
    change ‖quotientEta parameters 4 source‖ + physicalBudget parameters field rho epsilon 4 * ‖quotientEta parameters 4 source‖ ≤ _
    nlinarith only [scaled]
  have dataLow := (controlled 0).trans (mul_le_mul_of_nonneg_left paymentLow (dataNonnegative 0))
  have pay : (1+physicalBudget parameters field rho epsilon (grade+4))*‖quotientEta parameters 4 source‖ ≤
      finiteLiftAxisPayment parameters field rho epsilon source grade := by
    have sourceBound := originalSourceNorm_monotone parameters source (by omega : 4 ≤ grade+4)
    unfold finiteLiftAxisPayment
    nlinarith only [sourceBound]
  have budget := physicalBudget_nonnegative parameters field rho epsilon (grade+4)
  have d0 := dataNonnegative 0
  have lowTerm : (1+physicalBudget parameters field rho epsilon (grade+4)) * ‖Grad.AxisCore.axisEta parameters input 0 data‖ ≤
      (2*dataBound 0) * finiteLiftAxisPayment parameters field rho epsilon source grade := (mul_le_mul_of_nonneg_left dataLow (by positivity : 0 ≤ 1+physicalBudget parameters field rho epsilon (grade+4))).trans
    (by nlinarith only [mul_le_mul_of_nonneg_left pay (by positivity : 0 ≤ 2*dataBound 0)])
  apply (axisFamilyAction_actual_one_high family coherent coefficientBound coefficientNonnegative bound low data grade).trans
  exact (mul_le_mul_of_nonneg_left (add_le_add (controlled grade) lowTerm)
    (axisCoefficientActionConstant_nonnegative parameters coefficientBound coefficientNonnegative grade)).trans_eq (by ring)

end Grad.FinitePhysicalJetLift
