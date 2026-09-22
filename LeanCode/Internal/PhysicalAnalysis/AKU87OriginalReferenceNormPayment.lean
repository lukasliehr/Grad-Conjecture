import AKU86ActualFlatSourceReduction
import AXN2ReferenceLiftBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds Grad.NonlinearDivision
open Grad.QuotientProjection Grad.NonlinearRange Grad.NonlinearProduct Grad.CompletedReality
open Grad.GaugeCoefficients.Physical.Allocation Grad.Q24Realization Grad.ExhaustionSourceAllocation
open Grad.AxisSplit Grad.AxisJet Grad.FlatSourceProjection Grad.RealFixedRanges Grad.PhysicalCoordinates
open Grad.ConstrainedTransfer Grad.ChartAxisLift Grad.ChartAxisProjections Grad.ChartAxisSourceBound

theorem originalRealFiniteLiftState_norm_le (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (grade : ℕ) :
    ‖Grad.SmoothingFamily.stateToGrade parameters grade
      (originalRealFiniteLiftState parameters length rho epsilon field low source)‖ ≤
      originalFiniteLiftNorm parameters length rho epsilon field low source grade := by
  have normZero : tangentNorm (grade+1) (0 : TangentCoefficient parameters) = 0 := by
    rw [← tangentToGrade_norm]
    simp only [map_zero,norm_zero]
  rw [axb_stateToGrade_literal_norm]
  change tangentNorm (grade+1) 0+
    originalGradeNorm grade (toPhysicalCore parameters (originalRealFiniteLiftU parameters length rho epsilon field low source))+
      originalGradeNorm grade (originalRealFiniteLiftS parameters length rho epsilon field low source) ≤ _
  rw [normZero,zero_add,toPhysicalCore_norm]
  exact originalRealFiniteLift_norm_le parameters length rho epsilon field low source grade

/-- JC1 for this exact eta-zero lift: uniform on the original fixed seed
patch, with the actual inverse N18 transfer and the original reference norm. -/
theorem originalRealFiniteLift_reference_bound_on_patch (parameters : PhaseParameters) (length : ℝ) (grade : ℕ)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seedPatch : Set Seed.Parameters) (compact : IsCompact seedPatch) (insidePatch : seedPatch ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ seed ∈ seedPatch, ∀ (insideS : seed ∈ Seed.parameterDomain)
      (rho epsilon : ℝ) (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
      (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
      (source : SmoothQuotient parameters) (flat : IsFlat source),
      ‖Grad.SmoothingFamily.stateToGrade parameters grade
        (originalRealFiniteLiftAtReference parameters length rho epsilon field vanishes low source flat reference insideR seed insideS).val‖ ≤
      constant*(‖quotientEta parameters (grade+6) source‖+
        physicalBudget parameters field rho epsilon (grade+6)*‖quotientEta parameters 6 source‖) := by
  obtain ⟨transferConstant,transferNonnegative,transferBound⟩ := reverseCoreTransfer_bound_on_patch parameters grade reference insideR
    seedPatch compact insidePatch
  obtain ⟨liftConstant,liftNonnegative,liftBound⟩ := originalFiniteLiftNorm_sharp_payment parameters length grade
  refine ⟨transferConstant*liftConstant,mul_nonneg transferNonnegative liftNonnegative,
    fun seed member insideS rho epsilon field vanishes low source flat => ?_⟩
  have transfer := transferBound seed member insideS (originalRealFiniteLiftState parameters length rho epsilon field low source)
  have lift := (originalRealFiniteLiftState_norm_le parameters length rho epsilon field low source grade).trans
    (liftBound rho epsilon field low source)
  exact transfer.trans ((mul_le_mul_of_nonneg_left lift transferNonnegative).trans_eq (by ring))

/-- The exact fixed low source slot needed when the residual enters EX. -/
theorem actualFiniteSourceResidual_exhaustion_payment (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (rho epsilon : ℝ) (field : ACore parameters 3)
      (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
      (_bounded : physicalBudget parameters field rho epsilon 20 ≤ 1)
      (potential : ACore parameters 1) (source : SmoothQuotient parameters),
      ‖quotientEta parameters (grade+8) (originalRealFiniteLiftResidual parameters length rho epsilon field potential low source)‖+
        physicalBudget parameters field rho epsilon (grade+20)*
          ‖quotientEta parameters 8 (originalRealFiniteLiftResidual parameters length rho epsilon field potential low source)‖ ≤
      constant*(‖quotientEta parameters (grade+20) source‖+
        physicalBudget parameters field rho epsilon (grade+20)*‖quotientEta parameters 20 source‖) := by
  obtain ⟨highConstant,highNonnegative,highBound⟩ := originalRealFiniteLiftResidual_payment parameters length (grade+8)
  obtain ⟨lowConstant,lowNonnegative,lowBound⟩ := originalRealFiniteLiftResidual_low_payment parameters length
  refine ⟨highConstant+lowConstant,add_nonneg highNonnegative lowNonnegative,fun rho epsilon field low bounded potential source => ?_⟩
  have high := highBound rho epsilon field low
    ((physicalBudget_monotone parameters field rho epsilon (by omega : 8 ≤ 20)).trans bounded) potential source
  have small := lowBound rho epsilon field low bounded potential source
  have sourceSmall := originalSourceNorm_monotone parameters source (by omega : 12 ≤ 20)
  have currentNonnegative := physicalBudget_nonnegative parameters field rho epsilon (grade+20)
  have smallPaid := mul_le_mul_of_nonneg_left small currentNonnegative
  have highPaid := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left sourceSmall currentNonnegative) highNonnegative
  unfold finiteResidualPayment at high
  simp only [show grade+8+12 = grade+20 by omega] at high
  nlinarith only [high,smallPaid,highPaid,mul_nonneg lowNonnegative (norm_nonneg (quotientEta parameters (grade+20) source))]

end Grad.FinitePhysicalJetLift
