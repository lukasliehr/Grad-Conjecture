import AJS2SameLowRawRHSFidelity
import AJI30ActualFullRadialRHS
import AJT2SameClampedSystem

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularSourceGraph Grad.AnnularLowClassical
open Grad.AnnularLowEnergy Grad.AnnularReconstruction Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.AnnularStrongOrbit Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.Allocation

/-- Low graph entry zero is xi and entry one is x in the physical pair. -/
def lowPhysicalPairCoefficient (index : LowAnnularIndex) (field : PhysicalHilbertPair) : ComplexEuclidean 1 :=
  if index.1 = 0 then field.2 index.2.val else field.1 index.2.val

theorem lowPhysicalPairCoefficient_continuous (index : LowAnnularIndex) :
    Continuous (lowPhysicalPairCoefficient index) := by
  let projection := lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 index.2.val
  by_cases entry : index.1 = 0
  · exact (projection.continuous.comp continuous_snd : Continuous (fun field : PhysicalHilbertPair => field.2 index.2.val))
      |>.congr (fun _ => by simp only [lowPhysicalPairCoefficient, if_pos entry]; rfl)
  · exact (projection.continuous.comp continuous_fst : Continuous (fun field : PhysicalHilbertPair => field.1 index.2.val))
      |>.congr (fun _ => by simp only [lowPhysicalPairCoefficient, if_neg entry]; rfl)

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

def originalSmoothLowDerivativeCurve (index : LowAnnularIndex) : C(ℝ, ComplexEuclidean 1) where
  toFun radius := lowPhysicalPairCoefficient index
    (originalSmoothResponseClampedRHS parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core 0 radius)
  continuous_toFun := (lowPhysicalPairCoefficient_continuous index).comp
    (originalSmoothResponseClampedRHS_continuous parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core 0)

/-- The actual continuous Hilbert candidate equals the full low weak PDE RHS. -/
theorem originalSmoothLowDerivativeCurve_actual (index : LowAnnularIndex) :
    originalSmoothLowDerivativeCurve parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core index =ᵐ[volume.restrict (Icc lower 1)]
    sharedStrongLowRawSlope parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small
      ((strongSmoothDenseMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive).mapping core) index := by
  let field := originalSmoothSourceResponse parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core
  have coefficient := originalRadialSystemRHS_actual parameters length compact lower positive
    (lowerHalf.trans_lt (by norm_num)) lengthPositive state field core
    (originalSmoothSourceResponse_allGrades parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core) 0
  filter_upwards [sharedStrongLowRawSlope_actualRHS parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core index,
    coefficient, ae_restrict_mem measurableSet_Icc] with radius low actual inside
  change lowPhysicalPairCoefficient index
    (originalSmoothResponseClampedRHS parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core 0 radius) = _
  rw [originalSmoothResponseClampedRHS_same parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core 0 radius inside, low]
  have same := actual index.2.val
  simp only [pow_zero, Complex.ofReal_one, one_smul] at same
  by_cases entry : index.1 = 0
  · simp only [lowPhysicalPairCoefficient, if_pos entry]
    exact congrArg Prod.snd same
  · simp only [lowPhysicalPairCoefficient, if_neg entry]
    exact congrArg Prod.fst same

/-- Genuine derivative of the SAME original balanced low section, with no
solution regularity or derivative assumption. -/
theorem originalSmoothLowPhysicalSection_derivative (index : LowAnnularIndex)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt
      (radialSectionExtension 1 lower (lowerHalf.trans (by norm_num))
        (lowPhysicalSection parameters lower length positive (lowerHalf.trans_lt (by norm_num))
          (originalSmoothSourceResponse parameters length compact lower positive lowerHalf
            lengthPositive widthHalf widthLength state small core).ofLp.2 index))
      (lowPhysicalPairCoefficient index
        (originalSmoothResponseSystemRHS parameters length compact lower positive lowerHalf
          lengthPositive widthHalf widthLength state small core 0 radius))
      (Icc lower 1) radius := by
  have derivative := sharedStrongResponse_lowPhysicalSection_derivative parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small
    ((strongSmoothDenseMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive).mapping core)
    index (originalSmoothLowDerivativeCurve parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core index)
    (originalSmoothLowDerivativeCurve_actual parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core index) radius inside
  change HasDerivWithinAt _ (lowPhysicalPairCoefficient index
    (originalSmoothResponseClampedRHS parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core 0 radius)) _ _ at derivative
  rw [originalSmoothResponseClampedRHS_same parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core 0 radius inside] at derivative
  exact derivative

theorem originalSmoothResponsePairCurve_low_coefficient (index : LowAnnularIndex) (radius : ℝ) :
    lowPhysicalPairCoefficient index
      (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small core 0 radius) =
    radialSectionExtension 1 lower (lowerHalf.trans (by norm_num))
      (lowPhysicalSection parameters lower length positive (lowerHalf.trans_lt (by norm_num))
        (originalSmoothSourceResponse parameters length compact lower positive lowerHalf
          lengthPositive widthHalf widthLength state small core).ofLp.2 index) radius := by
  let field := originalSmoothSourceResponse parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core
  have grades := originalSmoothSourceResponse_allGrades parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core
  rcases index with ⟨entry, mode⟩
  have notLarge : ¬ 3 ≤ |mode.val.1| := by rcases mode.property with h | h <;> omega
  fin_cases entry
  · change sameCoupledPhysicalXiSection parameters lower length positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive 0 field (radialClamp lower (lowerHalf.trans (by norm_num)) radius) mode.val = _
    rw [sameCoupledPhysicalXiSection_coefficient parameters lower length positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive field grades]
    simp only [sameCoupledXiCoefficient, dif_neg notLarge, dif_pos mode.property,
      pow_zero, Complex.ofReal_one, one_smul, radialSectionExtension]
    rfl
  · change sameCoupledPhysicalXSection parameters lower length positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive 0 field (radialClamp lower (lowerHalf.trans (by norm_num)) radius) mode.val = _
    rw [sameCoupledPhysicalXSection_coefficient parameters lower length positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive field grades]
    simp only [sameCoupledXCoefficient, dif_neg notLarge, dif_pos mode.property,
      pow_zero, Complex.ofReal_one, one_smul, radialSectionExtension]
    rfl

/-- The grade-zero full Hilbert pair has the genuine original low-mode
coordinate derivative, ready for polynomial insertion and Hilbert FTC. -/
theorem originalSmoothResponsePairCurve_low_derivative (index : LowAnnularIndex)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt
      (fun point => lowPhysicalPairCoefficient index
        (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
          lengthPositive widthHalf widthLength state small core 0 point))
      (lowPhysicalPairCoefficient index
        (originalSmoothResponseSystemRHS parameters length compact lower positive lowerHalf
          lengthPositive widthHalf widthLength state small core 0 radius))
      (Icc lower 1) radius :=
  (originalSmoothLowPhysicalSection_derivative parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core index radius inside).congr
      (fun point _ => originalSmoothResponsePairCurve_low_coefficient parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small core index point)
      (originalSmoothResponsePairCurve_low_coefficient parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small core index radius)

end Grad.AnnularSmoothCore
