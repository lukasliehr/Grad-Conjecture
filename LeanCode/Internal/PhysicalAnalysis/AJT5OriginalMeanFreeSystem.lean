import AJT4SameAllGradeDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse

/-- The assembled high and low fields have no angular zero mode. The
unprojected physical row formula is therefore restricted to this actual
carrier before using it as a full Hilbert evolution equation. -/
def physicalPairMeanFree (parameters : PhaseParameters) : PhysicalHilbertPair →L[ℂ] PhysicalHilbertPair :=
  ((hilbertMeanFree parameters).comp (ContinuousLinearMap.fst ℂ (CellL2 1) (CellL2 1))).prod
    ((hilbertMeanFree parameters).comp (ContinuousLinearMap.snd ℂ (CellL2 1) (CellL2 1)))

theorem physicalPairMeanFree_coefficient (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (field : PhysicalHilbertPair) :
    hilbertPairCoefficient mode (physicalPairMeanFree parameters field) =
      (if mode.1 = 0 then (0 : ℂ) else 1) • hilbertPairCoefficient mode field := rfl

theorem physicalPairMeanFree_coefficient_nonzero (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (nonzero : mode.1 ≠ 0) (field : PhysicalHilbertPair) :
    hilbertPairCoefficient mode (physicalPairMeanFree parameters field) = hilbertPairCoefficient mode field := by
  rw [physicalPairMeanFree_coefficient, if_neg nonzero, one_smul]

theorem physicalPairMeanFree_coefficient_zero (parameters : PhaseParameters) (cell : ℤ)
    (field : PhysicalHilbertPair) :
    hilbertPairCoefficient (0,cell) (physicalPairMeanFree parameters field) = 0 := by
  rw [physicalPairMeanFree_coefficient, if_pos rfl, zero_smul]

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

def originalMeanFreeSystemOperator (grade : ℕ) (radius : ℝ) :
    PhysicalHilbertPair →L[ℂ] PhysicalHilbertPair :=
  (physicalPairMeanFree parameters).comp
    (originalRadialSystemOperator parameters length compact lower state positive
      (lowerHalf.trans_lt (by norm_num)) grade radius)

def originalMeanFreeSystemSource (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair :=
  physicalPairMeanFree parameters
    (originalRadialSystemSource parameters length compact lower positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive state core grade radius)

def originalMeanFreeSystemRHS (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair :=
  physicalPairMeanFree parameters
    (originalSmoothResponseSystemRHS parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade radius)

theorem originalMeanFreeSystemOperator_smooth (grade : ℕ) :
    ContDiffOn ℝ ∞ (originalMeanFreeSystemOperator parameters length compact lower positive lowerHalf state grade)
      (Icc lower 1) :=
  smoothOperatorComposition
    (show ContDiffOn ℝ ∞ (fun _ : ℝ => physicalPairMeanFree parameters) (Icc lower 1) from contDiffOn_const)
    (originalRadialSystemOperator_smooth parameters length compact lower state positive
      (lowerHalf.trans_lt (by norm_num)) grade)

theorem originalMeanFreeSystemSource_smooth (grade : ℕ) :
    ContDiffOn ℝ ∞ (originalMeanFreeSystemSource parameters length compact lower positive lowerHalf
      lengthPositive state core grade) (Icc lower 1) :=
  ((physicalPairMeanFree parameters).restrictScalars ℝ).contDiff.comp_contDiffOn
    (originalRadialSystemSource_smooth parameters length compact lower positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive state core grade)

theorem originalMeanFreeSystemRHS_continuousOn (grade : ℕ) :
    ContinuousOn (originalMeanFreeSystemRHS parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade) (Icc lower 1) :=
  (physicalPairMeanFree parameters).continuous.comp_continuousOn
    (originalSmoothResponseSystemRHS_continuousOn parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade)

theorem originalMeanFreeSystemRHS_operatorSource (grade : ℕ) (radius : ℝ) :
    originalMeanFreeSystemRHS parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade radius =
    (originalMeanFreeSystemOperator parameters length compact lower positive lowerHalf state grade radius)
      (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small core (grade + 2) radius) +
      originalMeanFreeSystemSource parameters length compact lower positive lowerHalf
        lengthPositive state core grade radius :=
  (physicalPairMeanFree parameters).map_add _ _

theorem originalSmoothResponsePairCurve_coefficient_meanZero (grade : ℕ) (radius : ℝ) (cell : ℤ) :
    hilbertPairCoefficient (0,cell) (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade radius) = 0 := by
  apply Prod.ext
  · exact sameCoupledPhysicalXSection_meanZero parameters lower length positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive (originalSmoothSourceResponse parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small core)
      (originalSmoothSourceResponse_allGrades parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small core) grade _ cell
  · exact sameCoupledPhysicalXiSection_meanZero parameters lower length positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive (originalSmoothSourceResponse parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small core)
      (originalSmoothSourceResponse_allGrades parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small core) grade _ cell

theorem originalMeanFreeSystemRHS_coefficient_grade (grade : ℕ) (mode : ℤ × ℤ) :
    (fun radius => hilbertPairCoefficient mode (originalMeanFreeSystemRHS parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core grade radius)) =ᵐ[volume.restrict (Icc lower 1)]
    (fun radius => ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
      hilbertPairCoefficient mode (originalMeanFreeSystemRHS parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small core 0 radius)) := by
  filter_upwards [originalSmoothSourceRHS_coefficient_grade parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core grade] with radius same
  unfold originalMeanFreeSystemRHS
  rw [physicalPairMeanFree_coefficient, physicalPairMeanFree_coefficient]
  change (if mode.1 = 0 then (0 : ℂ) else 1) •
    ((originalRadialSystemRHS parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state
      (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
      core grade radius).1 mode,
     (originalRadialSystemRHS parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state
      (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core)
      core grade radius).2 mode) = _
  rw [same mode]
  exact smul_comm _ _ _

end Grad.AnnularSmoothCore
