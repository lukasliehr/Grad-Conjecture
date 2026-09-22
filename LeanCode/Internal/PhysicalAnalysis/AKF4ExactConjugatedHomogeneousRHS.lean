import AKF3ActualConjugatedRadialOperator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.AnnularWeightedSystem
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit Grad.AnnularVariational
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.PhaseAlgebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularHighGenerators Grad.AnnularCurrentLow Grad.AnnularStrongSolution
open Grad.AnnularWeightedSmoothness Grad.AnnularKernelL2

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

/-- Exact common-phase relation to the accepted physical unknown rows.
Both sides act on the SAME field with the SAME original kernel. -/
theorem conjugatedUnknownPhysicalRowCurve_physical (row : Fin 3) (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      conjugatedUnknownPhysicalRowCurve parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core row grade radius mode =
        (Real.exp (radialPhase parameters radius mode.2) : ℂ) •
          sameUnknownPhysicalRowCurve parameters lower length compact positive
            (lowerHalf.trans_lt (by norm_num)) lengthPositive state
            (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive
              widthHalf widthLength state small core) row grade radius mode := by
  filter_upwards [conjugatedUnknownPhysicalRowCurve_actual parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small core row grade,
    sameUnknownPhysicalRowCurve_actual parameters lower length compact positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive state
      (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core)
      (originalSmoothSourceResponse_allGrades parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core) row grade] with radius weighted physical
  intro mode
  rw [weighted mode, physical mode]
  exact smul_comm _ _ _

/-- The actual conjugated homogeneous operator is exactly the original
physical radial system after inserting exp(Phi), at every Fourier grade. -/
theorem conjugatedRadialSystemOperator_physical (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      hilbertPairCoefficient mode
        (conjugatedRadialSystemOperator parameters length compact lower state positive
          (lowerHalf.trans_lt (by norm_num)) grade radius
          (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
            widthHalf widthLength state small core (grade + 2) radius)) =
        (Real.exp (radialPhase parameters radius mode.2) : ℂ) •
          hilbertPairCoefficient mode
            (originalRadialSystemOperator parameters length compact lower state positive
              (lowerHalf.trans_lt (by norm_num)) grade radius
              (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
                widthHalf widthLength state small core (grade + 2) radius)) := by
  filter_upwards [conjugatedUnknownPhysicalRowCurve_physical parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core 0 grade,
    conjugatedUnknownPhysicalRowCurve_physical parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core 1 grade,
    conjugatedUnknownPhysicalRowCurve_physical parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core 2 grade,
    ae_restrict_mem measurableSet_Icc] with radius sameJ sameC sameV inside
  intro mode
  rw [conjugatedRadialSystemOperator_coefficient]
  have physicalFormula := originalRadialSystemOperator_coefficient parameters lower length compact positive
    (lowerHalf.trans_lt (by norm_num)) state grade radius
    (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core (grade + 2) radius) mode
  dsimp only at physicalFormula
  change _ = (Real.exp (radialPhase parameters radius mode.2) : ℂ) •
    ((originalRadialSystemOperator parameters length compact lower state positive
      (lowerHalf.trans_lt (by norm_num)) grade radius
      (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core (grade + 2) radius)).1 mode,
     (originalRadialSystemOperator parameters length compact lower state positive
      (lowerHalf.trans_lt (by norm_num)) grade radius
      (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core (grade + 2) radius)).2 mode)
  rw [physicalFormula]
  change conjugatedUnknownPointRHS length radius mode
      ((conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core (grade + 2) radius).1 mode)
      (conjugatedUnknownPhysicalRowCurve parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core 0 grade radius mode)
      (conjugatedUnknownPhysicalRowCurve parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core 1 grade radius mode)
      (conjugatedUnknownPhysicalRowCurve parameters length compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state small core 2 grade radius mode) = _
  rw [sameJ mode, sameC mode, sameV mode]
  have sameX := congrArg Prod.fst (conjugatedSmoothResponsePairCurve_physical parameters length compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state small core (grade + 2) mode radius inside)
  change (conjugatedSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core (grade + 2) radius).1 mode =
      (Real.exp (radialPhase parameters radius mode.2) : ℂ) •
        (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf lengthPositive
          widthHalf widthLength state small core (grade + 2) radius).1 mode at sameX
  rw [sameX, conjugatedUnknownPointRHS_smul]
  rfl

end Grad.AnnularWeightedSystem
