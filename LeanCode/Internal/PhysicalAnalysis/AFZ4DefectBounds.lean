import AFZ2ActualDefectFormula

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 150000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryTrace

def matchingNormalDeviationSize {L sigma gamma ell : ℝ} (data : LedgerData L sigma gamma ell) (grade : ℕ) : ℝ :=
  apMultiplierConstant L sigma gamma grade * ‖data.traceDeviation grade‖

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)

include admissible in
theorem matchingNormalDeviationSize_nonnegative (data : LedgerData L sigma gamma ell) (grade : ℕ) :
    0 ≤ matchingNormalDeviationSize data grade :=
  mul_nonneg (apMultiplierConstant_nonnegative admissible grade) (norm_nonneg _)

/-- The actual AR16 bulk defect; each physical coefficient deviation remains
explicit, and the retained cross term uses the native scalar grade. -/
theorem apMatchingDefectBulk_bound (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (vector : apGrade L sigma gamma ell 3 grade) (psi : apGrade L sigma gamma ell 1 grade) :
    ‖apMatchingDefectBulk admissible data grade vector psi‖ ≤
      (fixedRowBoundConstant L sigma gamma grade radialRowJet * matchingFluxDeviationSize data grade +
        matchingNormalDeviationSize data grade) * ‖vector‖ +
      fixedRowBoundConstant L sigma gamma grade tangentRowJet * matchingFluxDeviationSize data grade *
        matchingColumnConstant L sigma gamma grade * ‖psi‖ := by
  have radial := (apFixedRow_bound admissible grade radialRowJet
    (apMultiplier admissible (data.fluxDeviation grade) vector)).trans
      (mul_le_mul_of_nonneg_left (apMultiplier_bound admissible (data.fluxDeviation grade) vector)
        (fixedRowBoundConstant_nonnegative admissible grade radialRowJet))
  have normal := apMultiplier_bound admissible (data.traceDeviation grade) vector
  have tangent := (apFixedRow_bound admissible grade tangentRowJet
      (apMultiplier admissible (data.fluxDeviation grade) (apMatchingRadialColumn admissible grade psi))).trans
    (mul_le_mul_of_nonneg_left
      ((apMultiplier_bound admissible (data.fluxDeviation grade) (apMatchingRadialColumn admissible grade psi)).trans
        (mul_le_mul_of_nonneg_left (apMatchingRadialColumn_bound admissible grade psi)
          (matchingFluxDeviationSize_nonnegative admissible data grade)))
      (fixedRowBoundConstant_nonnegative admissible grade tangentRowJet))
  have first := (norm_add_le _ _).trans (add_le_add radial normal)
  exact ((norm_add_le _ _).trans (add_le_add first tangent)).trans_eq
    (by unfold matchingFluxDeviationSize matchingNormalDeviationSize; ring)

/-- Native graph to original high boundary defect. No width or frequency
cutoff is changed; this is a coefficient-norm estimate, not a one-high claim. -/
def matchingDefectConstant (data : LedgerData L sigma gamma ell) (grade : ℕ) : ℝ :=
  Real.sqrt (traceCellConstant (grade + 1)) *
    ((fixedRowBoundConstant L sigma gamma (grade + 1) radialRowJet * matchingFluxDeviationSize data (grade + 1) +
        matchingNormalDeviationSize data (grade + 1)) * reconstructionBoundConstant L gamma grade +
      fixedRowBoundConstant L sigma gamma (grade + 1) tangentRowJet * matchingFluxDeviationSize data (grade + 1) *
        matchingColumnConstant L sigma gamma (grade + 1) * psiBoundConstant L sigma gamma grade)

include admissible in
theorem matchingDefectConstant_nonnegative (data : LedgerData L sigma gamma ell) (grade : ℕ) :
    0 ≤ matchingDefectConstant data grade := by
  exact mul_nonneg (Real.sqrt_nonneg _)
    (add_nonneg
      (mul_nonneg (add_nonneg
        (mul_nonneg (fixedRowBoundConstant_nonnegative admissible (grade + 1) radialRowJet)
          (matchingFluxDeviationSize_nonnegative admissible data (grade + 1)))
        (matchingNormalDeviationSize_nonnegative admissible data (grade + 1)))
        (reconstructionBoundConstant_nonnegative admissible grade))
      (mul_nonneg (mul_nonneg (mul_nonneg
        (fixedRowBoundConstant_nonnegative admissible (grade + 1) tangentRowJet)
        (matchingFluxDeviationSize_nonnegative admissible data (grade + 1)))
        (matchingColumnConstant_nonnegative admissible (grade + 1)))
        (psiBoundConstant_nonnegative admissible grade)))

theorem completedMatchingDefect_bound (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    ‖completedMatchingDefect admissible data grade core field‖ ≤ matchingDefectConstant data grade * ‖field‖ := by
  have vector := ((completedReconstruct admissible grade core).le_opNorm field).trans
    (mul_le_mul_of_nonneg_right (completedReconstruct_bound admissible grade core) (norm_nonneg field))
  have psi := ((completedPsi admissible grade core).le_opNorm field).trans
    (mul_le_mul_of_nonneg_right (completedPsi_bound admissible grade core) (norm_nonneg field))
  have inner := add_le_add
    (mul_le_mul_of_nonneg_left vector (add_nonneg
      (mul_nonneg (fixedRowBoundConstant_nonnegative admissible (grade + 1) radialRowJet)
        (matchingFluxDeviationSize_nonnegative admissible data (grade + 1)))
      (matchingNormalDeviationSize_nonnegative admissible data (grade + 1))))
    (mul_le_mul_of_nonneg_left psi (mul_nonneg
      (mul_nonneg (fixedRowBoundConstant_nonnegative admissible (grade + 1) tangentRowJet)
        (matchingFluxDeviationSize_nonnegative admissible data (grade + 1)))
      (matchingColumnConstant_nonnegative admissible (grade + 1))))
  have bulk := (apMatchingDefectBulk_bound admissible data (grade + 1)
    (completedReconstruct admissible grade core field) (completedPsi admissible grade core field)).trans inner
  have trace := (apHighTrace_bound L sigma gamma ell (grade + 1) (by omega)
    (completedMatchingDefectBulk admissible data grade core field)).trans
      (mul_le_mul_of_nonneg_left bulk (Real.sqrt_nonneg _))
  have formula := congrArg (fun value : APBoundaryGrade L sigma gamma ell 1 (grade + 1) => ‖value‖)
    (completedMatchingDefect_formula admissible data grade core field)
  exact formula.le.trans (trace.trans_eq (by unfold matchingDefectConstant; ring))

theorem completedMatchingDefect_opNorm (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    ‖completedMatchingDefect admissible data grade core‖ ≤ matchingDefectConstant data grade :=
  ContinuousLinearMap.opNorm_le_bound _ (matchingDefectConstant_nonnegative admissible data grade)
    (completedMatchingDefect_bound admissible data grade core)

end Grad.GaugeCoefficients.Physical.Compensated
