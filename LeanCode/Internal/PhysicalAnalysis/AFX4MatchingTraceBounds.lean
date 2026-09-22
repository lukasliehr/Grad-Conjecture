import AFX3PhysicalFluxIdentity
import AFX2CompletedMatchingTraces

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryTrace

def matchingColumnConstant (L sigma gamma : ℝ) (grade : ℕ) : ℝ :=
  apMultiplierConstant L sigma gamma grade * fixedJetConstant matchingRadialColumnJet grade

def matchingFluxDeviationSize {L sigma gamma ell : ℝ} (data : LedgerData L sigma gamma ell) (grade : ℕ) : ℝ :=
  apMultiplierConstant L sigma gamma grade * ‖data.fluxDeviation grade‖

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)

include admissible in
theorem matchingColumnConstant_nonnegative (grade : ℕ) : 0 ≤ matchingColumnConstant L sigma gamma grade :=
  mul_nonneg (apMultiplierConstant_nonnegative admissible grade) (fixedJetConstant_nonnegative _ grade)

include admissible in
theorem matchingFluxDeviationSize_nonnegative (data : LedgerData L sigma gamma ell) (grade : ℕ) :
    0 ≤ matchingFluxDeviationSize data grade :=
  mul_nonneg (apMultiplierConstant_nonnegative admissible grade) (norm_nonneg _)

theorem apMatchingRadialColumn_bound (grade : ℕ) (field : apGrade L sigma gamma ell 1 grade) :
    ‖apMatchingRadialColumn admissible grade field‖ ≤ matchingColumnConstant L sigma gamma grade * ‖field‖ :=
  (apMultiplier_bound admissible _ field).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (fixedJetFamily_norm_le L sigma gamma ell matchingRadialColumnJet grade)
      (apMultiplierConstant_nonnegative admissible grade)) (norm_nonneg field))

theorem apMatchingFlux_bound (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (field : apGrade L sigma gamma ell 3 grade) :
    ‖apMatchingFlux admissible data grade field‖ ≤ (1 + matchingFluxDeviationSize data grade) * ‖field‖ := by
  have multiplier := apMultiplier_bound admissible (data.fluxDeviation grade) field
  have summed := add_le_add (le_of_eq (norm_neg field)) multiplier
  have total := (norm_add_le (-field) (apMultiplier admissible (data.fluxDeviation grade) field)).trans summed
  exact total.trans_eq (by unfold matchingFluxDeviationSize; ring)


/-- The original AP2 grade bound, with both coefficient products in the bulk. -/
theorem apMatchingPrimitive_bound (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (field : apGrade L sigma gamma ell 3 grade) (psi : apGrade L sigma gamma ell 1 grade) :
    ‖apMatchingPrimitive admissible data grade field psi‖ ≤
      (1 + orthogonalGradeConstant grade) * (1 + matchingFluxDeviationSize data grade) *
        (fixedRowBoundConstant L sigma gamma grade radialRowJet * ‖field‖ +
          fixedRowBoundConstant L sigma gamma grade tangentRowJet * matchingColumnConstant L sigma gamma grade * ‖psi‖) := by
  have radial := (apFixedRow_bound admissible grade radialRowJet (apMatchingFlux admissible data grade field)).trans
    (mul_le_mul_of_nonneg_left (apMatchingFlux_bound admissible data grade field)
      (fixedRowBoundConstant_nonnegative admissible grade radialRowJet))
  have tangent := (apFixedRow_bound admissible grade tangentRowJet
      (apMatchingFlux admissible data grade (apMatchingRadialColumn admissible grade psi))).trans
    (mul_le_mul_of_nonneg_left
      ((apMatchingFlux_bound admissible data grade (apMatchingRadialColumn admissible grade psi)).trans
        (mul_le_mul_of_nonneg_left (apMatchingRadialColumn_bound admissible grade psi)
          (by linarith [matchingFluxDeviationSize_nonnegative admissible data grade])))
      (fixedRowBoundConstant_nonnegative admissible grade tangentRowJet))
  have total := (norm_add_le _ _).trans (add_le_add radial tangent)
  exact (apMeanFree_bound L sigma gamma ell 1 grade _).trans
    ((mul_le_mul_of_nonneg_left total (by linarith [orthogonalGradeConstant_nonnegative grade])).trans_eq (by ring))

/-- The exact error has an explicit factor of the actual `B_C+I` norm. -/
theorem apMatchingDeviation_bound (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (field : apGrade L sigma gamma ell 3 grade) (psi : apGrade L sigma gamma ell 1 grade) :
    ‖apMeanFree L sigma gamma ell 1 grade
      (apRadialContraction admissible grade (apMultiplier admissible (data.fluxDeviation grade) field) +
        apTangentContraction admissible grade
          (apMultiplier admissible (data.fluxDeviation grade) (apMatchingRadialColumn admissible grade psi)))‖ ≤
      (1 + orthogonalGradeConstant grade) * matchingFluxDeviationSize data grade *
        (fixedRowBoundConstant L sigma gamma grade radialRowJet * ‖field‖ +
          fixedRowBoundConstant L sigma gamma grade tangentRowJet * matchingColumnConstant L sigma gamma grade * ‖psi‖) := by
  have radial := (apFixedRow_bound admissible grade radialRowJet
    (apMultiplier admissible (data.fluxDeviation grade) field)).trans
      (mul_le_mul_of_nonneg_left (apMultiplier_bound admissible (data.fluxDeviation grade) field)
        (fixedRowBoundConstant_nonnegative admissible grade radialRowJet))
  have tangent := (apFixedRow_bound admissible grade tangentRowJet
      (apMultiplier admissible (data.fluxDeviation grade) (apMatchingRadialColumn admissible grade psi))).trans
    (mul_le_mul_of_nonneg_left
      ((apMultiplier_bound admissible (data.fluxDeviation grade) (apMatchingRadialColumn admissible grade psi)).trans
        (mul_le_mul_of_nonneg_left (apMatchingRadialColumn_bound admissible grade psi)
          (matchingFluxDeviationSize_nonnegative admissible data grade)))
      (fixedRowBoundConstant_nonnegative admissible grade tangentRowJet))
  have total := (norm_add_le _ _).trans (add_le_add radial tangent)
  exact (apMeanFree_bound L sigma gamma ell 1 grade _).trans
    ((mul_le_mul_of_nonneg_left total (by linarith [orthogonalGradeConstant_nonnegative grade])).trans_eq
      (by unfold matchingFluxDeviationSize; ring))

/-- AR14 with the original grade/phase and an explicit coefficient deviation.
The reconstructed current vector and preserved scalar keep their native grades. -/
theorem completedMatchingP_difference_bound (data : LedgerData L sigma gamma ell)
    (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation)
    (grade : ℕ) (large : 3 ≤ grade) (field : circularCompensatedClosure admissible grade) :
    let outputCore := currentCompensatedCore admissible data.gaugeDeviation smooth.coherent
    let output := completedTransfer smooth grade large field
    ‖completedMatchingP admissible data grade outputCore output -
      completedCircleMatchingP admissible grade (circularCompensatedCore admissible) field‖ ≤
      Real.sqrt (traceCellConstant (grade + 1)) * (1 + orthogonalGradeConstant (grade + 1)) *
        matchingFluxDeviationSize data (grade + 1) *
        (fixedRowBoundConstant L sigma gamma (grade + 1) radialRowJet *
          ‖completedReconstruct admissible grade outputCore output‖ +
         fixedRowBoundConstant L sigma gamma (grade + 1) tangentRowJet * matchingColumnConstant L sigma gamma (grade + 1) *
           ‖completedPsi admissible grade (circularCompensatedCore admissible) field‖) := by
  dsimp only
  have identity := congrArg (fun value : APBoundaryGrade L sigma gamma ell 1 (grade + 1) => ‖value‖)
    (completedMatchingP_difference admissible data smooth grade large field)
  have bulk := apMatchingDeviation_bound admissible data (grade + 1)
    (completedReconstruct admissible grade
      (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent) (completedTransfer smooth grade large field))
    (completedPsi admissible grade (circularCompensatedCore admissible) field)
  exact identity.le.trans ((apBoundaryTrace_bound L sigma gamma ell (grade + 1) (by omega) _).trans
    ((mul_le_mul_of_nonneg_left bulk (Real.sqrt_nonneg _)).trans_eq (by ring)))

/-- Native graph to original AP3 trace bound. All constants precede the
graph input, and no cap-cell frequency cutoff or width change occurs. -/
def matchingTraceConstant (data : LedgerData L sigma gamma ell) (grade : ℕ) : ℝ :=
  Real.sqrt (traceCellConstant (grade + 1)) *
    (1 + orthogonalGradeConstant (grade + 1)) * (1 + matchingFluxDeviationSize data (grade + 1)) *
      (fixedRowBoundConstant L sigma gamma (grade + 1) radialRowJet * reconstructionBoundConstant L gamma grade +
       fixedRowBoundConstant L sigma gamma (grade + 1) tangentRowJet * matchingColumnConstant L sigma gamma (grade + 1) *
         psiBoundConstant L sigma gamma grade)

include admissible in
theorem matchingTraceConstant_nonnegative (data : LedgerData L sigma gamma ell) (grade : ℕ) :
    0 ≤ matchingTraceConstant data grade := by
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (add_nonneg zero_le_one (orthogonalGradeConstant_nonnegative (grade + 1))))
      (add_nonneg zero_le_one (matchingFluxDeviationSize_nonnegative admissible data (grade + 1))))
    (add_nonneg (mul_nonneg (fixedRowBoundConstant_nonnegative admissible (grade + 1) radialRowJet)
      (reconstructionBoundConstant_nonnegative admissible grade))
      (mul_nonneg (mul_nonneg (fixedRowBoundConstant_nonnegative admissible (grade + 1) tangentRowJet)
        (matchingColumnConstant_nonnegative admissible (grade + 1))) (psiBoundConstant_nonnegative admissible grade)))


theorem completedMatchingP_bound (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    ‖completedMatchingP admissible data grade core field‖ ≤ matchingTraceConstant data grade * ‖field‖ := by
  have vector := (completedReconstruct admissible grade core).le_opNorm field
  have vector' := vector.trans (mul_le_mul_of_nonneg_right
    (completedReconstruct_bound admissible grade core) (norm_nonneg field))
  have psi := (completedPsi admissible grade core).le_opNorm field
  have psi' := psi.trans (mul_le_mul_of_nonneg_right
    (completedPsi_bound admissible grade core) (norm_nonneg field))
  have inner := add_le_add
    (mul_le_mul_of_nonneg_left vector' (fixedRowBoundConstant_nonnegative admissible (grade + 1) radialRowJet))
    (mul_le_mul_of_nonneg_left psi' (mul_nonneg
      (fixedRowBoundConstant_nonnegative admissible (grade + 1) tangentRowJet)
      (matchingColumnConstant_nonnegative admissible (grade + 1))))
  have coefficient : 0 ≤ (1 + orthogonalGradeConstant (grade + 1)) * (1 + matchingFluxDeviationSize data (grade + 1)) :=
    mul_nonneg (by linarith [orthogonalGradeConstant_nonnegative (grade + 1)])
      (by linarith [matchingFluxDeviationSize_nonnegative admissible data (grade + 1)])
  have primitive := (apMatchingPrimitive_bound admissible data (grade + 1)
    (completedReconstruct admissible grade core field) (completedPsi admissible grade core field)).trans
      (mul_le_mul_of_nonneg_left inner coefficient)
  exact (apBoundaryTrace_bound L sigma gamma ell (grade + 1) (by omega) _).trans
    ((mul_le_mul_of_nonneg_left primitive (Real.sqrt_nonneg _)).trans_eq (by unfold matchingTraceConstant; ring))

theorem completedMatchingP_opNorm (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    ‖completedMatchingP admissible data grade core‖ ≤ matchingTraceConstant data grade :=
  ContinuousLinearMap.opNorm_le_bound _ (matchingTraceConstant_nonnegative admissible data grade)
    (completedMatchingP_bound admissible data grade core)

theorem completedMatchingD_bound (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    ‖completedMatchingD admissible grade core field‖ ≤
      |ell| * Real.sqrt (traceCellConstant (grade + 1)) * psiBoundConstant L sigma gamma grade * ‖field‖ := by
  have psi := ((completedPsi admissible grade core).le_opNorm field).trans
    (mul_le_mul_of_nonneg_right (completedPsi_bound admissible grade core) (norm_nonneg field))
  have trace := (apBoundaryTrace_bound L sigma gamma ell (grade + 1) (by omega)
      (completedPsi admissible grade core field)).trans
    (mul_le_mul_of_nonneg_left psi (Real.sqrt_nonneg _))
  have weighted := mul_le_mul_of_nonneg_left trace (norm_nonneg (ell : ℂ))
  have scalar := norm_smul (ell : ℂ) (apBoundaryTrace L sigma gamma ell (grade + 1) (by omega)
    (completedPsi admissible grade core field))
  have equality : ‖(ell : ℂ)‖ = |ell| := (Complex.norm_real ell).trans (Real.norm_eq_abs ell)
  exact scalar.le.trans (weighted.trans_eq (by rw [equality]; ring))


end Grad.GaugeCoefficients.Physical.Compensated
