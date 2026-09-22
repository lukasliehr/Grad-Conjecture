import AIE2ExactFullOutputVariationalLaw

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.AnnularCurrentSolution
open Grad.AnnularVariational Grad.AnnularGrades Grad.AnnularTiltedReference Grad.CircularHighWeak

/-- Boundary normalization for the stored energy variable. -/
def physicalIncomingNormalize : AnnularBoundary →L[ℂ] AnnularBoundary :=
  realLpDiagonal bEnergyWeight 2 (by norm_num) bEnergyWeight_bound

def physicalIncomingDecode : AnnularBoundary →L[ℂ] AnnularBoundary :=
  realLpDiagonal (fun mode => Real.sqrt (highMultiplier mode.val.1)) 1
    (by norm_num) bEnergyDecode_bound

theorem physicalIncomingNormalize_bound (datum : AnnularBoundary) :
    ‖physicalIncomingNormalize datum‖ ≤ 2 * ‖datum‖ :=
  realLpDiagonal_bound bEnergyWeight 2 (by norm_num) bEnergyWeight_bound datum

@[simp] theorem physicalIncomingDecode_normalize (datum : AnnularBoundary) :
    physicalIncomingDecode (physicalIncomingNormalize datum) = datum := by
  apply lp.ext
  funext mode
  simp only [physicalIncomingDecode, physicalIncomingNormalize, realLpDiagonal_apply,
    bEnergyWeight, smul_smul, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (Real.sqrt_pos.mpr (highMultiplier_positive mode)).ne',
    Complex.ofReal_one, one_smul]

@[simp] theorem physicalIncomingNormalize_decode (datum : AnnularBoundary) :
    physicalIncomingNormalize (physicalIncomingDecode datum) = datum := by
  apply lp.ext
  funext mode
  simp only [physicalIncomingDecode, physicalIncomingNormalize, realLpDiagonal_apply,
    bEnergyWeight, smul_smul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (Real.sqrt_pos.mpr (highMultiplier_positive mode)).ne',
    Complex.ofReal_one, one_smul]

/-- Exact both-endpoint correspondence for the actual decoded field. -/
theorem physicalIncomingTrace_decode (lower L : ℝ) (positive : 0 < lower)
    (collar : lower < 1) (lengthPositive : 0 < L) (endpoint : Fin 2)
    (field : annularEnergySpace lower L positive) :
    annularEnergyTrace lower L positive collar lengthPositive endpoint
      (bEnergyDecode lower L positive field) =
    physicalIncomingDecode
      (annularEnergyTrace lower L positive collar lengthPositive endpoint field) := by
  exact annularEnergyTrace_diagonal lower L positive collar lengthPositive _ _ _ _ endpoint field

/-- The physical incoming datum is equivalent to its normalized stored trace. -/
theorem physicalIncomingTrace_iff (lower L : ℝ) (positive : 0 < lower)
    (collar : lower < 1) (lengthPositive : 0 < L)
    (field : annularEnergySpace lower L positive) (datum : AnnularBoundary) :
    annularEnergyTrace lower L positive collar lengthPositive 0
      (bEnergyDecode lower L positive field) = datum ↔
    annularEnergyTrace lower L positive collar lengthPositive 0 field =
      physicalIncomingNormalize datum := by
  rw [physicalIncomingTrace_decode]
  constructor
  · intro equality
    have normalized := congrArg physicalIncomingNormalize equality
    simpa only [physicalIncomingNormalize_decode] using normalized
  · intro equality
    rw [equality, physicalIncomingDecode_normalize]

end Grad.AnnularCurrentSolution
