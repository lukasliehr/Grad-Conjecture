import AKCB7ActualBaselineMatrixWeak

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 2000
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

/-- Raise only the coefficient cell reserve, preserving the spatial index. -/
def startupCellReserveIndex {grade : ℕ} (extra : ℕ) (index : DerivativeIndex grade) :
    DerivativeIndex (grade+extra) :=
  ⟨(⟨index.1.1.val,by have := index.1.1.isLt; omega⟩,
    ⟨index.1.2.val,by have := index.1.2.isLt; omega⟩),by
      change index.1.1.val+index.1.2.val≤grade+extra
      have := index.property
      omega⟩

theorem startupCellReserveIndex_order {grade : ℕ} (extra : ℕ) (index : DerivativeIndex grade) :
    derivativeOrder (startupCellReserveIndex extra index)=derivativeOrder index := rfl

theorem startupCellReserveIndex_multi {grade : ℕ} (extra : ℕ) (index : DerivativeIndex grade) :
    derivativeMultiIndex (startupCellReserveIndex extra index)=derivativeMultiIndex index := rfl

theorem startupWeightedDerivative_cellReserve {L sigma gamma ell : ℝ} {grade input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (extra : ℕ) (index : DerivativeIndex grade) (cell : ℤ) :
    weightedDerivative (family (grade+extra)) cell (startupCellReserveIndex extra index)=
      ((scaledCellWeight L ell cell^extra : ℝ):ℂ) • weightedDerivative (family grade) cell index := by
  apply ContinuousMap.ext
  intro point
  rw [ContinuousMap.smul_apply,weighted_derivative_literal,weighted_derivative_literal,
    coherent_derivative_raw family coherent,coherent_derivative_raw family coherent,
    startupCellReserveIndex_multi,smul_smul]
  congr 1
  rw [← Complex.ofReal_mul]
  congr 1
  unfold coefficientScale
  rw [startupCellReserveIndex_order]
  have exponent : grade+extra-derivativeOrder index=extra+(grade-derivativeOrder index) := by
    have := index.property
    change index.1.1.val+index.1.2.val≤grade at this
    unfold derivativeOrder
    omega
  rw [exponent,pow_add]
  ring

theorem startupCoefficientMap_smul_norm_le {input output : ℕ} (scalar : ℂ)
    (coefficient : C(ClosedDisk,OperatorValue input output)) :
    ‖scalar • coefficient‖≤‖scalar‖*‖coefficient‖ := by
  apply (ContinuousMap.norm_le (scalar • coefficient)
    (mul_nonneg (norm_nonneg scalar) (norm_nonneg coefficient))).mpr
  intro point
  change ‖scalar • coefficient point‖≤_
  exact (norm_smul_le scalar (coefficient point)).trans
    (mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm coefficient point) (norm_nonneg scalar))

theorem startupWeightedDerivative_cellReserve_norm {L sigma gamma ell : ℝ} {grade input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (extra : ℕ) (index : DerivativeIndex grade) (cell : ℤ) :
    ‖weightedDerivative (family (grade+extra)) cell (startupCellReserveIndex extra index)‖=
      scaledCellWeight L ell cell^extra * ‖weightedDerivative (family grade) cell index‖ := by
  have positive : 0<scaledCellWeight L ell cell^extra :=
    pow_pos (zero_lt_one.trans_le (scaledCellWeight_one_le L ell cell)) _
  let scalar : ℂ := ((scaledCellWeight L ell cell^extra : ℝ):ℂ)
  have scalarNorm : ‖scalar‖=scaledCellWeight L ell cell^extra := by
    rw [Complex.norm_real,Real.norm_of_nonneg positive.le]
  have nonzero : scalar≠0 := Complex.ofReal_ne_zero.mpr positive.ne'
  rw [startupWeightedDerivative_cellReserve family coherent]
  apply le_antisymm
  · exact (startupCoefficientMap_smul_norm_le scalar _).trans_eq (by rw [scalarNorm])
  · have inverse := startupCoefficientMap_smul_norm_le scalar⁻¹
      (scalar • weightedDerivative (family grade) cell index)
    rw [smul_smul,inv_mul_cancel₀ nonzero,one_smul,norm_inv,scalarNorm,
      mul_comm,← div_eq_mul_inv] at inverse
    exact (mul_comm _ _).le.trans ((le_div_iff₀ positive).mp inverse)

/-- Exact reserve payment in the full coefficient majorant, before mixing cells. -/
theorem startupDerivativeMajorant_cellReserve {L sigma gamma ell : ℝ} {grade input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (extra : ℕ) (index : DerivativeIndex grade) (cell : ℤ) :
    startupDerivativeMajorant (family (grade+extra)) (startupCellReserveIndex extra index) cell=
      scaledCellWeight L ell cell^extra * startupDerivativeMajorant (family grade) index cell := by
  unfold startupDerivativeMajorant
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro split _
  have normSame := startupWeightedDerivative_cellReserve_norm family coherent extra (upperDerivativeIndex index split) cell
  change _ * ‖weightedDerivative (family (grade+extra)) cell
    (startupCellReserveIndex extra (upperDerivativeIndex index split))‖ = _
  rw [normSame]
  change (splitMultiplicity index split : ℝ) *
    apRatioConstant L sigma gamma (derivativeOrder (lowerDerivativeIndex index split)) *
    (scaledCellWeight L ell cell^extra * ‖weightedDerivative (family grade) cell (upperDerivativeIndex index split)‖) = _
  ring

end Grad.CartesianStartup
