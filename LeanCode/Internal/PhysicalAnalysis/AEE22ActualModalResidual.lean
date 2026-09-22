import AEE21ActualPairedLowGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators ENNReal
namespace Grad.AnnularLowCompletion
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem normalized_row_cancel {E : Type*} [AddCommGroup E] [Module ℝ E]
    (mu a b : ℝ) (nonzero : mu ≠ 0) (first second forcing : E) :
    mu⁻¹ • (a • first + b • second + mu • forcing) -
      ((a / mu) • first + (b / mu) • second) = forcing := by
  simp only [smul_add, smul_smul, inv_mul_cancel₀ nonzero, one_smul, div_eq_mul_inv]
  rw [mul_comm (mu⁻¹) a, mul_comm (mu⁻¹) b]
  abel

/-- The actual weak modal equations imply the exact decoded residual. -/
theorem lowPairRadialGraph_residual (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (mode : LowAnnularMode) (first second : WeightedRadialH1 1 lower)
    (forcingFirst forcingSecond : C(ℝ, ℂ))
    (equations : ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowRadialSlope lower positive bounded first radius =
        lowReferenceMatrix parameters length radius mode 0 0 • lowRadialValue lower positive bounded first radius +
        lowReferenceMatrix parameters length radius mode 0 1 • lowRadialValue lower positive bounded second radius +
        lowMu length radius mode.val.2 • scalarOne (forcingFirst radius) ∧
      lowRadialSlope lower positive bounded second radius =
        lowReferenceMatrix parameters length radius mode 1 0 • lowRadialValue lower positive bounded first radius +
        lowReferenceMatrix parameters length radius mode 1 1 • lowRadialValue lower positive bounded second radius +
        lowMu length radius mode.val.2 • scalarOne (forcingSecond radius))
    (row : Fin 2) (other : LowAnnularMode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowDataResidual lower positive (lowReferenceDataOperator parameters length lower lengthPositive positive bounded
        (lowPairRadialGraph lower length positive bounded mode first second)) (row, other) radius =
        if other = mode then scalarOne (if row = 0 then forcingFirst radius else forcingSecond radius) else 0 := by
  have residual := lowReferenceDataResidual_ae parameters length lower lengthPositive positive bounded
    (lowPairRadialGraph lower length positive bounded mode first second) (row, other)
  rw [lowPairRadialGraph_derivative, lowPairRadialGraph_value, lowPairRadialGraph_value] at residual
  by_cases same : other = mode
  · subst other
    have rowCases : row = 0 ∨ row = 1 := by omega
    rcases rowCases with rfl | rfl
    · simp only [Fin.reduceEq, ite_true, ite_false] at residual ⊢
      filter_upwards [residual, equations,
        collarScalar_ae 1 lower (lowMuInverseCurve lower length positive mode.val.2) (lowRadialSlope lower positive bounded first),
        ae_restrict_mem measurableSet_Icc] with radius residual equations scaled member
      rw [residual, scaled]
      change (lowMu length (max lower radius) mode.val.2)⁻¹ • _ - _ = _
      rw [max_eq_right member.1, equations.1]
      exact normalized_row_cancel _ _ _ (lowMu_pos length radius mode.val.2 (positive.trans_le member.1)).ne' _ _ _
    · simp only [Fin.reduceEq, ite_true, ite_false] at residual ⊢
      filter_upwards [residual, equations,
        collarScalar_ae 1 lower (lowMuInverseCurve lower length positive mode.val.2) (lowRadialSlope lower positive bounded second),
        ae_restrict_mem measurableSet_Icc] with radius residual equations scaled member
      rw [residual, scaled]
      change (lowMu length (max lower radius) mode.val.2)⁻¹ • _ - _ = _
      rw [max_eq_right member.1, equations.2]
      exact normalized_row_cancel _ _ _ (lowMu_pos length radius mode.val.2 (positive.trans_le member.1)).ne' _ _ _
  · simp only [same, if_false, map_zero] at residual ⊢
    filter_upwards [residual, (Lp.coeFn_zero (ComplexEuclidean 1) 2 (volume.restrict (Icc lower 1)))] with radius residual zeroValue
    simpa only [zeroValue, Pi.zero_apply, smul_zero, add_zero, sub_zero] using residual

end Grad.AnnularLowCompletion
