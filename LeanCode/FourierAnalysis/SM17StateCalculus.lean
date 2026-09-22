import SM16StateSmoothing

noncomputable section

open scoped Topology ContDiff

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace Grad.SmoothingFamily

open Grad.ClosedJets Grad.CartesianState Grad.ImplementationReadiness

instance stateGradeCoreRealNormedSpace (parameters : PhaseParameters) (grade : ℕ) :
    NormedSpace ℝ (StateGradeCore parameters grade) where
  norm_smul_le scalar state := by
    change ‖scalar • state.1‖ ≤ ‖scalar‖ * ‖state.1‖
    exact norm_smul_le scalar state.1

instance stateGradeCoreRealContinuousSMul (parameters : PhaseParameters) (grade : ℕ) :
    ContinuousSMul ℝ (StateGradeCore parameters grade) where
  continuous_smul := by
    apply Continuous.subtype_mk
    exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)

theorem stateScaleDerivative_hasDerivAt (parameters : PhaseParameters) (order grade : ℕ)
    (scale : ℝ) (positive : 0 < scale) (state : StateCore parameters) :
    HasDerivAt (fun parameter => stateToGrade parameters grade (stateScaleDerivative parameters order parameter state))
      (stateToGrade parameters grade (stateScaleDerivative parameters (order + 1) scale state)) scale := by
  let inner := (WithLp.prodContinuousLinearEquiv 1 ℝ (AGrade parameters 3 grade) (AGrade parameters 1 grade)).symm.toContinuousLinearMap
  let outer := (WithLp.prodContinuousLinearEquiv 1 ℝ
    (TGrade parameters.sigma0 (ComplexEuclidean 2) (grade + 1))
    (WithLp 1 (AGrade parameters 3 grade × AGrade parameters 1 grade))).symm.toContinuousLinearMap
  exact outer.hasFDerivAt.comp_hasDerivAt scale
    ((axisScaleDerivative_hasDerivAt parameters.sigma0 order (grade + 1) scale positive state.1).prodMk
      (inner.hasFDerivAt.comp_hasDerivAt scale
        ((ambientScaleDerivative_hasDerivAt parameters order grade scale positive state.2.1).prodMk
          (ambientScaleDerivative_hasDerivAt parameters order grade scale positive state.2.2))))

theorem stateScaleDerivative_contDiffAt (parameters : PhaseParameters) (order grade : ℕ)
    (scale : ℝ) (positive : 0 < scale) (state : StateCore parameters) :
    ContDiffAt ℝ ∞ (fun parameter => stateToGrade parameters grade (stateScaleDerivative parameters order parameter state)) scale := by
  let inner := (WithLp.prodContinuousLinearEquiv 1 ℝ (AGrade parameters 3 grade) (AGrade parameters 1 grade)).symm.toContinuousLinearMap
  let outer := (WithLp.prodContinuousLinearEquiv 1 ℝ
    (TGrade parameters.sigma0 (ComplexEuclidean 2) (grade + 1))
    (WithLp 1 (AGrade parameters 3 grade × AGrade parameters 1 grade))).symm.toContinuousLinearMap
  exact outer.contDiff.contDiffAt.comp scale
    ((axisScaleDerivative_contDiffAt parameters.sigma0 order (grade + 1) scale positive state.1).prodMk
      (inner.contDiff.contDiffAt.comp scale
        ((ambientScaleDerivative_contDiffAt parameters order grade scale positive state.2.1).prodMk
          (ambientScaleDerivative_contDiffAt parameters order grade scale positive state.2.2))))

theorem hasDerivAt_of_stateEta (parameters : PhaseParameters) (grade : ℕ)
    (curve : ℝ → StateGradeCore parameters grade) (derivative : StateGradeCore parameters grade) (scale : ℝ)
    (checked : HasDerivAt (fun parameter => (curve parameter).1) derivative.1 scale) :
    HasDerivAt curve derivative scale := by
  let etaMap := ((stateToGrade parameters grade).range.subtype).restrictScalars ℝ
  have etaNorm : ∀ value, ‖etaMap value‖ = ‖value‖ := fun _ => rfl
  change HasDerivAt (fun parameter => etaMap (curve parameter)) (etaMap derivative) scale at checked
  rw [hasDerivAt_iff_tendsto] at checked ⊢
  simpa only [← map_smul etaMap, ← map_sub etaMap, etaNorm] using checked

theorem stateScaleDerivative_hasDerivAt_grade (parameters : PhaseParameters) (order grade : ℕ)
    (scale : ℝ) (positive : 0 < scale) (state : StateCore parameters) :
    HasDerivAt (fun parameter => stateGradeEquiv parameters grade (stateScaleDerivative parameters order parameter state))
      (stateGradeEquiv parameters grade (stateScaleDerivative parameters (order + 1) scale state)) scale :=
  hasDerivAt_of_stateEta parameters grade _ _ scale (stateScaleDerivative_hasDerivAt parameters order grade scale positive state)

theorem iteratedDeriv_stateSmoothing_grade (parameters : PhaseParameters) (order grade : ℕ)
    (scale : ℝ) (positive : 0 < scale) (state : StateCore parameters) :
    iteratedDeriv order (fun parameter => stateGradeEquiv parameters grade (stateSmoothing parameters parameter state)) scale =
      stateGradeEquiv parameters grade (stateScaleDerivative parameters order scale state) := by
  induction order generalizing scale with
  | zero => simp only [iteratedDeriv_zero, stateScaleDerivative_zero]
  | succ order inductionHypothesis =>
    rw [iteratedDeriv_succ]
    have locallyEqual : iteratedDeriv order (fun parameter => stateGradeEquiv parameters grade (stateSmoothing parameters parameter state))
        =ᶠ[nhds scale] fun parameter => stateGradeEquiv parameters grade (stateScaleDerivative parameters order parameter state) := by
      filter_upwards [isOpen_Ioi.mem_nhds positive] with parameter parameterPositive
      exact inductionHypothesis parameter parameterPositive
    rw [locallyEqual.deriv_eq]
    exact (stateScaleDerivative_hasDerivAt_grade parameters order grade scale positive state).deriv

end Grad.SmoothingFamily
