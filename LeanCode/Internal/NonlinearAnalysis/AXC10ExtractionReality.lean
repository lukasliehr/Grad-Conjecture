import AXC7ExtractionConsumer

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.ChartAxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.AxisSplit Grad.RealFixedRanges
open Grad.CompletedReality Grad.NonlinearQuotientBounds

variable {parameters : PhaseParameters}

theorem originValue_conjugate {dimension : ℕ} (field : ClosedJet dimension) :
    originValue (closedJetConjugate field) = cartesianPhysicalConjugation dimension (originValue field) := rfl

theorem originPartial_conjugate {dimension : ℕ} (direction : Fin 2) (field : ClosedJet dimension) :
    originPartial direction (closedJetConjugate field) =
      cartesianPhysicalConjugation dimension (originPartial direction field) := by
  rw [originPartial_eq_closedDerivative, closedJetConjugate_derivative]
  rfl

theorem sigmaExtraction_conjugate (source : QuotientRows parameters) (cell : ℤ) :
    sigmaExtraction (zCoreConjugation parameters source) cell =
      cartesianPhysicalConjugation 2 (sigmaExtraction source (-cell)) := by
  unfold sigmaExtraction
  rw [zCoreConjugation_coefficient, zCoreConjugation_coefficient, originValue_conjugate,
    originValue_conjugate]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · change (starRingEnd ℂ (originValue ((source 1).val (-cell)) 0) +
      starRingEnd ℂ (originValue ((source 0).val (-cell)) 0)) / 2 =
      starRingEnd ℂ ((originValue ((source 0).val (-cell)) 0 +
        originValue ((source 1).val (-cell)) 0) / 2)
    simp only [map_div₀, map_add, map_ofNat]
    ring
  · change (starRingEnd ℂ (originValue ((source 1).val (-cell)) 0) -
      starRingEnd ℂ (originValue ((source 0).val (-cell)) 0)) / (2 * Complex.I) =
      starRingEnd ℂ ((originValue ((source 0).val (-cell)) 0 -
        originValue ((source 1).val (-cell)) 0) / (2 * Complex.I))
    simp only [map_div₀, map_sub, map_mul, map_ofNat, Complex.conj_I]
    ring

theorem scalarOriginGradient_conjugate (field : ACore parameters 1) (cell : ℤ) :
    scalarOriginGradient (cartesianCoreConjugation parameters field) cell =
      cartesianPhysicalConjugation 2 (scalarOriginGradient field (-cell)) := by
  unfold scalarOriginGradient
  change planarPair (originPartial 0 (closedJetConjugate (field.val (-cell))) 0)
    (originPartial 1 (closedJetConjugate (field.val (-cell))) 0) = _
  rw [originPartial_conjugate, originPartial_conjugate]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> rfl

theorem planarJPair_conjugate (point : ComplexEuclidean 2) :
    planarJPair (cartesianPhysicalConjugation 2 point) =
      cartesianPhysicalConjugation 2 (planarJPair point) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · exact (map_neg (starRingEnd ℂ) (point 1)).symm
  · rfl

theorem etaExtraction_conjugate (cellLength : ℝ) (source : QuotientRows parameters) (cell : ℤ) :
    etaExtraction cellLength (zCoreConjugation parameters source) cell =
      cartesianPhysicalConjugation 2 (etaExtraction cellLength source (-cell)) := by
  unfold etaExtraction
  rw [show zCoreConjugation parameters source 3 = cartesianCoreConjugation parameters (source 3) from rfl,
    scalarOriginGradient_conjugate, sigmaExtraction_conjugate,
    Grad.AxisCore.axisConjugation_smul]
  have scalarLaw : starRingEnd ℂ ((cellLength : ℂ)⁻¹) = (cellLength : ℂ)⁻¹ := by simp
  rw [scalarLaw]
  congr 1
  rw [← planarJPair_conjugate]
  congr 1
  rw [map_add, Grad.AxisCore.axisConjugation_smul]
  have cellLaw : starRingEnd ℂ (((-cell : ℤ) : ℂ) * Complex.I) = (cell : ℂ) * Complex.I := by simp
  rw [cellLaw]

def axisDataConjugationLinear (parameters : PhaseParameters) (grade : ℕ) :
    AxisDataGrade parameters grade →ₗ[ℝ] AxisDataGrade parameters grade where
  toFun data := WithLp.toLp 1
    (axisConjugation parameters 2 (grade + 1) data.ofLp.1,
      axisConjugation parameters 2 (grade + 1) data.ofLp.2)
  map_add' first second := by
    change WithLp.toLp 1 _ = WithLp.toLp 1 _
    congr 1
    exact Prod.ext (map_add _ _ _) (map_add _ _ _)
  map_smul' scalar data := by
    change WithLp.toLp 1 _ = WithLp.toLp 1 _
    congr 1
    exact Prod.ext (map_smul _ _ _) (map_smul _ _ _)

theorem axisDataConjugationLinear_norm (parameters : PhaseParameters) (grade : ℕ)
    (data : AxisDataGrade parameters grade) :
    ‖axisDataConjugationLinear parameters grade data‖ = ‖data‖ := by
  rw [WithLp.prod_norm_eq_of_L1, WithLp.prod_norm_eq_of_L1]
  exact congrArg₂ (· + ·) ((axisConjugation parameters 2 (grade + 1)).norm_map data.ofLp.1)
    ((axisConjugation parameters 2 (grade + 1)).norm_map data.ofLp.2)

def axisDataConjugation (parameters : PhaseParameters) (grade : ℕ) :
    AxisDataGrade parameters grade →L[ℝ] AxisDataGrade parameters grade :=
  (axisDataConjugationLinear parameters grade).mkContinuous 1
    (fun data => by rw [axisDataConjugationLinear_norm, one_mul])

theorem axisExtractionData_real (parameters : PhaseParameters) (cellLength : ℝ) (grade : ℕ)
    (source : sourceSmoothRange parameters) :
    axisDataConjugation parameters grade
      (axisDataEmbedding parameters grade (extractionData cellLength source.val)) =
        axisDataEmbedding parameters grade (extractionData cellLength source.val) := by
  have realSource := ((mem_sourceSmoothRange parameters source.val).1 source.property).2
  apply (WithLp.equiv 1 _).injective
  apply Prod.ext
  all_goals
    apply Grad.ConstrainedGrades.axisCoefficient_ext parameters
    intro cell
  · change Grad.AxisCore.axisCoefficient parameters (grade + 1)
      (axisConjugation parameters 2 (grade + 1)
        (axisCoreEmbedding parameters (grade + 1) (sigmaData source.val))) cell = _
    change (Grad.AxisCore.axisWeight parameters (grade + 1) cell : ℂ)⁻¹ •
      cartesianPhysicalConjugation 2
        (axisCoordinates parameters (grade + 1) (sigmaData source.val).val (-cell)) = _
    rw [axisCoordinates, ← Complex.coe_smul, Grad.AxisCore.axisConjugation_real_smul,
      show axisWeight parameters (grade + 1) (-cell) = Grad.AxisCore.axisWeight parameters (grade + 1) cell from
        Grad.AxisCore.axisWeight_even parameters (grade + 1) cell,
      inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (Grad.AxisCore.axisWeight_pos parameters (grade + 1) cell).ne')]
    change cartesianPhysicalConjugation 2 ((sigmaData source.val).val (-cell)) =
      Grad.AxisCore.axisCoefficient parameters (grade + 1)
        (axisCoreEmbedding parameters (grade + 1) (sigmaData source.val)) cell
    rw [axisCoreEmbedding_coefficient]
    exact (sigmaExtraction_conjugate source.val cell).symm.trans (congrArg (fun rows => sigmaExtraction rows cell) realSource)
  · change Grad.AxisCore.axisCoefficient parameters (grade + 1)
      (axisConjugation parameters 2 (grade + 1)
        (axisCoreEmbedding parameters (grade + 1) (etaData cellLength source.val))) cell = _
    change (Grad.AxisCore.axisWeight parameters (grade + 1) cell : ℂ)⁻¹ •
      cartesianPhysicalConjugation 2
        (axisCoordinates parameters (grade + 1) (etaData cellLength source.val).val (-cell)) = _
    rw [axisCoordinates, ← Complex.coe_smul, Grad.AxisCore.axisConjugation_real_smul,
      show axisWeight parameters (grade + 1) (-cell) = Grad.AxisCore.axisWeight parameters (grade + 1) cell from
        Grad.AxisCore.axisWeight_even parameters (grade + 1) cell,
      inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (Grad.AxisCore.axisWeight_pos parameters (grade + 1) cell).ne')]
    change cartesianPhysicalConjugation 2 ((etaData cellLength source.val).val (-cell)) =
      Grad.AxisCore.axisCoefficient parameters (grade + 1)
        (axisCoreEmbedding parameters (grade + 1) (etaData cellLength source.val)) cell
    rw [axisCoreEmbedding_coefficient]
    exact (etaExtraction_conjugate cellLength source.val cell).symm.trans
      (congrArg (fun rows => etaExtraction cellLength rows cell) realSource)

theorem completedExtraction_real (parameters : PhaseParameters) (cellLength : ℝ) (grade : ℕ)
    (source : sourceRange parameters (grade + 3) (extractionLarge grade)) :
    axisDataConjugation parameters grade (completedExtraction parameters cellLength grade source) =
      completedExtraction parameters cellLength grade source := by
  apply isClosed_property (sourceSmoothEmbedding_denseRange parameters (grade + 3) (extractionLarge grade))
    (isClosed_eq ((axisDataConjugation parameters grade).continuous.comp
      (completedExtraction parameters cellLength grade).continuous)
      (completedExtraction parameters cellLength grade).continuous) _ source
  intro core
  simp only [Function.comp_apply, completedExtraction_core]
  exact axisExtractionData_real parameters cellLength grade core

end Grad.ChartAxisSplit
