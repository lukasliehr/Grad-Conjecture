import SM6FourierCalculus

noncomputable section

open scoped ContDiff Topology

namespace Grad.SmoothingFamily

open Grad.ClosedJets Grad.CartesianState Grad.FourierGrade Grad.COR12Extension Grad.COR13Completion

/-- Literal P21: W inverse, disk restriction, inverse Fourier cutoff,
Fourier extension, and the original unchanged phase W. -/
def ambientSmoothing {dimension : ℕ} (parameters : PhaseParameters) (scale : ℝ) :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension :=
  (weightedFourierRetraction parameters).comp
    ((fourierSmoothing scale).comp (weightedFourierExtension parameters))

def ambientScaleDerivative {dimension : ℕ} (parameters : PhaseParameters) (order : ℕ) (scale : ℝ) :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension :=
  (weightedFourierRetraction parameters).comp
    ((fourierScaleDerivative order scale).comp (weightedFourierExtension parameters))

theorem ambientSmoothing_apply {dimension : ℕ} (parameters : PhaseParameters) (scale : ℝ)
    (field : ACore parameters dimension) :
    ambientSmoothing parameters scale field =
      weightedFourierRetraction parameters (fourierSmoothing scale (weightedFourierExtension parameters field)) := rfl

theorem ambientScaleDerivative_apply {dimension : ℕ} (parameters : PhaseParameters) (order : ℕ)
    (scale : ℝ) (field : ACore parameters dimension) :
    ambientScaleDerivative parameters order scale field =
      weightedFourierRetraction parameters
        (fourierScaleDerivative order scale (weightedFourierExtension parameters field)) := rfl

theorem ambientScaleDerivative_zero {dimension : ℕ} (parameters : PhaseParameters) (scale : ℝ) :
    ambientScaleDerivative (dimension := dimension) parameters 0 scale = ambientSmoothing parameters scale := by
  unfold ambientScaleDerivative
  rw [fourierScaleDerivative_zero]
  rfl

theorem ambientRemainder_apply {dimension : ℕ} (parameters : PhaseParameters) (scale : ℝ)
    (field : ACore parameters dimension) :
    field - ambientSmoothing parameters scale field =
      weightedFourierRetraction parameters (weightedFourierExtension parameters field -
        fourierSmoothing scale (weightedFourierExtension parameters field)) := by
  rw [map_sub, weightedFourierRetraction_extension, ambientSmoothing_apply]

theorem ambientSmoothing_norm_le {dimension : ℕ} (parameters : PhaseParameters)
    (scale : ℝ) (scalePositive : 0 < scale) (lower upper : ℕ) (ordered : lower ≤ upper)
    (field : ACore parameters dimension) :
    ‖GradeCore.ofCoreLinear (grade := upper) (ambientSmoothing parameters scale field)‖ ≤
      (sameGradeConstant upper * sameGradeConstant lower * (2 : ℝ) ^ (upper - lower)) *
        scale ^ (upper - lower) * ‖GradeCore.ofCoreLinear (grade := lower) field‖ := by
  calc
    _ ≤ sameGradeConstant upper *
        ‖coreToGrade upper (fourierSmoothing scale (weightedFourierExtension parameters field))‖ :=
      weightedFourierRetraction_norm_le parameters _ upper
    _ ≤ sameGradeConstant upper * ((2 * scale) ^ (upper - lower) *
        ‖coreToGrade lower (weightedFourierExtension parameters field)‖) :=
      mul_le_mul_of_nonneg_left (fourierSmoothing_norm_le scale scalePositive lower upper ordered _)
        (sameGradeConstant_nonnegative upper)
    _ ≤ sameGradeConstant upper * ((2 * scale) ^ (upper - lower) *
        (sameGradeConstant lower * ‖GradeCore.ofCoreLinear (grade := lower) field‖)) := by
      apply mul_le_mul_of_nonneg_left _ (sameGradeConstant_nonnegative upper)
      exact mul_le_mul_of_nonneg_left (weightedFourierExtension_norm_le parameters field lower) (by positivity)
    _ = _ := by rw [mul_pow]; ring

theorem ambientRemainder_norm_le {dimension : ℕ} (parameters : PhaseParameters)
    (scale : ℝ) (scalePositive : 0 < scale) (lower upper : ℕ) (ordered : lower ≤ upper)
    (field : ACore parameters dimension) :
    ‖GradeCore.ofCoreLinear (grade := lower) (field - ambientSmoothing parameters scale field)‖ ≤
      (sameGradeConstant lower * sameGradeConstant upper) *
        scale ^ ((lower : ℝ) - (upper : ℝ)) * ‖GradeCore.ofCoreLinear (grade := upper) field‖ := by
  rw [ambientRemainder_apply]
  calc
    _ ≤ sameGradeConstant lower *
        ‖coreToGrade lower (weightedFourierExtension parameters field -
          fourierSmoothing scale (weightedFourierExtension parameters field))‖ :=
      weightedFourierRetraction_norm_le parameters _ lower
    _ ≤ sameGradeConstant lower * (scale ^ ((lower : ℝ) - (upper : ℝ)) *
        ‖coreToGrade upper (weightedFourierExtension parameters field)‖) :=
      mul_le_mul_of_nonneg_left (fourierRemainder_norm_le scale scalePositive lower upper ordered _)
        (sameGradeConstant_nonnegative lower)
    _ ≤ sameGradeConstant lower * (scale ^ ((lower : ℝ) - (upper : ℝ)) *
        (sameGradeConstant upper * ‖GradeCore.ofCoreLinear (grade := upper) field‖)) := by
      apply mul_le_mul_of_nonneg_left _ (sameGradeConstant_nonnegative lower)
      exact mul_le_mul_of_nonneg_left (weightedFourierExtension_norm_le parameters field upper)
        (Real.rpow_nonneg scalePositive.le _)
    _ = _ := by ring

theorem ambientScaleDerivative_norm_le {dimension : ℕ} (parameters : PhaseParameters)
    (scale : ℝ) (scalePositive : 0 < scale) (lower upper order : ℕ) (positiveOrder : 0 < order)
    (field : ACore parameters dimension) :
    ‖GradeCore.ofCoreLinear (grade := upper) (ambientScaleDerivative parameters order scale field)‖ ≤
      (sameGradeConstant upper * sameGradeConstant lower * (2 : ℝ) ^ upper * profileBound order) *
        scale ^ ((upper : ℝ) - (lower : ℝ) - (order : ℝ)) *
          ‖GradeCore.ofCoreLinear (grade := lower) field‖ := by
  calc
    _ ≤ sameGradeConstant upper * ‖coreToGrade upper
        (fourierScaleDerivative order scale (weightedFourierExtension parameters field))‖ :=
      weightedFourierRetraction_norm_le parameters _ upper
    _ ≤ sameGradeConstant upper * (((2 : ℝ) ^ upper * profileBound order) *
        scale ^ ((upper : ℝ) - (lower : ℝ) - (order : ℝ)) *
          ‖coreToGrade lower (weightedFourierExtension parameters field)‖) :=
      mul_le_mul_of_nonneg_left
        (fourierScaleDerivative_norm_le scale scalePositive lower upper order positiveOrder _)
        (sameGradeConstant_nonnegative upper)
    _ ≤ sameGradeConstant upper * (((2 : ℝ) ^ upper * profileBound order) *
        scale ^ ((upper : ℝ) - (lower : ℝ) - (order : ℝ)) *
          (sameGradeConstant lower * ‖GradeCore.ofCoreLinear (grade := lower) field‖)) := by
      apply mul_le_mul_of_nonneg_left _ (sameGradeConstant_nonnegative upper)
      exact mul_le_mul_of_nonneg_left (weightedFourierExtension_norm_le parameters field lower)
        (mul_nonneg (mul_nonneg (by positivity) (profileBound_nonnegative order))
          (Real.rpow_nonneg scalePositive.le _))
    _ = _ := by ring

theorem ambientScaleDerivative_eta {dimension : ℕ} (parameters : PhaseParameters)
    (order grade : ℕ) (scale : ℝ) (field : ACore parameters dimension) :
    aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade)
      (ambientScaleDerivative parameters order scale field)) =
      completedRetraction parameters (coreToGrade grade
        (fourierScaleDerivative order scale (weightedFourierExtension parameters field))) :=
  (completedRetraction_apply_core parameters _).symm

theorem ambientScaleDerivative_hasDerivAt {dimension : ℕ} (parameters : PhaseParameters)
    (order grade : ℕ) (scale : ℝ) (positive : 0 < scale) (field : ACore parameters dimension) :
    HasDerivAt (fun parameter => aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade)
      (ambientScaleDerivative parameters order parameter field)))
      (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade)
        (ambientScaleDerivative parameters (order + 1) scale field))) scale := by
  simp only [ambientScaleDerivative_eta]
  exact ((completedRetraction parameters).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt scale
    (fourierScaleDerivative_hasDerivAt order grade scale positive (weightedFourierExtension parameters field))

theorem ambientScaleDerivative_contDiffAt {dimension : ℕ} (parameters : PhaseParameters)
    (order grade : ℕ) (scale : ℝ) (positive : 0 < scale) (field : ACore parameters dimension) :
    ContDiffAt ℝ ∞ (fun parameter => aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade)
      (ambientScaleDerivative parameters order parameter field))) scale := by
  simp only [ambientScaleDerivative_eta]
  exact ((completedRetraction parameters).restrictScalars ℝ).contDiff.contDiffAt.comp scale
    (fourierScaleDerivative_contDiffAt order grade scale positive (weightedFourierExtension parameters field))

theorem iteratedDeriv_ambientSmoothing {dimension : ℕ} (parameters : PhaseParameters)
    (order grade : ℕ) (scale : ℝ) (positive : 0 < scale) (field : ACore parameters dimension) :
    iteratedDeriv order (fun parameter => aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade)
      (ambientSmoothing parameters parameter field))) scale =
      aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade)
        (ambientScaleDerivative parameters order scale field)) := by
  induction order generalizing scale with
  | zero => simp only [iteratedDeriv_zero, ambientScaleDerivative_zero]
  | succ order inductionHypothesis =>
    rw [iteratedDeriv_succ]
    have locallyEqual : iteratedDeriv order (fun parameter => aGradeEta parameters
        (GradeCore.ofCoreLinear (grade := grade) (ambientSmoothing parameters parameter field)))
        =ᶠ[nhds scale] fun parameter => aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade)
          (ambientScaleDerivative parameters order parameter field)) := by
      filter_upwards [isOpen_Ioi.mem_nhds positive] with parameter parameterPositive
      exact inductionHypothesis parameter parameterPositive
    rw [locallyEqual.deriv_eq]
    exact (ambientScaleDerivative_hasDerivAt parameters order grade scale positive field).deriv

end Grad.SmoothingFamily
