import AEA1ExactLowFrequencyDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowReference
open Grad.AnnularLowEnergy Grad.AnnularVariational Grad.PhaseAlgebra
open Grad.CartesianState

def lowCircularB (mode : LowAnnularMode) : ℝ := 1 - 4 / (mode.val.1 : ℝ) ^ 2

def lowCircularPotential (length radius : ℝ) (mode : LowAnnularMode) : ℝ :=
  ((mode.val.2 : ℝ) / length) ^ 2 + ((mode.val.1 : ℝ) / radius) ^ 2

theorem lowAngular_center_sq (mode : LowAnnularMode) (center : |mode.val.1| = 1) :
    (mode.val.1 : ℝ) ^ 2 = 1 := by
  have absolute : |(mode.val.1 : ℝ)| = 1 := by exact_mod_cast center
  nlinarith [sq_abs (mode.val.1 : ℝ)]

theorem lowAngular_exceptional_sq (mode : LowAnnularMode) (exceptional : ¬ |mode.val.1| = 1) :
    (mode.val.1 : ℝ) ^ 2 = 4 := by
  have absolute : |(mode.val.1 : ℝ)| = 2 := by exact_mod_cast mode.property.resolve_left exceptional
  nlinarith [sq_abs (mode.val.1 : ℝ)]

theorem lowCircularB_center (mode : LowAnnularMode) (center : |mode.val.1| = 1) : lowCircularB mode = -3 := by
  rw [lowCircularB, lowAngular_center_sq mode center]
  norm_num

theorem lowCircularB_exceptional (mode : LowAnnularMode) (exceptional : ¬ |mode.val.1| = 1) : lowCircularB mode = 0 := by
  rw [lowCircularB, lowAngular_exceptional_sq mode exceptional]
  norm_num

theorem lowCircularPotential_center (length radius : ℝ) (mode : LowAnnularMode)
    (center : |mode.val.1| = 1) : lowCircularPotential length radius mode = lowMu length radius mode.val.2 ^ 2 := by
  simp only [lowCircularPotential, lowMu_sq, div_pow]
  rw [lowAngular_center_sq mode center, one_div, inv_pow]

theorem lowCircularPotential_exceptional (length radius : ℝ) (mode : LowAnnularMode)
    (exceptional : ¬ |mode.val.1| = 1) :
    lowCircularPotential length radius mode = lowMu length radius mode.val.2 ^ 2 + 3 * radius⁻¹ ^ 2 := by
  simp only [lowCircularPotential, lowMu_sq, div_pow]
  rw [lowAngular_exceptional_sq mode exceptional]
  ring

/-- The exact off-diagonal entries displayed in BE10. -/
def lowReferenceUpper (length radius : ℝ) (mode : LowAnnularMode) : ℝ :=
  if |mode.val.1| = 1 then Real.sqrt 3 * lowMu length radius mode.val.2 else 0

def lowReferenceLower (length gamma radius : ℝ) (mode : LowAnnularMode) : ℝ :=
  if |mode.val.1| = 1 then -(Real.sqrt 3 * lowMu length radius mode.val.2)
  else -(lowMu length radius mode.val.2 ^ 2 + 3 * radius⁻¹ ^ 2) /
    (lowBalanceConstant length gamma * lowMu length radius mode.val.2)

theorem lowReferenceUpper_conjugation (length gamma radius : ℝ) (mode : LowAnnularMode) :
    lowReferenceUpper length radius mode = -(lowAmplitude length gamma mode * lowMu length radius mode.val.2) * lowCircularB mode := by
  by_cases center : |mode.val.1| = 1
  · rw [lowReferenceUpper, if_pos center, lowAmplitude, if_pos center, lowCircularB_center mode center]
    have root : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have rootPositive : 0 < Real.sqrt 3 := by positivity
    field_simp
    rw [root]
    ring
  · rw [lowReferenceUpper, if_neg center, lowCircularB_exceptional mode center, mul_zero]

theorem lowReferenceLower_conjugation (length gamma radius : ℝ) (mode : LowAnnularMode) (positive : 0 < radius) :
    lowReferenceLower length gamma radius mode =
      -(lowCircularPotential length radius mode) / (lowAmplitude length gamma mode * lowMu length radius mode.val.2) := by
  by_cases center : |mode.val.1| = 1
  · rw [lowReferenceLower, if_pos center, lowAmplitude, if_pos center, lowCircularPotential_center length radius mode center]
    have muPositive := lowMu_pos length radius mode.val.2 positive
    have rootPositive : 0 < Real.sqrt 3 := by positivity
    field_simp
  · rw [lowReferenceLower, if_neg center, lowAmplitude, if_neg center,
      lowCircularPotential_exceptional length radius mode center]

/-- Reference matrix after the actual exp(Phi)diag(a_m mu,1) conjugation.
The same matrix is used for both signs and every axial cell. -/
def lowReferenceMatrix (parameters : PhaseParameters) (length radius : ℝ) (mode : LowAnnularMode) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  ![![lowMuLogSlope length radius mode.val.2 - 2 / radius + annularPhaseSlope parameters mode.val.2 radius,
      lowReferenceUpper length radius mode],
    ![lowReferenceLower length parameters.gamma radius mode,
      1 / radius + annularPhaseSlope parameters mode.val.2 radius] ]

/-- Literal physical circular rows for (xi,x), before conjugation. -/
def lowCircularMatrix (length radius : ℝ) (mode : LowAnnularMode) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![-2 / radius, -lowCircularB mode], ![-lowCircularPotential length radius mode, 1 / radius] ]

def lowConjugatingEntry (length gamma radius : ℝ) (mode : LowAnnularMode) (entry : Fin 2) : ℝ :=
  if entry = 0 then lowAmplitude length gamma mode * lowMu length radius mode.val.2 else 1

theorem lowConjugatingEntry_pos (length gamma radius : ℝ) (mode : LowAnnularMode)
    (positive : 0 < radius) (entry : Fin 2) : 0 < lowConjugatingEntry length gamma radius mode entry := by
  unfold lowConjugatingEntry
  split_ifs
  · exact mul_pos (lowAmplitude_pos _ _ _) (lowMu_pos _ _ _ positive)
  · exact zero_lt_one

/-- Every entry, including the radial derivative of the balancing multiplier,
is the exact product-rule conjugation of the original physical circular rows. -/
theorem lowReferenceMatrix_conjugation (parameters : PhaseParameters) (length radius : ℝ)
    (mode : LowAnnularMode) (positive : 0 < radius) (row column : Fin 2) :
    lowReferenceMatrix parameters length radius mode row column =
      lowConjugatingEntry length parameters.gamma radius mode row * lowCircularMatrix length radius mode row column /
        lowConjugatingEntry length parameters.gamma radius mode column +
      (if row = column then annularPhaseSlope parameters mode.val.2 radius else 0) +
      (if row = 0 ∧ column = 0 then lowMuLogSlope length radius mode.val.2 else 0) := by
  fin_cases row <;> fin_cases column
  · change lowMuLogSlope length radius mode.val.2 - 2 / radius + annularPhaseSlope parameters mode.val.2 radius =
      (lowAmplitude length parameters.gamma mode * lowMu length radius mode.val.2) * (-2 / radius) /
        (lowAmplitude length parameters.gamma mode * lowMu length radius mode.val.2) +
      annularPhaseSlope parameters mode.val.2 radius + lowMuLogSlope length radius mode.val.2
    rw [mul_div_cancel_left₀ _ (mul_ne_zero (lowAmplitude_pos _ _ _).ne' (lowMu_pos _ _ _ positive).ne')]
    ring
  · change lowReferenceUpper length radius mode =
      (lowAmplitude length parameters.gamma mode * lowMu length radius mode.val.2) * (-lowCircularB mode) / 1 + 0 + 0
    rw [lowReferenceUpper_conjugation length parameters.gamma radius mode]
    ring
  · change lowReferenceLower length parameters.gamma radius mode =
      1 * (-lowCircularPotential length radius mode) /
        (lowAmplitude length parameters.gamma mode * lowMu length radius mode.val.2) + 0 + 0
    simpa only [one_mul, add_zero] using lowReferenceLower_conjugation length parameters.gamma radius mode positive
  · change 1 / radius + annularPhaseSlope parameters mode.val.2 radius =
      1 * (1 / radius) / 1 + annularPhaseSlope parameters mode.val.2 radius + 0
    ring

end Grad.AnnularLowReference
