import AKAQ2FourierFibreCauchySchwarz

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped BigOperators ENNReal
namespace Grad.OriginalFlatAxisDecay
open Grad.FourierGrade Grad.CartesianState Grad.ClosedJets

theorem fullWeight_spatial (mode : SpatialMode) (cell : ℤ) :
    spatialSquare mode ≤ frequencyWeight (fibreMode (cell,mode))^2 := by
  rw [frequencyWeight_sq_expanded]
  simp only [coordinateSquare,frequencyVector_zero,frequencyVector_one,frequencyVector_two,fibreMode,sq_abs]
  unfold spatialSquare
  have scale : 1 ≤ (Real.pi / 2)^2 := by nlinarith [Real.two_le_pi]
  nlinarith [mul_nonneg (sub_nonneg.mpr scale) (add_nonneg (sq_nonneg (mode.1 : ℝ)) (sq_nonneg (mode.2 : ℝ))),sq_nonneg (cell : ℝ)]

theorem fullWeight_cell (mode : SpatialMode) (cell : ℤ) :
    cellFrequency cell ^ 2 ≤ frequencyWeight (fibreMode (cell,mode))^2 := by
  rw [cellFrequency_formula,Real.sq_sqrt (by positivity),frequencyWeight_sq_expanded]
  simp only [coordinateSquare,frequencyVector_zero,frequencyVector_one,frequencyVector_two,fibreMode,sq_abs]
  nlinarith [sq_nonneg ((Real.pi / 2) * (mode.1 : ℝ)),sq_nonneg ((Real.pi / 2) * (mode.2 : ℝ))]

theorem spatialDecay_inverse (mode : SpatialMode) :
    spatialDecay mode = (Real.sqrt (spatialSquare mode)^3)⁻¹ := by
  unfold spatialDecay
  rw [show (-3 / 2 : ℝ) = -(3 / 2) by norm_num,Real.rpow_neg (spatialSquare_positive mode).le]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (spatialSquare_positive mode).le]
  norm_num

theorem spatialHalfCube_square (mode : SpatialMode) :
    (Real.sqrt (spatialSquare mode)^3)^2 = spatialSquare mode ^ 3 := by
  calc
    _ = (Real.sqrt (spatialSquare mode)^2)^3 := by ring
    _ = _ := by rw [Real.sq_sqrt (spatialSquare_positive mode).le]

/-- A4 pays H3 in the lambda-weighted cell Hilbert space. -/
theorem sameGrade_fourier_payment (mode : SpatialMode) (cell : ℤ) :
    cellFrequency cell ^ 2 * Real.sqrt (spatialSquare mode)^3 /
      frequencyWeight (fibreMode (cell,mode))^8 ≤ spatialDecay mode := by
  have combined := mul_le_mul (fullWeight_cell mode cell)
    (pow_le_pow_left₀ (spatialSquare_positive mode).le (fullWeight_spatial mode cell) 3)
    (pow_nonneg (spatialSquare_positive mode).le 3)
    (sq_nonneg (frequencyWeight (fibreMode (cell,mode))))
  have bound : cellFrequency cell^2 * spatialSquare mode^3 ≤ frequencyWeight (fibreMode (cell,mode))^8 := by
    nlinarith only [combined]
  rw [spatialDecay_inverse,← one_div]
  apply (div_le_div_iff₀ (pow_pos (frequencyWeight_pos _) 8)
    (pow_pos (Real.sqrt_pos.mpr (spatialSquare_positive mode)) 3)).mpr
  have square := spatialHalfCube_square mode
  nlinarith only [bound, congrArg (fun value : ℝ => cellFrequency cell^2 * value) square]

def cellFourierFactor (symbol : SpatialMode → ℂ) (mode : SpatialMode) (cell : ℤ) : ℂ :=
  (cellFrequency cell : ℂ) * symbol mode * ((frequencyWeight (fibreMode (cell,mode)) : ℂ)^4)⁻¹

theorem cellFourierFactor_norm_sq (symbol : SpatialMode → ℂ) (mode : SpatialMode) (cell : ℤ) :
    ‖cellFourierFactor symbol mode cell‖^2 =
      cellFrequency cell^2 * ‖symbol mode‖^2 / frequencyWeight (fibreMode (cell,mode))^8 := by
  simp only [cellFourierFactor,norm_mul,norm_inv,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos (cellFrequency_pos cell),abs_of_pos (frequencyWeight_pos _)]
  ring

theorem cellFourierFactor_bound (symbol : SpatialMode → ℂ) (payment : ℝ) (nonnegative : 0 ≤ payment)
    (bound : ∀ mode, ‖symbol mode‖^2 ≤ payment * Real.sqrt (spatialSquare mode)^3)
    (mode : SpatialMode) (cell : ℤ) :
    ‖cellFourierFactor symbol mode cell‖^2 ≤ payment * spatialDecay mode := by
  rw [cellFourierFactor_norm_sq]
  calc
    _ ≤ cellFrequency cell^2 * (payment * Real.sqrt (spatialSquare mode)^3) /
        frequencyWeight (fibreMode (cell,mode))^8 := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (frequencyWeight_pos _).le 8)
      exact mul_le_mul_of_nonneg_left (bound mode) (sq_nonneg _)
    _ = payment * (cellFrequency cell^2 * Real.sqrt (spatialSquare mode)^3 /
        frequencyWeight (fibreMode (cell,mode))^8) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (sameGrade_fourier_payment mode cell) nonnegative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem finiteFibre_symbol_identity (symbol : SpatialMode → ℂ) (field : JGrade E 4)
    (cell : ℤ) (support : Finset SpatialMode) :
    ‖∑ mode ∈ support, cellFourierFactor symbol mode cell • field.val (fibreMode (cell,mode))‖^2 =
      cellFrequency cell^2 * ‖∑ mode ∈ support, symbol mode • coefficient 4 field (fibreMode (cell,mode))‖^2 := by
  have same : (∑ mode ∈ support, cellFourierFactor symbol mode cell • field.val (fibreMode (cell,mode))) =
      (cellFrequency cell : ℂ) • ∑ mode ∈ support, symbol mode • coefficient 4 field (fibreMode (cell,mode)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro mode _
    simp only [cellFourierFactor,coefficient,smul_smul,mul_assoc]
  rw [same,norm_smul,mul_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (cellFrequency_pos cell)]

/-- Exact finite-fibre form of the original A4 Fourier estimate, with all
cell frequencies retained and no analytic-width loss. -/
theorem finiteFourier_symbol_bound (symbol : SpatialMode → ℂ) (payment : ℝ) (nonnegative : 0 ≤ payment)
    (bound : ∀ mode, ‖symbol mode‖^2 ≤ payment * Real.sqrt (spatialSquare mode)^3)
    (field : JGrade E 4) (cells : Finset ℤ) (support : Finset SpatialMode) :
    ∑ cell ∈ cells, cellFrequency cell^2 *
      ‖∑ mode ∈ support, symbol mode • coefficient 4 field (fibreMode (cell,mode))‖^2 ≤
      payment * spatialDecayConstant * ‖field‖^2 := by
  simp_rw [← finiteFibre_symbol_identity]
  exact finiteFibreEnergy_bound (cellFourierFactor symbol) payment nonnegative
    (cellFourierFactor_bound symbol payment nonnegative bound) field cells support

end Grad.OriginalFlatAxisDecay
