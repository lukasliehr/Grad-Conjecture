import GC14FamilyAssembly

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open Set
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Envelope

theorem phaseOutsideClosedDerivative_shifted {dimension order newOrder : ℕ}
    (parameters : PhaseParameters) (field : ClosedJet dimension) (cell : ℤ)
    (word : CartesianWord order) (newWord : CartesianWord newOrder) :
    phaseOutsideClosedDerivative parameters cell (shiftedClosedJet field word) newOrder newWord =
      phaseOutsideClosedDerivative parameters cell field (newOrder + order) (Fin.append newWord word) := by
  apply ContinuousMap.ext
  intro point
  change cartesianWeight parameters cell point.val •
      closedDerivative (shiftedClosedJet field word) newOrder newWord point = _
  rw [shiftedClosedJet_closedDerivative]
  rfl

def shiftedStateFamily {dimension inputDimension outputDimension order : ℕ}
    (parameters : PhaseParameters) (ell : ℝ)
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : ACore parameters dimension) (word : CartesianWord order) (cellOrder : ℕ)
    (cell : ℤ) : SmoothOperatorJet inputDimension outputDimension :=
  scaledOriginalJet ell (((Complex.I * (cell : ℂ)) ^ cellOrder) • mapping)
    (shiftedClosedJet (field.1 cell) word)

theorem shiftedStateFamily_weightedDerivative_bound
    {dimension inputDimension outputDimension grade order : ℕ} {L ell : ℝ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : ACore parameters dimension) (word : CartesianWord order) (cellOrder : ℕ)
    (cell : ℤ) (index : DerivativeIndex grade) :
    ‖weightedSmoothDerivative L parameters.sigma0 parameters.gamma ell grade cell
        (shiftedStateFamily parameters ell mapping field word cellOrder cell) index‖ ≤
      ‖mapping‖ * (cellFrequency cell ^ (grade - derivativeOrder index + cellOrder) *
        ‖phaseOutsideClosedDerivative parameters cell (field.1 cell)
          (derivativeOrder index + order) (Fin.append (derivativeWord index) word)‖) := by
  have first := scaledOriginalJet_weightedDerivative_bound parameters admissible
    (((Complex.I * (cell : ℂ)) ^ cellOrder) • mapping) (shiftedClosedJet (field.1 cell) word) cell index
  rw [phaseOutsideClosedDerivative_shifted] at first
  refine first.trans ((mul_le_mul_of_nonneg_right
    (ContinuousLinearMap.opNorm_smul_le ((Complex.I * (cell : ℂ)) ^ cellOrder) mapping)
    (mul_nonneg (pow_nonneg (cellFrequency_pos cell).le _) (norm_nonneg _))).trans ?_)
  rw [norm_pow, norm_mul, Complex.norm_I, one_mul]
  have cellNorm : ‖(cell : ℂ)‖ ≤ cellFrequency cell := by
    simpa only [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs] using
      cell_abs_le_frequency cell
  calc
    _ ≤ (cellFrequency cell ^ cellOrder * ‖mapping‖) *
        (cellFrequency cell ^ (grade - derivativeOrder index) *
          ‖phaseOutsideClosedDerivative parameters cell (field.1 cell)
            (derivativeOrder index + order) (Fin.append (derivativeWord index) word)‖) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg (cell : ℂ)) cellNorm cellOrder)
          (norm_nonneg mapping))
        (mul_nonneg (pow_nonneg (cellFrequency_pos cell).le _) (norm_nonneg _))
    _ = _ := by rw [pow_add]; ring

theorem shiftedStateFamily_summable
    {dimension inputDimension outputDimension grade order : ℕ} {L ell : ℝ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : ACore parameters dimension) (word : CartesianWord order) (cellOrder : ℕ) :
    familySummable L parameters.sigma0 parameters.gamma ell grade
      (shiftedStateFamily parameters ell mapping field word cellOrder) := by
  intro index
  exact Summable.of_nonneg_of_le
    (fun cell => norm_nonneg (weightedSmoothDerivative L parameters.sigma0 parameters.gamma ell grade cell
      (shiftedStateFamily parameters ell mapping field word cellOrder cell) index))
    (fun cell => shiftedStateFamily_weightedDerivative_bound parameters admissible mapping field word
      cellOrder cell index)
    ((phaseOutsideClosedDerivative_frequency_summable parameters field
      (Fin.append (derivativeWord index) word) (grade - derivativeOrder index + cellOrder)).mul_left ‖mapping‖)

def shiftedStateCoefficient {dimension inputDimension outputDimension order : ℕ}
    (parameters : PhaseParameters) (L ell : ℝ) (grade : ℕ)
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : ACore parameters dimension) (word : CartesianWord order) (cellOrder : ℕ) :
    Coefficient L parameters.sigma0 parameters.gamma ell grade inputDimension outputDimension :=
  familyCoefficient L parameters.sigma0 parameters.gamma ell grade
    (shiftedStateFamily parameters ell mapping field word cellOrder)

def shiftedStateConstant (parameters : PhaseParameters) (grade order : ℕ) : ℝ :=
  ∑ index : DerivativeIndex grade,
    originalDerivativeSumConstant parameters (derivativeOrder index + order)

theorem shiftedStateConstant_nonnegative (parameters : PhaseParameters) (grade order : ℕ) :
    0 ≤ shiftedStateConstant parameters grade order :=
  Finset.sum_nonneg fun _ _ => originalDerivativeSumConstant_nonnegative parameters _

theorem shiftedStateCoefficient_norm_bound
    {dimension inputDimension outputDimension grade order j : ℕ} {L ell : ℝ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : GradeCore parameters dimension (j + 3)) (word : CartesianWord order) (cellOrder : ℕ)
    (gradeLe : grade + order + cellOrder ≤ j) :
    ‖shiftedStateCoefficient parameters L ell grade mapping field.toCore word cellOrder‖ ≤
      shiftedStateConstant parameters grade order * ‖mapping‖ * ‖field‖ := by
  change ‖familyCoefficient L parameters.sigma0 parameters.gamma ell grade
    (shiftedStateFamily parameters ell mapping field.toCore word cellOrder)‖ ≤ _
  rw [familyCoefficient_norm_formula _
    (shiftedStateFamily_summable parameters admissible mapping field.toCore word cellOrder)]
  calc
    _ ≤ ∑ index : DerivativeIndex grade,
        ‖mapping‖ * (originalDerivativeSumConstant parameters (derivativeOrder index + order) * ‖field‖) := by
      apply Finset.sum_le_sum
      intro index _membership
      have bound := (shiftedStateFamily_summable parameters admissible mapping
        field.toCore word cellOrder index).tsum_le_tsum
        (fun cell => shiftedStateFamily_weightedDerivative_bound parameters admissible mapping field.toCore word
          cellOrder cell index)
        ((phaseOutsideClosedDerivative_frequency_summable parameters field.toCore
          (Fin.append (derivativeWord index) word) (grade - derivativeOrder index + cellOrder)).mul_left ‖mapping‖)
      rw [tsum_mul_left] at bound
      refine bound.trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg mapping))
      apply phaseOutsideClosedDerivative_frequency_tsum_bound parameters field
      have indexLe : derivativeOrder index ≤ grade := index.2
      omega
    _ = _ := by
      unfold shiftedStateConstant
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro index _membership
      ring

theorem shiftedStateCoefficient_derivative
    {dimension inputDimension outputDimension grade order : ℕ} {L ell : ℝ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (mapping : ComplexEuclidean dimension →L[ℂ] OperatorValue inputDimension outputDimension)
    (field : ACore parameters dimension) (word : CartesianWord order) (cellOrder : ℕ)
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative (shiftedStateCoefficient parameters L ell grade mapping field word cellOrder)
        cell index point =
      (ell ^ derivativeOrder index : ℂ) • ((Complex.I * (cell : ℂ)) ^ cellOrder) •
        mapping (closedMultiDerivative (shiftedClosedJet (field.1 cell) word) (derivativeMultiIndex index)
          (physicalScaledPoint ell admissible.2.2.2.1.le
            (admissible.2.2.2.2.trans (min_le_left _ _)) point)) := by
  change coefficientDerivative (familyCoefficient L parameters.sigma0 parameters.gamma ell grade
    (shiftedStateFamily parameters ell mapping field word cellOrder)) cell index point = _
  rw [familyCoefficient_derivative _
    (shiftedStateFamily_summable parameters admissible mapping field word cellOrder)]
  change smoothOperatorDerivative (scaledOriginalJet ell (((Complex.I * (cell : ℂ)) ^ cellOrder) • mapping)
    (shiftedClosedJet (field.1 cell) word)) (derivativeMultiIndex index) point = _
  rw [scaledOriginalJet_derivative admissible.2.2.2.1.le
      (admissible.2.2.2.2.trans (min_le_left _ _)),
    radialPoint_eq_physicalScaledPoint]
  rfl

end Grad.GaugeCoefficients.Physical.Frame
