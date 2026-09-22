import BL22CartesianEnergy

noncomputable section

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints

theorem spatialBasis_norm (coordinate : Fin 2) : ‖spatialBasis coordinate‖ = 1 := by
  simp [spatialBasis, PiLp.norm_single]

theorem globalClosedDerivative_norm_bound {dimension : ℕ} (field : SpatialPlane → ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ field) (index : CartesianMultiIndex) (point : ClosedDisk) :
    ‖closedMultiDerivative (globalClosedJet field smooth) index point‖ ≤
      ‖iteratedFDeriv ℝ (cartesianOrder index) field point.val‖ := by
  rw [closedMultiDerivative, globalClosedJet_derivative, cartesianDerivative]
  simpa only [spatialBasis_norm, Finset.prod_const_one, mul_one] using
    (iteratedFDeriv ℝ (cartesianOrder index) field point.val).le_opNorm
      (fun position => spatialBasis (cartesianMultiIndexWord index position))

theorem globalClosedDerivative_energy_bound {dimension : ℕ} (field : SpatialPlane → ComplexEuclidean dimension)
    (smooth : ContDiff ℝ ∞ field) (index : CartesianMultiIndex) :
    ‖closedDerivativeL2 index (globalClosedJet field smooth)‖ ^ 2 ≤
      ∫ point in closedUnitDisk, ‖iteratedFDeriv ℝ (cartesianOrder index) field point‖ ^ 2 := by
  rw [← closedDerivative_density_integral]
  have compactDisk : IsCompact closedUnitDisk := by
    rw [closedUnitDisk_eq_closedBall]
    exact isCompact_closedBall _ _
  have sourceContinuous : Continuous (fun point =>
      ‖closedMultiDerivative (globalClosedJet field smooth) index (ambientClosedDisk point)‖ ^ 2) :=
    (((closedMultiDerivative (globalClosedJet field smooth) index).continuous.comp
      continuous_ambientClosedDisk).norm).pow 2
  have targetContinuous : Continuous (fun point => ‖iteratedFDeriv ℝ (cartesianOrder index) field point‖ ^ 2) :=
    ((smooth.continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (cartesianOrder index : ℕ∞) ≤ ⊤))).norm).pow 2
  apply integral_mono_ae (sourceContinuous.continuousOn.integrableOn_compact compactDisk)
    (targetContinuous.continuousOn.integrableOn_compact compactDisk)
  filter_upwards [ae_restrict_mem compactDisk.measurableSet] with point inside
  have pointEquality : ambientClosedDisk point = (⟨point, inside⟩ : ClosedDisk) := by
    apply Subtype.ext
    exact ambientClosedDisk_val_of_mem inside
  rw [pointEquality]
  exact pow_le_pow_left₀ (norm_nonneg _) (globalClosedDerivative_norm_bound field smooth index ⟨point, inside⟩) 2

def originalLiftCellConstant (parameters : PhaseParameters) (grade : ℕ) : ℝ :=
  ∑ index : GradeMultiIndex grade, cartesianLiftDerivativeConstant parameters (cartesianOrder index.toCartesian)

theorem originalLiftCellConstant_nonnegative (parameters : PhaseParameters) (grade : ℕ) :
    0 ≤ originalLiftCellConstant parameters grade :=
  Finset.sum_nonneg (fun index _ => cartesianLiftDerivativeConstant_nonnegative parameters (cartesianOrder index.toCartesian))

theorem finiteBoundaryJet_original_bound {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (modes : Finset ℤ) (values : ℤ → ComplexEuclidean dimension) (grade : ℕ) (gradePositive : 1 ≤ grade) :
    ‖cellGradeRowLinear (grade := grade) parameters cell (finiteBoundaryJet cell modes values)‖ ^ 2 ≤
      originalLiftCellConstant parameters grade * ∑ mode ∈ modes,
        Real.exp (2 * boundaryPhase parameters cell) * boundaryFrequency (mode, cell) ^ (2 * grade - 1) *
          ‖values mode‖ ^ 2 := by
  rw [cellGradeRow_norm_sq, originalLiftCellConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index _
  rw [finiteBoundaryJet_weighted]
  change cellFrequency cell ^ (2 * (grade - cartesianOrder index.toCartesian)) *
    ‖closedDerivativeL2 index.toCartesian (globalClosedJet
      (weightedFiniteKernelField parameters cell modes values)
      (weightedFiniteKernelField_smooth parameters cell modes values))‖ ^ 2 ≤ _
  have comparison := mul_le_mul_of_nonneg_left
    (globalClosedDerivative_energy_bound (weightedFiniteKernelField parameters cell modes values)
      (weightedFiniteKernelField_smooth parameters cell modes values) index.toCartesian)
    (pow_nonneg (cellFrequency_pos cell).le (2 * (grade - cartesianOrder index.toCartesian)))
  exact comparison.trans (weightedFiniteKernel_cartesian_energy parameters cell modes values grade
    (cartesianOrder index.toCartesian) gradePositive index.property)

end Grad.BoundaryLift
