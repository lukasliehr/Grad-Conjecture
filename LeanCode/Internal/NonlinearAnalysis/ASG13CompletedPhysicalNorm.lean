import ASG12FaithfulFourierBulk

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryKernelAction Grad.PhaseAlgebra

/-- The genuine conjugated radial graph after undoing only the polynomial
Fourier normalization. Its value represents exp(Phi) times the physical mode. -/
def annularConjugatedMode (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ)
    (field : AnnularSourceH1 parameters dimension lower angular cell) (mode : ℤ × ℤ) :
    CollarH1 (ComplexEuclidean dimension) lower :=
  (splitTangentialWeight angular cell mode)⁻¹ •
    weightedToOrdinary dimension lower positive bounded (field mode)

def annularConjugatedCoordinate (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ)
    (field : AnnularSourceH1 parameters dimension lower angular cell) (mode : ℤ × ℤ)
    (coordinate : Fin 2) : CollarL2 (ComplexEuclidean dimension) lower :=
  collarH1Coordinate (ComplexEuclidean dimension) lower coordinate
    (annularConjugatedMode parameters dimension lower positive bounded angular cell field mode)

theorem annularConjugatedCoordinate_weak (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ)
    (field : AnnularSourceH1 parameters dimension lower angular cell) (mode : ℤ × ℤ) :
    CollarWeakDerivative lower
      (annularConjugatedCoordinate parameters dimension lower positive bounded angular cell field mode 0)
      (annularConjugatedCoordinate parameters dimension lower positive bounded angular cell field mode 1) :=
  collarH1_weak lower bounded _

theorem annularConjugatedCoordinate_storage (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ)
    (field : AnnularSourceH1 parameters dimension lower angular cell) (mode : ℤ × ℤ) (coordinate : Fin 2) :
    weightedRadialCoordinate dimension lower coordinate (field mode) =
      splitTangentialWeight angular cell mode • radialSqrtMap dimension lower
        (annularConjugatedCoordinate parameters dimension lower positive bounded angular cell field mode coordinate) := by
  rw [weightedRadialCoordinate_eq_sqrt dimension lower positive bounded]
  unfold annularConjugatedCoordinate annularConjugatedMode
  rw [map_smul, (radialSqrtMap dimension lower).map_smul_of_tower, smul_smul,
    mul_inv_cancel₀ (splitTangentialWeight_pos angular cell mode).ne', one_smul]

theorem radialSqrtMap_norm_sq (dimension : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : CollarL2 (ComplexEuclidean dimension) lower) :
    ‖radialSqrtMap dimension lower field‖ ^ 2 =
      ∫ radius in lower..1, radius * ‖field radius‖ ^ 2 := by
  rw [radialLp_norm_sq, intervalIntegral.integral_of_le bounded, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [radialSqrtMap_ae dimension lower field, ae_restrict_mem measurableSet_Icc]
    with radius stored inside
  rw [stored, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    mul_pow, Real.sq_sqrt (positive.le.trans inside.1)]

/-- Literal AH10 norm on the completed graph. Both integrals use r dr;
coordinate one is the weak derivative of the phase-conjugated coordinate zero. -/
theorem annularSource_completed_norm_sq (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ)
    (field : AnnularSourceH1 parameters dimension lower angular cell) :
    ‖field‖ ^ 2 = ∑' mode : ℤ × ℤ, splitTangentialWeight angular cell mode ^ 2 *
      ((∫ radius in lower..1, radius *
        ‖annularConjugatedCoordinate parameters dimension lower positive bounded angular cell field mode 0 radius‖ ^ 2) +
       (∫ radius in lower..1, radius *
        ‖annularConjugatedCoordinate parameters dimension lower positive bounded angular cell field mode 1 radius‖ ^ 2)) := by
  rw [annularSource_norm_sq]
  apply tsum_congr
  intro mode
  rw [annularConjugatedCoordinate_storage parameters dimension lower positive bounded angular cell field mode 0,
    annularConjugatedCoordinate_storage parameters dimension lower positive bounded angular cell field mode 1]
  simp only [norm_smul, Real.norm_of_nonneg (splitTangentialWeight_pos angular cell mode).le, mul_pow]
  rw [radialSqrtMap_norm_sq dimension lower positive bounded, radialSqrtMap_norm_sq dimension lower positive bounded]
  ring

/-- The completed physical Fourier value uses the original curved phase. -/
def annularSourceCoefficient (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ)
    (field : AnnularSourceH1 parameters dimension lower angular cell) (mode : ℤ × ℤ)
    (radius : ℝ) : ComplexEuclidean dimension :=
  (Real.exp (radialPhase parameters radius mode.2))⁻¹ •
    annularConjugatedCoordinate parameters dimension lower positive bounded angular cell field mode 0 radius

theorem annularSourceCoefficient_conjugation (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ)
    (field : AnnularSourceH1 parameters dimension lower angular cell) (mode : ℤ × ℤ) (radius : ℝ) :
    Real.exp (radialPhase parameters radius mode.2) •
      annularSourceCoefficient parameters dimension lower positive bounded angular cell field mode radius =
      annularConjugatedCoordinate parameters dimension lower positive bounded angular cell field mode 0 radius := by
  rw [annularSourceCoefficient, smul_smul, mul_inv_cancel₀ (Real.exp_pos _).ne', one_smul]

end Grad.AnnularSourceGraph
