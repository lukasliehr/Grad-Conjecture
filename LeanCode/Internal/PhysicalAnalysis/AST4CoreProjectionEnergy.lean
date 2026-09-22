import AST3OrdinaryOrbitRows

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace Grad.AngularSobolevTruncation
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.PhysicalFamily
local instance energyPeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

theorem coreAngular_square_sum (grade : ℕ) (modes : Finset ℤ) (field : ClosedJet 1) :
    (∑ mode ∈ modes, ‖apRowLinear (grade := grade) 1 0 0 1 0 (angularClosedJet mode field)‖ ^ 2) ≤
      orthogonalGradeConstant grade ^ 2 * ‖apRowLinear (grade := grade) 1 0 0 1 0 field‖ ^ 2 := by
  have bessel := hilbertFourier_bessel modes (gradeOrbitCircle grade field)
    (gradeOrbitCircle_continuous grade field)
  simp_rw [gradeOrbitCircle_coefficient] at bessel
  apply bessel.trans
  have bounded (angle : CellCircle) : ‖gradeOrbitCircle grade field angle‖ ^ 2 ≤
      orthogonalGradeConstant grade ^ 2 * ‖apRowLinear (grade := grade) 1 0 0 1 0 field‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (gradeOrbitCircle_bound grade field angle) 2
  have integralBound := integral_mono
    (circleContinuous_integrable ((gradeOrbitCircle_continuous grade field).norm.pow 2))
    (integrable_const (orthogonalGradeConstant grade ^ 2 * ‖apRowLinear (grade := grade) 1 0 0 1 0 field‖ ^ 2)) bounded
  simpa using integralBound

theorem angularClosedJet_rotation (mode : ℤ) (field : ClosedJet 1) (angle : ℝ) :
    orthogonalJet (planeRotationEquiv angle) (angularClosedJet mode field) =
      angularCharacter mode (-angle) • angularClosedJet mode field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  exact angularClosedJet_rotation_value mode field angle point

theorem selectedOrbitRow (grade : ℕ) (modes : Finset ℤ) (field : ClosedJet 1) (angle : ℝ) :
    gradeOrbitRow grade (selectedAngularJet modes field) angle =
      hilbertFourierSum modes (fun mode => apRowLinear (grade := grade) 1 0 0 1 0
        (angularClosedJet mode field)) (angle : CellCircle) := by
  unfold gradeOrbitRow hilbertFourierSum
  rw [selectedAngularJet_eq]
  change apRowLinear (grade := grade) 1 0 0 1 0
    (orthogonalJetLinear 1 (planeRotationEquiv angle) (∑ mode ∈ modes, angularClosedJet mode field)) = _
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro mode _
  change apRowLinear (grade := grade) 1 0 0 1 0
    (orthogonalJet (planeRotationEquiv angle) (angularClosedJet mode field)) = _
  rw [angularClosedJet_rotation, map_smul, angularCharacter_neg_angle, angularCharacter_fourier, neg_neg]

theorem selectedOrbitCircle (grade : ℕ) (modes : Finset ℤ) (field : ClosedJet 1) (angle : CellCircle) :
    gradeOrbitCircle grade (selectedAngularJet modes field) angle =
      hilbertFourierSum modes (fun mode => apRowLinear (grade := grade) 1 0 0 1 0
        (angularClosedJet mode field)) angle := by
  unfold gradeOrbitCircle AddCircle.liftIco
  change gradeOrbitRow grade (selectedAngularJet modes field) (AddCircle.equivIco (2 * Real.pi) 0 angle).val = _
  rw [selectedOrbitRow, AddCircle.coe_equivIco]

theorem gradeOrbitRow_inverse_bound (grade : ℕ) (field : ClosedJet 1) (angle : ℝ) :
    ‖apRowLinear (grade := grade) 1 0 0 1 0 field‖ ≤
      orthogonalGradeConstant grade * ‖gradeOrbitRow grade field angle‖ := by
  have bound := apOrthogonal_row_bound (grade := grade) 1 0 0 1 0
    (planeRotationEquiv angle).symm (orthogonalJet (planeRotationEquiv angle) field)
  rw [orthogonalJet_trans, LinearIsometryEquiv.symm_trans_self, orthogonalJet_refl] at bound
  exact bound

theorem coreSelected_square_bound (grade : ℕ) (modes : Finset ℤ) (field : ClosedJet 1) :
    ‖apRowLinear (grade := grade) 1 0 0 1 0 (selectedAngularJet modes field)‖ ^ 2 ≤
      orthogonalGradeConstant grade ^ 2 *
        ∑ mode ∈ modes, ‖apRowLinear (grade := grade) 1 0 0 1 0 (angularClosedJet mode field)‖ ^ 2 := by
  have pointwise (angle : CellCircle) :
      ‖apRowLinear (grade := grade) 1 0 0 1 0 (selectedAngularJet modes field)‖ ^ 2 ≤
        orthogonalGradeConstant grade ^ 2 *
          ‖gradeOrbitCircle grade (selectedAngularJet modes field) angle‖ ^ 2 := by
    have bound := gradeOrbitRow_inverse_bound grade (selectedAngularJet modes field)
      (AddCircle.equivIco (2 * Real.pi) 0 angle).val
    exact (pow_le_pow_left₀ (norm_nonneg _) bound 2).trans_eq (mul_pow _ _ 2)
  have integralBound := integral_mono
    (integrable_const (‖apRowLinear (grade := grade) 1 0 0 1 0 (selectedAngularJet modes field)‖ ^ 2))
    ((circleContinuous_integrable ((gradeOrbitCircle_continuous grade (selectedAngularJet modes field)).norm.pow 2)).const_mul
      (orthogonalGradeConstant grade ^ 2)) pointwise
  simp_rw [selectedOrbitCircle] at integralBound
  simpa [Pi.pow_apply, integral_const_mul, hilbertFourierSum_energy] using integralBound

theorem coreSelected_uniform_bound (grade : ℕ) (modes : Finset ℤ) (field : ClosedJet 1) :
    ‖apRowLinear (grade := grade) 1 0 0 1 0 (selectedAngularJet modes field)‖ ≤
      orthogonalGradeConstant grade ^ 2 * ‖apRowLinear (grade := grade) 1 0 0 1 0 field‖ := by
  have bound := (coreSelected_square_bound grade modes field).trans
    (mul_le_mul_of_nonneg_left (coreAngular_square_sum grade modes field) (sq_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (sq_nonneg _) (norm_nonneg _))).mp
  convert bound using 1
  ring

end Grad.AngularSobolevTruncation
