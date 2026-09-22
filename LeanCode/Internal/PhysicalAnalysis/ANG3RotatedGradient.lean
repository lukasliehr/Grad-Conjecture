import ANG2HighDiskModes

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
namespace Grad.CircularHighWeak
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Radial Grad.RepresentedKernel.SpatialProduct
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

/-- The first Cartesian derivative of the literal rotated jet. -/
theorem rotatedJet_first (angle : ℝ) (field : ClosedJet 1) (coordinate : Fin 2) :
    closedDerivative (orthogonalJet (planeRotationEquiv angle) field) 1 (fun _ => coordinate) =
      (planeRotationEquiv angle (Grad.PDEBootstrap.spatialDirection coordinate) 0 : ℂ) •
        (closedDerivative field 1 (fun _ => 0)).comp (orthogonalClosedMap (planeRotationEquiv angle)) +
      (planeRotationEquiv angle (Grad.PDEBootstrap.spatialDirection coordinate) 1 : ℂ) •
        (closedDerivative field 1 (fun _ => 1)).comp (orthogonalClosedMap (planeRotationEquiv angle)) := by
  rw [orthogonalJet_derivative, orthogonalDerivative_eq_sum]
  have words : (Finset.univ : Finset (CartesianWord 1)) = {fun _ => 0, fun _ => 1} := by decide
  rw [words, Finset.sum_pair (by decide : (fun _ : Fin 1 => (0 : Fin 2)) ≠ (fun _ => 1))]
  simp [chainFactor_eq]

/-- Rotation preserves the sum of the two real Hilbert coordinate energies. -/
theorem rotation_pair_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (angle : ℝ) (first second : E) :
    ‖(Real.cos angle : ℂ) • first + (Real.sin angle : ℂ) • second‖ ^ 2 +
      ‖(-Real.sin angle : ℂ) • first + (Real.cos angle : ℂ) • second‖ ^ 2 =
      ‖first‖ ^ 2 + ‖second‖ ^ 2 := by
  simp only [norm_add_sq (𝕜 := ℂ), norm_smul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs, inner_smul_left, inner_smul_right]
  simp only [map_neg, Complex.conj_ofReal, norm_neg, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  change Real.cos angle ^ 2 * ‖first‖ ^ 2 +
      2 * ((Real.sin angle : ℂ) * ((Real.cos angle : ℂ) * inner ℂ first second)).re +
      Real.sin angle ^ 2 * ‖second‖ ^ 2 +
      (Real.sin angle ^ 2 * ‖first‖ ^ 2 +
      2 * ((Real.cos angle : ℂ) * (-(Real.sin angle : ℂ) * inner ℂ first second)).re +
      Real.cos angle ^ 2 * ‖second‖ ^ 2) = _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re,
    Complex.neg_im, zero_mul, sub_zero, neg_zero]
  nlinarith [Real.sin_sq_add_cos_sq angle,
    congrArg (fun scalar : ℝ => scalar * ‖first‖ ^ 2) (Real.sin_sq_add_cos_sq angle),
    congrArg (fun scalar : ℝ => scalar * ‖second‖ ^ 2) (Real.sin_sq_add_cos_sq angle)]

def rotatedCoreDerivative (angle : ℝ) (field : ClosedJet 1) (coordinate : Fin 2) : DiskL2 1 :=
  closedContinuousToDiskL2
    ((closedDerivative field 1 (fun _ => coordinate)).comp (orthogonalClosedMap (planeRotationEquiv angle)))

theorem rotatedCoreDerivative_norm (angle : ℝ) (field : ClosedJet 1) (coordinate : Fin 2) :
    ‖rotatedCoreDerivative angle field coordinate‖ =
      ‖closedContinuousToDiskL2 (closedDerivative field 1 (fun _ => coordinate))‖ :=
  closedValueL2_orthogonal_norm (planeRotationEquiv angle) _

theorem rotatedJet_first_L2 (angle : ℝ) (field : ClosedJet 1) (coordinate : Fin 2) :
    closedContinuousToDiskL2 (closedDerivative (orthogonalJet (planeRotationEquiv angle) field) 1 (fun _ => coordinate)) =
      (planeRotationEquiv angle (Grad.PDEBootstrap.spatialDirection coordinate) 0 : ℂ) • rotatedCoreDerivative angle field 0 +
      (planeRotationEquiv angle (Grad.PDEBootstrap.spatialDirection coordinate) 1 : ℂ) • rotatedCoreDerivative angle field 1 := by
  rw [rotatedJet_first]
  change closedValueL2Linear 1 (_ + _) = _
  rw [map_add, map_smul, map_smul]
  rfl

theorem rotatedJet_gradient_energy (angle : ℝ) (field : ClosedJet 1) :
    ‖closedContinuousToDiskL2 (closedDerivative (orthogonalJet (planeRotationEquiv angle) field) 1 (fun _ => 0))‖ ^ 2 +
      ‖closedContinuousToDiskL2 (closedDerivative (orthogonalJet (planeRotationEquiv angle) field) 1 (fun _ => 1))‖ ^ 2 =
        ‖closedContinuousToDiskL2 (closedDerivative field 1 (fun _ => 0))‖ ^ 2 +
          ‖closedContinuousToDiskL2 (closedDerivative field 1 (fun _ => 1))‖ ^ 2 := by
  have energy := rotation_pair_norm_sq angle
    (rotatedCoreDerivative angle field 0) (rotatedCoreDerivative angle field 1)
  rw [rotatedJet_first_L2, rotatedJet_first_L2]
  convert energy.trans (congrArg₂ (fun first second : ℝ => first ^ 2 + second ^ 2)
    (rotatedCoreDerivative_norm angle field 0) (rotatedCoreDerivative_norm angle field 1)) using 1
  simp [planeRotationEquiv_apply, planeRotation, Grad.PDEBootstrap.spatialDirection]

theorem unitRow_norm_sq (field : ClosedJet 1) :
    ‖apRowLinear (grade := 1) 1 0 0 1 0 field‖ ^ 2 =
      ‖closedContinuousToDiskL2 field.value‖ ^ 2 +
      ‖closedContinuousToDiskL2 (closedDerivative field 1 (fun _ => 0))‖ ^ 2 +
      ‖closedContinuousToDiskL2 (closedDerivative field 1 (fun _ => 1))‖ ^ 2 := by
  have normLaw : ‖apRowLinear (grade := 1) 1 0 0 1 0 field‖ ^ 2 =
      ∑ index : DerivativeIndex 1, ‖closedDerivativeL2 (derivativeMultiIndex index) field‖ ^ 2 := by
    simpa [scaledCellWeight, unweightedJet] using apRowLinear_norm_sq (grade := 1) 1 0 0 1 0 field
  rw [normLaw, diskIndex_sum]
  change ‖closedContinuousToDiskL2 (closedMultiDerivative field (0, 0))‖ ^ 2 +
      ‖closedContinuousToDiskL2 (closedMultiDerivative field (1, 0))‖ ^ 2 +
      ‖closedContinuousToDiskL2 (closedMultiDerivative field (0, 1))‖ ^ 2 = _
  rw [closedMultiDerivative_zero, ← partialJet_zero_value, ← partialJet_one_value]
  rfl

/-- Exact rotational invariance of the actual AP1 Cartesian H1 norm. -/
theorem rotatedJet_unitRow_norm (angle : ℝ) (field : ClosedJet 1) :
    ‖apRowLinear (grade := 1) 1 0 0 1 0 (orthogonalJet (planeRotationEquiv angle) field)‖ =
      ‖apRowLinear (grade := 1) 1 0 0 1 0 field‖ := by
  have bulk : ‖closedContinuousToDiskL2 (orthogonalJet (planeRotationEquiv angle) field).value‖ =
      ‖closedContinuousToDiskL2 field.value‖ := closedValueL2_orthogonal_norm (planeRotationEquiv angle) field.value
  have equality : ‖apRowLinear (grade := 1) 1 0 0 1 0 (orthogonalJet (planeRotationEquiv angle) field)‖ ^ 2 =
      ‖apRowLinear (grade := 1) 1 0 0 1 0 field‖ ^ 2 := by
    rw [unitRow_norm_sq, unitRow_norm_sq, bulk, add_assoc, add_assoc, rotatedJet_gradient_energy]
  nlinarith only [equality, norm_nonneg (apRowLinear (grade := 1) 1 0 0 1 0 (orthogonalJet (planeRotationEquiv angle) field)),
    norm_nonneg (apRowLinear (grade := 1) 1 0 0 1 0 field)]

end Grad.CircularHighWeak
