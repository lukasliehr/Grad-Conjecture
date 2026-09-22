import ANS6ShiftPrimitive

noncomputable section
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualAngularInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.GaugeCoefficients.Radial Grad.PhysicalFamily Grad.FourierGrade Grad.NonlinearRange Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.FlatSourceProjection

theorem scalarJet_angular_ext {first second : ClosedJet 1}
    (same : ∀ mode : ℤ, angularClosedJet mode first = angularClosedJet mode second) : first = second := by
  apply closedL2Core_injective
  apply diskFourierIsometry.injective
  apply lp.ext
  funext mode
  change diskMode mode (closedL2Core first) = diskMode mode (closedL2Core second)
  rw [diskMode_core, diskMode_core, same]

theorem closedJet_angular_ext {dimension : ℕ} {first second : ClosedJet dimension}
    (same : ∀ mode : ℤ, angularClosedJet mode first = angularClosedJet mode second) : first = second := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  have projected : valueMapJet (componentValue dimension coordinate) first =
      valueMapJet (componentValue dimension coordinate) second := by
    apply scalarJet_angular_ext
    intro mode
    rw [angularClosedJet_valueMap, angularClosedJet_valueMap, same mode]
  have value := congrArg (fun jet : ClosedJet 1 => jet.value point 0) projected
  simpa only [valueMapJet_value, componentValue_apply] using value

theorem angular_rotationJet_all {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension) :
    angularClosedJet mode (rotationJet field) = (Complex.I * (mode : ℂ)) • angularClosedJet mode field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have periodic : field.value (rotatedPoint Real.pi point) = field.value (rotatedPoint (-Real.pi) point) := by
    have rotation := diskOrbit_periodic point (-Real.pi)
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at rotation
    exact congrArg field.value rotation
  have coefficient := angularCoefficient_derivative
    (fun angle => field.value (rotatedPoint angle point))
    (fun angle => (rotationJet field).value (rotatedPoint angle point))
    (orbitValue_continuous field point) (orbitValue_continuous (rotationJet field) point)
    (closedOrbit_hasDerivAt field point) periodic mode
  exact (orbitCoefficient_projection (rotationJet field) point mode).symm.trans
    (coefficient.trans (congrArg (fun value : ComplexEuclidean dimension => (Complex.I * (mode : ℂ)) • value)
      (orbitCoefficient_projection field point mode)))

def shiftedRotationJet {dimension : ℕ} (shift : ℤ) (field : ClosedJet dimension) : ClosedJet dimension :=
  rotationJet field + (Complex.I * (shift : ℂ)) • field

theorem shiftedRotationJet_coefficient {dimension : ℕ} (shift mode : ℤ) (field : ClosedJet dimension) :
    angularClosedJet mode (shiftedRotationJet shift field) =
      (Complex.I * ((mode + shift : ℤ) : ℂ)) • angularClosedJet mode field := by
  rw [shiftedRotationJet, angularClosedJet_add, angular_rotationJet_all, angularClosedJet_smul, ← add_smul]
  congr 1
  push_cast
  ring

theorem excluded_single_coefficient {dimension : ℕ} (shift mode : ℤ) (field : ClosedJet dimension) :
    angularClosedJet mode (excludedAngularJet {-shift} field) =
      if mode = -shift then 0 else angularClosedJet mode field := by
  change angularClosedJetLinear dimension mode (field - selectedAngularJet {-shift} field) = _
  rw [map_sub]
  change angularClosedJet mode field - angularClosedJet mode (selectedAngularJet {-shift} field) = _
  rw [angularClosedJet_selected]
  by_cases resonant : mode = -shift <;> simp [resonant]

/-- Both actual Cartesian angular inverse laws hold with the literal resonant
projection, including the axis and the boundary. -/
theorem shiftInverse_right {dimension : ℕ} (shift : ℤ) (field : ClosedJet dimension) :
    shiftedRotationJet shift (shiftInverseJet shift field) = excludedAngularJet {-shift} field := by
  apply closedJet_angular_ext
  intro mode
  rw [shiftedRotationJet_coefficient, shiftInverseJet_coefficient, excluded_single_coefficient]
  by_cases resonant : mode = -shift
  · simp only [if_pos resonant, smul_zero]
  · have frequency : Complex.I * ((mode + shift : ℤ) : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (by exact_mod_cast (show mode + shift ≠ 0 by omega))
    simp only [if_neg resonant, smul_smul, mul_inv_cancel₀ frequency, one_smul]

theorem shiftInverse_left {dimension : ℕ} (shift : ℤ) (field : ClosedJet dimension) :
    shiftInverseJet shift (shiftedRotationJet shift field) = excludedAngularJet {-shift} field := by
  apply closedJet_angular_ext
  intro mode
  rw [shiftInverseJet_coefficient, shiftedRotationJet_coefficient, excluded_single_coefficient]
  by_cases resonant : mode = -shift
  · simp only [if_pos resonant]
  · have frequency : Complex.I * ((mode + shift : ℤ) : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (by exact_mod_cast (show mode + shift ≠ 0 by omega))
    simp only [if_neg resonant, smul_smul, inv_mul_cancel₀ frequency, one_smul]

theorem shiftInverse_nonresonant {dimension : ℕ} (shift : ℤ) (field : ClosedJet dimension) :
    angularClosedJet (-shift) (shiftInverseJet shift field) = 0 := by
  rw [shiftInverseJet_coefficient, if_pos rfl]

theorem excluded_single_eq {dimension : ℕ} (shift : ℤ) (field : ClosedJet dimension) :
    excludedAngularJet {-shift} field = field - angularClosedJet (-shift) field := by
  change field - selectedAngularJet {-shift} field = _
  rw [selectedAngularJet_eq]
  simp

theorem shiftInverse_solves {dimension : ℕ} (shift : ℤ) (field : ClosedJet dimension)
    (nonresonant : angularClosedJet (-shift) field = 0) :
    shiftedRotationJet shift (shiftInverseJet shift field) = field := by
  rw [shiftInverse_right, excluded_single_eq, nonresonant, sub_zero]

theorem shiftInverse_unique {dimension : ℕ} (shift : ℤ) (source candidate : ClosedJet dimension)
    (nonresonant : angularClosedJet (-shift) candidate = 0)
    (equation : shiftedRotationJet shift candidate = source) : candidate = shiftInverseJet shift source := by
  have law := shiftInverse_left shift candidate
  rw [equation, excluded_single_eq, nonresonant, sub_zero] at law
  exact law.symm

end Grad.ActualAngularInverse
