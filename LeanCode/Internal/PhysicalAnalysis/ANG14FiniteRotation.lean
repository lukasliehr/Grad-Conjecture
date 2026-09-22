import ANG13RotationSpectrum

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
namespace Grad.CircularHighWeak
open Grad.CartesianState

def highFiniteRotation (modes : Finset ℤ) : highDiskGrade →L[ℂ] highDiskGrade :=
  ∑ mode ∈ modes, (Complex.I * (mode : ℂ)) • highDiskMode mode

theorem highFiniteRotation_apply (modes : Finset ℤ) (field : highDiskGrade) :
    highFiniteRotation modes field = ∑ mode ∈ modes, (Complex.I * (mode : ℂ)) • highDiskMode mode field := by
  simp only [highFiniteRotation, sum_apply, smul_apply]

theorem highFiniteRotation_bulk (modes : Finset ℤ) (field : highDiskGrade) :
    highDiskBulk (highFiniteRotation modes field) = diskSelectedModes modes (highRotation field) := by
  have expanded := congrArg highDiskBulk (highFiniteRotation_apply modes field)
  refine expanded.trans ((map_sum highDiskBulk _ modes).trans
    (Eq.trans ?_ (diskSelectedModes_apply modes (highRotation field)).symm))
  apply Finset.sum_congr rfl
  intro mode _
  exact ((highDiskBulk.map_smul (Complex.I * (mode : ℂ)) (highDiskMode mode field)).trans
    (congrArg (fun value : DiskL2 1 => (Complex.I * (mode : ℂ)) • value) (highDiskMode_bulk mode field))).trans
      (highRotation_coefficient mode field).symm

theorem highFiniteRotation_bulk_bound (modes : Finset ℤ) (field : highDiskGrade) :
    ‖highDiskBulk (highFiniteRotation modes field)‖ ≤ ‖field‖ :=
  (congrArg norm (highFiniteRotation_bulk modes field)).le.trans
    ((diskSelectedModes_contract modes (highRotation field)).trans (highRotation_contract field))

private def robinFieldLinear (parameter : ℝ) (test : highDiskGrade) : highDiskGrade →ₗ[ℂ] ℂ where
  toFun field := robinValue parameter field test
  map_add' first second := by
    simp only [robinValue, map_add, inner_add_right]
    ring
  map_smul' scalar field := by
    simp only [robinValue, map_smul, inner_smul_right, RingHom.id_apply]
    change _ = scalar * robinValue parameter field test
    simp only [robinValue]
    ring

private def robinTestSemilinear (parameter : ℝ) (field : highDiskGrade) : highDiskGrade →ₗ⋆[ℂ] ℂ where
  toFun test := robinValue parameter field test
  map_add' first second := by
    simp only [robinValue, map_add, inner_add_left]
    ring
  map_smul' scalar test := by
    simp only [robinValue, map_smul, inner_smul_left]
    ring

theorem robinValue_sum_field {ι : Type*} (parameter : ℝ) (test : highDiskGrade) (terms : ι → highDiskGrade) (indices : Finset ι) :
    robinValue parameter (∑ index ∈ indices, terms index) test = ∑ index ∈ indices, robinValue parameter (terms index) test :=
  map_sum (robinFieldLinear parameter test) terms indices

theorem robinValue_sum_test {ι : Type*} (parameter : ℝ) (field : highDiskGrade) (terms : ι → highDiskGrade) (indices : Finset ι) :
    robinValue parameter field (∑ index ∈ indices, terms index) = ∑ index ∈ indices, robinValue parameter field (terms index) :=
  map_sum (robinTestSemilinear parameter field) terms indices

theorem robinValue_field_smul (parameter : ℝ) (scalar : ℂ) (field test : highDiskGrade) :
    robinValue parameter (scalar • field) test = scalar * robinValue parameter field test :=
  (robinFieldLinear parameter test).map_smul scalar field

theorem robinValue_test_scalar (parameter : ℝ) (scalar : ℂ) (field test : highDiskGrade) :
    robinValue parameter field (scalar • test) = starRingEnd ℂ scalar * robinValue parameter field test :=
  (robinTestSemilinear parameter field).map_smulₛₗ scalar test

theorem robinValue_finiteRotation (parameter : ℝ) (modes : Finset ℤ) (field test : highDiskGrade) :
    robinValue parameter (highFiniteRotation modes field) test =
      -robinValue parameter field (highFiniteRotation modes test) := by
  have left := (congrArg (fun value : highDiskGrade => robinValue parameter value test) (highFiniteRotation_apply modes field)).trans
    (robinValue_sum_field parameter test _ modes)
  have right := (congrArg (robinValue parameter field) (highFiniteRotation_apply modes test)).trans
    (robinValue_sum_test parameter field _ modes)
  refine left.trans (Eq.trans ?_ (congrArg Neg.neg right).symm)
  have negativeSum : (∑ mode ∈ modes, -robinValue parameter field ((Complex.I * (mode : ℂ)) • highDiskMode mode test)) =
      -(∑ mode ∈ modes, robinValue parameter field ((Complex.I * (mode : ℂ)) • highDiskMode mode test)) :=
    Finset.sum_neg_distrib _
  refine (Eq.trans ?_ negativeSum)
  apply Finset.sum_congr rfl
  intro mode _
  have first := (robinValue_field_smul parameter (Complex.I * (mode : ℂ)) (highDiskMode mode field) test).trans
    (congrArg (fun value : ℂ => (Complex.I * (mode : ℂ)) * value) (robinValue_angular parameter mode field test))
  have second := robinValue_test_scalar parameter (Complex.I * (mode : ℂ)) field (highDiskMode mode test)
  refine first.trans (Eq.trans ?_ (congrArg Neg.neg second).symm)
  simp

end Grad.CircularHighWeak
