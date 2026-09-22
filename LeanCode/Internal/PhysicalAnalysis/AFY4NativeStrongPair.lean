import AFY3WeakMatchingInclusion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryTrace

/-- The AY2 matching space with its prescribed SUM norm. -/
abbrev StrongMatchingPair (L sigma gamma ell : ℝ) (grade : ℕ) :=
  WithLp 1 (StrongMatchingGrade L sigma gamma ell (grade + 1) × StrongMatchingGrade L sigma gamma ell grade)

theorem strongMatchingPair_norm (L sigma gamma ell : ℝ) (grade : ℕ)
    (pair : StrongMatchingPair L sigma gamma ell grade) :
    ‖pair‖ = ‖pair.fst‖ + ‖pair.snd‖ := by
  simpa using WithLp.prod_norm_eq_add (p := 1) (by norm_num) pair

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)

/-- The native, unlowered scalar slot at bulk grade s+2. -/
def completedNativeTheta (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] apGrade L sigma gamma ell 1 (grade + 2) :=
  compensatedClosureEntry admissible grade core 0

theorem completedNativeTheta_core (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : core) :
    completedNativeTheta admissible grade core (compensatedIntoClosure admissible grade core field) =
      apSmoothGrade L sigma gamma ell 1 (grade + 2) field.val.1 := rfl

theorem completedNativeTheta_bound (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    ‖completedNativeTheta admissible grade core field‖ ≤ ‖field‖ :=
  PiLp.norm_apply_le field.val 0

def completedNativeThetaTrace (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] APBoundaryGrade L sigma gamma ell 1 (grade + 2) :=
  (apBoundaryTrace L sigma gamma ell (grade + 2) (by omega)).comp
    (completedNativeTheta admissible grade core)

def completedStrongScalar (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] StrongMatchingGrade L sigma gamma ell (grade + 1) :=
  (highAngularIsometry L sigma gamma ell (grade + 1)).toLinearIsometry.toContinuousLinearMap.comp
    ((highBoundaryProjection L sigma gamma ell (grade + 2)).comp
      (completedNativeThetaTrace admissible grade core))

def completedStrongFlux (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] StrongMatchingGrade L sigma gamma ell grade :=
  (highAngularIsometry L sigma gamma ell grade).toLinearIsometry.toContinuousLinearMap.comp
    ((highBoundaryProjection L sigma gamma ell (grade + 1)).comp
      (completedMatchingP admissible data grade core))

theorem completedStrongScalar_norm (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    ‖completedStrongScalar admissible grade core field‖ =
      ‖apHighProjection L sigma gamma ell (grade + 2) (completedNativeThetaTrace admissible grade core field)‖ :=
  (highAngularIsometry L sigma gamma ell (grade + 1)).norm_map _

theorem completedStrongFlux_norm (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    ‖completedStrongFlux admissible data grade core field‖ =
      ‖apHighProjection L sigma gamma ell (grade + 1) (completedMatchingP admissible data grade core field)‖ :=
  (highAngularIsometry L sigma gamma ell grade).norm_map _

theorem completedStrongScalar_bound (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    ‖completedStrongScalar admissible grade core field‖ ≤ Real.sqrt (traceCellConstant (grade + 2)) * ‖field‖ := by
  rw [completedStrongScalar_norm]
  exact (apHighProjection_bound L sigma gamma ell (grade + 2) _).trans
    ((apBoundaryTrace_bound L sigma gamma ell (grade + 2) (by omega) _).trans
      (mul_le_mul_of_nonneg_left (completedNativeTheta_bound admissible grade core field) (Real.sqrt_nonneg _)))

theorem completedStrongFlux_bound (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (field : compensatedClosure admissible grade core) :
    ‖completedStrongFlux admissible data grade core field‖ ≤ matchingTraceConstant data grade * ‖field‖ := by
  rw [completedStrongFlux_norm]
  exact (apHighProjection_bound L sigma gamma ell (grade + 1) _).trans
    (completedMatchingP_bound admissible data grade core field)

def completedStrongPairLinear (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →ₗ[ℂ] StrongMatchingPair L sigma gamma ell grade where
  toFun field := WithLp.toLp 1
    (completedStrongScalar admissible grade core field, completedStrongFlux admissible data grade core field)
  map_add' first second := by
    change WithLp.toLp 1 (_, _) = WithLp.toLp 1 (_, _)
    simp only [map_add]
    rfl
  map_smul' scalar field := by
    change WithLp.toLp 1 (_, _) = WithLp.toLp 1 (_, _)
    simp only [map_smul]
    rfl

/-- AY4: the actual matching map on the original compensated graph completion. -/
def completedStrongPair (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] StrongMatchingPair L sigma gamma ell grade :=
  (completedStrongPairLinear admissible data grade core).mkContinuous
    (Real.sqrt (traceCellConstant (grade + 2)) + matchingTraceConstant data grade) (fun field => by
      rw [strongMatchingPair_norm]
      change ‖completedStrongScalar admissible grade core field‖ +
        ‖completedStrongFlux admissible data grade core field‖ ≤ _
      exact (add_le_add (completedStrongScalar_bound admissible grade core field)
        (completedStrongFlux_bound admissible data grade core field)).trans_eq (add_mul _ _ _).symm)

theorem completedStrongPair_fst (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (field : compensatedClosure admissible grade core) :
    (completedStrongPair admissible data grade core field).fst = completedStrongScalar admissible grade core field := rfl

theorem completedStrongPair_snd (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (field : compensatedClosure admissible grade core) :
    (completedStrongPair admissible data grade core field).snd = completedStrongFlux admissible data grade core field := rfl

/-- The exact AY5 equality; no loss or extra coefficient factor is inserted. -/
theorem completedStrongPair_norm (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (field : compensatedClosure admissible grade core) :
    ‖completedStrongPair admissible data grade core field‖ =
      ‖apHighProjection L sigma gamma ell (grade + 2) (completedNativeThetaTrace admissible grade core field)‖ +
      ‖apHighProjection L sigma gamma ell (grade + 1) (completedMatchingP admissible data grade core field)‖ :=
  (strongMatchingPair_norm L sigma gamma ell grade (completedStrongPair admissible data grade core field)).trans
    (congrArg₂ (fun first second : ℝ => first + second)
      (completedStrongScalar_norm admissible grade core field)
      (completedStrongFlux_norm admissible data grade core field))

theorem completedStrongPair_bound (data : LedgerData L sigma gamma ell) (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (field : compensatedClosure admissible grade core) :
    ‖completedStrongPair admissible data grade core field‖ ≤
      (Real.sqrt (traceCellConstant (grade + 2)) + matchingTraceConstant data grade) * ‖field‖ :=
  (strongMatchingPair_norm L sigma gamma ell grade (completedStrongPair admissible data grade core field)).trans_le
    ((add_le_add (completedStrongScalar_bound admissible grade core field)
      (completedStrongFlux_bound admissible data grade core field)).trans_eq (add_mul _ _ _).symm)

end Grad.GaugeCoefficients.Physical.Compensated
