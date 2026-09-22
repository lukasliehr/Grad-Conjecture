import ANH4BoundaryL2

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory
open scoped BigOperators ENNReal

namespace Grad.CircularHighWeak

open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.RadialLedger

local instance circlePeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

/-- Genuine circle L2 with ordinary angular measure dθ, of total mass 2π. -/
abbrev BoundaryL2 := Lp (PhysicalValue 1) 2 (volume : Measure CellCircle)

def closedBoundaryValue : ClosedJet 1 →ₗ[ℂ] C(CellCircle, PhysicalValue 1) where
  toFun field := ⟨fun angle => field.value (boundaryDiskPoint angle),
    field.value.continuous.comp boundaryDiskPoint_continuous⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coreBoundaryL2 : ClosedJet 1 →ₗ[ℂ] BoundaryL2 :=
  (ContinuousMap.toLp 2 volume ℂ).toLinearMap.comp closedBoundaryValue

theorem coreBoundaryL2_ae (field : ClosedJet 1) :
    ∀ᵐ angle : CellCircle, coreBoundaryL2 field angle = field.value (boundaryDiskPoint angle) :=
  ContinuousMap.coeFn_toLp volume (closedBoundaryValue field)

theorem boundaryL2_norm_sq (field : BoundaryL2) :
    ‖field‖ ^ 2 = ∫ angle : CellCircle, ‖field angle‖ ^ 2 := by
  let := InnerProductSpace.rclikeToReal ℂ (PhysicalValue 1)
  calc
    ‖field‖ ^ 2 = inner ℝ field field := (real_inner_self_eq_norm_sq field).symm
    _ = ∫ angle : CellCircle, inner ℝ (field angle) (field angle) :=
      L2.inner_def (𝕜 := ℝ) field field
    _ = _ := by simp only [real_inner_self_eq_norm_sq]

theorem coreBoundaryL2_norm_sq (field : ClosedJet 1) :
    ‖coreBoundaryL2 field‖ ^ 2 =
      ∫ angle in -Real.pi..Real.pi,
        ‖field.value (boundaryDiskPoint (angle : CellCircle))‖ ^ 2 := by
  rw [boundaryL2_norm_sq]
  have literal : (∫ angle : CellCircle, ‖coreBoundaryL2 field angle‖ ^ 2) =
      ∫ angle : CellCircle, ‖field.value (boundaryDiskPoint angle)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [coreBoundaryL2_ae field] with angle equality
    rw [equality]
  rw [literal, ← AddCircle.intervalIntegral_preimage (2 * Real.pi) (-Real.pi)]
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring]

theorem coreBoundaryL2_fourier_norm_sq (field : ClosedJet 1) :
    ‖coreBoundaryL2 field‖ ^ 2 =
      (2 * Real.pi) * ‖diskBoundaryFourier (diskCoreInto field)‖ ^ 2 := by
  rw [coreBoundaryL2_norm_sq, diskBoundaryFourier_core_norm_sq]
  rw [← mul_assoc, mul_inv_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_mul]

theorem coreBoundaryL2_bound (field : ClosedJet 1) :
    ‖coreBoundaryL2 field‖ ≤
      (Real.sqrt (2 * Real.pi) * Real.sqrt (traceCellConstant 1)) * ‖diskCoreInto field‖ := by
  have equal : ‖coreBoundaryL2 field‖ =
      Real.sqrt (2 * Real.pi) * ‖diskBoundaryFourier (diskCoreInto field)‖ := by
    have squared := congrArg Real.sqrt (coreBoundaryL2_fourier_norm_sq field)
    simpa only [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi),
      Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using squared
  rw [equal, mul_assoc]
  exact mul_le_mul_of_nonneg_left (diskBoundaryFourier_bound _) (Real.sqrt_nonneg _)

theorem diskCoreInto_injective : Function.Injective diskCoreInto := by
  intro first second equal
  have embedded : apFiniteInto (grade := 1) 1 0 0 1 (Finsupp.single 0 first) =
      apFiniteInto (grade := 1) 1 0 0 1 (Finsupp.single 0 second) := congrArg Subtype.val equal
  have finite := apFiniteInto_injective 1 0 0 1 embedded
  simpa using congrArg (fun value : ℤ →₀ ClosedJet 1 => value 0) finite

theorem diskBoundary_exists : ∃ trace : diskGrade →L[ℂ] BoundaryL2,
    (∀ core, trace (diskCoreInto core) = coreBoundaryL2 core) ∧
      ∀ field, ‖trace field‖ ≤
        (Real.sqrt (2 * Real.pi) * Real.sqrt (traceCellConstant 1)) * ‖field‖ :=
  @apDense_extension (ClosedJet 1) diskGrade BoundaryL2 _ _ _ diskGrade.normedSpace _ _ _
    diskCoreInto diskCoreInto_injective diskCoreInto_denseRange
    coreBoundaryL2 _ (by positivity) coreBoundaryL2_bound

/-- Actual ordinary boundary trace on the same faithful full-disk H1 carrier. -/
def diskBoundary : diskGrade →L[ℂ] BoundaryL2 := diskBoundary_exists.choose

theorem diskBoundary_core (field : ClosedJet 1) :
    diskBoundary (diskCoreInto field) = coreBoundaryL2 field :=
  diskBoundary_exists.choose_spec.1 field

theorem diskBoundary_bound (field : diskGrade) :
    ‖diskBoundary field‖ ≤
      (Real.sqrt (2 * Real.pi) * Real.sqrt (traceCellConstant 1)) * ‖field‖ :=
  diskBoundary_exists.choose_spec.2 field

theorem diskBoundary_fourier_norm_sq (field : diskGrade) :
    ‖diskBoundary field‖ ^ 2 = (2 * Real.pi) * ‖diskBoundaryFourier field‖ ^ 2 := by
  apply isClosed_property diskCoreInto_denseRange
    (isClosed_eq (diskBoundary.continuous.norm.pow 2)
      (continuous_const.mul (diskBoundaryFourier.continuous.norm.pow 2))) _ field
  intro core
  exact (congrArg (fun value : BoundaryL2 => ‖value‖ ^ 2) (diskBoundary_core core)).trans
    (coreBoundaryL2_fourier_norm_sq core)

end Grad.CircularHighWeak
