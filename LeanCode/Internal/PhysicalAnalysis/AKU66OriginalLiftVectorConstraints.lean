import AKU65OriginalLiftGaugeModes

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct Grad.NonlinearDivision
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.GaugeCoefficients.Physical.Allocation
open Grad.Cor18 Grad.Constraints.Gauges Grad.Constraints.Multipliers Grad.PhysicalCoordinates Grad.BoundaryTrace

theorem smoothMultiplier_value_zero {parameters : PhaseParameters} {input output : ℕ}
    (coefficients : ℤ → ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (summable : ∀ grade, Summable (envelopeTerm parameters grade coefficients))
    (field : ACore parameters input) (point : ClosedDisk)
    (zero : ∀ cell, (field.val cell).value point = 0) (cell : ℤ) :
    ((smoothMultiplier parameters coefficients summable field).val cell).value point = 0 := by
  rw [← (smoothMultiplier_value_hasSum parameters coefficients summable field cell point).tsum_eq]
  simp only [zero,map_zero,tsum_zero]

theorem physicalRow_zero_of_boundary_zero (parameters : PhaseParameters)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) (field : ACore parameters 3)
    (zero : ∀ cell angle, (field.val cell).value (boundaryDiskPoint angle) = 0) :
    physicalRow parameters seed inside field = 0 := by
  have planar (cell : ℤ) (angle : CellCircle) :
      ((planarPartCore parameters field).val cell).value (boundaryDiskPoint angle) = 0 := by
    change (valueMapJet planarPartMap (field.val cell)).value (boundaryDiskPoint angle) = 0
    rw [valueMapJet_value,zero,map_zero]
  have rowZero (cell : ℤ) (angle : CellCircle) :
      ((rowField parameters seed inside field).val cell).value (boundaryDiskPoint angle) = 0 := by
    change ((seedInverseCore parameters seed inside (planarPartCore parameters field)).val cell).value (boundaryDiskPoint angle) = 0
    rw [seedInverseCore_eq_full]
    exact smoothMultiplier_value_zero _ _ _ _ (fun index => planar index angle) cell
  have functionZero (cell : ℤ) : rowFunction parameters (rowField parameters seed inside field) cell = 0 := by
    funext angle
    simp only [rowFunction,rowZero,PiLp.zero_apply,mul_zero,add_zero,Pi.zero_apply]
  apply Subtype.ext
  funext mode
  change physicalRowFamily parameters seed inside field mode = 0
  unfold physicalRowFamily
  split_ifs
  · rfl
  · rw [functionZero]
    simp [fourierCoeff]

theorem originalFiniteLiftU_storage_outer_zero (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) :
    physicalRow parameters seed inside
      (toPhysicalCore parameters (originalFiniteLiftU parameters length rho epsilon field low source)) = 0 := by
  apply physicalRow_zero_of_boundary_zero
  intro cell angle
  rw [toPhysicalCore_value,(originalFiniteLift_outer_support parameters length rho epsilon field low source cell
    (boundaryDiskPoint angle) (by change 1/4 ≤ ‖boundaryCirclePoint angle‖; rw [boundaryCirclePoint_norm]; norm_num)).1,map_zero]

/-- The actual fixed cutoff lift lies in the original vector constraint
kernel at every seed: genuine first jets, both gauges, and the full outer row. -/
theorem originalFiniteLiftU_storage_constraints (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) :
    VectorConstraints parameters seed inside
      (toPhysicalCore parameters (originalFiniteLiftU parameters length rho epsilon field low source)) := by
  refine ⟨?_,originalFiniteLiftU_storage_poloidal_zero parameters length rho epsilon field low source seed inside,
    originalFiniteLiftU_storage_toroidal_zero parameters length rho epsilon field vanishes low source seed inside,
    originalFiniteLiftU_storage_outer_zero parameters length rho epsilon field low source seed inside⟩
  apply toPhysicalCore_zeroJets
  intro cell
  rw [zeroCartesianFirstJets_iff]
  have jets := originalFiniteLiftU_zero_jets parameters length rho epsilon field low source
  constructor
  · exact congrArg (fun axis : Grad.AxisCore.AxisSmoothCore parameters 3 => axis.val cell) jets.1
  · intro direction
    exact congrArg (fun axis : Grad.AxisCore.AxisSmoothCore parameters 3 => axis.val cell) (jets.2 direction)

end Grad.FinitePhysicalJetLift
