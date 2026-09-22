import AKU80RealOriginalDomain
import AXL21ReferenceLift
import AXD1SmoothFlatDomain

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 4000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds Grad.NonlinearDivision
open Grad.QuotientProjection Grad.NonlinearRange Grad.NonlinearProduct Grad.CompletedReality
open Grad.GaugeCoefficients.Physical.Allocation Grad.Q24Realization Grad.ExhaustionSourceAllocation
open Grad.AxisCore
open Grad.AxisSplit Grad.AxisJet Grad.FlatSourceProjection Grad.RealFixedRanges Grad.PhysicalCoordinates
open Grad.ConstrainedTransfer Grad.ChartAxisLift Grad.ChartAxisProjections

theorem finiteRealCore_traceFirst_zero {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (direction : Fin 2) (zero : traceFirst direction field = 0) :
    traceFirst direction (finiteRealCore field) = 0 := by
  have involutionZero : axisCoreInvolution parameters dimension 0 = 0 := by
    apply Subtype.ext
    funext cell
    exact (cartesianPhysicalConjugation dimension).map_zero
  have conjugate := traceFirst_conjugate parameters direction field
  rw [zero,involutionZero] at conjugate
  change ((traceFirst direction).restrictScalars ℝ) ((1/2 : ℝ) • (field+cartesianCoreConjugation parameters field)) = 0
  rw [map_smul,map_add]
  change (1/2 : ℝ) • (traceFirst direction field+traceFirst direction (cartesianCoreConjugation parameters field)) = 0
  rw [zero,conjugate,add_zero]
  exact @smul_zero ℝ (Grad.AxisCore.AxisSmoothCore parameters dimension) _ _ (1/2 : ℝ)

def originalRealFiniteLiftAtSeed (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) : stateSmoothRange parameters seed inside :=
  ⟨originalRealFiniteLiftState parameters length rho epsilon field low source,
    originalRealFiniteLiftState_mem parameters length rho epsilon field vanishes low source flat seed inside⟩

def originalRealFiniteLiftAtReference (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) : stateSmoothRange parameters reference insideR :=
  constrainedCoreTransfer parameters seed insideS reference insideR
    (originalRealFiniteLiftAtSeed parameters length rho epsilon field vanishes low source flat seed insideS)

/-- The specified inverse seed transfer, followed by the original forward
coordinate map, is exactly the same physical pair. -/
theorem originalRealFiniteLift_reference_transfer (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) :
    physicalFixedReferenceTransfer parameters reference insideR seed insideS
      (smoothingChartCore parameters (originalRealFiniteLiftAtReference parameters length rho epsilon field vanishes low source flat
        reference insideR seed insideS).val) =
      (0,originalRealFiniteLiftU parameters length rho epsilon field low source,
        originalRealFiniteLiftS parameters length rho epsilon field low source) := by
  have constraints := smoothState_constraints parameters seed insideS
    (originalRealFiniteLiftAtSeed parameters length rho epsilon field vanishes low source flat seed insideS)
  change (0,toPhysicalCore parameters (Gauges.seedTransfer parameters reference insideR seed insideS
    (Gauges.seedTransfer parameters seed insideS reference insideR
      (toPhysicalCore parameters (originalRealFiniteLiftU parameters length rho epsilon field low source)))),
        originalRealFiniteLiftS parameters length rho epsilon field low source) = _
  rw [Gauges.seedTransfer_reverse parameters seed insideS reference insideR
    (toPhysicalCore parameters (originalRealFiniteLiftU parameters length rho epsilon field low source)) constraints.1.2.1 constraints.1.2.2.1,
    toPhysicalCore_involutive]

/-- The actual first chart derivative has eta zero and exactly this physical
U/S pair, for every original base state. -/
theorem originalRealFiniteLift_physical_first (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR) :
    physicalFixedReferenceFamily parameters reference insideR seed insideS 1
      (realJointCoreToJoint parameters reference insideR base)
      (fun _ => realJointCoreToJoint parameters reference insideR
        (0,originalRealFiniteLiftAtReference parameters length rho epsilon field vanishes low source flat reference insideR seed insideS)) =
      (0,originalRealFiniteLiftU parameters length rho epsilon field low source,
        originalRealFiniteLiftS parameters length rho epsilon field low source) := by
  apply Prod.ext
  · rfl
  · change chartDerivativeFamily parameters seed insideS 1 _
      (fun _ => physicalFixedReferenceTransfer parameters reference insideR seed insideS
        (smoothingChartCore parameters (originalRealFiniteLiftAtReference parameters length rho epsilon field vanishes low source flat
          reference insideR seed insideS).val)) = _
    rw [originalRealFiniteLift_reference_transfer,chartDerivativeFamily_one_root,
      Grad.ChartAxisProjections.rootDerivativeFamily_one_zero,Grad.ChartAxisProjections.chartAffineField_zero_inputs]

theorem originalRealFiniteLift_reference_flat (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) :
    originalRealFiniteLiftAtReference parameters length rho epsilon field vanishes low source flat reference insideR seed insideS ∈
      LinearMap.ker (realChartKappa parameters reference insideR) := by
  apply (realChartKappa_eq_zero_iff reference insideR _).mpr
  constructor
  · change smoothingToTangent parameters 0 = 0
    exact map_zero _
  · apply (Grad.FlatDomainProjection.scalarOriginGradient_eq_zero_iff_traceFirst _).mpr
    intro direction
    exact finiteRealCore_traceFirst_zero _ direction
      ((originalFiniteLiftS_zero_jets parameters length rho epsilon field low source).2 direction)

end Grad.FinitePhysicalJetLift
