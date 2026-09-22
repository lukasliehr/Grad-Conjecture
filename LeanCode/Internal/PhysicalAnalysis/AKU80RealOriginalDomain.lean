import AKU79RealResidualVanishing
import AKU66OriginalLiftVectorConstraints

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 3000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearDivision
open Grad.QuotientProjection Grad.NonlinearRange Grad.NonlinearProduct Grad.CompletedReality
open Grad.FlatSourceProjection Grad.ExhaustionSourceAllocation Grad.GaugeCoefficients.Physical.Allocation
open Grad.Cor18 Grad.RealFixedRanges Grad.PhysicalCoordinates Grad.AxisSplit Grad.AxisJet

theorem finiteRealCore_vectorConstraints (parameters : PhaseParameters)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (field : ACore parameters 3) (constraints : VectorConstraints parameters seed inside field) :
    VectorConstraints parameters seed inside (finiteRealCore field) := by
  have fixed := vectorProjection_fixes parameters seed inside field constraints
  apply (vectorProjection_range_iff parameters seed inside _).mp
  refine ⟨finiteRealCore field,?_⟩
  change ((vectorProjection parameters seed inside).restrictScalars ℝ)
    ((1/2 : ℝ) • (field+cartesianCoreConjugation parameters field)) = _
  rw [map_smul,map_add]
  change (1/2 : ℝ) • (vectorProjection parameters seed inside field+
    vectorProjection parameters seed inside (cartesianCoreConjugation parameters field)) = _
  rw [← vectorProjection_conjugate,fixed]
  rfl

theorem toPhysicalCore_finiteRealCore (parameters : PhaseParameters) (field : ACore parameters 3) :
    toPhysicalCore parameters (finiteRealCore field) = finiteRealCore (toPhysicalCore parameters field) := by
  change ((toPhysicalCore parameters).restrictScalars ℝ) ((1/2 : ℝ) • (field+cartesianCoreConjugation parameters field)) = _
  rw [map_smul,map_add]
  change (1/2 : ℝ) • (toPhysicalCore parameters field+toPhysicalCore parameters (cartesianCoreConjugation parameters field)) = _
  rw [← toPhysicalCore_conjugate]
  rfl

theorem finiteRealCore_mean_zero (parameters : PhaseParameters) {dimension : ℕ}
    (field : ACore parameters dimension) (mean : angularCore parameters 0 field = 0) :
    angularCore parameters 0 (finiteRealCore field) = 0 := by
  change ((angularCore parameters 0).restrictScalars ℝ) ((1/2 : ℝ) • (field+cartesianCoreConjugation parameters field)) = 0
  rw [map_smul,map_add]
  change (1/2 : ℝ) • (angularCore parameters 0 field+angularCore parameters 0 (cartesianCoreConjugation parameters field)) = 0
  have commute := angularCore_conjugate parameters 0 field
  norm_num only [neg_zero] at commute
  rw [← commute,mean,map_zero,add_zero]
  change (1/2 : ℝ) • (0 : ACore parameters dimension) = 0
  exact @smul_zero ℝ (ACore parameters dimension) _ _ (1/2 : ℝ)

def originalRealFiniteLiftState (parameters : PhaseParameters) (length rho epsilon : ℝ) (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) : Grad.SmoothingFamily.StateCore parameters :=
  (0,toPhysicalCore parameters (originalRealFiniteLiftU parameters length rho epsilon field low source),
    originalRealFiniteLiftS parameters length rho epsilon field low source)

/-- Genuine original real domain membership at every seed. The two gauges
and full physical outer row are inherited through the actual commuting projection. -/
theorem originalRealFiniteLiftState_mem (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3) (vanishes : ∀ cell, (field.val cell).value closedOrigin = 0)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) :
    originalRealFiniteLiftState parameters length rho epsilon field low source ∈ stateSmoothRange parameters seed inside := by
  apply (mem_stateSmoothRange parameters seed inside _).mpr
  constructor
  · apply fullProjection_fixes
    constructor
    · change VectorConstraints parameters seed inside
        (toPhysicalCore parameters (finiteRealCore (originalFiniteLiftU parameters length rho epsilon field low source)))
      rw [toPhysicalCore_finiteRealCore]
      exact finiteRealCore_vectorConstraints parameters seed inside _
        (originalFiniteLiftU_storage_constraints parameters length rho epsilon field vanishes low source seed inside)
    · exact finiteRealCore_mean_zero parameters _
        (originalFiniteLiftS_mean_zero parameters length rho epsilon field low source flat)
  · apply Prod.ext
    · change smoothAxisConjugation parameters 2 0 = 0
      exact map_zero _
    · apply Prod.ext
      · change cartesianCoreConjugation parameters (toPhysicalCore parameters (finiteRealCore _)) = _
        rw [toPhysicalCore_conjugate,finiteRealCore_real]
        rfl
      · exact finiteRealCore_real _

/-- Real averaging does not enlarge either original norm. -/
theorem originalRealFiniteLift_norm_le (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCubicLowRadius parameters length)
    (source : SmoothQuotient parameters) (grade : ℕ) :
    originalGradeNorm grade (originalRealFiniteLiftU parameters length rho epsilon field low source) +
      originalGradeNorm grade (originalRealFiniteLiftS parameters length rho epsilon field low source) ≤
      originalFiniteLiftNorm parameters length rho epsilon field low source grade :=
  add_le_add (finiteRealCore_norm _ grade) (finiteRealCore_norm _ grade)

end Grad.FinitePhysicalJetLift
