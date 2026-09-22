import AKU77ActualForwardReality

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.QuotientProjection Grad.NonlinearRange Grad.NonlinearProduct Grad.CompletedReality
open Grad.FlatSourceProjection

/-- Canonical real averaging on an actual real linear coefficient space. -/
def finiteRealAverage {E : Type*} [AddCommGroup E] [Module ℝ E] (symmetry : E →ₗ[ℝ] E) : E →ₗ[ℝ] E :=
  (1/2 : ℝ) • (LinearMap.id+symmetry)

theorem finiteRealAverage_apply {E : Type*} [AddCommGroup E] [Module ℝ E]
    (symmetry : E →ₗ[ℝ] E) (value : E) :
    finiteRealAverage symmetry value = (1/2 : ℝ) • (value+symmetry value) := rfl

theorem finiteRealAverage_fixed {E : Type*} [AddCommGroup E] [Module ℝ E]
    (symmetry : E →ₗ[ℝ] E) (involutive : Function.Involutive symmetry) (value : E) :
    symmetry (finiteRealAverage symmetry value) = finiteRealAverage symmetry value := by
  simp only [finiteRealAverage_apply,map_smul,map_add]
  rw [involutive value,add_comm]

theorem finiteRealAverage_of_fixed {E : Type*} [AddCommGroup E] [Module ℝ E]
    (symmetry : E →ₗ[ℝ] E) (value : E) (fixed : symmetry value = value) :
    finiteRealAverage symmetry value = value := by
  rw [finiteRealAverage_apply,fixed,← two_smul ℝ value,smul_smul]
  norm_num

def finiteRealCore {parameters : PhaseParameters} {dimension : ℕ} :
    ACore parameters dimension →ₗ[ℝ] ACore parameters dimension :=
  finiteRealAverage (cartesianCoreConjugation parameters)

def finiteRealSource (parameters : PhaseParameters) : SmoothQuotient parameters →ₗ[ℝ] SmoothQuotient parameters :=
  finiteRealAverage (zCoreConjugation parameters)

theorem finiteRealCore_real {parameters : PhaseParameters} {dimension : ℕ} (field : ACore parameters dimension) :
    cartesianCoreConjugation parameters (finiteRealCore field) = finiteRealCore field :=
  finiteRealAverage_fixed _ (cartesianCoreConjugation_involutive parameters) field

theorem finiteRealCore_norm {parameters : PhaseParameters} {dimension : ℕ} (field : ACore parameters dimension) (grade : ℕ) :
    originalGradeNorm grade (finiteRealCore field) ≤ originalGradeNorm grade field := by
  change ‖(1/2 : ℝ) • (GradeCore.ofCoreLinear (grade := grade) field +
    gradeCoreConjugationMap parameters (GradeCore.ofCoreLinear (grade := grade) field))‖ ≤
    ‖GradeCore.ofCoreLinear (grade := grade) field‖
  rw [norm_smul,Real.norm_eq_abs]
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
  have bound := norm_add_le (GradeCore.ofCoreLinear (grade := grade) field)
    (gradeCoreConjugationMap parameters (GradeCore.ofCoreLinear (grade := grade) field))
  rw [gradeCoreConjugationMap_norm] at bound
  linarith

theorem finiteRealSource_cartesian (parameters : PhaseParameters) (source : SmoothQuotient parameters) :
    cartesianSourceVector (finiteRealSource parameters source) = finiteRealCore (cartesianSourceVector source) := by
  have conjugate := congrArg Prod.fst (spinCartesianEquiv_conjugation source)
  change cartesianSourceVector (zCoreConjugation parameters source) =
    cartesianCoreConjugation parameters (cartesianSourceVector source) at conjugate
  have linear := ((spinCartesianEquiv (parameters := parameters)).toLinearMap.restrictScalars ℝ).map_smul
    (1/2 : ℝ) (source+zCoreConjugation parameters source)
  have first := congrArg Prod.fst linear
  change cartesianSourceVector ((1/2 : ℝ) • (source+zCoreConjugation parameters source)) =
    (1/2 : ℝ) • cartesianSourceVector (source+zCoreConjugation parameters source) at first
  change cartesianSourceVector ((1/2 : ℝ) • (source+zCoreConjugation parameters source)) = _
  rw [first]
  have addition := congrArg Prod.fst (spinCartesianEquiv.map_add source (zCoreConjugation parameters source))
  change cartesianSourceVector (source+zCoreConjugation parameters source) =
    cartesianSourceVector source+cartesianSourceVector (zCoreConjugation parameters source) at addition
  rw [addition,conjugate]
  rfl

theorem physicalEtaZeroRows_realAverage (parameters : PhaseParameters) (length : ℝ)
    (base : QuotientState parameters) (scalarReal : starRingEnd ℂ base.1 = base.1)
    (fieldReal : cartesianCoreConjugation parameters base.2.1 = base.2.1)
    (vector : ACore parameters 3) (scalar : ACore parameters 1) :
    physicalEtaZeroRows parameters length base (finiteRealCore vector) (finiteRealCore scalar) =
      finiteRealSource parameters (physicalEtaZeroRows parameters length base vector scalar) := by
  change ((physicalEtaZeroLinear parameters length base).restrictScalars ℝ)
    ((1/2 : ℝ) • ((vector,scalar)+(cartesianCoreConjugation parameters vector,cartesianCoreConjugation parameters scalar))) = _
  rw [map_smul,map_add]
  change (1/2 : ℝ) • (physicalEtaZeroRows parameters length base vector scalar +
    physicalEtaZeroRows parameters length base (cartesianCoreConjugation parameters vector) (cartesianCoreConjugation parameters scalar)) = _
  rw [← physicalEtaZeroRows_conjugate parameters length base scalarReal fieldReal]
  rfl

end Grad.FinitePhysicalJetLift
