import AIQ11ExactCrossSourceAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularPhysicalSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularCurrentSource
open Grad.AnnularCurrentBoundary Grad.AnnularReconstruction Grad.AnnularCrossMaps Grad.AnnularTiltedReference

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

/-- The SAME physical source solution on the exact BF16 data subspace. -/
def crossEnergyValue (data : CrossHighData parameters lower) : annularEnergySpace lower L positive :=
  graphDataEnergySolution parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (data.toGraphKnown parameters lower)

theorem crossEnergyValue_inner (data : CrossHighData parameters lower) :
    annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (bEnergyDecode lower L positive
        (crossEnergyValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)) = 0 :=
  graphDataEnergySolution_physical_inner parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (data.toGraphKnown parameters lower)

theorem crossEnergyValue_equation (data : CrossHighData parameters lower)
    (test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
    currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (crossEnergyValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) test.val =
      crossKnownValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data test.val :=
  (actualHighGraphEnergySolution_complex parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (data.toGraphKnown parameters lower).weighted (data.toGraphKnown parameters lower).auxiliary
    (data.toGraphKnown parameters lower).graphs (data.toGraphKnown parameters lower).datum 0 test).trans
      (crossKnownValue_literal parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data test.val)

theorem crossEnergyValue_unique (data : CrossHighData parameters lower) (candidate : annularEnergySpace lower L positive)
    (incoming : annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (bEnergyDecode lower L positive candidate) = 0)
    (equation : ∀ test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive,
      currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state candidate test.val =
        crossKnownValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data test.val) :
    candidate = crossEnergyValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data := by
  apply graphDataEnergySolution_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (data.toGraphKnown parameters lower) candidate incoming
  intro test
  exact (equation test).trans (crossKnownValue_literal parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data test.val).symm

theorem crossEnergyValue_add (first second : CrossHighData parameters lower) :
    crossEnergyValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small (first + second) =
      crossEnergyValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small first +
      crossEnergyValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small second := by
  symm
  apply crossEnergyValue_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
  · rw [map_add, map_add, crossEnergyValue_inner, crossEnergyValue_inner, add_zero]
  · intro test
    rw [currentHighFormValue_add_field, crossEnergyValue_equation, crossEnergyValue_equation, crossKnownValue_add]

theorem crossEnergyValue_smul (scalar : ℂ) (data : CrossHighData parameters lower) :
    crossEnergyValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small (scalar • data) =
      scalar • crossEnergyValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data := by
  symm
  apply crossEnergyValue_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
  · rw [map_smul, map_smul, crossEnergyValue_inner, smul_zero]
  · intro test
    rw [currentHighFormValue_smul_field, crossEnergyValue_equation, crossKnownValue_smul]

def crossEnergyLinear : CrossHighData parameters lower →ₗ[ℂ] annularEnergySpace lower L positive where
  toFun := crossEnergyValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
  map_add' := crossEnergyValue_add parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
  map_smul' := crossEnergyValue_smul parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small

end Grad.AnnularPhysicalSolution
