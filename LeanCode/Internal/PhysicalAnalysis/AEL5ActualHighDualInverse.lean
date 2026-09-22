import AEL4ActualCurrentCoercivity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularCurrentInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularCurrentEnergy

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule

local instance currentZero_normedGroup (lower L : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < L) :
    NormedAddCommGroup (annularInnerZero lower L positive bounded lengthPositive) := inferInstance
local instance currentZero_seminormedGroup (lower L : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < L) :
    SeminormedAddCommGroup (annularInnerZero lower L positive bounded lengthPositive) :=
  (currentZero_normedGroup lower L positive bounded lengthPositive).toSeminormedAddCommGroup
local instance currentZero_realNormedSpace (lower L : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < L) :
    NormedSpace ℝ (annularInnerZero lower L positive bounded lengthPositive) :=
  (annularInnerZero_realInner lower L positive bounded lengthPositive).toNormedSpace

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

/-- The dual equivalence of the proved actual current form, on the same
original closed energy space. No inverse or coercivity is assumed. -/
def currentHighDualEquiv :
    (annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ) ≃L[ℝ]
    annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive :=
  coerciveDualEquiv _ (currentHighZeroForm_isCoercive parameters L compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small)

def currentHighDualInverse :
    (annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ) →L[ℝ]
    annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive :=
  (currentHighDualEquiv parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small).toContinuousLinearMap

theorem currentHighDualInverse_solves
    (source : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ)
    (test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
    currentHighZeroForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (currentHighDualInverse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small source) test = source test :=
  coerciveDualEquiv_solves _ _ source test

theorem currentHighDualInverse_right :
    (currentHighZeroForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state).comp
      (currentHighDualInverse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) =
        ContinuousLinearMap.id ℝ _ :=
  coerciveDualEquiv_forward _ _

theorem currentHighDualInverse_left :
    (currentHighDualInverse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small).comp
      (currentHighZeroForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state) =
        ContinuousLinearMap.id ℝ _ :=
  coerciveDualEquiv_inverse _ _

theorem currentHighDualInverse_apply_bound
    (source : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ) :
    ‖currentHighDualInverse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small source‖ ≤
      32 * ‖source‖ :=
  coerciveDualEquiv_bound _ _
    (currentHighZeroForm_coercive_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) source

theorem currentHighDualInverse_norm :
    ‖currentHighDualInverse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small‖ ≤ 32 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  exact currentHighDualInverse_apply_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small

theorem currentHighDualInverse_unique
    (source : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ)
    (candidate : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)
    (equation : ∀ test, currentHighZeroForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state candidate test = source test) :
    candidate = currentHighDualInverse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small source := by
  have equality : currentHighZeroForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state candidate = source := by
    ext test
    exact equation test
  have law := congrArg (fun mapping => mapping candidate)
    (currentHighDualInverse_left parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
  change currentHighDualInverse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    (currentHighZeroForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state candidate) = candidate at law
  rw [equality] at law
  exact law.symm

end Grad.AnnularCurrentInverse
