import AJP6FullHighFluxRow
import AJI30ActualFullRadialRHS
import AJT2SameClampedSystem

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularSourceGraph Grad.AnnularHighRadial
open Grad.AnnularVariational Grad.CircularHighRegularity Grad.AnnularReconstruction Grad.AnnularStrongData
open Grad.AnnularStrongSolution Grad.AnnularStrongOrbit Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.Allocation

/-- Entry zero is xi and entry one is x in the original physical high pair. -/
def highPhysicalPairCoefficient (entry : Fin 2) (mode : HighAnnularMode) (field : PhysicalHilbertPair) : ComplexEuclidean 1 :=
  if entry = 0 then field.2 mode.val else field.1 mode.val

theorem highPhysicalPairCoefficient_continuous (entry : Fin 2) (mode : HighAnnularMode) :
    Continuous (highPhysicalPairCoefficient entry mode) := by
  let projection := lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode.val
  by_cases zero : entry = 0
  · exact (projection.continuous.comp continuous_snd : Continuous (fun field : PhysicalHilbertPair => field.2 mode.val))
      |>.congr (fun _ => by simp only [highPhysicalPairCoefficient, if_pos zero]; rfl)
  · exact (projection.continuous.comp continuous_fst : Continuous (fun field : PhysicalHilbertPair => field.1 mode.val))
      |>.congr (fun _ => by simp only [highPhysicalPairCoefficient, if_neg zero]; rfl)

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

def originalSmoothHighDerivativeCurve (entry : Fin 2) (mode : HighAnnularMode) : C(ℝ, ComplexEuclidean 1) where
  toFun radius := highPhysicalPairCoefficient entry mode
    (originalSmoothResponseClampedRHS parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core 0 radius)
  continuous_toFun := (highPhysicalPairCoefficient_continuous entry mode).comp
    (originalSmoothResponseClampedRHS_continuous parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core 0)

/-- The globally continuous candidate equals the exact full high weak PDE RHS. -/
theorem originalSmoothHighDerivativeCurve_actual (entry : Fin 2) (mode : HighAnnularMode) :
    originalSmoothHighDerivativeCurve parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core entry mode =ᵐ[volume.restrict (Icc lower 1)]
    if entry = 0 then originalSmoothHighXiRHS parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core mode
    else originalSmoothHighXRHS parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core mode := by
  let field := originalSmoothSourceResponse parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core
  have coefficient := originalRadialSystemRHS_actual parameters length compact lower positive
    (lowerHalf.trans_lt (by norm_num)) lengthPositive state field core
    (originalSmoothSourceResponse_allGrades parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core) 0
  filter_upwards [originalSmoothHighXiRHS_actual parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core mode,
    originalSmoothHighXRHS_actual parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core mode,
    coefficient, ae_restrict_mem measurableSet_Icc] with radius xi x actual inside
  change highPhysicalPairCoefficient entry mode
    (originalSmoothResponseClampedRHS parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core 0 radius) = _
  rw [originalSmoothResponseClampedRHS_same parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core 0 radius inside]
  have same := actual mode.val
  simp only [pow_zero, Complex.ofReal_one, one_smul] at same
  by_cases zero : entry = 0
  · simp only [highPhysicalPairCoefficient, if_pos zero]
    exact (congrArg Prod.snd same).trans xi.symm
  · simp only [highPhysicalPairCoefficient, if_neg zero]
    exact (congrArg Prod.fst same).trans x.symm

/-- Every high grade-zero Hilbert coefficient is its exact accepted raw section. -/
theorem originalSmoothResponsePairCurve_high_coefficient (entry : Fin 2) (mode : HighAnnularMode) (radius : ℝ) :
    highPhysicalPairCoefficient entry mode
      (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small core 0 radius) =
    radialSectionExtension 1 lower (lowerHalf.trans (by norm_num))
      (if entry = 0 then
        rawHighXiSection parameters lower length positive (lowerHalf.trans_lt (by norm_num))
          (originalSmoothSourceResponse parameters length compact lower positive lowerHalf
            lengthPositive widthHalf widthLength state small core).ofLp.1.ofLp.1 mode
      else rawHighXSection parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
          (originalSmoothSourceResponse parameters length compact lower positive lowerHalf
            lengthPositive widthHalf widthLength state small core).ofLp.1.ofLp.2 mode) radius := by
  let field := originalSmoothSourceResponse parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core
  have grades := originalSmoothSourceResponse_allGrades parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core
  by_cases zero : entry = 0
  · simp only [highPhysicalPairCoefficient, if_pos zero]
    change sameCoupledPhysicalXiSection parameters lower length positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive 0 field (radialClamp lower (lowerHalf.trans (by norm_num)) radius) mode.val = _
    rw [sameCoupledPhysicalXiSection_coefficient parameters lower length positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive field grades,
      sameCoupledXiCoefficient_high]
    rfl
  · simp only [highPhysicalPairCoefficient, if_neg zero]
    change sameCoupledPhysicalXSection parameters lower length positive (lowerHalf.trans_lt (by norm_num))
      lengthPositive 0 field (radialClamp lower (lowerHalf.trans (by norm_num)) radius) mode.val = _
    rw [sameCoupledPhysicalXSection_coefficient parameters lower length positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive field grades,
      sameCoupledXCoefficient_high]
    rfl

/-- Genuine high Fourier coefficient derivative of the SAME full Hilbert pair.
The original weak equations, full sources and physical RHS are all proved. -/
theorem originalSmoothResponsePairCurve_high_derivative (entry : Fin 2) (mode : HighAnnularMode)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt
      (fun point => highPhysicalPairCoefficient entry mode
        (originalSmoothResponsePairCurve parameters length compact lower positive lowerHalf
          lengthPositive widthHalf widthLength state small core 0 point))
      (highPhysicalPairCoefficient entry mode
        (originalSmoothResponseSystemRHS parameters length compact lower positive lowerHalf
          lengthPositive widthHalf widthLength state small core 0 radius))
      (Icc lower 1) radius := by
  let data := (strongSmoothDenseMap parameters lower length positive (lowerHalf.trans (by norm_num)) lengthPositive).mapping core
  let rhs := originalSmoothHighDerivativeCurve parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core entry mode
  have same := (originalSmoothHighDerivativeCurve_actual parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core entry mode).symm
  have raw : HasDerivWithinAt
      (radialSectionExtension 1 lower (lowerHalf.trans (by norm_num))
        (if entry = 0 then rawHighXiSection parameters lower length positive (lowerHalf.trans_lt (by norm_num))
            (originalSmoothSourceResponse parameters length compact lower positive lowerHalf
              lengthPositive widthHalf widthLength state small core).ofLp.1.ofLp.1 mode
        else rawHighXSection parameters lower length positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
            (originalSmoothSourceResponse parameters length compact lower positive lowerHalf
              lengthPositive widthHalf widthLength state small core).ofLp.1.ofLp.2 mode))
      (rhs radius) (Icc lower 1) radius := by
    by_cases zero : entry = 0
    · simp only [if_pos zero] at same ⊢
      exact sharedRawHighXi_hasDerivWithinAt parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small data mode rhs same radius inside
    · simp only [if_neg zero] at same ⊢
      exact sharedRawHighX_hasDerivWithinAt parameters length compact lower positive lowerHalf
        lengthPositive widthHalf widthLength state small data mode rhs same radius inside
  change HasDerivWithinAt _ (highPhysicalPairCoefficient entry mode
    (originalSmoothResponseClampedRHS parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core 0 radius)) _ _ at raw
  rw [originalSmoothResponseClampedRHS_same parameters length compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state small core 0 radius inside] at raw
  exact raw.congr
    (fun point _ => originalSmoothResponsePairCurve_high_coefficient parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core entry mode point)
    (originalSmoothResponsePairCurve_high_coefficient parameters length compact lower positive lowerHalf
      lengthPositive widthHalf widthLength state small core entry mode radius)

end Grad.AnnularSmoothCore
