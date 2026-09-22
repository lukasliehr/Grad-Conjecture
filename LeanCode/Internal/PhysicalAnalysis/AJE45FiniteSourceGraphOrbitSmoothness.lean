import AJE41ExactSourceGraphCut
import AJB23ActualAxisDerivativeRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open Set Filter
open scoped Topology BigOperators ContDiff
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularKernelL2 Grad.AnnularOrbitGenerators Grad.AnnularInverseCalculus

def sourceAxisFrequency (axis : Bool) (mode : ℤ × ℤ) : ℤ := if axis then mode.2 else mode.1

theorem sourceOrbitCharacter_axis (axis : Bool) (time : ℝ) (mode : ℤ × ℤ) :
    orbitCharacter (time • axisVector axis) mode = cellExponential (sourceAxisFrequency axis mode) time := by
  cases axis <;> simp [axisVector,sourceAxisFrequency,orbitCharacter,orbitAngle,cellExponential,mul_assoc]

/-- Complex scalar dependence on the genuine real radial graph is a real
continuous linear map, derived from its already proved complex invariance. -/
def sourceGraphScalarMap (dimension : ℕ) (lower : ℝ) (field : WeightedRadialH1 dimension lower) :
    ℂ →L[ℝ] WeightedRadialH1 dimension lower :=
  Complex.reCLM.smulRight field + Complex.imCLM.smulRight (sourceGraphScalar dimension lower Complex.I field)

theorem sourceGraphScalarMap_apply (dimension : ℕ) (lower : ℝ)
    (field : WeightedRadialH1 dimension lower) (scalar : ℂ) :
    sourceGraphScalarMap dimension lower field scalar = sourceGraphScalar dimension lower scalar field := by
  apply Subtype.ext
  change scalar.re • field.val + scalar.im • (Complex.I • field.val) = scalar • field.val
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ),RCLike.real_smul_eq_coe_smul (K := ℂ),
    smul_smul,← add_smul]
  exact congrArg (fun value : ℂ => value • field.val) (Complex.re_add_im scalar)

def sourceGraphLpAmbient (dimension : ℕ) (lower : ℝ) :
    lp (fun _ : ℤ × ℤ => WeightedRadialH1 dimension lower) 2 →L[ℝ]
      lp (fun _ : ℤ × ℤ => WeightedRadialAmbient dimension lower) 2 :=
  lpTwoMap (fun _ => (WeightedRadialH1 dimension lower).subtypeL) 1 zero_le_one
    (fun _ field => by change ‖field.val‖ ≤ 1 * ‖field.val‖; rw [one_mul])

theorem sourceGraphLpAmbient_apply (dimension : ℕ) (lower : ℝ)
    (field : lp (fun _ : ℤ × ℤ => WeightedRadialH1 dimension lower) 2) (mode : ℤ × ℤ) :
    sourceGraphLpAmbient dimension lower field mode = (field mode).val := rfl

theorem sourceGraphLpAmbient_norm (dimension : ℕ) (lower : ℝ)
    (field : lp (fun _ : ℤ × ℤ => WeightedRadialH1 dimension lower) 2) :
    ‖sourceGraphLpAmbient dimension lower field‖ = ‖field‖ :=
  le_antisymm (lp.norm_mono (by norm_num) (fun _ => le_rfl))
    (lp.norm_mono (by norm_num) (fun _ => le_rfl))

theorem sourceGraphLpAmbient_translation (dimension : ℕ) (lower : ℝ) (tau : OrbitParameter)
    (field : lp (fun _ : ℤ × ℤ => WeightedRadialH1 dimension lower) 2) :
    sourceGraphLpAmbient dimension lower (sourceGraphTranslation dimension lower tau field) =
      orbitLpAction (WeightedRadialAmbient dimension lower) tau (sourceGraphLpAmbient dimension lower field) := by
  apply lp.ext
  funext mode
  rfl

/-- Finite Fourier support gives genuine C∞ source graph orbits, including
both actual radial graph coordinates in the complete Hilbert norm. -/
theorem finiteSourceGraphOrbit_contDiff (dimension : ℕ) (lower : ℝ)
    (field : lp (fun _ : ℤ × ℤ => WeightedRadialH1 dimension lower) 2)
    (support : Finset (ℤ × ℤ)) (finite : ∀ mode, mode ∉ support → field mode = 0) (axis : Bool) :
    ContDiff ℝ ∞ (fun time : ℝ => sourceGraphTranslation dimension lower (time • axisVector axis) field) := by
  have formula (time : ℝ) : sourceGraphTranslation dimension lower (time • axisVector axis) field =
      ∑ mode ∈ support, sourceModeSingle dimension lower mode
        (sourceGraphScalar dimension lower (cellExponential (sourceAxisFrequency axis mode) time) (field mode)) := by
    apply lp.ext
    funext mode
    rw [sourceGraphTranslation_apply,sourceOrbitCharacter_axis,lp.coeFn_sum,Finset.sum_apply]
    symm
    change (∑ other ∈ support,
      (lp.single 2 other (sourceGraphScalar dimension lower (cellExponential (sourceAxisFrequency axis other) time) (field other)) :
        lp (fun _ : ℤ × ℤ => WeightedRadialH1 dimension lower) 2) mode) = _
    simp only [lp.single_apply,Pi.single_apply]
    rw [Finset.sum_eq_single mode]
    · simp only [ite_true]
    · intro other _ different
      exact if_neg (Ne.symm different)
    · intro outside
      rw [finite mode outside,map_zero]
      simp only [ite_true]
  have same : (fun time : ℝ => sourceGraphTranslation dimension lower (time • axisVector axis) field) =
      fun time => ∑ mode ∈ support, sourceModeSingle dimension lower mode
        (sourceGraphScalarMap dimension lower (field mode) (cellExponential (sourceAxisFrequency axis mode) time)) := by
    funext time
    simp_rw [sourceGraphScalarMap_apply]
    exact formula time
  rw [same]
  apply ContDiff.sum
  intro mode _
  have scalarSmooth : ContDiff ℝ ∞ (cellExponential (sourceAxisFrequency axis mode)) := by
    unfold cellExponential
    exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  exact (sourceModeSingle dimension lower mode).contDiff.comp
    ((sourceGraphScalarMap dimension lower (field mode)).contDiff.comp scalarSmooth)

end Grad.AnnularStrongOrbit
