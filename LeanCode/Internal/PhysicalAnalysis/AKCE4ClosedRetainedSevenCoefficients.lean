import AKCE3FullSourcedOuterSeven

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (field : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (smooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade) (Icc lower 1))
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field))

include allGrades in
 theorem originalComponentCurve_xCoefficient (radius : Icc lower (1 : ℝ)) (mode : ℤ×ℤ) :
    originalPhysicalComponentCurve parameters lower length positive bounded lengthPositive field 0 0 radius.val mode=
      sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0 radius mode := by
  change sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive 0 field
    (radialClamp lower bounded.le radius.val) mode=_
  rw [radialClamp_eq lower bounded.le radius.val radius.property]
  exact sameCoupledPhysicalXSection_coefficient parameters lower length positive bounded lengthPositive field allGrades 0 radius mode

include allGrades in
 theorem originalComponentCurve_xiCoefficient (radius : Icc lower (1 : ℝ)) (mode : ℤ×ℤ) :
    originalPhysicalComponentCurve parameters lower length positive bounded lengthPositive field 1 0 radius.val mode=
      sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0 radius mode := by
  change sameCoupledPhysicalXiSection parameters lower length positive bounded lengthPositive 0 field
    (radialClamp lower bounded.le radius.val) mode=_
  rw [radialClamp_eq lower bounded.le radius.val radius.property]
  exact sameCoupledPhysicalXiSection_coefficient parameters lower length positive bounded lengthPositive field allGrades 0 radius mode

include allGrades smooth in
/-- Exact first-four physical coefficients extend to the closed outer endpoint by their SAME continuous representatives. -/
theorem fullSeven_firstFour_closed (radius : ℝ) (inside : radius∈Icc lower 1) (mode : ℤ×ℤ) (slot : Fin 4) :
    matrixUnit (0 : Fin 1) (slot.castLE (by omega : 4≤7)) (seven.physicalCurve 0 radius mode)=
      if slot=0 then sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0 ⟨radius,inside⟩ mode
      else if slot=1 then (radius : ℂ)⁻¹ • (frequencyNumerator (some false) mode •
        sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0 ⟨radius,inside⟩ mode)
      else if slot=2 then frequencyNumerator (some true) mode •
        sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0 ⟨radius,inside⟩ mode
      else (radius : ℂ)⁻¹ • sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0 ⟨radius,inside⟩ mode := by
  let x := fun location => originalPhysicalComponentCurve parameters lower length positive bounded lengthPositive field 0 0 location mode
  let xi := fun location => originalPhysicalComponentCurve parameters lower length positive bounded lengthPositive field 1 0 location mode
  let rhs := fun location : ℝ => if slot=0 then x location else if slot=1 then
    (location : ℂ)⁻¹ • (frequencyNumerator (some false) mode • xi location)
    else if slot=2 then frequencyNumerator (some true) mode • xi location else (location : ℂ)⁻¹ • xi location
  have xContinuous : ContinuousOn x (Icc lower 1) :=
    (lp.evalCLM ℂ (fun _ : ℤ×ℤ => ComplexEuclidean 1) 2 mode).continuous.comp_continuousOn
      (originalPhysicalComponentCurve_smooth parameters lower length positive bounded lengthPositive field allGrades smooth 0 0).continuousOn
  have xiContinuous : ContinuousOn xi (Icc lower 1) :=
    (lp.evalCLM ℂ (fun _ : ℤ×ℤ => ComplexEuclidean 1) 2 mode).continuous.comp_continuousOn
      (originalPhysicalComponentCurve_smooth parameters lower length positive bounded lengthPositive field allGrades smooth 1 0).continuousOn
  have reciprocal : ContinuousOn (fun location : ℝ => (location : ℂ)⁻¹) (Icc lower 1) :=
    Complex.continuous_ofReal.continuousOn.inv₀
      (fun location member => Complex.ofReal_ne_zero.mpr (positive.trans_le member.1).ne')
  have rhsContinuous : ContinuousOn rhs (Icc lower 1) := by
    dsimp only [rhs]
    split_ifs
    · exact xContinuous
    · exact reciprocal.smul ((continuousOn_const : ContinuousOn (fun _ : ℝ => frequencyNumerator (some false) mode) (Icc lower 1)).smul xiContinuous)
    · exact (continuousOn_const : ContinuousOn (fun _ : ℝ => frequencyNumerator (some true) mode) (Icc lower 1)).smul xiContinuous
    · exact reciprocal.smul xiContinuous
  have same : matrixUnit (0 : Fin 1) (slot.castLE (by omega : 4≤7)) (seven.physicalCurve 0 radius mode)=rhs radius := by
    apply collarCurve_eq_of_ae lower bounded _ _
      ((matrixUnit (0 : Fin 1) (slot.castLE (by omega : 4≤7))).continuous.comp_continuousOn
        ((lp.evalCLM ℂ (fun _ : ℤ×ℤ => ComplexEuclidean 7) 2 mode).continuous.comp_continuousOn
          (seven.physicalCurve_smooth bounded 0).continuousOn)) rhsContinuous _ inside
    filter_upwards [seven.physicalCurve_actual bounded 0,
      fullStrongSevenInput_firstFour_physical parameters lower length positive bounded lengthPositive data field,
      ae_restrict_mem measurableSet_Icc] with location represented actual member
    change matrixUnit (0 : Fin 1) (slot.castLE (by omega : 4≤7)) (seven.physicalCurve 0 location mode)=rhs location
    rw [represented mode]
    simp only [pow_zero,one_smul]
    have coefficient := actual mode slot
    rw [radialClamp_eq lower bounded.le location member] at coefficient
    rw [← originalComponentCurve_xCoefficient parameters lower length positive bounded lengthPositive field allGrades ⟨location,member⟩ mode,
      ← originalComponentCurve_xiCoefficient parameters lower length positive bounded lengthPositive field allGrades ⟨location,member⟩ mode] at coefficient
    exact coefficient
  rw [same]
  dsimp only [rhs,x,xi]
  rw [originalComponentCurve_xCoefficient parameters lower length positive bounded lengthPositive field allGrades ⟨radius,inside⟩ mode,
    originalComponentCurve_xiCoefficient parameters lower length positive bounded lengthPositive field allGrades ⟨radius,inside⟩ mode]

end Grad.OriginalCoreRealization
