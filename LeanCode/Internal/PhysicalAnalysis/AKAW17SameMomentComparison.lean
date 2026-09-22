import AKAW8SameNativeCellCarrier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.ActualNativeCellMoments
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.ActualPuncturedFamily Grad.AnnularRestriction Grad.AnnularCurrentLow
open Grad.ActualCartesianDescent Grad.ActualCartesianIntegrability Grad.CartesianStartup Grad.GenericCarriers
open Grad.AnnularWeightedSmoothness

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow dimension (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second)=rows first)
include compatible bounded

theorem sameConjugatedCurve_grade_norm_le (first second : ℕ) (ordered : first ≤ second)
    (radius : ℝ) (inside : radius ∈ Ioc (0 : ℝ) 1) :
    ‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves first radius‖ ≤
      ‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves second radius‖ := by
  let index := selectedInnerCollar lower cofinal radius inside.1
  have localInside : radius ∈ Icc (lower index) 1 := ⟨(selectedInnerCollar_lt lower cofinal radius inside.1).le,inside.2⟩
  rw [gluedWeightedFamilyCurve_same parameters lower positive bounded cofinal decreasing rows curves compatible first index radius localInside,
    gluedWeightedFamilyCurve_same parameters lower positive bounded cofinal decreasing rows curves compatible second index radius localInside]
  have reserve : hilbertReserve parameters dimension (second-first) ((curves index).curve second radius) = (curves index).curve first radius := by
    apply hilbertReserve_same
    intro mode
    have same := (curves index).shift (bounded index) first (second-first) radius localInside mode
    simpa only [Nat.add_sub_of_le ordered] using same
  rw [← reserve]
  exact ((hilbertReserve parameters dimension (second-first)).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (hilbertReserve_norm_le parameters dimension (second-first)) (norm_nonneg _)).trans_eq (one_mul _))

theorem sameConjugatedCurve_grade_energy_le (first second : ℕ) (ordered : first ≤ second) :
    (∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal (‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves first radius‖ ^ 2)) ≤
      ∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal (‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves second radius‖ ^ 2) := by
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius inside
  exact ENNReal.ofReal_le_ofReal ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (sameConjugatedCurve_grade_norm_le parameters lower positive bounded cofinal decreasing rows curves compatible first second ordered radius inside))

theorem sameNativeCellField_moment (grade : ℕ)
    (finiteZero : (∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal (‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves 0 radius‖ ^ 2)) < ⊤)
    (finiteGrade : (∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal (‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves grade radius‖ ^ 2)) < ⊤) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell,
      sameNativeCellField parameters lower positive bounded cofinal decreasing rows curves compatible grade finiteGrade point cell =
        cellFrequency cell ^ grade •
          sameNativeCellField parameters lower positive bounded cofinal decreasing rows curves compatible 0 finiteZero point cell := by
  filter_upwards [sameNativeCellField_same parameters lower positive bounded cofinal decreasing rows curves compatible grade finiteGrade,
    sameNativeCellField_same parameters lower positive bounded cofinal decreasing rows curves compatible 0 finiteZero] with point high low
  intro cell
  rw [high cell,low cell,pow_zero,one_smul]

/-- One higher native grade pays every lower physical cell moment. -/
theorem sameNativeCellField_higherEnergy (grade paid : ℕ) (ordered : grade ≤ paid)
    (finite : (∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal (‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves grade radius‖ ^ 2)) < ⊤)
    (constant : ℝ)
    (bound : (∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal (‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves paid radius‖ ^ 2)) ≤ ENNReal.ofReal (constant ^ 2)) :
    ENNReal.ofReal (‖sameNativeCellField parameters lower positive bounded cofinal decreasing rows curves compatible grade finite‖ ^ 2) ≤
      ENNReal.ofReal ((2 * Real.pi) * constant ^ 2) := by
  rw [sameNativeCellField_normSquare parameters lower positive bounded cofinal decreasing rows curves compatible grade finite]
  apply (sameWeightedCartesianCell_energy parameters lower positive bounded cofinal decreasing rows curves compatible grade).trans
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2*Real.pi)]
  gcongr
  exact (sameConjugatedCurve_grade_energy_le parameters lower positive bounded cofinal decreasing rows curves compatible grade paid ordered).trans bound

end Grad.ActualNativeCellMoments
