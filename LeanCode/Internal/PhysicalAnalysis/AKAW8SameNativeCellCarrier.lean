import AKAW7SameWeightedCartesianCells

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.ActualNativeCellMoments
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.ActualPuncturedFamily Grad.AnnularRestriction Grad.AnnularCurrentLow
open Grad.ActualCartesianDescent Grad.ActualCartesianIntegrability Grad.CartesianStartup Grad.GenericCarriers

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow dimension (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second)=rows first)
include compatible

theorem sameWeightedCartesianCell_energy (grade : ℕ) :
    (∫⁻ point in openUnitDisk, ∑' cell : ℤ, ENNReal.ofReal
      (‖sameWeightedCartesianCell parameters lower positive bounded cofinal rows curves grade cell point‖ ^ 2)) ≤
        ENNReal.ofReal (2 * Real.pi) *
          ∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal
            (‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves grade radius‖ ^ 2) := by
  apply fullCell_disk_energy _ _
    ((gluedWeightedFamilyCurve_continuous parameters lower positive bounded cofinal decreasing rows curves compatible grade).aestronglyMeasurable measurableSet_Ioc)
    (sameWeightedCartesianCell_polar_aestronglyMeasurable parameters lower positive bounded cofinal decreasing rows curves compatible grade)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius inside
    intro cell
    exact sameWeightedCartesianCell_continuousSlices parameters lower positive bounded cofinal decreasing rows curves compatible grade cell radius inside
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius inside
    exact sameWeightedCartesianCell_coefficient_bound parameters lower positive bounded cofinal decreasing rows curves compatible grade radius inside

theorem sameWeightedCartesianCell_finite (grade : ℕ)
    (finite : (∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal
      (‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves grade radius‖ ^ 2)) < ⊤) :
    (∫⁻ point in openUnitDisk, ∑' cell : ℤ, ENNReal.ofReal
      (‖sameWeightedCartesianCell parameters lower positive bounded cofinal rows curves grade cell point‖ ^ 2)) < ⊤ :=
  (sameWeightedCartesianCell_energy parameters lower positive bounded cofinal decreasing rows curves compatible grade).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top finite)

/-- The genuine all-integer-cell L2 carrier at the original analytic width. -/
def sameNativeCellField (grade : ℕ)
    (finite : (∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal
      (‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves grade radius‖ ^ 2)) < ⊤) : StartupL2 dimension :=
  (jointCellRepresentative_memLp (volume.restrict openUnitDisk)
    (sameWeightedCartesianCell parameters lower positive bounded cofinal rows curves grade)
    (sameWeightedCartesianCell_aestronglyMeasurable parameters lower positive bounded cofinal decreasing rows curves compatible grade)
    (sameWeightedCartesianCell_finite parameters lower positive bounded cofinal decreasing rows curves compatible grade finite)).toLp _

theorem sameNativeCellField_same (grade : ℕ)
    (finite : (∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal
      (‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves grade radius‖ ^ 2)) < ⊤) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell,
      sameNativeCellField parameters lower positive bounded cofinal decreasing rows curves compatible grade finite point cell =
        cellFrequency cell ^ grade • (cartesianWeight parameters cell point •
          gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell point) := by
  let field := sameWeightedCartesianCell parameters lower positive bounded cofinal rows curves grade
  have measurable := sameWeightedCartesianCell_aestronglyMeasurable parameters lower positive bounded cofinal decreasing rows curves compatible grade
  have energy := sameWeightedCartesianCell_finite parameters lower positive bounded cofinal decreasing rows curves compatible grade finite
  have membership := jointCellRepresentative_memLp (volume.restrict openUnitDisk) field measurable energy
  filter_upwards [membership.coeFn_toLp,finiteCellEnergy_ae_memlp (volume.restrict openUnitDisk) field measurable energy] with point same member
  intro cell
  exact (congrArg (fun value : CellValues dimension => value cell) same).trans
    (jointCellRepresentative_same field point member cell)

theorem sameNativeCellField_normSquare (grade : ℕ)
    (finite : (∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal
      (‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves grade radius‖ ^ 2)) < ⊤) :
    ENNReal.ofReal (‖sameNativeCellField parameters lower positive bounded cofinal decreasing rows curves compatible grade finite‖ ^ 2) =
      ∫⁻ point in openUnitDisk, ∑' cell : ℤ, ENNReal.ofReal
        (‖sameWeightedCartesianCell parameters lower positive bounded cofinal rows curves grade cell point‖ ^ 2) := by
  let value := sameNativeCellField parameters lower positive bounded cofinal decreasing rows curves compatible grade finite
  have measurable := sameWeightedCartesianCell_aestronglyMeasurable parameters lower positive bounded cofinal decreasing rows curves compatible grade
  have energy := sameWeightedCartesianCell_finite parameters lower positive bounded cofinal decreasing rows curves compatible grade finite
  have membership := jointCellRepresentative_memLp (volume.restrict openUnitDisk)
    (sameWeightedCartesianCell parameters lower positive bounded cofinal rows curves grade) measurable energy
  rw [domainL2_norm_sq openUnitDisk value]
  rw [ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable value)).mp (Lp.memLp value))
    (Eventually.of_forall (fun _ => sq_nonneg _))]
  calc
    _ = ∫⁻ point in openUnitDisk, ENNReal.ofReal (‖jointCellRepresentative
      (sameWeightedCartesianCell parameters lower positive bounded cofinal rows curves grade) point‖ ^ 2) :=
      lintegral_congr_ae (membership.coeFn_toLp.fun_comp (fun value => ENNReal.ofReal (‖value‖ ^ 2)))
    _ = _ := jointCellRepresentative_energy (volume.restrict openUnitDisk) _ measurable energy

end Grad.ActualNativeCellMoments
