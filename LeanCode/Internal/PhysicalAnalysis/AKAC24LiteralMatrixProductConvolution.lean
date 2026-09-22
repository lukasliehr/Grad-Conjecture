import AKAC23LiteralMatrixFourierSynthesis

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceCollarRestriction
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryLift Grad.PhaseAlgebra Grad.ActualPhysicalField
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Allocation
open Grad.BoundaryKernelAction

local instance matrixProductPeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

variable {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (row : Fin output) (column : Fin input)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
include coherent

def physicalMatrixAngleEntry (angles : ℝ × ℝ) : ℂ :=
  familyMatrix family 0 angles.2 (polarClosedPoint radius angles.1 nonnegative bounded) row column

theorem physicalMatrixAngleEntry_eq_tsum (angles : ℝ × ℝ) :
    physicalMatrixAngleEntry parameters family row column radius nonnegative bounded angles =
      ∑' mode : ℤ × ℤ, cellExponential mode.2 angles.2 *
        (cellExponential mode.1 angles.1 * physicalMatrixScalar parameters family coherent row column 0 radius mode) :=
  (physicalMatrixScalar_double_hasSum parameters family coherent row column radius nonnegative bounded angles.1 angles.2).tsum_eq.symm

theorem physicalMatrixAngleEntry_continuous :
    Continuous (physicalMatrixAngleEntry parameters family row column radius nonnegative bounded) := by
  simp_rw [show physicalMatrixAngleEntry parameters family row column radius nonnegative bounded =
    (fun angles => ∑' mode : ℤ × ℤ, cellExponential mode.2 angles.2 *
      (cellExponential mode.1 angles.1 * physicalMatrixScalar parameters family coherent row column 0 radius mode)) from
    funext (physicalMatrixAngleEntry_eq_tsum parameters family coherent row column radius nonnegative bounded)]
  apply continuous_tsum
    (fun mode : ℤ × ℤ => ((cellExponential_smooth mode.2).continuous.comp continuous_snd).mul
      (((cellExponential_smooth mode.1).continuous.comp continuous_fst).mul continuous_const))
    (physicalMatrixScalar_norm_summable parameters family coherent row column radius nonnegative bounded)
  intro mode angles
  change ‖cellExponential mode.2 angles.2 * (cellExponential mode.1 angles.1 *
    physicalMatrixScalar parameters family coherent row column 0 radius mode)‖ ≤ _
  simp only [norm_mul,cellExponential_norm,one_mul,le_refl]

theorem physicalMatrixAngleEntry_periodic (angles : ℝ × ℝ) :
    physicalMatrixAngleEntry parameters family row column radius nonnegative bounded (angles.1+2*Real.pi,angles.2) =
      physicalMatrixAngleEntry parameters family row column radius nonnegative bounded angles ∧
    physicalMatrixAngleEntry parameters family row column radius nonnegative bounded (angles.1,angles.2+2*Real.pi) =
      physicalMatrixAngleEntry parameters family row column radius nonnegative bounded angles := by
  constructor <;> rw [physicalMatrixAngleEntry_eq_tsum parameters family coherent,
    physicalMatrixAngleEntry_eq_tsum parameters family coherent] <;>
    apply tsum_congr <;> intro mode <;> simp only [← cellCharacter_coe,AddCircle.coe_add_period]

theorem physicalMatrixScalar_product_hasSum {dimension : ℕ}
    (source : ℝ × ℝ → ComplexEuclidean dimension) (continuousSource : Continuous source) (mode : ℤ × ℤ) :
    HasSum (fun shift => physicalMatrixScalar parameters family coherent row column 0 radius shift •
      doubleCoefficient source (twoFrequencyTranslation shift mode))
      (doubleCoefficient (fun angles => physicalMatrixAngleEntry parameters family row column radius nonnegative bounded angles • source angles) mode) := by
  obtain ⟨bound, dominated⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (s := Icc (-Real.pi) Real.pi ×ˢ Icc (-Real.pi) Real.pi) continuousSource.continuousOn
  exact doubleCoefficient_series_product
    (physicalMatrixScalar parameters family coherent row column 0 radius)
    (physicalMatrixScalar_norm_summable parameters family coherent row column radius nonnegative bounded)
    (physicalMatrixAngleEntry parameters family row column radius nonnegative bounded) source
    (fun cell polar => angularCoefficient (fun axial => source (polar,axial)) cell)
    (fun polar => continuousSource.comp (continuous_const.prodMk continuous_id))
    (fun cell => Grad.SourceCollarFullSource.angularCoefficient_continuous_parameter source continuousSource cell)
    (fun _ _ => rfl) (max bound 0) (le_max_right _ _)
    (fun polar polarInside axial axialInside => (dominated (polar,axial) ⟨polarInside,axialInside⟩).trans (le_max_left _ _))
    (fun polar _ axial _ => physicalMatrixScalar_double_hasSum parameters family coherent row column radius nonnegative bounded polar axial) mode

omit coherent in
theorem doubleCoefficient_finset_sum {Index : Type*} {dimension : ℕ} (indices : Finset Index)
    (field : Index → ℝ × ℝ → ComplexEuclidean dimension) (continuousField : ∀ index,Continuous (field index))
    (mode : ℤ × ℤ) :
    doubleCoefficient (fun angles => ∑ index ∈ indices,field index angles) mode =
      ∑ index ∈ indices,doubleCoefficient (field index) mode := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp [doubleCoefficient,angularCoefficient_constant]
  | @insert index indices absent induction =>
    simp only [Finset.sum_insert absent]
    rw [doubleCoefficient_add _ _ (continuousField index) (continuous_finsetSum _ (fun i _ => continuousField i)),induction]

def physicalMatrixProduct (source : ℝ × ℝ → ComplexEuclidean input) (angles : ℝ × ℝ) : ComplexEuclidean output :=
  ∑ row : Fin output, ∑ column : Fin input,
    physicalMatrixAngleEntry parameters family row column radius nonnegative bounded angles • matrixUnit row column (source angles)

theorem physicalMatrixProduct_continuous (source : ℝ × ℝ → ComplexEuclidean input) (continuousSource : Continuous source) :
    Continuous (physicalMatrixProduct parameters family radius nonnegative bounded source) :=
  continuous_finsetSum _ (fun row _ => continuous_finsetSum _ (fun column _ =>
    (physicalMatrixAngleEntry_continuous parameters family coherent row column radius nonnegative bounded).smul
      ((matrixUnit row column).continuous.comp continuousSource)))

theorem physicalMatrixProduct_hasSum (source : ℝ × ℝ → ComplexEuclidean input)
    (continuousSource : Continuous source) (mode : ℤ × ℤ) :
    HasSum (fun shift => matrixMultiplicationEntry input output
      (fun row column => physicalMatrixScalar parameters family coherent row column 0 radius)
      shift (twoFrequencyTranslation shift mode) (doubleCoefficient source (twoFrequencyTranslation shift mode)))
      (doubleCoefficient (physicalMatrixProduct parameters family radius nonnegative bounded source) mode) := by
  have each (row : Fin output) (column : Fin input) := physicalMatrixScalar_product_hasSum parameters family coherent
    row column radius nonnegative bounded (fun angles => matrixUnit row column (source angles))
    ((matrixUnit row column).continuous.comp continuousSource) mode
  have summed := hasSum_sum (s := Finset.univ) (fun row (_ : row ∈ (Finset.univ : Finset (Fin output))) =>
    hasSum_sum (s := Finset.univ) (fun column (_ : column ∈ (Finset.univ : Finset (Fin input))) => each row column))
  have coefficients (shift : ℤ × ℤ) :
      (∑ row : Fin output,∑ column : Fin input,physicalMatrixScalar parameters family coherent row column 0 radius shift •
        doubleCoefficient (fun angles => matrixUnit row column (source angles)) (twoFrequencyTranslation shift mode)) =
      matrixMultiplicationEntry input output (fun row column => physicalMatrixScalar parameters family coherent row column 0 radius)
        shift (twoFrequencyTranslation shift mode) (doubleCoefficient source (twoFrequencyTranslation shift mode)) := by
    simp only [doubleCoefficient_valueMap _ source continuousSource,matrixMultiplicationEntry,sum_apply,smul_apply]
  have limits : (∑ row : Fin output,∑ column : Fin input,doubleCoefficient
      (fun angles => physicalMatrixAngleEntry parameters family row column radius nonnegative bounded angles • matrixUnit row column (source angles)) mode) =
      doubleCoefficient (physicalMatrixProduct parameters family radius nonnegative bounded source) mode := by
    unfold physicalMatrixProduct
    rw [doubleCoefficient_finset_sum]
    apply Finset.sum_congr rfl
    intro row _
    rw [doubleCoefficient_finset_sum]
    · intro column
      exact (physicalMatrixAngleEntry_continuous parameters family coherent row column radius nonnegative bounded).smul
        ((matrixUnit row column).continuous.comp continuousSource)
    · intro row
      exact continuous_finsetSum _ (fun column _ =>
        (physicalMatrixAngleEntry_continuous parameters family coherent row column radius nonnegative bounded).smul
          ((matrixUnit row column).continuous.comp continuousSource))
  rw [limits] at summed
  exact summed.congr_fun (fun shift => (coefficients shift).symm)

end Grad.ActualSmoothPhysicalField
