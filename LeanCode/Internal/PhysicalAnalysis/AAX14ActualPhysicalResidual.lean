import AAX5NaturalWeakBoundary

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFourSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.AnnularGrades Grad.AnnularConverse
open Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem annularAngularDecode_angularP (lower : ℝ) (q : AnnularBulk lower) :
    annularAngularDecode lower (annularAngularPMap lower q) = annularPMap lower q := by
  apply lp.ext
  funext mode
  rw [annularAngularDecode_apply]
  change (((annularAngularWeight mode)⁻¹ : ℝ) : ℂ) •
    ((annularAngularWeight mode : ℂ) • (-(annularDSymbol mode)⁻¹ • q mode)) =
      -(annularDSymbol mode)⁻¹ • q mode
  rw [smul_smul, Complex.ofReal_inv,
    inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (annularAngularWeight_pos mode).ne'), one_smul]

section Physical
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
local notation "FG" => annularFourGraph parameters lower length positive lengthPositive widthHalf widthLength

theorem annularFourP_recovered (data : AnnularFourAmbient lower length positive) :
    annularAngularDecode lower (annularFourP lower length positive data) =
      annularRecoveredP parameters lower length positive lengthPositive widthHalf widthLength
        (annularFourW lower length positive data)
        (annularFourF parameters lower length positive lengthPositive widthHalf widthLength data) :=
  (congrArg (annularAngularDecode lower)
    (annularFour_recoveredAngularP parameters lower length positive lengthPositive widthHalf widthLength data)).symm.trans
    (annularAngularDecode_angularP lower _)

/-- The actual original physical p, removing precisely the stored sqrt(r),
curved phase and one angular weight. -/
def annularFourPhysicalP (data : AnnularFourAmbient lower length positive) (mode : HighAnnularMode) :
    CollarL2 (ComplexEuclidean 1) lower :=
  annularDecodeMode parameters lower positive mode
    (annularAngularDecode lower (annularFourP lower length positive data) mode)

theorem annularFourPhysicalP_recovered (data : AnnularFourAmbient lower length positive) (mode : HighAnnularMode) :
    annularFourPhysicalP parameters lower length positive data mode =
      annularPhysicalP parameters lower length positive lengthPositive widthHalf widthLength
        (annularFourW lower length positive data)
        (annularFourF parameters lower length positive lengthPositive widthHalf widthLength data) mode :=
  congrArg (fun field : AnnularBulk lower => annularDecodeMode parameters lower positive mode (field mode))
    (annularFourP_recovered parameters lower length positive lengthPositive widthHalf widthLength data)

/-- Actual weak derivative of the stored physical p on every element of the
independent closed graph, obtained from the already proved converse. -/
theorem annularFourPhysicalP_weak (data : FG) (mode : HighAnnularMode) :
    CollarWeakDerivative lower
      (annularFourPhysicalP parameters lower length positive data.val mode)
      (annularPhysicalPSlope parameters lower length positive lengthPositive widthHalf widthLength bounded.le
        (annularFourW lower length positive data.val)
        (annularFourZeroBetaForcing parameters lower length positive lengthPositive widthHalf widthLength data.val) mode) := by
  let source := (annularFourNaturalData parameters lower length positive bounded lengthPositive widthHalf widthLength data).val.2
  let innerValue := annularEnergyTrace lower length positive bounded lengthPositive 0 (annularFourW lower length positive data.val)
  have equality := annularFourGraph_energy_unique parameters lower length positive bounded lengthPositive widthHalf widthLength data
  have actual := annularPhysicalP_weak parameters lower length positive lengthPositive widthHalf widthLength bounded source innerValue mode
  have atState := (congrArg (fun w : annularEnergySpace lower length positive =>
    CollarWeakDerivative lower
      (annularPhysicalP parameters lower length positive lengthPositive widthHalf widthLength w source.1 mode)
      (annularPhysicalPSlope parameters lower length positive lengthPositive widthHalf widthLength bounded.le w source mode)) equality).mpr actual
  exact (congrArg (fun p : CollarL2 (ComplexEuclidean 1) lower =>
    CollarWeakDerivative lower p
      (annularPhysicalPSlope parameters lower length positive lengthPositive widthHalf widthLength bounded.le
        (annularFourW lower length positive data.val) source mode))
    (annularFourPhysicalP_recovered parameters lower length positive lengthPositive widthHalf widthLength data.val mode)).mpr atState

/-- The graph's G3 coordinate is exactly the original physical second
residual p_r-p/r-i(m/r²+n²/(mL²))xi-n/(mL)F2. The preceding theorem proves
that the displayed p_r is its genuine weak derivative. -/
theorem annularFourPhysical_second_residual (data : FG) (mode : HighAnnularMode) :
    annularPhysicalPSlope parameters lower length positive lengthPositive widthHalf widthLength bounded.le
        (annularFourW lower length positive data.val)
        (annularFourZeroBetaForcing parameters lower length positive lengthPositive widthHalf widthLength data.val) mode -
      collarScalar 1 lower (annularInverseRadiusCurve lower positive)
        (annularFourPhysicalP parameters lower length positive data.val mode) -
      Complex.I • collarScalar 1 lower (annularSecondRealCurve lower length positive mode)
        (annularPhysicalValue parameters lower length positive bounded.le mode (annularFourW lower length positive data.val)) =
      annularDecodeMode parameters lower positive mode (annularAngularDecode lower (annularFourG lower length positive data.val) mode) +
        (((mode.val.2 : ℝ) / ((mode.val.1 : ℝ) * length) : ℝ) : ℂ) •
          annularDecodeMode parameters lower positive mode (annularFourF2 lower length positive data.val mode) := by
  let w := annularFourW lower length positive data.val
  let source := annularFourZeroBetaForcing parameters lower length positive lengthPositive widthHalf widthLength data.val
  have p := annularFourPhysicalP_recovered parameters lower length positive lengthPositive widthHalf widthLength data.val mode
  exact (congrArg (fun value : CollarL2 (ComplexEuclidean 1) lower =>
    annularPhysicalPSlope parameters lower length positive lengthPositive widthHalf widthLength bounded.le w source mode -
      collarScalar 1 lower (annularInverseRadiusCurve lower positive) value -
      Complex.I • collarScalar 1 lower (annularSecondRealCurve lower length positive mode)
        (annularPhysicalValue parameters lower length positive bounded.le mode w)) p).trans
    (annularOriginal_second_row parameters lower length positive bounded.le lengthPositive widthHalf widthLength w source mode)

end Physical
end Grad.AnnularFourSource
