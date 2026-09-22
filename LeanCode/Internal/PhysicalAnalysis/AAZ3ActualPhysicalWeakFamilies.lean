import AAZ2LiteralRawGrade

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRadialJets
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The weight is removed BEFORE testing the physical derivative. The
stored next coordinate is therefore exp(Phi) times the physical derivative,
not a derivative of the phase-conjugated unknown. -/
def AnnularPhysicalWeakDerivative (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (value derivative : AnnularRawFamily lower) : Prop :=
  ∀ mode, CompactWeakDerivative 1 lower
    (annularDecodeMode parameters lower positive mode (value mode))
    (annularDecodeMode parameters lower positive mode (derivative mode))

def annularRawRadiusPower (lower : ℝ) (positive : 0 < lower) (order : ℕ)
    (field : AnnularRawFamily lower) : AnnularRawFamily lower :=
  fun mode => annularRadiusPower lower positive order (field mode)

def annularRawSymbol (lower : ℝ) (symbol : HighAnnularMode → ℂ)
    (field : AnnularRawFamily lower) : AnnularRawFamily lower := fun mode => symbol mode • field mode

theorem annularRadiusInverse_decode (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (field : RadialL2 1 lower) :
    annularDecodeMode parameters lower positive mode (annularRadiusInverse lower positive field) =
      annularRadiusInverse lower positive (annularDecodeMode parameters lower positive mode field) := by
  change collarScalar 1 lower (annularInversePhase parameters mode.val.2)
    (radialOrdinary 1 lower positive (collarScalar 1 lower (annularInverseRadiusCurve lower positive) field)) = _
  rw [radialOrdinary_collarScalar, collarScalar_comm]
  rfl

theorem annularRadiusPower_decode (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (order : ℕ) (field : RadialL2 1 lower) :
    annularDecodeMode parameters lower positive mode (annularRadiusPower lower positive order field) =
      annularRadiusPower lower positive order (annularDecodeMode parameters lower positive mode field) := by
  induction order with
  | zero => rfl
  | succ order previous =>
    change annularDecodeMode parameters lower positive mode (annularRadiusInverse lower positive _) =
      annularRadiusInverse lower positive _
    exact (annularRadiusInverse_decode parameters lower positive mode _).trans
      (congrArg (annularRadiusInverse lower positive) previous)

theorem annularPhysicalWeak_zero (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) :
    AnnularPhysicalWeakDerivative parameters lower positive 0 0 := by
  intro mode test smooth compact supported vector
  simp only [Pi.zero_apply, map_zero, neg_zero]

theorem annularPhysicalWeak_add (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (first firstSlope second secondSlope : AnnularRawFamily lower)
    (firstWeak : AnnularPhysicalWeakDerivative parameters lower positive first firstSlope)
    (secondWeak : AnnularPhysicalWeakDerivative parameters lower positive second secondSlope) :
    AnnularPhysicalWeakDerivative parameters lower positive (first + second) (firstSlope + secondSlope) := by
  intro mode test smooth compact supported vector
  simp only [Pi.add_apply, map_add, firstWeak mode test smooth compact supported vector,
    secondWeak mode test smooth compact supported vector, neg_add]

theorem annularPhysicalWeak_symbol (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (symbol : HighAnnularMode → ℂ) (value derivative : AnnularRawFamily lower)
    (weak : AnnularPhysicalWeakDerivative parameters lower positive value derivative) :
    AnnularPhysicalWeakDerivative parameters lower positive
      (annularRawSymbol lower symbol value) (annularRawSymbol lower symbol derivative) := by
  intro mode test smooth compact supported vector
  change collarPairing lower _ vector (annularDecodeMode parameters lower positive mode (symbol mode • derivative mode)) =
    -collarPairing lower _ vector (annularDecodeMode parameters lower positive mode (symbol mode • value mode))
  rw [(annularDecodeMode parameters lower positive mode).map_smul (symbol mode) (derivative mode),
    (annularDecodeMode parameters lower positive mode).map_smul (symbol mode) (value mode),
    collarPairing_complex_smul, collarPairing_complex_smul,
    weak mode test smooth compact supported vector, mul_neg]

theorem annularPhysicalWeak_radiusPower (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (order : ℕ) (value derivative : AnnularRawFamily lower)
    (weak : AnnularPhysicalWeakDerivative parameters lower positive value derivative) :
    AnnularPhysicalWeakDerivative parameters lower positive (annularRawRadiusPower lower positive order value)
      (annularRawRadiusPower lower positive order derivative -
        (order : ℝ) • annularRawRadiusPower lower positive (order + 1) value) := by
  intro mode
  change CompactWeakDerivative 1 lower
    (annularDecodeMode parameters lower positive mode (annularRadiusPower lower positive order (value mode)))
    (annularDecodeMode parameters lower positive mode
      (annularRadiusPower lower positive order (derivative mode) -
        (order : ℝ) • annularRadiusPower lower positive (order + 1) (value mode)))
  rw [map_sub, (annularDecodeMode parameters lower positive mode).map_smul_of_tower,
    annularRadiusPower_decode, annularRadiusPower_decode, annularRadiusPower_decode]
  exact annularRadiusPower_weak lower positive order _ _ (weak mode)

end Grad.AnnularRadialJets
