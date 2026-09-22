import ADY2LiteralLowHilbertGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace
open Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

def lowMuInverseCurve (lower length : ℝ) (positive : 0 < lower) (cell : ℤ) : C(ℝ, ℝ) :=
  ⟨fun radius => (lowMuCurve lower length positive cell radius)⁻¹,
    (lowMuCurve lower length positive cell).continuous.inv₀
      (fun radius => (lowMuCurve_pos lower length positive cell radius).ne')⟩

theorem lowMu_decode_encode (lower length : ℝ) (positive : 0 < lower) (cell : ℤ)
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower (lowMuCurve lower length positive cell)
      (collarScalar 1 lower (lowMuInverseCurve lower length positive cell) field) = field := by
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower (lowMuCurve lower length positive cell)
      (collarScalar 1 lower (lowMuInverseCurve lower length positive cell) field),
    collarScalar_ae 1 lower (lowMuInverseCurve lower length positive cell) field] with radius outer inner
  rw [outer, inner, smul_smul]
  change (lowMuCurve lower length positive cell radius * (lowMuCurve lower length positive cell radius)⁻¹) • _ = _
  rw [mul_inv_cancel₀ (lowMuCurve_pos lower length positive cell radius).ne', one_smul]

theorem lowMu_encode_decode (lower length : ℝ) (positive : 0 < lower) (cell : ℤ)
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower (lowMuInverseCurve lower length positive cell)
      (collarScalar 1 lower (lowMuCurve lower length positive cell) field) = field := by
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower (lowMuInverseCurve lower length positive cell)
      (collarScalar 1 lower (lowMuCurve lower length positive cell) field),
    collarScalar_ae 1 lower (lowMuCurve lower length positive cell) field] with radius outer inner
  rw [outer, inner, smul_smul]
  change ((lowMuCurve lower length positive cell radius)⁻¹ * lowMuCurve lower length positive cell radius) • _ = _
  rw [inv_mul_cancel₀ (lowMuCurve_pos lower length positive cell radius).ne', one_smul]

/-- The normalized slope in the exact BE18 norm is mu^-1 times the genuine derivative. -/
theorem lowEnergy_normalized_derivative (lower length : ℝ) (positive : 0 < lower)
    (field : LowEnergyAmbient lower) (index : LowAnnularIndex) :
    collarScalar 1 lower (lowMuInverseCurve lower length positive index.2.val.2)
      (lowEnergyDerivative lower length positive index field) =
      collarScalar 1 lower (lowStorageInverse lower positive) (field 1 index) :=
  lowMu_encode_decode lower length positive index.2.val.2 _

def lowEnergyRadialGraph (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) : WeightedRadialH1 1 lower :=
  compactWeakRadialGraph lower positive bounded _ _
    (collarWeak_isCompact 1 lower _ _ (field.property index))

theorem lowEnergyRadialGraph_value (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    collarH1Coordinate (ComplexEuclidean 1) lower 0
      (weightedToOrdinary 1 lower positive bounded.le (lowEnergyRadialGraph lower length positive bounded field index)) =
      lowEnergyValue lower positive index field.val := compactWeakRadialGraph_value _ _ _ _ _ _

theorem lowEnergyRadialGraph_slope (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    collarH1Coordinate (ComplexEuclidean 1) lower 1
      (weightedToOrdinary 1 lower positive bounded.le (lowEnergyRadialGraph lower length positive bounded field index)) =
      lowEnergyDerivative lower length positive index field.val := compactWeakRadialGraph_slope _ _ _ _ _ _

/-- One canonical representative on the closed interval, including both endpoints. -/
def lowEnergySection (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) : RadialContinuousSection 1 lower :=
  weightedRadialSection 1 lower positive bounded (lowEnergyRadialGraph lower length positive bounded field index)

theorem lowEnergySection_bulk (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    radialSectionL2 1 lower positive bounded.le (lowEnergySection lower length positive bounded field index) =
      lowEnergyValue lower positive index field.val := by
  unfold lowEnergySection
  rw [weightedRadialSection_bulk, lowEnergyRadialGraph_value]

theorem lowEnergySection_add (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (first second : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    lowEnergySection lower length positive bounded (first + second) index =
      lowEnergySection lower length positive bounded first index + lowEnergySection lower length positive bounded second index := by
  apply radialSectionL2_injective lower positive bounded
  rw [map_add, lowEnergySection_bulk, lowEnergySection_bulk, lowEnergySection_bulk]
  exact map_add (lowEnergyValue lower positive index) first.val second.val

theorem lowEnergySection_smul (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (scalar : ℂ) (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    lowEnergySection lower length positive bounded (scalar • field) index =
      scalar • lowEnergySection lower length positive bounded field index := by
  apply radialSectionL2_injective lower positive bounded
  rw [radialSectionL2_complex_smul, lowEnergySection_bulk, lowEnergySection_bulk]
  exact map_smul (lowEnergyValue lower positive index) scalar field.val

/-- The two natural traces are evaluations of this same representative. -/
def lowEnergyEndpoint (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (endpoint : Fin 2) (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) : ComplexEuclidean 1 :=
  lowEnergySection lower length positive bounded field index
    ⟨radialEndpointRadius lower endpoint, radialEndpointRadius_mem lower bounded.le endpoint⟩

theorem lowEnergyEndpoint_radialTrace (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (endpoint : Fin 2) (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    lowEnergyEndpoint lower length positive bounded endpoint field index =
      weightedRadialTrace 1 lower positive bounded endpoint (lowEnergyRadialGraph lower length positive bounded field index) :=
  weightedRadialSection_endpoint 1 lower positive bounded endpoint _

/-- The literal normalized incoming coefficient used in BE18. -/
def lowIncomingCoefficient (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) : ComplexEuclidean 1 :=
  (lower ^ (-(7 / 4 : ℝ)) * (Real.sqrt (lowMu length lower index.2.val.2))⁻¹) •
    lowEnergyEndpoint lower length positive bounded 0 field index

theorem lowIncomingCoefficient_norm_sq (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    ‖lowIncomingCoefficient lower length positive bounded field index‖ ^ 2 =
      lower ^ (-(7 / 2 : ℝ)) * (lowMu length lower index.2.val.2)⁻¹ *
        ‖lowEnergyEndpoint lower length positive bounded 0 field index‖ ^ 2 := by
  rw [lowIncomingCoefficient, norm_smul, Real.norm_of_nonneg (by positivity), mul_pow, mul_pow,
    inv_pow, Real.sq_sqrt (lowMu_nonneg _ _ _)]
  have weight : (lower ^ (-(7 / 4 : ℝ))) ^ 2 = lower ^ (-(7 / 2 : ℝ)) := by
    rw [pow_two, ← Real.rpow_add positive]
    norm_num
  rw [weight]

end Grad.AnnularLowEnergy
