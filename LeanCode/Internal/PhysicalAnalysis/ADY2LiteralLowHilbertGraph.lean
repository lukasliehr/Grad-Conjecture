import ADY1OriginalLowWeights

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

/-- Storage is r^-7/4 times each of the two physical low entries, in dr. -/
abbrev LowEnergyBulk (lower : ℝ) := lp (fun _ : LowAnnularIndex => CollarL2 (ComplexEuclidean 1) lower) 2
abbrev LowEnergyAmbient (lower : ℝ) := PiLp 2 (fun _ : Fin 2 => LowEnergyBulk lower)

def lowEnergyCoordinate (lower : ℝ) (coordinate : Fin 2) (index : LowAnnularIndex) :
    LowEnergyAmbient lower →L[ℂ] CollarL2 (ComplexEuclidean 1) lower :=
  (lp.evalCLM ℂ (fun _ : LowAnnularIndex => CollarL2 (ComplexEuclidean 1) lower) 2 index).comp
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => LowEnergyBulk lower) coordinate)

def lowEnergyValue (lower : ℝ) (positive : 0 < lower) (index : LowAnnularIndex) :
    LowEnergyAmbient lower →L[ℂ] CollarL2 (ComplexEuclidean 1) lower :=
  (collarScalar 1 lower (lowStorageInverse lower positive)).comp (lowEnergyCoordinate lower 0 index)

def lowEnergyDerivative (lower length : ℝ) (positive : 0 < lower) (index : LowAnnularIndex) :
    LowEnergyAmbient lower →L[ℂ] CollarL2 (ComplexEuclidean 1) lower :=
  (collarScalar 1 lower (lowMuCurve lower length positive index.2.val.2)).comp
    ((collarScalar 1 lower (lowStorageInverse lower positive)).comp (lowEnergyCoordinate lower 1 index))

/-- Literal BE18 graph, independently specified by the actual weak derivative.
No endpoint is an ambient coordinate. The low w already contains exp(Phi),
and its only storage weight is r^-7/4. -/
def lowEnergyGraph (lower length : ℝ) (positive : 0 < lower) : Submodule ℂ (LowEnergyAmbient lower) where
  carrier := {data | ∀ index, CollarWeakDerivative lower
    (lowEnergyValue lower positive index data) (lowEnergyDerivative lower length positive index data)}
  zero_mem' := by
    intro index test vector
    simp only [map_zero, neg_zero]
  add_mem' := by
    intro first second firstWeak secondWeak index test vector
    simp only [map_add, firstWeak index test vector, secondWeak index test vector, neg_add]
  smul_mem' := by
    intro scalar data weak index
    simp only [map_smul]
    exact collarWeakDerivative_complex_smul lower scalar _ _ (weak index)

theorem lowEnergyGraph_closed (lower length : ℝ) (positive : 0 < lower) :
    IsClosed (lowEnergyGraph lower length positive : Set (LowEnergyAmbient lower)) := by
  change IsClosed {data | ∀ index, ∀ test : CollarTest lower, ∀ vector : ComplexEuclidean 1,
    collarPairing lower test.value vector (lowEnergyDerivative lower length positive index data) =
      -collarPairing lower test.derivative vector (lowEnergyValue lower positive index data)}
  simp only [ofPred_forall]
  exact isClosed_iInter (fun index => isClosed_iInter (fun test => isClosed_iInter (fun vector =>
    isClosed_eq ((collarPairing lower test.value vector).continuous.comp
      (lowEnergyDerivative lower length positive index).continuous)
      (((collarPairing lower test.derivative vector).continuous.comp
        (lowEnergyValue lower positive index).continuous).neg))))

instance lowEnergyGraph_complete (lower length : ℝ) (positive : 0 < lower) :
    CompleteSpace (lowEnergyGraph lower length positive) :=
  (lowEnergyGraph_closed lower length positive).completeSpace_coe

theorem lowEnergyGraph_mem_iff (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (field : LowEnergyAmbient lower) :
    field ∈ lowEnergyGraph lower length positive ↔ ∀ index,
      CompactWeakDerivative 1 lower (lowEnergyValue lower positive index field)
        (lowEnergyDerivative lower length positive index field) := by
  change (∀ index, CollarWeakDerivative lower _ _) ↔ _
  simp_rw [compactWeak_iff_collarWeak 1 lower positive bounded]

/-- Closedness and uniqueness are independent of existence of an ODE inverse. -/
theorem lowEnergyGraph_value_injective (lower length : ℝ) (positive : 0 < lower) :
    Function.Injective (fun field : lowEnergyGraph lower length positive => field.val 0) := by
  intro first second same
  change first.val 0 = second.val 0 at same
  have derivativeSame (index : LowAnnularIndex) :
      lowEnergyDerivative lower length positive index first.val =
      lowEnergyDerivative lower length positive index second.val := by
    apply sub_eq_zero.mp
    apply collarPairing_separates lower
    intro test vector
    rw [map_sub, first.property index test vector, second.property index test vector]
    have valueSame : lowEnergyValue lower positive index first.val = lowEnergyValue lower positive index second.val := by
      change collarScalar 1 lower (lowStorageInverse lower positive) (first.val 0 index) =
        collarScalar 1 lower (lowStorageInverse lower positive) (second.val 0 index)
      rw [same]
    rw [valueSame, sub_self]
  have slopeSame : first.val 1 = second.val 1 := by
    apply lp.ext
    funext index
    apply collarScalar_injective_of_pos lower (lowStorageInverse lower positive)
      (lowPowerCurve_pos lower (7 / 4 : ℝ) positive)
    apply collarScalar_injective_of_pos lower (lowMuCurve lower length positive index.2.val.2)
      (lowMuCurve_pos lower length positive index.2.val.2)
    exact derivativeSame index
  apply Subtype.ext
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · exact same
  · exact slopeSame

theorem lowEnergyGraph_norm_sq (lower length : ℝ) (positive : 0 < lower)
    (field : lowEnergyGraph lower length positive) :
    ‖field‖ ^ 2 = ‖field.val 0‖ ^ 2 + ‖field.val 1‖ ^ 2 := by
  change ‖field.val‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]

/-- Decoding shows that the stored norm is precisely the rho dr integral. -/
theorem lowWeighted_norm_sq (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    ‖field‖ ^ 2 = ∫ radius in lower..1, radius ^ (-(7 / 2 : ℝ)) *
      ‖collarScalar 1 lower (lowStorageInverse lower positive) field radius‖ ^ 2 := by
  rw [show ‖field‖ ^ 2 = ∫ radius in Icc lower 1, ‖field radius‖ ^ 2 from radialLp_norm_sq lower field,
    intervalIntegral.integral_of_le bounded, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  have same := lowStorage_encode_decode lower positive field
  filter_upwards [collarScalar_ae 1 lower (lowStorageWeight lower positive)
      (collarScalar 1 lower (lowStorageInverse lower positive) field),
    ae_restrict_mem measurableSet_Icc] with radius encoded inside
  rw [same] at encoded
  have weightNonnegative : 0 ≤ lowStorageWeight lower positive radius :=
    (lowPowerCurve_pos lower (-(7 / 4 : ℝ)) positive radius).le
  rw [encoded, norm_smul, Real.norm_of_nonneg weightNonnegative,
    mul_pow, lowStorageWeight_sq lower positive radius inside]

theorem lowEnergyGraph_literal_norm_sq (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : lowEnergyGraph lower length positive) :
    ‖field‖ ^ 2 =
      (∑' index : LowAnnularIndex, ∫ radius in lower..1, radius ^ (-(7 / 2 : ℝ)) *
        ‖lowEnergyValue lower positive index field.val radius‖ ^ 2) +
      (∑' index : LowAnnularIndex, ∫ radius in lower..1, radius ^ (-(7 / 2 : ℝ)) *
        ‖collarScalar 1 lower (lowStorageInverse lower positive) (field.val 1 index) radius‖ ^ 2) := by
  rw [lowEnergyGraph_norm_sq]
  have first := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (field.val 0)
  have second := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (field.val 1)
  norm_num at first second
  rw [first, second]
  congr 1
  · exact tsum_congr (fun index => lowWeighted_norm_sq lower positive bounded (field.val 0 index))
  · exact tsum_congr (fun index => lowWeighted_norm_sq lower positive bounded (field.val 1 index))

end Grad.AnnularLowEnergy
