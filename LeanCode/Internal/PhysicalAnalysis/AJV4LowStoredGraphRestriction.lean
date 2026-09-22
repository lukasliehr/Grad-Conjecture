import AJV3RestrictionScalarAndFourierMaps

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped BigOperators
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CircularHighRegularity Grad.AnnularVariational
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularLowEnergy

def lowAmbientRestrictionLinear (lower upper : ℝ) (included : lower ≤ upper) :
    LowEnergyAmbient lower →ₗ[ℂ] LowEnergyAmbient upper where
  toFun field := WithLp.toLp 2 (fun slot : Fin 2 => collarBulkRestriction LowAnnularIndex 1 lower upper included (field slot))
  map_add' first second := by
    apply PiLp.ext
    intro slot
    change collarBulkRestriction LowAnnularIndex 1 lower upper included (first slot + second slot) = _
    exact map_add _ _ _
  map_smul' scalar field := by
    apply PiLp.ext
    intro slot
    change collarBulkRestriction LowAnnularIndex 1 lower upper included (scalar • field slot) = _
    exact map_smul _ _ _

theorem lowAmbientRestrictionLinear_bound (lower upper : ℝ) (included : lower ≤ upper)
    (field : LowEnergyAmbient lower) : ‖lowAmbientRestrictionLinear lower upper included field‖ ≤ ‖field‖ := by
  let output := lowAmbientRestrictionLinear lower upper included field
  have first := collarBulkRestriction_bound LowAnnularIndex 1 lower upper included (field 0)
  have second := collarBulkRestriction_bound LowAnnularIndex 1 lower upper included (field 1)
  change ‖output 0‖ ≤ ‖field 0‖ at first
  change ‖output 1‖ ≤ ‖field 1‖ at second
  have firstSq := (sq_le_sq₀ (norm_nonneg (output 0)) (norm_nonneg (field 0))).mpr first
  have secondSq := (sq_le_sq₀ (norm_nonneg (output 1)) (norm_nonneg (field 1))).mpr second
  have inputNorm : ‖field‖ ^ 2 = ‖field 0‖ ^ 2 + ‖field 1‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  have outputNorm : ‖output‖ ^ 2 = ‖output 0‖ ^ 2 + ‖output 1‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  change ‖output‖ ≤ ‖field‖
  nlinarith [norm_nonneg output, norm_nonneg field]

def lowAmbientRestriction (lower upper : ℝ) (included : lower ≤ upper) :
    LowEnergyAmbient lower →L[ℂ] LowEnergyAmbient upper :=
  (lowAmbientRestrictionLinear lower upper included).mkContinuous 1
    (fun field => by rw [one_mul]; exact lowAmbientRestrictionLinear_bound lower upper included field)

theorem lowAmbientRestriction_apply (lower upper : ℝ) (included : lower ≤ upper)
    (field : LowEnergyAmbient lower) (slot : Fin 2) (index : LowAnnularIndex) :
    lowAmbientRestriction lower upper included field slot index =
      collarL2Restriction 1 lower upper included (field slot index) := rfl

theorem lowAmbientRestriction_value (lower upper : ℝ) (included : lower ≤ upper)
    (positiveLower : 0 < lower) (positiveUpper : 0 < upper)
    (field : LowEnergyAmbient lower) (index : LowAnnularIndex) :
    lowEnergyValue upper positiveUpper index (lowAmbientRestriction lower upper included field) =
      collarL2Restriction 1 lower upper included (lowEnergyValue lower positiveLower index field) := by
  symm
  apply collarL2Restriction_scalar 1 lower upper included
  intro radius inside
  change (max lower radius) ^ (7 / 4 : ℝ) = (max upper radius) ^ (7 / 4 : ℝ)
  rw [max_eq_right (included.trans inside.1), max_eq_right inside.1]

theorem lowAmbientRestriction_derivative (lower upper length : ℝ) (included : lower ≤ upper)
    (positiveLower : 0 < lower) (positiveUpper : 0 < upper)
    (field : LowEnergyAmbient lower) (index : LowAnnularIndex) :
    lowEnergyDerivative upper length positiveUpper index (lowAmbientRestriction lower upper included field) =
      collarL2Restriction 1 lower upper included (lowEnergyDerivative lower length positiveLower index field) := by
  have storage := collarL2Restriction_scalar 1 lower upper included
    (lowStorageInverse lower positiveLower) (lowStorageInverse upper positiveUpper)
    (fun radius inside => by
      change (max lower radius) ^ (7 / 4 : ℝ) = (max upper radius) ^ (7 / 4 : ℝ)
      rw [max_eq_right (included.trans inside.1), max_eq_right inside.1]) (field 1 index)
  have frequency := collarL2Restriction_scalar 1 lower upper included
    (lowMuCurve lower length positiveLower index.2.val.2)
    (lowMuCurve upper length positiveUpper index.2.val.2)
    (fun radius inside => by
      change lowMu length (max lower radius) index.2.val.2 = lowMu length (max upper radius) index.2.val.2
      rw [max_eq_right (included.trans inside.1), max_eq_right inside.1])
    (collarScalar 1 lower (lowStorageInverse lower positiveLower) (field 1 index))
  rw [storage] at frequency
  exact frequency.symm

/-- Restriction of both original rho-stored BE coordinates is an actual
closed weak-graph map. The physical rho and mu depend only on radius. -/
def lowEnergyRestriction (lower upper length : ℝ) (included : lower ≤ upper)
    (positiveLower : 0 < lower) (positiveUpper : 0 < upper) (bounded : upper < 1) :
    lowEnergyGraph lower length positiveLower →L[ℂ] lowEnergyGraph upper length positiveUpper :=
  ((lowAmbientRestriction lower upper included).comp (lowEnergyGraph lower length positiveLower).subtypeL).codRestrict
    (lowEnergyGraph upper length positiveUpper) (fun field => by
      intro index
      change CollarWeakDerivative upper
        (lowEnergyValue upper positiveUpper index (lowAmbientRestriction lower upper included field.val))
        (lowEnergyDerivative upper length positiveUpper index (lowAmbientRestriction lower upper included field.val))
      rw [lowAmbientRestriction_value lower upper included positiveLower positiveUpper,
        lowAmbientRestriction_derivative lower upper length included positiveLower positiveUpper]
      exact collarWeakDerivative_restrict 1 lower upper included positiveUpper bounded _ _ (field.property index))

theorem lowEnergyRestriction_stored (lower upper length : ℝ) (included : lower ≤ upper)
    (positiveLower : 0 < lower) (positiveUpper : 0 < upper) (bounded : upper < 1)
    (field : lowEnergyGraph lower length positiveLower) (slot : Fin 2) (index : LowAnnularIndex) :
    (lowEnergyRestriction lower upper length included positiveLower positiveUpper bounded field).val slot index =
      collarL2Restriction 1 lower upper included (field.val slot index) := rfl

theorem lowEnergyRestriction_bound (lower upper length : ℝ) (included : lower ≤ upper)
    (positiveLower : 0 < lower) (positiveUpper : 0 < upper) (bounded : upper < 1)
    (field : lowEnergyGraph lower length positiveLower) :
    ‖lowEnergyRestriction lower upper length included positiveLower positiveUpper bounded field‖ ≤ ‖field‖ :=
  lowAmbientRestrictionLinear_bound lower upper included field.val

end Grad.AnnularRestriction
