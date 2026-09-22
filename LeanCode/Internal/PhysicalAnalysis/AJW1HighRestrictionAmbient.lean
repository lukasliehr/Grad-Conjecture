import AIV9LiteralWeightedGraphBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 100000
open scoped Topology
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational

/-- The Hilbert product map between two possibly different endpoint carriers. -/
def restrictionPairMap {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (first : E →L[ℂ] G) (second : F →L[ℂ] H) : WithLp 2 (E × F) →L[ℂ] WithLp 2 (G × H) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ G H).symm.toContinuousLinearMap.comp
    ((first.prodMap second).comp (WithLp.prodContinuousLinearEquiv 2 ℂ E F).toContinuousLinearMap)

theorem restrictionPairMap_fst {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (first : E →L[ℂ] G) (second : F →L[ℂ] H) (field : WithLp 2 (E × F)) :
    (restrictionPairMap first second field).ofLp.1 = first field.ofLp.1 := rfl

theorem restrictionPairMap_snd {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (first : E →L[ℂ] G) (second : F →L[ℂ] H) (field : WithLp 2 (E × F)) :
    (restrictionPairMap first second field).ofLp.2 = second field.ofLp.2 := rfl

theorem restrictionPairNorm_mono (a b c d input output : ℝ)
    (aNonnegative : 0 ≤ a) (bNonnegative : 0 ≤ b) (cNonnegative : 0 ≤ c) (dNonnegative : 0 ≤ d)
    (inputNonnegative : 0 ≤ input) (_outputNonnegative : 0 ≤ output)
    (inputSq : input ^ 2 = a ^ 2 + b ^ 2) (outputSq : output ^ 2 = c ^ 2 + d ^ 2)
    (first : c ≤ a) (second : d ≤ b) : output ≤ input := by
  have firstSq : c ^ 2 ≤ a ^ 2 := (sq_le_sq₀ cNonnegative aNonnegative).2 first
  have secondSq : d ^ 2 ≤ b ^ 2 := (sq_le_sq₀ dNonnegative bNonnegative).2 second
  nlinarith only [inputSq, outputSq, firstSq, secondSq, inputNonnegative]

theorem restrictionPairMap_norm_le {E F G H : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (first : E →L[ℂ] G) (second : F →L[ℂ] H)
    (firstBound : ∀ value, ‖first value‖ ≤ ‖value‖) (secondBound : ∀ value, ‖second value‖ ≤ ‖value‖)
    (field : WithLp 2 (E × F)) : ‖restrictionPairMap first second field‖ ≤ ‖field‖ := by
  have input := WithLp.prod_norm_sq_eq_of_L2 field
  have output := WithLp.prod_norm_sq_eq_of_L2 (restrictionPairMap first second field)
  change ‖field‖ ^ 2 = ‖field.ofLp.1‖ ^ 2 + ‖field.ofLp.2‖ ^ 2 at input
  change ‖restrictionPairMap first second field‖ ^ 2 =
    ‖first field.ofLp.1‖ ^ 2 + ‖second field.ofLp.2‖ ^ 2 at output
  exact restrictionPairNorm_mono _ _ _ _ _ _
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    input output (firstBound field.ofLp.1) (secondBound field.ofLp.2)

/-- Restrict both radial energy coordinates and retain the exact outer scalar value. -/
def highModeRadialMap (source target : ℝ) (radial : RadialL2 1 source →L[ℂ] RadialL2 1 target) :
    AnnularModeEnergyAmbient source →L[ℂ] AnnularModeEnergyAmbient target :=
  restrictionPairMap radial (restrictionPairMap radial (ContinuousLinearMap.id ℂ (ComplexEuclidean 1)))

theorem highModeRadialMap_norm_le (source target : ℝ)
    (radial : RadialL2 1 source →L[ℂ] RadialL2 1 target)
    (bound : ∀ value, ‖radial value‖ ≤ ‖value‖) (field : AnnularModeEnergyAmbient source) :
    ‖highModeRadialMap source target radial field‖ ≤ ‖field‖ := by
  let identity := ContinuousLinearMap.id ℂ (ComplexEuclidean 1)
  let rest := restrictionPairMap radial identity
  have restBound : ∀ value : WithLp 2 (RadialL2 1 source × ComplexEuclidean 1), ‖rest value‖ ≤ ‖value‖ := by
    intro value
    exact restrictionPairMap_norm_le radial identity bound (fun _ => le_rfl) value
  exact restrictionPairMap_norm_le radial rest bound restBound field

theorem highModeRadialMap_derivative (source target : ℝ)
    (radial : RadialL2 1 source →L[ℂ] RadialL2 1 target) (field : AnnularModeEnergyAmbient source) :
    annularModeDerivative target (highModeRadialMap source target radial field) =
      radial (annularModeDerivative source field) := rfl

theorem highModeRadialMap_mass (source target : ℝ)
    (radial : RadialL2 1 source →L[ℂ] RadialL2 1 target) (field : AnnularModeEnergyAmbient source) :
    annularModeMass target (highModeRadialMap source target radial field) =
      radial (annularModeMass source field) := rfl

theorem annularModeOuter_projection (lower : ℝ) (field : AnnularModeEnergyAmbient lower) :
    annularModeOuter lower field = field.ofLp.2.ofLp.2 := rfl

theorem highModeRadialMap_outerProjection (source target : ℝ)
    (radial : RadialL2 1 source →L[ℂ] RadialL2 1 target) (field : AnnularModeEnergyAmbient source) :
    (highModeRadialMap source target radial field).ofLp.2.ofLp.2 = field.ofLp.2.ofLp.2 := by
  change (restrictionPairMap radial (restrictionPairMap radial (ContinuousLinearMap.id ℂ (ComplexEuclidean 1))) field).ofLp.2.ofLp.2 = field.ofLp.2.ofLp.2
  rw [restrictionPairMap_snd, restrictionPairMap_snd]
  rfl

theorem highModeRadialMap_outer (source target : ℝ)
    (radial : RadialL2 1 source →L[ℂ] RadialL2 1 target) (field : AnnularModeEnergyAmbient source) :
    annularModeOuter target (highModeRadialMap source target radial field) =
      annularModeOuter source field :=
  (annularModeOuter_projection target (highModeRadialMap source target radial field)).trans
    ((highModeRadialMap_outerProjection source target radial field).trans
      (annularModeOuter_projection source field).symm)

def highAmbientRadialMap (source target : ℝ) (radial : RadialL2 1 source →L[ℂ] RadialL2 1 target)
    (bound : ∀ value, ‖radial value‖ ≤ ‖value‖) : AnnularEnergyAmbient source →L[ℂ] AnnularEnergyAmbient target :=
  complexLpTwoMap (fun _ : HighAnnularMode => highModeRadialMap source target radial) 1 (by norm_num)
    (fun _ field => by simpa only [one_mul] using highModeRadialMap_norm_le source target radial bound field)

theorem highAmbientRadialMap_apply (source target : ℝ) (radial : RadialL2 1 source →L[ℂ] RadialL2 1 target)
    (bound : ∀ value, ‖radial value‖ ≤ ‖value‖) (field : AnnularEnergyAmbient source) (mode : HighAnnularMode) :
    highAmbientRadialMap source target radial bound field mode = highModeRadialMap source target radial (field mode) := rfl

theorem highAmbientRadialMap_norm_le (source target : ℝ)
    (radial : RadialL2 1 source →L[ℂ] RadialL2 1 target) (bound : ∀ value, ‖radial value‖ ≤ ‖value‖)
    (field : AnnularEnergyAmbient source) : ‖highAmbientRadialMap source target radial bound field‖ ≤ ‖field‖ := by
  exact (complexLpTwoMap_bound (fun _ : HighAnnularMode => highModeRadialMap source target radial) 1 (by norm_num)
    (fun _ value => by simpa only [one_mul] using highModeRadialMap_norm_le source target radial bound value) field).trans_eq (one_mul _)

end Grad.AnnularRestriction
