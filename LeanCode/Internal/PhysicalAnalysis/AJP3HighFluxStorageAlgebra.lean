import AJP2HighPhysicalStorageDecode

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularHighRadial Grad.AnnularCurrentLow Grad.AnnularReconstruction Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

private theorem collarScalar_commute (lower : ℝ) (a b : C(ℝ, ℝ))
    (field : CollarL2 (ComplexEuclidean 1) lower) :
    collarScalar 1 lower a (collarScalar 1 lower b field) =
      collarScalar 1 lower b (collarScalar 1 lower a field) := by
  apply Lp.ext
  filter_upwards [collarScalar_ae 1 lower a (collarScalar 1 lower b field),
    collarScalar_ae 1 lower b field, collarScalar_ae 1 lower b (collarScalar 1 lower a field),
    collarScalar_ae 1 lower a field] with radius ab bvalue ba avalue
  rw [ab, bvalue, ba, avalue, smul_comm]

private theorem fluxCombination_ae (lower : ℝ) (a b : ℂ)
    (x c v g : CollarL2 (ComplexEuclidean 1) lower)
    (rx rc rv rg : ℝ → ComplexEuclidean 1)
    (hx : x =ᵐ[volume.restrict (Icc lower 1)] rx)
    (hc : c =ᵐ[volume.restrict (Icc lower 1)] rc)
    (hv : v =ᵐ[volume.restrict (Icc lower 1)] rv)
    (hg : g =ᵐ[volume.restrict (Icc lower 1)] rg) :
    (-x - a • c - b • v + b • g : CollarL2 (ComplexEuclidean 1) lower) =ᵐ[volume.restrict (Icc lower 1)]
      fun radius => -rx radius - a • rc radius - b • rv radius + b • rg radius := by
  filter_upwards [Lp.coeFn_add (-x - a • c - b • v) (b • g),
    Lp.coeFn_sub (-x - a • c) (b • v), Lp.coeFn_sub (-x) (a • c),
    Lp.coeFn_neg x, Lp.coeFn_smul a c, Lp.coeFn_smul b v, Lp.coeFn_smul b g,
    hx,hc,hv,hg] with radius added subV subC negX smulC smulV smulG sameX sameC sameV sameG
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply] at *
  rw [added, subV, subC, negX, smulC, smulV, smulG, sameX, sameC, sameV, sameG]

theorem rawHighPhase_reciprocalOrdinary_ae (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (field : DivisionRow 1 lower) (mode : ℤ × ℤ) :
    collarScalar 1 lower (rawHighPhase parameters lower positive mode.2)
      (collarScalar 1 lower (Grad.AnnularCurrentEnergy.highReciprocalRadius lower positive)
        (radialOrdinary 1 lower positive (field mode))) =ᵐ[volume.restrict (Icc lower 1)]
      fun radius => (radius : ℂ)⁻¹ • lowRhoPhysicalCoefficient parameters lower positive field radius mode := by
  rw [collarScalar_commute]
  filter_upwards [collarScalar_ae 1 lower (Grad.AnnularCurrentEnergy.highReciprocalRadius lower positive)
      (collarScalar 1 lower (rawHighPhase parameters lower positive mode.2) (radialOrdinary 1 lower positive (field mode))),
    rawHighPhase_radialOrdinary_ae parameters lower positive field mode,
    ae_restrict_mem measurableSet_Icc] with radius outer decoded inside
  rw [outer, decoded]
  change (max lower radius)⁻¹ • _ = _
  rw [max_eq_right inside.1, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact congrArg (fun scalar : ℂ => scalar • lowRhoPhysicalCoefficient parameters lower positive field radius mode)
    (Complex.ofReal_inv radius)

/-- The complete high flux expression decodes to the original physical signs, including positive Rg. -/
theorem rawHighFlux_full_decode (parameters : PhaseParameters) (length lower : ℝ) (positive : 0 < lower)
    (x c v g : DivisionRow 1 lower) (mode : ℤ × ℤ) :
    collarScalar 1 lower (rawHighPhase parameters lower positive mode.2)
      (-collarScalar 1 lower (Grad.AnnularCurrentEnergy.highReciprocalRadius lower positive)
          (radialOrdinary 1 lower positive (x mode)) -
        (Complex.I * (((mode.2 : ℝ) / length) : ℝ)) • radialOrdinary 1 lower positive (c mode) -
        (Complex.I * (mode.1 : ℂ)) • collarScalar 1 lower (Grad.AnnularCurrentEnergy.highReciprocalRadius lower positive)
          (radialOrdinary 1 lower positive (v mode)) +
        (Complex.I * (mode.1 : ℂ)) • radialOrdinary 1 lower positive (g mode)) =ᵐ[volume.restrict (Icc lower 1)]
      fun radius => -((radius : ℂ)⁻¹ • lowRhoPhysicalCoefficient parameters lower positive x radius mode) -
        (Complex.I * (((mode.2 : ℝ) / length) : ℝ)) • lowRhoPhysicalCoefficient parameters lower positive c radius mode -
        (Complex.I * (mode.1 : ℂ)) • ((radius : ℂ)⁻¹ • lowRhoPhysicalCoefficient parameters lower positive v radius mode) +
        (Complex.I * (mode.1 : ℂ)) • lowRhoPhysicalCoefficient parameters lower positive g radius mode := by
  simp only [map_add, map_sub, map_neg, map_smul]
  exact fluxCombination_ae lower _ _ _ _ _ _ _ _ _ _
    (rawHighPhase_reciprocalOrdinary_ae parameters lower positive x mode)
    (rawHighPhase_radialOrdinary_ae parameters lower positive c mode)
    (rawHighPhase_reciprocalOrdinary_ae parameters lower positive v mode)
    (rawHighPhase_radialOrdinary_ae parameters lower positive g mode)

end Grad.AnnularSmoothCore
