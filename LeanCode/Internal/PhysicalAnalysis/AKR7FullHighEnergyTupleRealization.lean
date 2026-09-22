import AKR6OriginalEnergyFixedCollarBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularVariational Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (tuple : OriginalSmoothTuple parameters lower) (slot : Fin 4)

theorem tupleConjugatedRadialGraph_weighted_summable (grade : ℕ) :
    Summable (fun mode : ℤ × ℤ => Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 ^ grade *
      ‖tupleConjugatedRadialGraph parameters lower positive bounded tuple slot mode‖) := by
  have sum := ((tupleConjugatedJet_summable parameters lower bounded tuple slot 0 grade).add
    (tupleConjugatedJet_summable parameters lower bounded tuple slot 1 grade)).mul_left ‖radialSqrtMap 1 lower‖
  apply Summable.of_nonneg_of_le (fun mode => mul_nonneg (by unfold Grad.SourceCollarDivision.annularFrequency; positivity) (norm_nonneg _)) _ sum
  intro mode
  have bound := mul_le_mul_of_nonneg_left
    (tupleConjugatedRadialGraph_bound parameters lower positive bounded tuple slot mode)
    (show 0 ≤ Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 ^ grade by unfold Grad.SourceCollarDivision.annularFrequency; positivity)
  exact bound.trans_eq (by ring)

theorem tupleHighEnergyMode_summable (length : ℝ) :
    Summable (fun mode : HighAnnularMode =>
      ‖radialGraphEnergyMode lower length positive bounded mode
        (tupleConjugatedRadialGraph parameters lower positive bounded tuple slot mode.val)‖) := by
  have full := (tupleConjugatedRadialGraph_weighted_summable parameters lower positive bounded tuple slot 1).mul_left
    (originalEnergyRealizationConstant lower length)
  have restricted := full.subtype (fun mode : ℤ × ℤ => 3 ≤ |mode.1|)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ restricted
  intro mode
  simpa only [pow_one,mul_assoc,Function.comp_apply] using radialGraphEnergyMode_bound lower length positive bounded mode
    (tupleConjugatedRadialGraph parameters lower positive bounded tuple slot mode.val)

def tupleHighEnergyAmbient (length : ℝ) : AnnularEnergyAmbient lower :=
  ⟨fun mode => radialGraphEnergyMode lower length positive bounded mode
    (tupleConjugatedRadialGraph parameters lower positive bounded tuple slot mode.val), by
    have one : Memℓp (fun mode : HighAnnularMode => radialGraphEnergyMode lower length positive bounded mode
        (tupleConjugatedRadialGraph parameters lower positive bounded tuple slot mode.val)) 1 := by
      apply memℓp_gen
      simpa only [ENNReal.toReal_one,Real.rpow_one] using tupleHighEnergyMode_summable parameters lower positive bounded tuple slot length
    exact one.of_exponent_ge (by norm_num)⟩

/-- All high modes of every original tuple field lie in the closure of the
literal original Fourier energy core, with its full energy norm. -/
theorem tupleHighEnergyAmbient_mem (length : ℝ) :
    tupleHighEnergyAmbient parameters lower positive bounded tuple slot length ∈ annularEnergySpace lower length positive := by
  have convergence := lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (tupleHighEnergyAmbient parameters lower positive bounded tuple slot length)
  apply (LinearMap.range (finiteAnnularEnergyCore lower length positive)).isClosed_topologicalClosure.mem_of_tendsto convergence
  apply Filter.Eventually.of_forall
  intro support
  apply (annularEnergySpace lower length positive).sum_mem
  intro mode _
  exact radialGraphEnergySingle_mem lower length positive bounded mode
    (tupleConjugatedRadialGraph parameters lower positive bounded tuple slot mode.val)

def tupleHighEnergy (length : ℝ) : annularEnergySpace lower length positive :=
  ⟨tupleHighEnergyAmbient parameters lower positive bounded tuple slot length,
    tupleHighEnergyAmbient_mem parameters lower positive bounded tuple slot length⟩

end Grad.AnnularOriginalCoreRealization
