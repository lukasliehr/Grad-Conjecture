import AKCO17ActualSignedLowerFlux
import AKCO16SameAllPowerStartupInduction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 3000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets Grad.CellWeights Grad.CellBinomial
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- A genuine weighted punctured first graph gives the SAME signed
localized field, using the accepted CellBinomial derivative jet. -/
theorem StartupSignedFamily.cutoff_first {L ell : ℝ} (family : StartupSignedFamily 3 L ell)
    (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff) (compact : HasCompactSupport cutoff)
    (power : ℕ) (weighted : GraphGrade 3 1 power openUnitDisk)
    (sameBase : base 3 1 openUnitDisk (fun _ => power) weighted = startupCutoffL2 cutoff smooth compact family.field) :
    ∃ graph : StartupFirst 3, base 3 1 openUnitDisk (fun _ => 0) graph =
      startupCutoffL2 cutoff smooth compact (family.moment power) := by
  let derivative := derivativeJetOfGrade 3 1 power power openUnitDisk le_rfl weighted
  let scalar : ℂ := ((ell/L : ℝ) : ℂ)^power
  refine ⟨scalar • derivative.jet,?_⟩
  rw [map_smul]
  have graph := operatorJet_graph 3 1 openUnitDisk (derivativeFactor power) _ derivative
  have pairSame := congrArg (fun value : StartupL2 3 =>
    (value,base 3 1 openUnitDisk (fun _ => 0) derivative.jet)) sameBase
  rw [pairSame] at graph
  apply Lp.ext
  filter_upwards [fieldGraph_ae 3 openUnitDisk (derivativeFactor power) _ _ graph,
    startupCutoffL2_ae cutoff smooth compact family.field,
    startupCutoffL2_ae cutoff smooth compact (family.moment power),family.same power,
    Lp.coeFn_smul scalar (base 3 1 openUnitDisk (fun _ => 0) derivative.jet)]
    with point derived localized localizedMoment signed scaled
  apply lp.ext
  funext cell
  rw [scaled,Pi.smul_apply,lp.coeFn_smul,Pi.smul_apply,derived cell,localized cell,localizedMoment cell,signed cell]
  simp only [smul_smul]
  congr 1
  have frequency : startupAxialFrequency L ell cell = ((ell/L : ℝ) : ℂ) * (Complex.I * (cell : ℂ)) := by
    unfold startupAxialFrequency
    push_cast
    ring
  simp only [frequency,mul_pow,derivativeFactor,scalar]
  ring

theorem startupCircle_cutoff (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff)
    (compact : HasCompactSupport cutoff)
    (radial : ∀ first second : Spatial, ‖first‖ = ‖second‖ → cutoff first = cutoff second)
    (field : StartupL2 3) :
    originalCircleKernel (startupCutoffL2 cutoff smooth compact field) =
      startupCutoffL2 cutoff smooth compact (originalCircleKernel field) := by
  have first := (startupCutoff_related cutoff smooth compact field).radialCircle (fun _ => radial)
  have second := startupCutoff_related cutoff smooth compact (originalCircleKernel field)
  apply Lp.ext
  filter_upwards [first,second] with point one two
  apply lp.ext
  funext cell
  exact (one cell).trans (two cell).symm

/-- The original punctured reserve supplies every complement graph needed
by the inner startup induction, for the SAME fixed quotient Q0(a_C). -/
theorem StartupSignedFamily.circle_outside_first {L ell : ℝ} (family : StartupSignedFamily 3 L ell)
    (inside annular : Spatial → ℝ) (insideSmooth : ContDiff ℝ ∞ inside) (annularSmooth : ContDiff ℝ ∞ annular)
    (insideCompact : HasCompactSupport inside) (annularCompact : HasCompactSupport annular)
    (annularRadial : ∀ first second : Spatial, ‖first‖ = ‖second‖ → annular first = annular second)
    (partition : ∀ point ∈ openUnitDisk, annular point = 1-inside point)
    (reserve : ∀ weight : ℕ, ∃ graph : GraphGrade 3 1 weight openUnitDisk,
      base 3 1 openUnitDisk (fun _ => weight) graph = startupCutoffL2 annular annularSmooth annularCompact family.field) :
    ∀ power : ℕ, ∃ graph : StartupFirst 3, base 3 1 openUnitDisk (fun _ => 0) graph =
      family.circle.moment power - startupCutoffL2 inside insideSmooth insideCompact (family.circle.moment power) := by
  intro power
  obtain ⟨weighted,weightedSame⟩ := reserve power
  obtain ⟨graph,same⟩ := family.cutoff_first annular annularSmooth annularCompact power weighted weightedSame
  refine ⟨originalCircleFirstGraph graph,?_⟩
  rw [originalCircleFirstGraph_compatible,same,startupCircle_cutoff annular annularSmooth annularCompact annularRadial]
  change startupCutoffL2 annular annularSmooth annularCompact (family.circle.moment power) = _
  apply Lp.ext
  filter_upwards [startupCutoffL2_ae annular annularSmooth annularCompact (family.circle.moment power),
    startupCutoffL2_ae inside insideSmooth insideCompact (family.circle.moment power),
    Lp.coeFn_sub (family.circle.moment power) (startupCutoffL2 inside insideSmooth insideCompact (family.circle.moment power)),
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point annularAt insideAt subtract member
  apply lp.ext
  funext cell
  rw [subtract,Pi.sub_apply,lp.coeFn_sub,Pi.sub_apply,annularAt cell,insideAt cell,partition point member]
  push_cast
  rw [sub_smul,one_smul]

end Grad.CartesianStartup
