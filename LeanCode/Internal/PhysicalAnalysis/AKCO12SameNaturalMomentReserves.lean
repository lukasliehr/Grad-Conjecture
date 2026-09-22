import AKCO11ExistingCellWeightSynthesis

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets Grad.CellWeights Grad.CellBinomial
namespace StartupSignedFamily
variable {dimension : ℕ} {L ell : ℝ}

/-- The same signed derivative carries all later signed powers; this
shift changes no physical or phase representative. -/
def shift (family : StartupSignedFamily dimension L ell) (power : ℕ) : StartupSignedFamily dimension L ell where
  field := family.moment power
  moment q := family.moment (power+q)
  same q := by
    filter_upwards [family.same power,family.same (power+q)] with point one two
    intro cell
    rw [two cell,one cell,pow_add,mul_smul]
    exact smul_comm _ _ _

/-- Existing CellBinomial jets supply the exact natural output moments
needed by phase differentiation, including for full coefficient outputs. -/
def toNatural (family : StartupSignedFamily dimension L ell)
    (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0) : StartupAllMoments dimension := by
  let jets (weight : ℕ) : GraphGrade dimension 0 weight openUnitDisk :=
    (family.allNaturalZeroGraphs lengthNonzero scaleNonzero weight).choose
  have bases (weight : ℕ) : base dimension 0 openUnitDisk (fun _ => weight) (jets weight) = family.field :=
    (family.allNaturalZeroGraphs lengthNonzero scaleNonzero weight).choose_spec
  let moments (weight : ℕ) : StartupL2 dimension := (jets weight).val (zeroIndex 0)
  have same (weight : ℕ) : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      moments weight point cell = cellWeight cell ^ weight • family.field point cell := by
    have graph := weighted_zero_graph dimension 0 weight openUnitDisk (jets weight)
    rw [bases] at graph
    filter_upwards [fieldGraph_ae dimension openUnitDisk (positiveFactor weight) family.field _ graph] with point coordinates
    intro cell
    change (jets weight).val (zeroIndex 0) point cell = _
    rw [coordinates cell,RCLike.real_smul_eq_coe_smul (K := ℂ)]
    congr 1
    change (cellWeight cell : ℂ)^weight = ((cellWeight cell ^ weight : ℝ) : ℂ)
    exact (Complex.ofReal_pow _ _).symm
  refine ⟨family.field,moments,?_,?_⟩
  · apply Lp.ext
    filter_upwards [same 0] with point sameZero
    apply lp.ext
    funext cell
    simpa only [pow_zero,one_smul] using sameZero cell
  · apply ae_all_iff.mpr
    exact same

end StartupSignedFamily
end Grad.CartesianStartup
