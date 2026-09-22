import ANG23AllOrderAngularRegularity

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open scoped BigOperators
namespace Grad.CircularHighWeak
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- Ordinary disk H^s: the closure of actual smooth scalar disk jets at
cell zero, with every Cartesian multi-index through s counted once. -/
def unitDiskCore (grade : ℕ) : ClosedJet 1 →ₗ[ℂ] apGrade 1 0 0 1 1 grade :=
  (apFiniteInto 1 0 0 1).comp (Finsupp.lsingle 0)

def unitDiskSobolev (grade : ℕ) : Submodule ℂ (apGrade 1 0 0 1 1 grade) :=
  (unitDiskCore grade).range.topologicalClosure

def unitDiskCoreInto (grade : ℕ) : ClosedJet 1 →ₗ[ℂ] unitDiskSobolev grade :=
  (unitDiskCore grade).codRestrict _ (fun field => Submodule.le_topologicalClosure _ ⟨field, rfl⟩)

theorem unitDiskCoreInto_denseRange (grade : ℕ) : DenseRange (unitDiskCoreInto grade) := by
  have dense : DenseRange (Set.inclusion (Submodule.le_topologicalClosure (unitDiskCore grade).range)) := by
    apply (denseRange_inclusion_iff _).2
    intro point member
    exact member
  apply dense.mono
  rintro _ ⟨⟨point, field, equality⟩, rfl⟩
  exact ⟨field, Subtype.ext equality⟩

theorem unitDiskCore_norm (grade : ℕ) (field : ClosedJet 1) :
    ‖unitDiskCoreInto grade field‖ = ‖unitSobolevRow grade field‖ := by
  change ‖apFiniteEmbed (grade := grade) 1 0 0 1 (Finsupp.single 0 field)‖ = _
  rw [apFiniteEmbed_single]
  change ‖(lp.single 2 0 (unitSobolevRow grade field) : APAmbient 1 grade)‖ = _
  rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

def unitDiskDerivative (grade : ℕ) (index : DerivativeIndex grade) : unitDiskSobolev grade →L[ℂ] DiskL2 1 :=
  (apUnscaledCoordinate 1 0 0 1 0 index).comp (unitDiskSobolev grade).subtypeL

theorem unitDiskDerivative_core (grade : ℕ) (index : DerivativeIndex grade) (field : ClosedJet 1) :
    unitDiskDerivative grade index (unitDiskCoreInto grade field) = closedDerivativeL2 (derivativeMultiIndex index) field := by
  change apUnscaledCoordinate 1 0 0 1 0 index (apFiniteInto 1 0 0 1 (Finsupp.single 0 field)) = _
  rw [apUnscaledCoordinate_core, Finsupp.single_eq_same, unweightedJet]

theorem unitDiskSobolev_norm_sq (grade : ℕ) (field : unitDiskSobolev grade) :
    ‖field‖ ^ 2 = ∑ index : DerivativeIndex grade, ‖unitDiskDerivative grade index field‖ ^ 2 := by
  apply isClosed_property (unitDiskCoreInto_denseRange grade)
    (isClosed_eq (continuous_norm.pow 2) (continuous_finsetSum _ (fun index _ => (unitDiskDerivative grade index).continuous.norm.pow 2))) _ field
  intro core
  have norm := congrArg (fun value : ℝ => value ^ 2) (unitDiskCore_norm grade core)
  refine norm.trans ((PiLp.norm_sq_eq_of_L2 (fun _ : DerivativeIndex grade => DiskL2 1) (unitSobolevRow grade core)).trans ?_)
  apply Finset.sum_congr rfl
  intro index _
  exact congrArg (fun value : DiskL2 1 => ‖value‖ ^ 2)
    ((unitSobolevRow_coordinate grade core index).trans (unitDiskDerivative_core grade index core).symm)

def unitDiskBulk (grade : ℕ) : unitDiskSobolev grade →L[ℂ] DiskL2 1 :=
  (sourceBulk grade).comp (unitDiskSobolev grade).subtypeL

theorem unitDiskBulk_core (grade : ℕ) (field : ClosedJet 1) :
    unitDiskBulk grade (unitDiskCoreInto grade field) = closedL2Core field :=
  (sourceBulk_core grade (Finsupp.single 0 field)).trans (congrArg closedL2Core (Finsupp.single_eq_same))

/-- Exact AN20 source-domain consumer. The high condition is precisely the
paper's five removed angular modes; no other source or boundary restriction. -/
theorem ordinaryDisk_angularRegularity (parameter : ℝ) (order : ℕ) (source : unitDiskSobolev order)
    (high : unitDiskBulk order source ∈ highDiskL2) :
    ∃ derivative : highDiskGrade,
      HasH1AngularPower (order + 1) (highRobinWeakInverse parameter ⟨unitDiskBulk order source, high⟩) derivative ∧
      ‖derivative‖ ≤ (2 * unitRotationPowerConstant order) * ‖source‖ := by
  have sources : sourceHighBulk order source.val = ⟨unitDiskBulk order source, high⟩ :=
    Subtype.ext (highL2Projection_fixed ⟨unitDiskBulk order source, high⟩)
  refine ⟨angularWeakSolutionPower parameter order source.val, ?_, angularWeakSolutionPower_bound parameter order source.val⟩
  have transfer := congrArg (fun value : highDiskL2 => HasH1AngularPower (order + 1)
    (highRobinWeakInverse parameter value) (angularWeakSolutionPower parameter order source.val)) sources
  exact transfer.mp (actualAngularRegularity parameter order source.val).1

end Grad.CircularHighWeak
