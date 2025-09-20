import Mathlib
import IndisputableMonolith.Measurement
import IndisputableMonolith.Patterns
import IndisputableMonolith.RH.RS.Spec
import IndisputableMonolith.Quantum

namespace IndisputableMonolith
namespace RH
namespace RS
namespace Witness

/-- Eight‑tick minimality witness tied to `Patterns` theorem. -/
def eightTickMinimalHolds : Prop :=
  ∃ w : IndisputableMonolith.Patterns.CompleteCover 3, w.period = 8

/-- Born rule witness interface: existence of a measurement pipeline whose averaging
    recovers a window integer (DNARP bridge). -/
def bornHolds : Prop :=
  ∃ (w : IndisputableMonolith.Patterns.Pattern 8),
    IndisputableMonolith.Measurement.observeAvg8 1 (IndisputableMonolith.Measurement.extendPeriodic8 w)
      = IndisputableMonolith.Measurement.Z_of_window w

/-- Bose–Fermi witness: provide a concrete interface instance from a trivial path system. -/
def boseFermiHolds : Prop :=
  IndisputableMonolith.Quantum.BoseFermiIface PUnit
    ({ C := fun _ => 0
     , comp := fun _ _ => PUnit.unit
     , cost_additive := by intro _ _; simp
     , normSet := { PUnit.unit }
     , sum_prob_eq_one := by
         -- sum over singleton = exp(0) = 1
         simp [IndisputableMonolith.Quantum.PathWeight.prob] })

/-- Minimal witnesses for the above props. -/
theorem eightTick_from_TruthCore : eightTickMinimalHolds := by
  refine ⟨IndisputableMonolith.Patterns.grayCoverQ3, ?_⟩
  simpa using IndisputableMonolith.Patterns.period_exactly_8

theorem born_from_TruthCore : bornHolds := by
  refine ⟨IndisputableMonolith.Patterns.grayWindow, ?_⟩
  have hk : (1 : Nat) ≠ 0 := by decide
  simpa using IndisputableMonolith.Measurement.observeAvg8_periodic_eq_Z (k:=1) hk _
theorem boseFermi_from_TruthCore : boseFermiHolds := by
  -- Derived from the generic RS pathweight interface
  simpa using
    (IndisputableMonolith.Quantum.rs_pathweight_iface PUnit
      { C := fun _ => 0
      , comp := fun _ _ => PUnit.unit
      , cost_additive := by intro _ _; simp
      , normSet := { PUnit.unit }
      , sum_prob_eq_one := by simp [IndisputableMonolith.Quantum.PathWeight.prob] }).right

/-- Provisional φ-closed proof for alpha (constant 1/alphaInv expression). -/
instance phiClosed_alpha (φ : ℝ) : RH.RS.PhiClosed φ (0 : ℝ) := ⟨⟩

/-- Minimal universal dimless pack using current dimensionless exports. -/
noncomputable def UD_minimal (φ : ℝ) : RH.RS.UniversalDimless φ where
  alpha0 := 0
  massRatios0 := []
  mixingAngles0 := []
  g2Muon0 := 0
  strongCP0 := True
  eightTick0 := True
  born0 := True
  boseFermi0 := True
  alpha0_isPhi := by infer_instance
  massRatios0_isPhi := by intro r hr; cases hr
  mixingAngles0_isPhi := by intro th hth; cases hth
  g2Muon0_isPhi := by infer_instance

/-- Minimal dimless pack associated to any bridge (spec-level placeholder). -/
noncomputable def dimlessPack_minimal (L : RH.RS.Ledger) (B : RH.RS.Bridge L) : RH.RS.DimlessPack L B :=
{ alpha := 0
, massRatios := []
, mixingAngles := []
, g2Muon := 0
, strongCPNeutral := True
, eightTickMinimal := True
, bornRule := True
, boseFermi := True }

/-- Matches holds for the minimal universal pack (partial witness for α and placeholder fields). -/
theorem matches_minimal (φ : ℝ) (L : RH.RS.Ledger) (B : RH.RS.Bridge L) :
  RH.RS.Matches φ L B (UD_minimal φ) := by
  refine Exists.intro (dimlessPack_minimal L B) ?h
  dsimp [UD_minimal, dimlessPack_minimal, RH.RS.Matches]
  -- chain equalities and trivial props
  repeat' first
    | rfl
    | apply And.intro rfl

/-- Combined witness: Matches plus the TruthCore-provided proofs for the three props. -/
theorem matches_withTruthCore (φ : ℝ) (L : RH.RS.Ledger) (B : RH.RS.Bridge L) :
  RH.RS.Matches φ L B (UD_minimal φ)
  ∧ eightTickMinimalHolds ∧ bornHolds ∧ boseFermiHolds := by
  refine And.intro (matches_minimal φ L B) ?rest
  refine And.intro eightTick_from_TruthCore (And.intro born_from_TruthCore boseFermi_from_TruthCore)

/-- Partial inevitability: dimensionless layer witnessed by UD_minimal and matches_withTruthCore. -/
theorem inevitability_dimless_partial (φ : ℝ) : RH.RS.Inevitability_dimless φ := by
  intro L B
  refine Exists.intro (UD_minimal φ) ?h
  exact matches_minimal φ L B

end Witness
end RS
end RH
end IndisputableMonolith
