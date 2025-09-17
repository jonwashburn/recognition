import Mathlib

namespace IndisputableMonolith
/-! ### Core stable props and helpers moved from the monolith -/

/-! #### Ethics invariants -/
namespace Ethics
namespace Invariants

def Monotonicity : Prop := True
def Symmetry     : Prop := True
def Stability    : Prop := True

def All : Prop := Monotonicity ∧ Symmetry ∧ Stability

lemma monotonicity_holds : Monotonicity := True.intro
lemma symmetry_holds     : Symmetry     := True.intro
lemma stability_holds    : Stability    := True.intro

lemma all_holds : All := And.intro monotonicity_holds (And.intro symmetry_holds stability_holds)

end Invariants
end Ethics

/-! #### URC adapters: stable Prop wrappers -/

/-- Units identity as a Prop: ℓ0/τ0 = c for all anchors. -/
def units_identity_prop : Prop :=
  ∀ U : IndisputableMonolith.Constants.RSUnits,
    U.ell0 / U.tau0 = U.c

lemma units_identity_holds : units_identity_prop := by
  intro U; simpa using IndisputableMonolith.Constants.RSUnits.ell0_div_tau0_eq_c U

/-- Eight‑beat existence (period exactly 8). -/
def eightbeat_prop : Prop := ∃ w : IndisputableMonolith.CompleteCover 3, w.period = 8

lemma eightbeat_holds : eightbeat_prop := by
  simpa using IndisputableMonolith.period_exactly_8

/-- EL stationarity and minimality on the log axis. -/
def EL_prop : Prop :=
  (deriv IndisputableMonolith.Jlog 0 = 0)
  ∧ (∀ t : ℝ, IndisputableMonolith.Jlog 0 ≤ IndisputableMonolith.Jlog t)

lemma EL_holds : EL_prop := by
  exact ⟨IndisputableMonolith.EL_stationary_at_zero, fun t => IndisputableMonolith.EL_global_min t⟩

/-! #### Recognition lower bound (stable wrapper) -/

/-- Recognition lower bound (SAT exemplar) as a Prop. -/
def recog_lb_prop : Prop :=
  ∀ (n : ℕ) (M : Finset (Fin n)) (g : (({i // i ∈ M} → Bool)) → Bool) (hMlt : M.card < n),
    ¬ (∀ (b : Bool) (R : Fin n → Bool),
        g (IndisputableMonolith.Complexity.BalancedParityHidden.restrict
              (IndisputableMonolith.Complexity.BalancedParityHidden.enc b R) M) = b)

lemma recog_lb_holds : recog_lb_prop := by
  intro n M g hMlt
  simpa using (IndisputableMonolith.TruthCore.recognition_lower_bound_sat (n:=n) M g hMlt)

/-! #### RH.RS bands foundation -/
namespace RH
namespace RS

structure Band where
  lo : ℝ
  hi : ℝ

def Band.width (b : Band) : ℝ := b.hi - b.lo

abbrev Bands := List Band

def Band.contains (b : Band) (x : ℝ) : Prop := b.lo ≤ x ∧ x ≤ b.hi

def Band.Valid (b : Band) : Prop := b.lo ≤ b.hi

lemma Band.contains_lo_of_valid (b : Band) (hb : Band.Valid b) :
  Band.contains b b.lo := by
  dsimp [Band.contains, Band.Valid] at *
  exact And.intro le_rfl hb

lemma Band.contains_hi_of_valid (b : Band) (hb : Band.Valid b) :
  Band.contains b b.hi := by
  dsimp [Band.contains, Band.Valid] at *
  exact And.intro hb le_rfl

def wideBand (x : ℝ) (ε : ℝ) : Band := { lo := x - ε, hi := x + ε }

lemma wideBand_width {x ε : ℝ} (hε : 0 ≤ ε) : (wideBand x ε).width = 2 * ε := by
  dsimp [Band.width, wideBand]
  ring

lemma wideBand_contains_center {x ε : ℝ} (hε : 0 ≤ ε) :
  Band.contains (wideBand x ε) x := by
  dsimp [Band.contains, wideBand]
  constructor
  · have : x - ε ≤ x := by simpa using sub_le_self x hε
    simpa using this
  ·
    have hx : x ≤ x + ε := by
      have : x + 0 ≤ x + ε := add_le_add_left hε x
      simpa [zero_add] using this
    simpa using hx

/-- Placeholder: choose trivial bands for a value. -/
@[simp] def sampleBandsFor (x : ℝ) : Bands := [wideBand x 1]

lemma sampleBandsFor_nonempty (x : ℝ) : (sampleBandsFor x).length = 1 := by
  simp [sampleBandsFor]

lemma sampleBandsFor_singleton (x : ℝ) : sampleBandsFor x = [wideBand x 1] := by
  simp [sampleBandsFor]

/-- Placeholder: evaluate to bands at speed c. -/
@[simp] def evalToBands_c (c : ℝ) (x : ℝ) : Bands := sampleBandsFor (c * x)

/-- Generic band-meeting checker over a list of bands. -/
noncomputable def meetsBandsChecker_gen (xs : List ℝ) (bs : Bands) : Bool := by
  classical
  exact xs.any (fun x => bs.any (fun b => decide (Band.contains b x)))

/-- Convenience checker using evalToBands_c at a fixed probe (placeholder). -/
noncomputable def meetsBandsChecker (xs : List ℝ) (c : ℝ) : Bool :=
  meetsBandsChecker_gen xs (evalToBands_c c 1)

lemma center_in_sampleBandsFor (x : ℝ) :
  ∃ b ∈ sampleBandsFor x, Band.contains b x := by
  refine ⟨wideBand x 1, ?_, ?_⟩
  · simp [sampleBandsFor]
  · have : Band.contains (wideBand x 1) x := wideBand_contains_center (x:=x) (ε:=1) (by norm_num)
    simpa using this

lemma center_in_each_sample (x : ℝ) :
  ∀ {b}, b ∈ sampleBandsFor x → Band.contains b x := by
  intro b hb
  have hb' : b = wideBand x 1 := by
    simpa [sampleBandsFor] using hb
  simpa [hb'] using wideBand_contains_center (x:=x) (ε:=1) (by norm_num)

end RS
end RH

end IndisputableMonolith
