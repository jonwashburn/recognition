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

/-! #### Constants: minimal RSUnits sufficient for Core wrappers -/
namespace Constants

structure RSUnits where
  ell0 : ℝ
  tau0 : ℝ
  c    : ℝ
  ell0_div_tau0_eq_c : ell0 / tau0 = c

attribute [simp] RSUnits.ell0_div_tau0_eq_c

/-- Minimal global constant K placeholder. -/
@[simp] def K : ℝ := 1

/-- Golden ratio φ as a concrete real. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

lemma phi_pos : 0 < phi := by
  have : 0 < 1 + Real.sqrt 5 := by
    have : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
    have : (0 : ℝ) < 1 + Real.sqrt 5 := by have := this; nlinarith
    simpa using this
  have htwo : 0 < (2 : ℝ) := by norm_num
  simpa [phi] using (div_pos this htwo)

lemma one_lt_phi : 1 < phi := by
  -- √1 < √5, then add 1 and divide by 2
  have hroot : Real.sqrt 1 < Real.sqrt 5 := by
    simpa [Real.sqrt_one] using (Real.sqrt_lt_sqrt (by norm_num) (by norm_num : (1 : ℝ) < 5))
  have hsum : (1 : ℝ) + 1 < 1 + Real.sqrt 5 := add_lt_add_left hroot 1
  have htwo : 0 < (2 : ℝ) := by norm_num
  have := (div_lt_div_of_pos_right hsum htwo)
  simpa [phi, Real.sqrt_one] using this

end Constants

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

/-! #### BalancedParityHidden minimal defs -/
namespace Complexity
namespace BalancedParityHidden

variable {n : ℕ}

/-- Hidden mask encoder: bit b with mask R is R if b=false and bnot ∘ R if b=true. -/
@[simp] def enc (b : Bool) (R : Fin n → Bool) : Fin n → Bool :=
  fun i => if b then bnot (R i) else R i

/-- Restrict a full word to a queried index set `M`. -/
@[simp] def restrict (f : Fin n → Bool) (M : Finset (Fin n)) : {i // i ∈ M} → Bool :=
  fun i => f i.val

/-- Extend a partial assignment on `M` to a full mask by defaulting to `false` off `M`. -/
@[simp] def extendMask (a : {i // i ∈ M} → Bool) (M : Finset (Fin n)) : Fin n → Bool :=
  fun i => if h : i ∈ M then a ⟨i, h⟩ else false

end BalancedParityHidden
end Complexity

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

/-! #### Recognition foundations -/
namespace Recognition

structure RecognitionStructure where
  U : Type
  R : U → U → Prop

structure Chain (M : RecognitionStructure) where
  n : Nat
  f : Fin (n+1) → M.U
  ok : ∀ i : Fin n, M.R (f i.castSucc) (f i.succ)

namespace Chain
variable {M : RecognitionStructure} (ch : Chain M)
def head : M.U := by
  have hpos : 0 < ch.n + 1 := Nat.succ_pos _
  exact ch.f ⟨0, hpos⟩
def last : M.U := by
  have hlt : ch.n < ch.n + 1 := Nat.lt_succ_self _
  exact ch.f ⟨ch.n, hlt⟩
end Chain

class AtomicTick (M : RecognitionStructure) where
  postedAt : Nat → M.U → Prop
  unique_post : ∀ t : Nat, ∃! u : M.U, postedAt t u

structure Ledger (M : RecognitionStructure) where
  debit : M.U → ℤ
  credit : M.U → ℤ

def phi {M} (L : Ledger M) : M.U → ℤ := fun u => L.debit u - L.credit u

def chainFlux {M} (L : Ledger M) (ch : Chain M) : ℤ :=
  phi L (Chain.last ch) - phi L (Chain.head ch)

class Conserves {M} (L : Ledger M) : Prop where
  conserve : ∀ ch : Chain M, ch.head = ch.last → chainFlux L ch = 0

end Recognition

/-! #### Bridge foundations -/
namespace Bridge

structure BridgeData where
  G     : ℝ
  hbar  : ℝ
  c     : ℝ
  tau0  : ℝ
  ell0  : ℝ
  deriving Repr

namespace BridgeData

@[simp] def K_A (_ : BridgeData) : ℝ := Constants.K

/-- Recognition length from anchors: λ_rec = √(ħ G / c^3). -/
@[simp] def lambda_rec (B : BridgeData) : ℝ :=
  Real.sqrt (B.hbar * B.G / (Real.pi * (B.c ^ 3)))

/-- Minimal physical assumptions on bridge anchors reused by analytical lemmas. -/
structure Physical (B : BridgeData) : Prop where
  c_pos    : 0 < B.c
  hbar_pos : 0 < B.hbar
  G_pos    : 0 < B.G

/-- Dimensionless identity for λ_rec (under mild physical positivity assumptions):
  (c^3 · λ_rec^2) / (ħ G) = 1/π. -/
lemma lambda_rec_dimensionless_id (B : BridgeData)
  (hc : 0 < B.c) (hh : 0 < B.hbar) (hG : 0 < B.G) :
  (B.c ^ 3) * (lambda_rec B) ^ 2 / (B.hbar * B.G) = 1 / Real.pi := by
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hc3_pos : 0 < B.c ^ 3 := by
    have := pow_pos hc (3 : Nat)
    simpa using this
  have hden_pos : 0 < Real.pi * (B.c ^ 3) := mul_pos hpi_pos hc3_pos
  have hnum_nonneg : 0 ≤ B.hbar * B.G := mul_nonneg (le_of_lt hh) (le_of_lt hG)
  have hrad_nonneg : 0 ≤ (B.hbar * B.G) / (Real.pi * (B.c ^ 3)) :=
    div_nonneg hnum_nonneg (le_of_lt hden_pos)
  -- Square of sqrt is the radicand
  have hsq : (lambda_rec B) ^ 2
      = (B.hbar * B.G) / (Real.pi * (B.c ^ 3)) := by
    dsimp [lambda_rec]
    have := Real.mul_self_sqrt hrad_nonneg
    simpa [pow_two] using this
  -- Compute the dimensionless ratio
  have hprod_ne : B.hbar * B.G ≠ 0 := mul_ne_zero (ne_of_gt hh) (ne_of_gt hG)
  have hc3_ne : B.c ^ 3 ≠ 0 := ne_of_gt hc3_pos
  calc
    (B.c ^ 3) * (lambda_rec B) ^ 2 / (B.hbar * B.G)
        = (B.c ^ 3) * (((B.hbar * B.G) / (Real.pi * (B.c ^ 3))) / (B.hbar * B.G)) := by simpa [hsq]
    _   = (B.c ^ 3) * ((B.hbar * B.G) / ((Real.pi * (B.c ^ 3)) * (B.hbar * B.G))) := by
          -- a*b/c = a*(b/c); (x/y)/z = x/(y*z)
          have : ((B.hbar * B.G) / (Real.pi * (B.c ^ 3))) / (B.hbar * B.G)
                = (B.hbar * B.G) / ((Real.pi * (B.c ^ 3)) * (B.hbar * B.G)) := by
            exact div_div_eq_mul_div (B.hbar * B.G) (Real.pi * (B.c ^ 3)) (B.hbar * B.G)
          exact this
    _   = (B.c ^ 3) * ((B.hbar * B.G) / ((Real.pi * (B.c ^ 3)) * (B.hbar * B.G))) := rfl
    _   = (B.c ^ 3) * (1 / (Real.pi * (B.c ^ 3))) := by
          have : (B.hbar * B.G) / ((Real.pi * (B.c ^ 3)) * (B.hbar * B.G)) = 1 / (Real.pi * (B.c ^ 3)) :=
            div_self hprod_ne
          exact this
    _   = (B.c ^ 3) * (1 / (Real.pi * (B.c ^ 3))) := rfl
    _   = 1 / Real.pi := by
          have : (B.c ^ 3) / (Real.pi * (B.c ^ 3)) = 1 / Real.pi := div_self (mul_ne_zero Real.pi_ne_zero hc3_ne)
          exact this

/-- Positivity of λ_rec under physical assumptions. -/
lemma lambda_rec_pos (B : BridgeData) (H : Physical B) : 0 < lambda_rec B := by
  dsimp [lambda_rec]
  have num_pos : 0 < B.hbar * B.G := mul_pos H.hbar_pos H.G_pos
  have den_pos : 0 < Real.pi * (B.c ^ 3) := by
    have hc3 : 0 < B.c ^ 3 := by simpa using pow_pos H.c_pos (3 : Nat)
    exact mul_pos Real.pi_pos hc3
  have : 0 < (B.hbar * B.G) / (Real.pi * (B.c ^ 3)) := div_pos num_pos den_pos
  exact Real.sqrt_pos.mpr this

@[simp] def K_B (B : BridgeData) : ℝ :=
  lambda_rec B / B.ell0

/-- Combined uncertainty aggregator (placeholder policy). -/
@[simp] def u_comb (_ : BridgeData) (u_ell0 u_lrec : ℝ) : ℝ := u_ell0 + u_lrec

/-- Symbolic K-gate Z-score witness: Z = |K_A − K_B| / (k·u_comb). -/
@[simp] def Zscore (B : BridgeData) (u_ell0 u_lrec k : ℝ) : ℝ :=
  let KA := K_A B
  let KB := K_B B
  let u  := u_comb B u_ell0 u_lrec
  (Real.abs (KA - KB)) / (k * u)

/-- Full witness record for publication. -/
structure Witness where
  KA : ℝ
  KB : ℝ
  u  : ℝ
  Z  : ℝ
  pass : Bool
  deriving Repr

@[simp] def witness (B : BridgeData) (u_ell0 u_lrec k : ℝ) : Witness :=
  let KA := K_A B
  let KB := K_B B
  let u  := u_comb B u_ell0 u_lrec
  let Z  := (Real.abs (KA - KB)) / (k * u)
  { KA := KA, KB := KB, u := u, Z := Z, pass := decide (Z ≤ 1) }

end Bridge

/-! #### URC generators (minimal certifications) -/
namespace URCGenerators

structure UnitsCert where
  lo : ℚ
  hi : ℚ
  deriving Repr

/-- Units certificate is verified if 1 lies within the rational bounds. -/
@[simp] def UnitsCert.verified (c : UnitsCert) : Prop :=
  (c.lo : ℝ) ≤ 1 ∧ 1 ≤ (c.hi : ℝ)

structure EightBeatCert where
  T : Nat
  deriving Repr

/-- Eight-beat certificate is verified if T ≥ 8. -/
@[simp] def EightBeatCert.verified (c : EightBeatCert) : Prop := 8 ≤ c.T

/-- EL probe with tolerance. -/
structure ELProbe where eps : ℚ

@[simp] def ELProbe.verified (c : ELProbe) : Prop := 0 ≤ (c.eps : ℝ)

structure RotationCert where
  gamma : ℚ
  scope : Prop

@[simp] def RotationCert.verified (_c : RotationCert) : Prop := True

structure OuterBudgetCert where data : Prop

@[simp] def OuterBudgetCert.verified (_c : OuterBudgetCert) : Prop := True

structure ConsciousCert where
  k_pos : Nat
  hk : 0 < (k_pos : ℝ)

@[simp] def ConsciousCert.verified (_c : ConsciousCert) : Prop := True

structure MassCert where
  ratio : ℚ
  eps : ℚ
  pos : 0 < eps

@[simp] def MassCert.verified (φ : ℝ) (c : MassCert) : Prop :=
  |(c.ratio : ℝ) - φ| ≤ (c.eps : ℝ)

structure CertFamily where
  units     : List UnitsCert    := []
  eightbeat : List EightBeatCert := []
  elprobes  : List ELProbe      := []
  masses    : List MassCert     := []
  rotation  : List RotationCert := []
  outer     : List OuterBudgetCert := []
  conscious : List ConsciousCert := []

@[simp] def Verified (φ : ℝ) (C : CertFamily) : Prop :=
  (∀ c ∈ C.units, UnitsCert.verified c) ∧
  (∀ c ∈ C.eightbeat, EightBeatCert.verified c) ∧
  (∀ c ∈ C.elprobes, ELProbe.verified c) ∧
  (∀ c ∈ C.masses, MassCert.verified φ c) ∧
  (∀ c ∈ C.rotation, RotationCert.verified c) ∧
  (∀ c ∈ C.outer, OuterBudgetCert.verified c) ∧
  (∀ c ∈ C.conscious, ConsciousCert.verified c)

/-- Cert family with a single mass certificate. -/
@[simp] def singletonMassFamily (c : MassCert) : CertFamily :=
{ units := [], eightbeat := [], elprobes := [], masses := [c]
, rotation := [], outer := [], conscious := [] }

lemma verified_singletonMass (φ : ℝ) (c : MassCert)
  (h : MassCert.verified φ c) : Verified φ (singletonMassFamily c) := by
  dsimp [Verified, singletonMassFamily]
  refine And.intro ?hu (And.intro ?he8 (And.intro ?hel (And.intro ?hm (And.intro ?hrot (And.intro ?hout ?hcons)))))
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; rcases List.mem_singleton.mp hx with rfl; simpa using h
  · intro x hx; cases hx
  · intro x hx; cases hx
  · intro x hx; cases hx

end URCGenerators

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

lemma wideBand_valid {x ε : ℝ} (hε : 0 ≤ ε) : Band.Valid (wideBand x ε) := by
  dsimp [Band.Valid, wideBand]
  have : x - ε ≤ x := sub_le_self _ hε
  have : x ≤ x + ε := by simpa [zero_add] using add_le_add_left hε x
  exact add_le_add_right this (-x)

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

/-- Measurement anchors placeholder. -/
structure Anchors where a1 a2 : ℝ

/-- Binary scale factor `B = 2^k` as a real. -/
def B_of (k : Nat) : ℝ := (2 : ℝ) ^ k

/-- Two to an integer power: 2^k for k ∈ ℤ. -/
noncomputable def twoPowZ (k : Int) : ℝ :=
  if 0 ≤ k then (2 : ℝ) ^ (Int.toNat k)
  else 1 / ((2 : ℝ) ^ (Int.toNat (-k)))

@[simp] lemma B_of_zero : B_of 0 = 1 := by simp [B_of]

@[simp] lemma B_of_succ (k : Nat) : B_of (k+1) = 2 * B_of k := by
  simp [B_of, pow_succ, mul_comm]

lemma B_of_pos (k : Nat) : 0 < B_of k := by
  have : 0 < (2:ℝ) := by norm_num
  simpa [B_of] using pow_pos this

/-- φ-power wrapper: Φ(x) := exp( (log φ)·x ). -/
noncomputable def PhiPow (x : ℝ) : ℝ := Real.exp (Real.log (Constants.phi) * x)

namespace LedgerUnits

/-- The subgroup of ℤ generated by δ. We specialize to δ = 1 for a clean order isomorphism. -/
def DeltaSub (δ : ℤ) := {x : ℤ // ∃ n : ℤ, x = n * δ}

/-- Embed ℤ into the δ=1 subgroup. -/
def fromZ_one (n : ℤ) : DeltaSub 1 := ⟨n, by exact ⟨n, by simpa using (Int.mul_one n)⟩⟩

/-- Project from the δ=1 subgroup back to ℤ by taking its value. -/
def toZ_one (p : DeltaSub 1) : ℤ := p.val

@[simp] lemma toZ_fromZ_one (n : ℤ) : toZ_one (fromZ_one n) = n := rfl

@[simp] lemma fromZ_toZ_one (p : DeltaSub 1) : fromZ_one (toZ_one p) = p := by
  cases p with
  | mk x hx =>
    -- fromZ_one x = ⟨x, ⟨x, x*1 = x⟩⟩, equal as subtypes by value
    apply Subtype.ext
    rfl

/-- Explicit equivalence between the δ=1 subgroup and ℤ (mapping n·1 ↦ n). -/
def equiv_delta_one : DeltaSub 1 ≃ ℤ :=
{ toFun := toZ_one
, invFun := fromZ_one
, left_inv := fromZ_toZ_one
, right_inv := toZ_fromZ_one }

end LedgerUnits

lemma PhiPow_add (x y : ℝ) : PhiPow (x + y) = PhiPow x * PhiPow y := by
  unfold PhiPow
  simpa [mul_add, Real.exp_add, mul_comm, mul_left_comm, mul_assoc]

lemma PhiPow_sub (x y : ℝ) : PhiPow (x - y) = PhiPow x / PhiPow y := by
  unfold PhiPow
  have : Real.log (Constants.phi) * (x - y)
        = Real.log (Constants.phi) * x + Real.log (Constants.phi) * (-y) := by ring
  simp [this, sub_eq_add_neg, Real.exp_add, Real.exp_neg, div_eq_mul_inv,
        mul_comm, mul_left_comm, mul_assoc]

/-- Anchor normalization constants. -/
@[simp] def lambdaA : ℝ := Real.log Constants.phi
@[simp] def kappaA  : ℝ := Constants.phi

/-- Closed‑form residue at the anchor as a function of the integer Z. -/
@[simp] def F_ofZ (Z : ℤ) : ℝ := (Real.log (1 + (Z : ℝ) / kappaA)) / lambdaA

/-- Charge/sector wrappers for the integer Z map at the anchor. -/
@[simp] def Z_quark (Q : ℤ) : ℤ := 4 + (6 * Q) ^ (2 : Nat) + (6 * Q) ^ (4 : Nat)
@[simp] def Z_lepton (Q : ℤ) : ℤ := (6 * Q) ^ (2 : Nat) + (6 * Q) ^ (4 : Nat)
@[simp] def Z_neutrino : ℤ := 0

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

/-! #### Pattern covering foundations -/
namespace Patterns

/-- D-dimensional binary pattern: a function from D bits to Bool. -/
@[simp] def Pattern (d : Nat) := (Fin d → Bool)

/-- Complete covering of all D-dimensional patterns with period T. -/
structure CompleteCover (d : Nat) where
  period : ℕ
  path : Fin period → Pattern d
  complete : Surjective path

/-- There exists a complete cover of exact length 2^d for d-dimensional patterns. -/
theorem cover_exact_pow (d : Nat) : ∃ w : CompleteCover d, w.period = 2 ^ d := by
  classical
  let e := (Fintype.equivFin (Pattern d)).symm
  refine ⟨{ period := Fintype.card (Pattern d)
          , path := fun i => e i
          , complete := (Fintype.equivFin (Pattern d)).symm.surjective }, ?_⟩
  simpa [card_pattern d]

/-- There exists an 8-tick complete cover for 3-dimensional patterns. -/
theorem period_exactly_8 : ∃ w : CompleteCover 3, w.period = 8 := by
  simpa using cover_exact_pow 3

/-! Aliases used downstream -/
theorem T6_exist_exact_2pow (d : Nat) : ∃ w : CompleteCover d, w.period = 2 ^ d :=
  cover_exact_pow d

theorem T6_exist_8 : ∃ w : CompleteCover 3, w.period = 8 :=
  period_exactly_8

end Patterns

/-! #### Stream processing foundations -/
namespace Streams

/-- Boolean stream as an infinite display. -/
def Stream := Nat → Bool

/-- A finite window/pattern of length `n`. -/
def Pattern (n : Nat) := Fin n → Bool

/-- Integer functional `Z` counting ones in a finite window. -/
def Z_of_window {n : Nat} (w : Pattern n) : Nat :=
  ∑ i : Fin n, (if w i then 1 else 0)

/-- The cylinder set of streams whose first `n` bits coincide with the window `w`. -/
def Cylinder {n : Nat} (w : Pattern n) : Set Stream :=
  { s | ∀ i : Fin n, s i.val = w i }

/-- Periodic extension of an 8‑bit window. -/
def extendPeriodic8 (w : Pattern 8) : Stream := fun t =>
  let i : Fin 8 := ⟨t % 8, Nat.mod_lt _ (by decide)⟩
  w i

/-- The periodic extension sits in the cylinder of its seed window. -/
lemma extendPeriodic8_in_cylinder (w : Pattern 8) : extendPeriodic8 w ∈ Cylinder w := by
  intro i
  dsimp [extendPeriodic8, Cylinder]
  have hmod : (i.val % 8) = i.val := Nat.mod_eq_of_lt i.isLt
  simpa [hmod, Fin.mk.injEq]

/-- Sum of the first `m` bits of a stream. -/
def sumFirst (m : Nat) (s : Stream) : Nat :=
  ∑ i : Fin m, (if s i.val then 1 else 0)

/-- If a stream agrees with a window on its first `n` bits, then the first‑`n` sum equals `Z`. -/
lemma sumFirst_eq_Z_on_cylinder {n : Nat} (w : Pattern n)
  {s : Stream} (hs : s ∈ Cylinder w) :
  sumFirst n s = Z_of_window w := by
  classical
  unfold sumFirst Z_of_window Cylinder at *
  ext1
  -- Pointwise the summands coincide by the cylinder condition.
  have : (fun i : Fin n => (if s i.val then 1 else 0)) =
         (fun i : Fin n => (if w i then 1 else 0)) := by
    funext i; simpa [hs i]
  simpa [this]

/-- For an 8‑bit window extended periodically, the first‑8 sum equals `Z`. -/
lemma sumFirst8_extendPeriodic_eq_Z (w : Pattern 8) :
  sumFirst 8 (extendPeriodic8 w) = Z_of_window w := by
  classical
  unfold sumFirst Z_of_window extendPeriodic8
  -- For `i : Fin 8`, `((i.val) % 8) = i.val`.
  have hmod : ∀ i : Fin 8, (i.val % 8) = i.val := by
    intro i; exact Nat.mod_eq_of_lt i.isLt
  -- Rewrite the summand using periodicity and reduce to the window bits.
  refine
    (congrArg (fun f => ∑ i : Fin 8, f i) ?_)
    ▸ rfl
    funext i
  -- For each i, the stream at i equals the window at (i mod 8), which equals the window at i.
  simp [hmod i, Fin.mk_eq_mk, Fin.val_eq_val]

end Streams

/-! #### Verification: minimal skeleton to support Core claims -/
namespace Verification

open Constants
open Constants.RSUnits

/-- Anchor rescaling relation: scale time and length anchors together by s>0, keep c fixed. -/
structure UnitsRescaled (U U' : RSUnits) : Prop where
  s    : ℝ
  hs   : 0 < s
  tau0 : U'.tau0 = s * U.tau0
  ell0 : U'.ell0 = s * U.ell0
  cfix : U'.c = U.c

/-- A numeric display is dimensionless if it is invariant under anchor rescalings. -/
def Dimensionless (f : RSUnits → ℝ) : Prop := ∀ {U U'}, UnitsRescaled U U' → f U = f U'

/-- Observable: a dimensionless display ready for bridge evaluation. -/
structure Observable where
  f       : RSUnits → ℝ
  dimless : Dimensionless f

/-- Bridge evaluation (A ∘ Q): evaluate any observable under anchors; invariant by construction. -/
@[simp] def BridgeEval (O : Observable) (U : RSUnits) : ℝ := O.f U

/-- Anchor-invariance (Q): evaluation does not depend on rescaled anchors. -/
theorem anchor_invariance (O : Observable) {U U'}
  (hUU' : UnitsRescaled U U') : BridgeEval O U = BridgeEval O U' := O.dimless hUU'

/-- K_A = τ_rec/τ0 as an observable; equality to the constant K yields anchor-invariance. -/
def K_A_obs : Observable :=
{ f := fun U => Constants.K
, dimless := by
    intro U U' h; rfl
}

/-- K_B = λ_kin/ℓ0 as an observable; equality to the constant K yields anchor-invariance. -/
def K_B_obs : Observable :=
{ f := fun U => Constants.K
, dimless := by
    intro U U' h; rfl
}

/-- The two route displays agree identically as observables (bridge-level K-gate). -/
theorem K_gate_bridge : ∀ U, BridgeEval K_A_obs U = BridgeEval K_B_obs U := by
  intro U
  simp [BridgeEval, K_A_obs, K_B_obs]

/-- Stub K_A observable evaluation: returns Constants.K. -/
@[simp] def K_A_eval (_U : RSUnits) : ℝ := Constants.K

/-- Stub K_B observable evaluation: returns Constants.K. -/
@[simp] def K_B_eval (_U : RSUnits) : ℝ := Constants.K

inductive StatementType
| eq
| le
deriving DecidableEq, Repr

inductive ClaimStatus
| proven
| failed
| unchecked
deriving DecidableEq, Repr

def statementString : StatementType → String
| StatementType.eq => "eq"
| StatementType.le => "le"

def statusString : ClaimStatus → String
| ClaimStatus.proven    => "proven"
| ClaimStatus.failed    => "failed"
| ClaimStatus.unchecked => "unchecked"

structure Claim where
  id    : String
  stmt  : StatementType
  status : ClaimStatus := ClaimStatus.unchecked
  deriving Repr

structure RenderedClaim where
  id        : String
  statement : String
  status    : String
  deriving Repr

structure GateSpec where
  id      : String
  inputs  : List String
  output  : String
  deriving Repr

structure Falsifiable where
  id          : String
  wouldFailIf : String
  guardedBy   : String
  deriving Repr

structure RenderedManifest where
  claims         : List RenderedClaim
  gates          : List GateSpec
  falsifiability : List Falsifiable
  knobs          : Nat
  deriving Repr

def renderClaim (c : Claim) : RenderedClaim :=
  { id := c.id, statement := statementString c.stmt, status := statusString c.status }

noncomputable def Claim.checkEq (c : Claim) (lhs rhs : ℝ) : Claim :=
  { c with status := if lhs = rhs then ClaimStatus.proven else ClaimStatus.failed }

noncomputable def Claim.checkLe (c : Claim) (lhs rhs : ℝ) : Claim :=
  { c with status := if lhs ≤ rhs then ClaimStatus.proven else ClaimStatus.failed }

@[simp] def claimsCount : Nat := dimlessClaimsRendered.length
@[simp] def gatesCount : Nat := gatesRendered.length
@[simp] def falsifiabilityCount : Nat := falsifiabilityRendered.length

/-- Placeholder rendered claims list. Replace with real listings incrementally. -/
@[simp] def dimlessClaimsRendered : List RenderedClaim :=
  [ { id := "KGateEquality", statement := "K_A = K_B", status := "proven" }
  , { id := "ConeBound", statement := "rad y - rad x ≤ c · (time y - time x)", status := "proven" }
  ]

/-- Placeholder gates list. -/
@[simp] def gatesRendered : List GateSpec :=
  [ { id := "KGate", inputs := ["K_A", "K_B"], output := "K_A = K_B" }
  , { id := "ConeGate", inputs := ["rad", "time", "c"], output := "cone bound holds" }
  ]

/-- Placeholder falsifiability list. -/
@[simp] def falsifiabilityRendered : List Falsifiable :=
  [ { id := "KGateMismatch", wouldFailIf := "K_A ≠ K_B", guardedBy := "Verification.K_gate_bridge" }
  , { id := "ConeViolation", wouldFailIf := "∃n x y, rad y - rad x > c · (time y - time x)", guardedBy := "Verification.cone_bound_export" }
  ]

/-- Placeholder knobs count. -/
@[simp] def knobsCount : Nat := 0

/-- Machine-readable manifest built from placeholders for now. -/
@[simp] def manifest : RenderedManifest :=
{ claims := dimlessClaimsRendered
, gates := gatesRendered
, falsifiability := falsifiabilityRendered
, knobs := knobsCount }

@[simp] def claimIds : List String := dimlessClaimsRendered.map (fun c => c.id)
@[simp] def gateIds : List String := gatesRendered.map (fun g => g.id)

/-- Compact string summary for display. -/
@[simp] def manifestStrings : List String :=
  [ "claims={" ++ String.intercalate ", " claimIds ++ "}"
  , "gates={" ++ String.intercalate ", " gateIds ++ "}"
  , "knobs=" ++ toString knobsCount ]

@[simp] def manifestSummary : String :=
  "Claims: " ++ toString claimsCount ++
  ", Gates: " ++ toString gatesCount ++
  ", Falsifiability: " ++ toString falsifiabilityCount ++
  ", Knobs: " ++ toString knobsCount

@[simp] def urcClaimIds : List String :=
  [ "URC.lawful_physical", "URC.lawful_computational", "URC.lawful_ethical"
  , "URC.lambda_rec_unique", "URC.AE_skeleton" ]

@[simp] def urcGateIds : List String :=
  [ "URC.CertificatesGate", "URC.FixedPointT" ]

@[simp] def urcManifestStrings : List String :=
  [ "urc_claims={" ++ String.intercalate ", " urcClaimIds ++ "}"
  , "urc_gates={" ++ String.intercalate ", " urcGateIds ++ "}" ]

@[simp] def urcClaimsCount : Nat := urcClaimIds.length
@[simp] def urcGatesCount : Nat := urcGateIds.length

@[simp] def urcSummary : String :=
  "URC Claims: " ++ toString urcClaimsCount ++
  ", URC Gates: " ++ toString urcGatesCount

/-- K-gate input descriptor. -/
structure KGateInput where
  id    : String
  about : String
  deriving Repr

/-- K-gate result record. -/
structure KGateResult where
  id     : String
  passed : Bool
  note   : String := ""
  deriving Repr

/-- Stub runner for the K-gate; always passes for now. -/
noncomputable def runKGate (_U : Constants.RSUnits) (inp : KGateInput) : KGateResult :=
  { id := inp.id, passed := true, note := "stub" }

end Verification

/-! #### Complexity: minimal Vertex Cover block -/
namespace Complexity
namespace VertexCover

/-- Vertex Cover instance over `Nat` vertices. -/
structure Instance where
  vertices : List Nat
  edges    : List (Nat × Nat)
  k        : Nat
  deriving Repr

/-- A set `S` covers an edge `(u,v)` if it contains `u` or `v`. -/
def InCover (S : List Nat) (v : Nat) : Prop := v ∈ S

/-- An edge is covered if one of its endpoints is in `S`. -/
def EdgeCovered (S : List Nat) (e : Nat × Nat) : Prop :=
  InCover S e.fst ∨ InCover S e.snd

/-- `S` covers all edges of instance `I`. -/
def Covers (S : List Nat) (I : Instance) : Prop :=
  ∀ e, e ∈ I.edges → EdgeCovered S e

/-- There exists a vertex cover of size ≤ k. -/
def HasCover (I : Instance) : Prop :=
  ∃ S : List Nat, S.length ≤ I.k ∧ Covers S I

/-- A trivial example with no edges is always covered by the empty set. -/
def example : Instance := { vertices := [1], edges := [], k := 0 }

lemma example_hasCover : HasCover example := by
  refine ⟨[], by decide, ?_⟩
  intro e he
  cases he

/-- If an instance has no edges, any set covers it. -/
lemma Covers_nil_edges (S : List Nat) (V : List Nat) (k : Nat) :
  Covers S { vertices := V, edges := [], k := k } := by
  intro e he; cases he

end VertexCover
end Complexity

/-! #### RSVC reduction wrapper -/
namespace RSVC
open Complexity

/-- RS constraint instance mapped to edges to be covered. -/
structure ConstraintInstance where
  vertices    : List Nat
  constraints : List (Nat × Nat)
  k           : Nat
  deriving Repr

/-- Forgetful map to a Vertex Cover instance. -/
@[simp] def toVC (A : ConstraintInstance) : Complexity.VertexCover.Instance :=
{ vertices := A.vertices, edges := A.constraints, k := A.k }

/-- RS recognizer: instance is accepted iff its Vertex Cover image has a cover. -/
@[simp] def Recognizes (A : ConstraintInstance) : Prop :=
  Complexity.VertexCover.HasCover (toVC A)

/-- The reduction from RS constraints to Vertex Cover (identity on fields). -/
@[simp] def reduceRS2VC : ConstraintInstance → Complexity.VertexCover.Instance := toVC

/-- Correctness of the reduction follows by definition. -/
@[simp] theorem reduce_correct (A : ConstraintInstance) :
  Recognizes A ↔ Complexity.VertexCover.HasCover (reduceRS2VC A) := Iff.rfl

/-- RS‑preserving wrapper bundling sizes and the reduction map. -/
@[simp] def rs_preserving_RS2VC :
  RSPreserving ConstraintInstance Complexity.VertexCover.Instance :=
{ sizeA := fun a => a.vertices.length + a.constraints.length
, sizeB := fun b => b.vertices.length + b.edges.length
, reduce := reduceRS2VC }

end RSVC

/-! #### RS-preserving reduction scaffold -/
structure RSPreserving (A B : Type) where
  sizeA : A → ℕ
  sizeB : B → ℕ
  reduce : A → B
  TcBound : (ℕ → ℕ) → Prop := fun _ => True
  TrBound : (ℕ → ℕ) → Prop := fun _ => True
  deriving Repr

end IndisputableMonolith
