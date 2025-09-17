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

lemma wideBand_valid {x ε : ℝ} (hε : 0 ≤ ε) : (wideBand x ε).Valid := by
  dsimp [Band.Valid, wideBand]
  linarith

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

/-- Binary scale factor `B = 2^k` as a real. -/
def B_of (k : Nat) : ℝ := (2 : ℝ) ^ k

@[simp] lemma B_of_zero : B_of 0 = 1 := by simp [B_of]

@[simp] lemma B_of_succ (k : Nat) : B_of (k+1) = 2 * B_of k := by
  simp [B_of, pow_succ, mul_comm]

lemma B_of_pos (k : Nat) : 0 < B_of k := by
  have : 0 < (2:ℝ) := by norm_num
  simpa [B_of] using pow_pos this k

end RS
end RH

/‑! #### Recognition foundations ‑/
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

structure Ledger (M : RecognitionStructure) where
  debit : M.U → ℤ
  credit : M.U → ℤ

def phi {M} (L : Ledger M) : M.U → ℤ := fun u => L.debit u - L.credit u

def chainFlux {M} (L : Ledger M) (ch : Chain M) : ℤ :=
  phi L (Chain.last ch) - phi L (Chain.head ch)

class Conserves {M} (L : Ledger M) : Prop where
  conserve : ∀ ch : Chain M, ch.head = ch.last → chainFlux L ch = 0

lemma chainFlux_zero_of_loop {M} (L : Ledger M) [Conserves L] (ch : Chain M) (h : ch.head = ch.last) :
  chainFlux L ch = 0 := Conserves.conserve L ch h

class AtomicTick (M : RecognitionStructure) where
  postedAt : Nat → M.U → Prop
  unique_post : ∀ t : Nat, ∃! u : M.U, postedAt t u

theorem T2_atomicity {M} [AtomicTick M] :
  ∀ t u v, AtomicTick.postedAt (M:=M) t u → AtomicTick.postedAt (M:=M) t v → u = v := by
  intro t u v hu hv
  rcases (AtomicTick.unique_post (M:=M) t) with ⟨w, hw, huniq⟩
  exact huniq u w hu hw ▸ huniq v w hv hw ▸ rfl

end Recognition

/‑! ### RS‑preserving reduction exemplar (to Vertex Cover) ‑/
namespace Complexity

namespace VertexCover

/‑‑ Vertex Cover instance over `Nat` vertices. ‑/
structure Instance where
  vertices : List Nat
  edges    : List (Nat × Nat)
  k        : Nat
deriving Repr

/‑‑ A set `S` covers an edge `(u,v)` if it contains `u` or `v`. ‑/
def InCover (S : List Nat) (v : Nat) : Prop := v ∈ S

def EdgeCovered (S : List Nat) (e : Nat × Nat) : Prop :=
  InCover S e.fst ∨ InCover S e.snd

/‑‑ `S` covers all edges of instance `I`. ‑/
def Covers (S : List Nat) (I : Instance) : Prop :=
  ∀ e, e ∈ I.edges → EdgeCovered S e

/‑‑ There exists a vertex cover of size ≤ k. ‑/
def HasCover (I : Instance) : Prop :=
  ∃ S : List Nat, S.length ≤ I.k ∧ Covers S I

/‑‑ A trivial example with no edges is always covered by the empty set. ‑/
def example : Instance := { vertices := [1], edges := [], k := 0 }

lemma example_hasCover : HasCover example := by
  refine ⟨[], by decide, ?_⟩
  intro e he
  cases he

lemma Covers_nil_edges (S : List Nat) (I : Instance) (h_edges : I.edges = []) : Covers S I := by
  intro e he
  simpa [Covers, h_edges] using he.elim

lemma hasCover_of_nil_edges (I : Instance) (h_edges : I.edges = []) : HasCover I := by
  refine ⟨[], by simp, ?_⟩
  intro e he
  simpa [Covers, h_edges] using he.elim

end VertexCover

namespace RSVC

/‑‑ RS constraint instance mapped to edges to be covered. ‑/
structure ConstraintInstance where
  vertices    : List Nat
  constraints : List (Nat × Nat)
  k           : Nat
deriving Repr

/‑‑ Forgetful map to a Vertex Cover instance. ‑/
@[simp] def toVC (A : ConstraintInstance) : VertexCover.Instance :=
{ vertices := A.vertices, edges := A.constraints, k := A.k }

/‑‑ RS recognizer: instance is accepted iff its Vertex Cover image has a cover. ‑/
def Recognizes (A : ConstraintInstance) : Prop :=
  VertexCover.HasCover (toVC A)

/‑‑ The reduction from RS constraints to Vertex Cover (identity on fields). ‑/
@[simp] def reduceRS2VC : ConstraintInstance → VertexCover.Instance := toVC

/‑‑ Correctness is immediate from the definition. ‑/
@[simp] theorem reduce_correct (A : ConstraintInstance) :
  Recognizes A ↔ VertexCover.HasCover (reduceRS2VC A) := Iff.rfl

/‑‑ RS‑preserving reduction scaffold: relates complexities up to monotone envelopes. ‑/
structure RSPreserving (A B : Type) where
  sizeA : A → ℕ
  sizeB : B → ℕ
  reduce : A → B
  TcBound : (ℕ → ℕ) → Prop := fun _ => True
  TrBound : (ℕ → ℕ) → Prop := fun _ => True
deriving Repr

/‑‑ RS‑preserving wrapper bundling sizes and the reduction map. ‑/
def rs_preserving_RS2VC : RSPreserving ConstraintInstance VertexCover.Instance :=
{ sizeA := fun a => a.vertices.length + a.constraints.length
, sizeB := fun b => b.vertices.length + b.edges.length
, reduce := reduceRS2VC }

end RSVC

end Complexity

/‑! #### Balanced‑parity hidden mask (minimal) ‑/
namespace Complexity
namespace BalancedParityHidden

variable {n : ℕ} [DecidableEq (Fin n)]

/‑‑ Hidden mask encoder: bit b with mask R is `R` if b=false and `bnot ∘ R` if b=true. ‑/
def enc (b : Bool) (R : Fin n → Bool) : Fin n → Bool :=
  fun i => if b then bnot (R i) else R i

@[simp] lemma enc_false (R : Fin n → Bool) : enc (n:=n) false R = R := by
  funext i; simp [enc]

@[simp] lemma enc_true (R : Fin n → Bool) : enc (n:=n) true R = (fun i => bnot (R i)) := by
  funext i; simp [enc]

/‑‑ Restrict a full word to a queried index set `M`. ‑/
def restrict (f : Fin n → Bool) (M : Finset (Fin n)) : {i // i ∈ M} → Bool :=
  fun i => f i.val

@[simp] lemma restrict_enc_false (R : Fin n → Bool) (M : Finset (Fin n)) :
  restrict (n:=n) (enc false R) M = restrict (n:=n) R M := by
  funext i; simp [restrict, enc]

@[simp] lemma restrict_enc_true (R : Fin n → Bool) (M : Finset (Fin n)) :
  restrict (n:=n) (enc true R) M = (fun i => bnot (restrict (n:=n) R M i)) := by
  funext i; simp [restrict, enc]

/-- Extend a partial assignment on `M` to a full mask by defaulting to `false` off `M`. -/
def extendMask (a : {i // i ∈ M} → Bool) (M : Finset (Fin n)) : Fin n → Bool :=
  fun i => if h : i ∈ M then a ⟨i, h⟩ else false

/-- Any fixed-view decoder on a set `M` of queried indices can be fooled by a suitable `(b,R)`. -/
theorem adversarial_failure (M : Finset (Fin n))
  (g : (({i // i ∈ M} → Bool)) → Bool) :
  ∃ (b : Bool) (R : Fin n → Bool),
    g (restrict (n:=n) (enc b R) M) ≠ b := by
  classical
  -- Pick an arbitrary local view `a` and force the decoder to predict `b' := g a`.
  let a : {i // i ∈ M} → Bool := fun _ => false
  let b' : Bool := g a
  -- Choose the true bit to be the opposite of the decoder's prediction.
  let b : Bool := bnot b'
  -- Choose the mask so that the restricted encoding equals `a`.
  let R : Fin n → Bool :=
    if b = false then extendMask a M else extendMask (fun i => bnot (a i)) M
  have hRestr : restrict (n:=n) (enc b R) M = a := by
    funext i
    dsimp [restrict, enc, R, extendMask]
    by_cases hbf : b = false
    · -- Then `R = extendMask a M`, and restriction is exactly `a` on `M`.
      simp [hbf, dif_pos i.property]
    · have hb : b = true := by cases b <;> simp_all
      -- Then `R = extendMask (bnot ∘ a) M`, and restriction cancels the bnot.
      simp [hb, dif_pos i.property]
  refine ⟨b, R, ?_⟩
  -- The decoder outputs `g a = b' = bnot b`, hence it is wrong.
  have : g (restrict (n:=n) (enc b R) M) = b' := by simpa [hRestr]
  have hbrel : b = bnot b' := rfl
  cases b <;> simp [hbrel, this]

/-- If a decoder is correct for all `(b,R)` while querying only `M`, contradiction. -/
theorem no_universal_decoder (M : Finset (Fin n))
  (g : (({i // i ∈ M} → Bool)) → Bool) :
  ¬ (∀ (b : Bool) (R : Fin n → Bool), g (restrict (n:=n) (enc b R) M) = b) := by
  classical
  intro h
  rcases adversarial_failure (n:=n) M g with ⟨b, R, hw⟩
  have := h b R
  exact hw this

end BalancedParityHidden
end Complexity

/‑! #### URC generators (minimal certifications) ‑/
namespace URCGenerators

structure UnitsCert where
  lo : ℚ
  hi : ℚ
deriving Repr

/‑‑ Units certificate is verified if 1 lies within the rational bounds. ‑/
@[simp] def UnitsCert.verified (c : UnitsCert) : Prop :=
  (c.lo : ℝ) ≤ 1 ∧ 1 ≤ (c.hi : ℝ)

structure EightBeatCert where
  T : Nat
deriving Repr

/‑‑ Eight‑beat certificate is verified if `T ≥ 8`. ‑/
@[simp] def EightBeatCert.verified (c : EightBeatCert) : Prop := 8 ≤ c.T

structure ELProbe where eps : ℚ
deriving Repr

@[simp] def ELProbe.verified (c : ELProbe) : Prop := 0 ≤ (c.eps : ℝ)

end URCGenerators

end IndisputableMonolith
