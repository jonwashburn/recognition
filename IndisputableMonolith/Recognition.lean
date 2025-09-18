import Mathlib
-- LightCone is not required by the minimal Recognition core; avoid heavy deps

namespace IndisputableMonolith
namespace Recognition

/-! ### T1 (MP): Nothing cannot recognize itself -/

abbrev Nothing := Empty

/-- Minimal recognizer→recognized pairing. -/
structure Recognize (A : Type) (B : Type) : Type where
  recognizer : A
  recognized : B

/-- MP: It is impossible for Nothing to recognize itself. -/
def MP : Prop := ¬ ∃ _ : Recognize Nothing Nothing, True

theorem mp_holds : MP := by
  intro h
  rcases h with ⟨⟨r, _⟩, _⟩
  cases r

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

lemma phi_zero_of_balanced {M} (L : Ledger M) (hbal : ∀ u, L.debit u = L.credit u) :
  ∀ u, phi L u = 0 := by
  intro u; simp [phi, hbal u, sub_self]

lemma chainFlux_zero_of_balanced {M} (L : Ledger M) (ch : Chain M)
  (hbal : ∀ u, L.debit u = L.credit u) :
  chainFlux L ch = 0 := by
  simp [chainFlux, phi_zero_of_balanced (M:=M) L hbal]

class AtomicTick (M : RecognitionStructure) where
  postedAt : Nat → M.U → Prop
  unique_post : ∀ t : Nat, ∃! u : M.U, postedAt t u

theorem T2_atomicity {M} [AtomicTick M] :
  ∀ t u v, AtomicTick.postedAt (M:=M) t u → AtomicTick.postedAt (M:=M) t v → u = v := by
  intro t u v hu hv
  rcases (AtomicTick.unique_post (M:=M) t) with ⟨w, hw, huniq⟩
  exact huniq u w hu hw ▸ huniq v w hv hw ▸ rfl

end Recognition

namespace Demo

open Recognition

structure U where
  a : Unit

def recog : U → U → Prop := fun _ _ => True

def M : RecognitionStructure := { U := U, R := recog }

def L : Ledger M := { debit := fun _ => 1, credit := fun _ => 1 }

def twoStep : Chain M :=
  { n := 1
  , f := fun _ => ⟨()⟩
  , ok := by intro i; trivial }

example : chainFlux L twoStep = 0 := by
  haveI : Conserves L :=
    { conserve := by
        intro ch h; simp [chainFlux, phi, Recognition.Chain.head, Recognition.Chain.last, h] }
  have hloop : twoStep.head = twoStep.last := rfl
  simpa [hloop] using (chainFlux_zero_of_loop L twoStep hloop)

end Demo

/‑! ## Classical bridge: determinized posting schedule under atomicity -/
namespace ClassicalBridge

open Recognition

variable {M : Recognition.RecognitionStructure}

noncomputable def schedule [Recognition.AtomicTick M] (t : Nat) : M.U :=
  Classical.choose (by
    have h := (Recognition.AtomicTick.unique_post (M:=M) t)
    rcases h with ⟨w, hw, _⟩
    exact ⟨w, hw⟩)

lemma postedAt_schedule [Recognition.AtomicTick M] (t : Nat) :
  Recognition.AtomicTick.postedAt (M:=M) t (schedule (M:=M) t) := by
  classical
  have h := (Recognition.AtomicTick.unique_post (M:=M) t)
  rcases h with ⟨w, hw, _⟩
  dsimp [schedule]
  simpa [Classical.choose] using (Classical.choose_spec ⟨w, hw⟩)

lemma schedule_unique [Recognition.AtomicTick M] {t : Nat} {u : M.U}
  (hu : Recognition.AtomicTick.postedAt (M:=M) t u) : u = schedule (M:=M) t := by
  classical
  rcases (Recognition.AtomicTick.unique_post (M:=M) t) with ⟨w, hw, huniq⟩
  have : u = w := huniq u hu
  have : schedule (M:=M) t = w := by
    apply (huniq (schedule (M:=M) t) (postedAt_schedule (M:=M) t)).symm
  simpa [this]

end ClassicalBridge

/‑! ## Nontrivial modeling instances: concrete `AtomicTick` examples -/
namespace ModelingExamples

open Recognition

/-- A simple 2‑vertex recognition structure with bidirectional relation. -/
def SimpleStructure : Recognition.RecognitionStructure :=
  { U := Bool
  , R := fun a b => a ≠ b }

/-- Deterministic posting schedule: the unique poster at time `t` is `(t % 2 == 1)`. -/
def SimpleTicks : Nat → Bool → Prop := fun t v => v = (t % 2 == 1)

instance : Recognition.AtomicTick SimpleStructure :=
  { postedAt := SimpleTicks
  , unique_post := by
      intro t
      refine ⟨(t % 2 == 1), rfl, ?uniq⟩
      intro u hu
      simpa [SimpleTicks] using hu }

/-- A 3‑cycle recognition structure on `Fin 3`. -/
def Cycle3 : Recognition.RecognitionStructure :=
  { U := Fin 3
  , R := fun i j => j = ⟨(i.val + 1) % 3, by
                        have : (i.val + 1) % 3 < 3 := by
                          have : (i.val + 1) % 3 < 3 := Nat.mod_lt _ (by decide : 0 < 3)
                          simpa using this
                        exact this⟩ }

/-- Unique poster at time `t` is the residue class `t % 3`. -/
def Cycle3Ticks : Nat → (Fin 3) → Prop := fun t v => v.val = t % 3

instance : Recognition.AtomicTick Cycle3 :=
  { postedAt := Cycle3Ticks
  , unique_post := by
      intro t
      refine ⟨⟨t % 3, by exact Nat.mod_lt _ (by decide : 0 < 3)⟩, ?posted, ?uniq⟩
      · rfl
      · intro u hu
        -- Coerce equality on values to equality in `Fin 3`.
        apply Fin.ext
        simpa [Cycle3Ticks] using hu }

end ModelingExamples

end IndisputableMonolith

/-! ## ClassicalBridge (components and gauge): reach components and equality up to a constant. -/
namespace IndisputableMonolith
namespace ClassicalBridge

open Recognition
open Recognition.Potential
open Causality

variable {M : Recognition.RecognitionStructure}

/-- The reach component of a basepoint `x0`. -/
structure Component (M : Recognition.RecognitionStructure) (x0 : M.U) where
  y : M.U
  reachable : Reaches (Potential.Kin M) x0 y

/-- Potentials restricted to the reach component of `x0`. -/
abbrev PotOnComp (M : Recognition.RecognitionStructure) (x0 : M.U) := Component M x0 → ℤ

/-- Restrict a potential to the reach component of `x0`. -/
def restrictToComponent (x0 : M.U) (p : Potential.Pot M) : PotOnComp M x0 :=
  fun yc => p yc.y

/-- Equality up to an additive constant on a component (classical gauge freedom). -/
def GaugeEq (x0 : M.U) (f g : PotOnComp M x0) : Prop := ∃ c : ℤ, ∀ yc, f yc = g yc + c

lemma gauge_refl (x0 : M.U) (f : PotOnComp M x0) : GaugeEq (M:=M) x0 f f :=
  ⟨0, by intro yc; simp⟩

lemma gauge_symm (x0 : M.U) {f g : PotOnComp M x0}
  (hfg : GaugeEq (M:=M) x0 f g) : GaugeEq (M:=M) x0 g f := by
  rcases hfg with ⟨c, hc⟩
  refine ⟨-c, ?_⟩
  intro yc
  have := hc yc
  -- f yc = g yc + c ⇒ g yc = f yc - c = f yc + (-c)
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    (eq_sub_iff_add_eq.mp (Eq.symm this))

lemma gauge_trans (x0 : M.U) {f g h : PotOnComp M x0}
  (hfg : GaugeEq (M:=M) x0 f g) (hgh : GaugeEq (M:=M) x0 g h) :
  GaugeEq (M:=M) x0 f h := by
  rcases hfg with ⟨c1, hc1⟩
  rcases hgh with ⟨c2, hc2⟩
  refine ⟨c1 + c2, ?_⟩
  intro yc
  have := hc1 yc
  have := this.trans (by simpa [add_comm, add_left_comm, add_assoc] using congrArg (fun t => t + c2) (hc2 yc).symm)
  -- f = g + c1 and g = h + c2 ⇒ f = h + (c1+c2)
  simpa [add_comm, add_left_comm, add_assoc] using this

end ClassicalBridge
end IndisputableMonolith

/-! ## T4 (potential uniqueness): invariants along reaches and uniqueness on components. -/
namespace IndisputableMonolith
namespace Recognition

open Causality

variable {M : RecognitionStructure}

namespace Potential

abbrev Pot (M : RecognitionStructure) := M.U → ℤ

/-- Discrete edge rule: potential increments by a fixed integer `δ` along each edge. -/
def DE (δ : ℤ) (p : Pot M) : Prop := ∀ {a b}, M.R a b → p b - p a = δ

/-- View a recognition structure as a kinematics (step relation `R`). -/
def Kin (M : RecognitionStructure) : Causality.Kinematics M.U := { step := M.R }

/-- On each edge, the difference (p − q) is invariant if both satisfy the same δ rule. -/
lemma edge_diff_invariant {δ : ℤ} {p q : Pot M}
  (hp : DE (M:=M) δ p) (hq : DE (M:=M) δ q) {a b : M.U} (h : M.R a b) :
  (p b - q b) = (p a - q a) := by
  have harr : (p b - q b) - (p a - q a) = (p b - p a) - (q b - q a) := by ring
  have hδ : (p b - p a) - (q b - q a) = δ - δ := by simp [hp h, hq h]
  have : (p b - q b) - (p a - q a) = 0 := by simp [harr, hδ]
  exact sub_eq_zero.mp this

/-- The difference (p − q) is constant along any n‑step reach. -/
lemma diff_const_on_ReachN {δ : ℤ} {p q : Pot M}
  (hp : DE (M:=M) δ p) (hq : DE (M:=M) δ q) :
  ∀ {n x y}, Causality.ReachN (Kin M) n x y → (p y - q y) = (p x - q x) := by
  intro n x y h
  induction h with
  | zero => rfl
  | @succ n x y z hxy hyz ih =>
      have h_edge : (p z - q z) = (p y - q y) :=
        edge_diff_invariant (M:=M) (δ:=δ) (p:=p) (q:=q) hp hq hyz
      exact h_edge.trans ih

/-- On reach components, the difference (p − q) equals its basepoint value. -/
lemma diff_const_on_component {δ : ℤ} {p q : Pot M}
  (hp : DE (M:=M) δ p) (hq : DE (M:=M) δ q) {x0 y : M.U}
  (hreach : Causality.Reaches (Kin M) x0 y) :
  (p y - q y) = (p x0 - q x0) := by
  rcases hreach with ⟨n, h⟩
  simpa using diff_const_on_ReachN (M:=M) (δ:=δ) (p:=p) (q:=q) hp hq (n:=n) (x:=x0) (y:=y) h

/-- If two δ‑potentials agree at a basepoint, they agree on its n-step reach set. -/
theorem T4_unique_on_reachN {δ : ℤ} {p q : Pot M}
  (hp : DE (M:=M) δ p) (hq : DE (M:=M) δ q) {x0 : M.U}
  (hbase : p x0 = q x0) : ∀ {n y}, Causality.ReachN (Kin M) n x0 y → p y = q y := by
  intro n y h
  have hdiff := diff_const_on_ReachN (M:=M) (δ:=δ) (p:=p) (q:=q) hp hq h
  have : p x0 - q x0 = 0 := by simp [hbase]
  have : p y - q y = 0 := by simpa [this] using hdiff
  exact sub_eq_zero.mp this

/-- Componentwise uniqueness: if p and q agree at x0, they agree at every y reachable from x0. -/
theorem T4_unique_on_component {δ : ℤ} {p q : Pot M}
  (hp : DE (M:=M) δ p) (hq : DE (M:=M) δ q) {x0 y : M.U}
  (hbase : p x0 = q x0)
  (hreach : Causality.Reaches (Kin M) x0 y) : p y = q y := by
  rcases hreach with ⟨n, h⟩
  exact T4_unique_on_reachN (M:=M) (δ:=δ) (p:=p) (q:=q) hp hq (x0:=x0) hbase (n:=n) (y:=y) h

/-- If y lies within some ≤ n-step reach, p and q agree at y. -/
theorem T4_unique_on_inBall {δ : ℤ} {p q : Pot M}
  (hp : DE (M:=M) δ p) (hq : DE (M:=M) δ q) {x0 y : M.U}
  (hbase : p x0 = q x0) {n : Nat}
  (hin : ∃ k ≤ n, Causality.ReachN (Kin M) k x0 y) : p y = q y := by
  rcases hin with ⟨k, _, hreach⟩
  exact T4_unique_on_reachN (M:=M) (δ:=δ) (p:=p) (q:=q) hp hq (x0:=x0) hbase (n:=k) (y:=y) hreach

/-- Quantization: along any n‑step reach, `p` changes by exactly `n·δ`. -/
lemma increment_on_ReachN {δ : ℤ} {p : Pot M}
  (hp : DE (M:=M) δ p) :
  ∀ {n x y}, Causality.ReachN (Kin M) n x y → p y - p x = (n : ℤ) * δ := by
  intro n x y h
  induction h with
  | zero =>
      simp
  | @succ n x y z hxy hyz ih =>
      have hz : p z - p y = δ := hp hyz
      calc
        p z - p x = (p z - p y) + (p y - p x) := by ring
        _ = δ + (n : ℤ) * δ := by simpa [hz, ih]
        _ = ((n : ℤ) + 1) * δ := by ring
        _ = ((Nat.succ n : Nat) : ℤ) * δ := by
              simp [Nat.cast_add, Nat.cast_ofNat]

/-- Differences along any reach lie in the δ-generated subgroup. -/
lemma diff_in_deltaSub {δ : ℤ} {p : Pot M}
  (hp : DE (M:=M) δ p) {n x y}
  (h : Causality.ReachN (Kin M) n x y) : ∃ k : ℤ, p y - p x = k * δ := by
  refine ⟨(n : ℤ), ?_⟩
  simpa using increment_on_ReachN (M:=M) (δ:=δ) (p:=p) hp (n:=n) (x:=x) (y:=y) h

end Potential

/-! Ledger uniqueness via affine edge increments (wrappers around potentials). -/
namespace LedgerUniqueness

open Potential

variable {M : RecognitionStructure}

def IsAffine (δ : ℤ) (L : Ledger M) : Prop :=
  Potential.DE (M:=M) δ (phi L)

lemma phi_edge_increment (δ : ℤ) {L : Ledger M}
  (h : IsAffine (M:=M) δ L) {a b : M.U} (hR : M.R a b) :
  phi L b - phi L a = δ := h hR

/-- If two affine ledgers (same δ) agree at a basepoint, they agree on its n-step reach set. -/
theorem unique_on_reachN {δ : ℤ} {L L' : Ledger M}
  (hL : IsAffine (M:=M) δ L) (hL' : IsAffine (M:=M) δ L')
  {x0 : M.U} (hbase : phi L x0 = phi L' x0) :
  ∀ {n y}, Causality.ReachN (Potential.Kin M) n x0 y → phi L y = phi L' y := by
  intro n y hreach
  have :=
    Potential.T4_unique_on_reachN (M:=M) (δ:=δ)
      (p := phi L) (q := phi L') (hp := hL) (hq := hL') (x0 := x0) hbase (n:=n) (y:=y) hreach
  simpa using this

/-- If two affine ledgers (same δ) agree at a basepoint, they agree within any ≤ n-step reach. -/
theorem unique_on_inBall {δ : ℤ} {L L' : Ledger M}
  (hL : IsAffine (M:=M) δ L) (hL' : IsAffine (M:=M) δ L')
  {x0 y : M.U} (hbase : phi L x0 = phi L' x0) {n : Nat}
  (hin : ∃ k ≤ n, Causality.ReachN (Potential.Kin M) k x0 y) : phi L y = phi L' y := by
  exact Potential.T4_unique_on_inBall (M:=M) (δ:=δ)
    (p := phi L) (q := phi L') (hp := hL) (hq := hL') (x0 := x0)
    hbase (n:=n) (y:=y) hin

/-- Uniqueness up to a constant on the reach component: affine ledgers differ by a constant. -/
theorem unique_up_to_const_on_component {δ : ℤ} {L L' : Ledger M}
  (hL : IsAffine (M:=M) δ L) (hL' : IsAffine (M:=M) δ L')
  {x0 : M.U} : ∃ c : ℤ, ∀ {y : M.U}, Causality.Reaches (Potential.Kin M) x0 y →
    phi L y = phi L' y + c := by
  refine ⟨phi L x0 - phi L' x0, ?_⟩
  intro y hreach
  have hdiff := Potential.diff_const_on_component (M:=M) (δ:=δ)
                  (p := phi L) (q := phi L') hL hL' (x0:=x0) (y:=y) hreach
  simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
    using (eq_add_of_sub_eq hdiff)

end LedgerUniqueness

end Recognition
end IndisputableMonolith
