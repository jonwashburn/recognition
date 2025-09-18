import Mathlib

namespace IndisputableMonolith
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

lemma Band.width_nonneg (b : Band) (hb : Band.Valid b) : 0 ≤ b.width := by
  dsimp [Band.width, Band.Valid] at *
  exact sub_nonneg.mpr hb

def wideBand (x : ℝ) (ε : ℝ) : Band := { lo := x - ε, hi := x + ε }

lemma wideBand_width {x ε : ℝ} (hε : 0 ≤ ε) : (wideBand x ε).width = 2 * ε := by
  dsimp [Band.width, wideBand]
  ring

lemma wideBand_valid' {x ε : ℝ} (hε : 0 ≤ ε) : (wideBand x ε).Valid := by
  dsimp [Band.Valid, wideBand]
  linarith

lemma wideBand_width_nonneg {x ε : ℝ} (hε : 0 ≤ ε) : 0 ≤ (wideBand x ε).width := by
  -- Use general width nonneg from validity instead of rewriting
  exact Band.width_nonneg _ (wideBand_valid' (x:=x) (ε:=ε) hε)

lemma wideBand_width_pos {x ε : ℝ} (hε : 0 < ε) : 0 < (wideBand x ε).width := by
  have hε' : 0 ≤ ε := le_of_lt hε
  have h2 : 0 < (2 : ℝ) := by norm_num
  -- width = 2 * ε
  simpa [wideBand_width hε', mul_comm] using mul_pos_of_pos_of_pos h2 hε

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

lemma wideBand_contains_lo {x ε : ℝ} (hε : 0 ≤ ε) :
  Band.contains (wideBand x ε) (wideBand x ε).lo :=
  Band.contains_lo_of_valid _ (wideBand_valid (x:=x) (ε:=ε) hε)

lemma wideBand_contains_hi {x ε : ℝ} (hε : 0 ≤ ε) :
  Band.contains (wideBand x ε) (wideBand x ε).hi :=
  Band.contains_hi_of_valid _ (wideBand_valid (x:=x) (ε:=ε) hε)

@[simp] def sampleBandsFor (x : ℝ) : Bands := [wideBand x 1]

lemma sampleBandsFor_nonempty (x : ℝ) : (sampleBandsFor x).length = 1 := by
  simp [sampleBandsFor]

lemma sampleBandsFor_singleton (x : ℝ) : sampleBandsFor x = [wideBand x 1] := by
  simp [sampleBandsFor]

@[simp] def evalToBands_c (c : ℝ) (x : ℝ) : Bands := sampleBandsFor (c * x)

noncomputable def meetsBandsChecker_gen (xs : List ℝ) (bs : Bands) : Bool := by
  classical
  exact xs.any (fun x => bs.any (fun b => decide (Band.contains b x)))

noncomputable def meetsBandsChecker (xs : List ℝ) (c : ℝ) : Bool :=
  meetsBandsChecker_gen xs (evalToBands_c c 1)

@[simp] lemma meetsBandsChecker_gen_nil (bs : Bands) :
  meetsBandsChecker_gen [] bs = false := by
  classical
  simp [meetsBandsChecker_gen]

@[simp] lemma meetsBandsChecker_nil (c : ℝ) :
  meetsBandsChecker [] c = false := by
  classical
  simp [meetsBandsChecker, meetsBandsChecker_gen]

@[simp] lemma meetsBandsChecker_gen_nilBands (xs : List ℝ) :
  meetsBandsChecker_gen xs [] = false := by
  classical
  simp [meetsBandsChecker_gen]

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

    /-! ### Abs-based characterization of wide bands -/
    lemma wideBand_contains_of_abs_le {x ε y : ℝ}
      (hε : 0 ≤ ε) (h : |y - x| ≤ ε) :
      Band.contains (wideBand x ε) y := by
      dsimp [Band.contains, wideBand]
      have h' := abs_le.mp h
      rcases h' with ⟨hle, hre⟩
      constructor
      · -- x - ε ≤ y
        have : -ε ≤ y - x := hle
        -- add x to both sides
        have := add_le_add_left this x
        simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
      · -- y ≤ x + ε
        -- rewrite to y - x ≤ ε then add x to both sides
        have := add_le_add_left hre x
        simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this

    lemma abs_le_of_wideBand_contains {x ε y : ℝ}
      (hε : 0 ≤ ε) (h : Band.contains (wideBand x ε) y) :
      |y - x| ≤ ε := by
      dsimp [Band.contains, wideBand] at h
      rcases h with ⟨hlo, hhi⟩
      -- x - ε ≤ y ≤ x + ε ⇒ -ε ≤ y - x ≤ ε
      have h_left : -ε ≤ y - x := by
        -- hlo: x - ε ≤ y ⇒ (x - ε) - x ≤ y - x ⇒ -ε ≤ y - x
        have := sub_le_sub_right hlo x
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      have h_right : y - x ≤ ε := by
        -- hhi: y ≤ x + ε ⇒ y - x ≤ (x + ε) - x ⇒ y - x ≤ ε
        have := sub_le_sub_left hhi x
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      exact abs_le.mpr ⟨h_left, h_right⟩

    lemma wideBand_contains_iff_abs_le {x ε y : ℝ}
      (hε : 0 ≤ ε) :
      Band.contains (wideBand x ε) y ↔ |y - x| ≤ ε := by
      constructor
      · exact abs_le_of_wideBand_contains (x:=x) (ε:=ε) (y:=y) hε
      · intro h; exact wideBand_contains_of_abs_le (x:=x) (ε:=ε) (y:=y) hε h

end RS
end RH
end IndisputableMonolith
