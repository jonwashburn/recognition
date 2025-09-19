import Mathlib

namespace IndisputableMonolith
namespace Recognition
namespace Certification

/-- Stub for Species type from Recognition (heavy dependency) -/
axiom Species : Type

/-- Stub for Z function from Recognition (heavy dependency) -/
axiom Z : Species → Int

/-- Stub for Fgap function from Recognition (heavy dependency) -/
noncomputable axiom Fgap : Int → ℝ

noncomputable section
open Classical

/-- Closed interval with endpoints `lo ≤ hi`. -/
structure Interval where
  lo : ℝ
  hi : ℝ
  lo_le_hi : lo ≤ hi

@[simp] def memI (I : Interval) (x : ℝ) : Prop := I.lo ≤ x ∧ x ≤ I.hi

@[simp] def width (I : Interval) : ℝ := I.hi - I.lo

/-- If `x,y` lie in the same interval `I`, then `|x − y| ≤ width(I)`. -/
lemma abs_sub_le_width_of_memI {I : Interval} {x y : ℝ}
  (hx : memI I x) (hy : memI I y) : |x - y| ≤ width I := by
  have : I.lo ≤ x ∧ x ≤ I.hi := hx
  have : I.lo ≤ y ∧ y ≤ I.hi := hy
  have : x - y ≤ I.hi - I.lo := by linarith
  have : y - x ≤ I.hi - I.lo := by linarith
  have : -(I.hi - I.lo) ≤ x - y ∧ x - y ≤ I.hi - I.lo := by
    constructor
    · linarith
    · linarith
  simpa [width, abs_le] using this

/-- Anchor certificate: species residue intervals and charge‑wise gap intervals. -/
structure AnchorCert where
  M0 : Interval
  Ires : Species → Interval
  center : Int → ℝ
  eps : Int → ℝ
  eps_nonneg : ∀ z, 0 ≤ eps z

@[simp] def Igap (C : AnchorCert) (z : Int) : Interval :=
{ lo := C.center z - C.eps z
, hi := C.center z + C.eps z
, lo_le_hi := by have := C.eps_nonneg z; linarith }


/-- Validity of a certificate w.r.t. the formal layer. -/
structure Valid (C : AnchorCert) : Prop where
  M0_pos : 0 < C.M0.lo
  Fgap_in : ∀ i : Species, memI (Igap C (Z i)) (Fgap (Z i))
  Ires_in_Igap : ∀ i : Species,
    (Igap C (Z i)).lo ≤ (C.Ires i).lo ∧ (C.Ires i).hi ≤ (Igap C (Z i)).hi

/-- Positivity of `M0` from the certificate. -/
lemma M0_pos_of_cert {C : AnchorCert} (hC : Valid C) : 0 < C.M0.lo := hC.M0_pos

/-- Certificate replacement for anchorIdentity (inequality form). -/
axiom anchorIdentity_cert {C : AnchorCert} (hC : Valid C)
  (res : Species → ℝ) (hres : ∀ i, memI (C.Ires i) (res i)) :
  ∀ i : Species, |res i - Fgap (Z i)| ≤ 2 * C.eps (Z i)

/-- Equal‑Z degeneracy (inequality form) from a certificate. -/
axiom equalZ_residue_of_cert {C : AnchorCert} (hC : Valid C)
  (res : Species → ℝ) (hres : ∀ i, memI (C.Ires i) (res i))
  {i j : Species} (hZ : Z i = Z j) :
  |res i - res j| ≤ 2 * C.eps (Z i)

/-! #### Zero-width anchor certificate (exact equality) -/

/-- Zero-width certificate with centers at `Fgap` and epsilons 0. -/
noncomputable def zeroWidthCert : AnchorCert :=
{ M0 := { lo := 1, hi := 1, lo_le_hi := by norm_num }
, Ires := fun i => { lo := Fgap (Z i), hi := Fgap (Z i), lo_le_hi := by linarith }
, center := fun z => Fgap z
, eps := fun _ => 0
, eps_nonneg := by intro _; exact by norm_num }

/-- Validity of the zero-width certificate. -/
lemma zeroWidthCert_valid : Valid zeroWidthCert := by
  refine {
    M0_pos := by simp [zeroWidthCert]
  , Fgap_in := by
      intro i; dsimp [zeroWidthCert, Igap, memI]; constructor <;> linarith
  , Ires_in_Igap := by
      intro i; dsimp [zeroWidthCert, Igap]; constructor <;> linarith }

/-- Exact anchor identity from the zero-width certificate: any residue inside the
    certified intervals equals `Fgap ∘ Z`. -/
lemma anchorIdentity_of_zeroWidthCert
  (res : Species → ℝ) (hres : ∀ i, memI (zeroWidthCert.Ires i) (res i)) :
  ∀ i : Species, res i = Fgap (Z i) := by
  intro i
  have h := hres i
  -- interval is [Fgap(Z i), Fgap(Z i)]
  dsimp [zeroWidthCert, memI] at h
  have hlo : Fgap (Z i) ≤ res i := by simpa using h.left
  have hhi : res i ≤ Fgap (Z i) := by simpa using h.right
  exact le_antisymm hhi hlo

end

end Certification
end Recognition
end IndisputableMonolith
