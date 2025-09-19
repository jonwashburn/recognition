import Mathlib
import IndisputableMonolith

namespace IndisputableMonolith
namespace Ethics
namespace Decision

universe u
variable {A : Type u}

-- Prop-level counterparts (skeletal: default True)
def JusticeOKP (r : Request A) : Prop := True
def ReciprocityOKP (r : Request A) : Prop := True
def TemperanceOKP (r : Request A) : Prop := True
def WithinWindowP (r : Request A) : Prop := True
def UniqueInWindowP (r : Request A) : Prop := True
def FairnessOKP (r : Request A) : Prop := True
def AdversarialOKP (r : Request A) : Prop := True
def TruthOKP (P : Policy A) (r : Request A) : Prop := True
def ConsentOKP (P : Policy A) (r : Request A) : Prop := True
def HarmOKP (P : Policy A) (r : Request A) : Prop := True
def DeonticOKP (P : Policy A) (r : Request A) : Prop := True
def PrivacyOKP (P : Policy A) (r : Request A) : Prop := True
def COIOKP (P : Policy A) (r : Request A) : Prop := True
def RobustOKP (P : Policy A) (r : Request A) : Prop := True
def FairnessBatchOKP (P : Policy A) (xs : List (Request A)) : Prop := True

-- Bool ↔ Prop bridging lemmas
@[simp] lemma justiceOk_true_iff (r : Request A) : justiceOk r = true ↔ JusticeOKP r := by
  simp [justiceOk, JusticeOKP]

@[simp] lemma reciprocityOk_true_iff (P : Policy A) (r : Request A) :
  reciprocityOk (P:=P) r = true ↔ ReciprocityOKP r := by
  simp [reciprocityOk, ReciprocityOKP]

@[simp] lemma temperanceOk_true_iff (P : Policy A) (r : Request A) :
  temperanceOk (P:=P) r = true ↔ TemperanceOKP r := by
  simp [temperanceOk, TemperanceOKP]

@[simp] lemma withinWindow_true_iff (r : Request A) :
  withinWindow r = true ↔ WithinWindowP r := by
  simp [withinWindow, WithinWindowP]

@[simp] lemma uniqueInWindow_true_iff (r : Request A) :
  uniqueInWindow r = true ↔ UniqueInWindowP r := by
  simp [uniqueInWindow, UniqueInWindowP]

@[simp] lemma fairnessOk_true_iff (r : Request A) :
  fairnessOk r = true ↔ FairnessOKP r := by
  simp [fairnessOk, FairnessOKP]

@[simp] lemma adversarialOk_true_iff (r : Request A) :
  adversarialOk r = true ↔ AdversarialOKP r := by
  simp [adversarialOk, AdversarialOKP]

@[simp] lemma truthOk_true_iff (P : Policy A) (r : Request A) :
  truthOk (P:=P) r = true ↔ TruthOKP (P:=P) r := by
  simp [truthOk, TruthOKP]

@[simp] lemma consentOk_true_iff (P : Policy A) (r : Request A) :
  consentOk (P:=P) r = true ↔ ConsentOKP (P:=P) r := by
  simp [consentOk, ConsentOKP]

@[simp] lemma harmOk_true_iff (P : Policy A) (r : Request A) :
  harmOk (P:=P) r = true ↔ HarmOKP (P:=P) r := by
  simp [harmOk, HarmOKP]

@[simp] lemma deonticOk_true_iff (P : Policy A) (r : Request A) :
  deonticOk (P:=P) r = true ↔ DeonticOKP (P:=P) r := by
  simp [deonticOk, DeonticOKP]

@[simp] lemma privacyOk_true_iff (P : Policy A) (r : Request A) :
  privacyOk (P:=P) r = true ↔ PrivacyOKP (P:=P) r := by
  simp [privacyOk, PrivacyOKP]

@[simp] lemma coiOk_true_iff (P : Policy A) (r : Request A) :
  coiOk (P:=P) r = true ↔ COIOKP (P:=P) r := by
  simp [coiOk, COIOKP]

@[simp] lemma robustOk_true_iff (P : Policy A) (r : Request A) :
  robustOk (P:=P) r = true ↔ RobustOKP (P:=P) r := by
  simp [robustOk, RobustOKP]

lemma admissible_true_iff (P : Policy A) (r : Request A) :
  admissible (P:=P) r = true ↔ Admissible P.period r.cq r.hasExperience := by
  classical
  by_cases h : Admissible P.period r.cq r.hasExperience
  · simp [admissible, h]
  · simp [admissible, h]

end Decision
end Ethics
end IndisputableMonolith
