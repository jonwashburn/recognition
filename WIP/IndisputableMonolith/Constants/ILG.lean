import Mathlib
import IndisputableMonolith.Constants

namespace IndisputableMonolith
namespace Constants

@[simp] noncomputable def alpha_locked : ℝ := (1 - 1 / phi) / 2

@[simp] noncomputable def Clag : ℝ := 1 / (phi ^ (5 : Nat))

axiom alpha_locked_pos : 0 < alpha_locked

axiom alpha_locked_lt_one : alpha_locked < 1

lemma Clag_pos : 0 < Clag := by
  have hφ : 0 < phi := phi_pos
  have hpow : 0 < phi ^ (5 : Nat) := pow_pos hφ 5
  simpa [Clag, one_div] using inv_pos.mpr hpow

end Constants
end IndisputableMonolith
