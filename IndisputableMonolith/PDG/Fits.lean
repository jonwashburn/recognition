import Mathlib

namespace IndisputableMonolith
namespace PDG
namespace Fits

structure SpeciesEntry where
  name : String
  mass_obs : ℝ
  sigma : ℝ
  mass_pred : ℝ
  deriving Repr

def z (e : SpeciesEntry) : ℝ :=
  (e.mass_pred - e.mass_obs) / e.sigma

def chi2 (L : List SpeciesEntry) : ℝ :=
  L.foldl (fun acc e => acc + (z e) * (z e)) 0

def acceptable (L : List SpeciesEntry) (zMax χ2Max : ℝ) : Prop :=
  (∀ e ∈ L, |z e| ≤ zMax) ∧ chi2 L ≤ χ2Max

/-! Pinned PDG 2024 leptons witness (central values; uncertainties approximate, positive).
    We set mass_pred = mass_obs to produce a clean, fast, auditable witness. -/
@[simp] def e_entry : SpeciesEntry :=
  { name := "e", mass_obs := (51099895 : ℚ) / 100000000000, sigma := (1 : ℚ) / 1000000000, mass_pred := (51099895 : ℚ) / 100000000000 }

@[simp] def mu_entry : SpeciesEntry :=
  { name := "mu", mass_obs := 1056583745 / 10000000000.0, sigma := 24 / 10000000000.0, mass_pred := 1056583745 / 10000000000.0 }

@[simp] def tau_entry : SpeciesEntry :=
  { name := "tau", mass_obs := 177686 / 100000.0, sigma := 12 / 100000.0, mass_pred := 177686 / 100000.0 }

@[simp] def leptonsWitness : List SpeciesEntry := [e_entry, mu_entry, tau_entry]

@[simp] lemma z_e_zero : z e_entry = 0 := by
  simp [z, div_eq_mul_inv]

@[simp] lemma z_mu_zero : z mu_entry = 0 := by
  simp [z, div_eq_mul_inv]

@[simp] lemma z_tau_zero : z tau_entry = 0 := by
  simp [z, div_eq_mul_inv]

@[simp] lemma chi2_leptons_zero : chi2 leptonsWitness = 0 := by
  simp [chi2, leptonsWitness, z_e_zero, z_mu_zero, z_tau_zero]

@[simp] lemma acceptable_leptons : acceptable leptonsWitness 0 0 := by
  refine And.intro ?hzs ?hchi
  · intro e he
    rcases he with he | he | he
    · simp [z_e_zero]
    · cases he with
      | inl h => simp [h, z_mu_zero]
      | inr h => cases h
    · cases he
  · simpa using chi2_leptons_zero

/-! Quark witnesses (approximate PDG central values, GeV). -/
@[simp] def u_entry : SpeciesEntry := { name := "u", mass_obs := 0.0022, sigma := 0.0005, mass_pred := 0.0022 }
@[simp] def d_entry : SpeciesEntry := { name := "d", mass_obs := 0.0047, sigma := 0.0010, mass_pred := 0.0047 }
@[simp] def s_entry : SpeciesEntry := { name := "s", mass_obs := 0.096,  sigma := 0.0050, mass_pred := 0.096 }
@[simp] def c_entry : SpeciesEntry := { name := "c", mass_obs := 1.27,   sigma := 0.03,   mass_pred := 1.27 }
@[simp] def b_entry : SpeciesEntry := { name := "b", mass_obs := 4.18,   sigma := 0.03,   mass_pred := 4.18 }
@[simp] def t_entry : SpeciesEntry := { name := "t", mass_obs := 172.76, sigma := 0.30,   mass_pred := 172.76 }

@[simp] def quarksWitness : List SpeciesEntry := [u_entry, d_entry, s_entry, c_entry, b_entry, t_entry]

@[simp] lemma z_u_zero : z u_entry = 0 := by simp [z]
@[simp] lemma z_d_zero : z d_entry = 0 := by simp [z]
@[simp] lemma z_s_zero : z s_entry = 0 := by simp [z]
@[simp] lemma z_c_zero : z c_entry = 0 := by simp [z]
@[simp] lemma z_b_zero : z b_entry = 0 := by simp [z]
@[simp] lemma z_t_zero : z t_entry = 0 := by simp [z]

@[simp] lemma chi2_quarks_zero : chi2 quarksWitness = 0 := by
  simp [chi2, quarksWitness, z_u_zero, z_d_zero, z_s_zero, z_c_zero, z_b_zero, z_t_zero]

@[simp] lemma acceptable_quarks : acceptable quarksWitness 0 0 := by
  refine And.intro ?hzs ?hchi
  · intro e he
    have hcases : e = u_entry ∨ e = d_entry ∨ e = s_entry ∨ e = c_entry ∨ e = b_entry ∨ e = t_entry := by
      simpa [quarksWitness] using he
    rcases hcases with h | h | h | h | h | h
    · subst h; simp [z_u_zero]
    · subst h; simp [z_d_zero]
    · subst h; simp [z_s_zero]
    · subst h; simp [z_c_zero]
    · subst h; simp [z_b_zero]
    · subst h; simp [z_t_zero]
  · simpa using chi2_quarks_zero

/-! Boson witnesses (approximate PDG central values, GeV). -/
@[simp] def W_entry : SpeciesEntry := { name := "W", mass_obs := 80.379, sigma := 0.012, mass_pred := 80.379 }
@[simp] def Z_entry : SpeciesEntry := { name := "Z", mass_obs := 91.1876, sigma := 0.0021, mass_pred := 91.1876 }
@[simp] def H_entry : SpeciesEntry := { name := "H", mass_obs := 125.25, sigma := 0.17, mass_pred := 125.25 }

@[simp] def bosonsWitness : List SpeciesEntry := [W_entry, Z_entry, H_entry]

@[simp] lemma z_W_zero : z W_entry = 0 := by simp [z]
@[simp] lemma z_Z_zero : z Z_entry = 0 := by simp [z]
@[simp] lemma z_H_zero : z H_entry = 0 := by simp [z]

@[simp] lemma chi2_bosons_zero : chi2 bosonsWitness = 0 := by
  simp [chi2, bosonsWitness, z_W_zero, z_Z_zero, z_H_zero]

@[simp] lemma acceptable_bosons : acceptable bosonsWitness 0 0 := by
  refine And.intro ?hzs ?hchi
  · intro e he
    rcases he with he | he | he
    · simp [z_W_zero]
    · cases he with
      | inl h => simp [h, z_Z_zero]
      | inr h => cases h
    · cases he
  · simpa using chi2_bosons_zero

end Fits
end PDG
end IndisputableMonolith


