/-
SOLUTION — proves every statement of `Challenge.lean` by direct term assignment from the
development (`Erdos361.Core`, `Erdos361.InverseMain`, `Erdos361.Asymptotics`). Because the
development imports `Erdos361.Statement`, the trusted definitions `Avoids/Avoiders/F/Fc` are the
very same constants, so the assignments type-check with no transport lemma. (The file
`Erdos361/InverseGlue.lean` uses its own `Erdos361InverseGlue.Avoids`, which is definitionally
equal.)

Axiom footprint of every theorem (see the `#print axioms` commands at the end):
`[propext, Classical.choice, Quot.sound]`.
-/
import Erdos361
set_option autoImplicit false

namespace Erdos361.Statement
open Filter Topology
open scoped Pointwise

theorem erdos361_cge1 (M n : ℕ) (hn : 1 ≤ n) (hM : n ≤ M) :
    F M n = M - (n + 1) / 2 :=
  _root_.Erdos361.erdos361_cge1 M n hn hM

theorem erdos361_cge1_limit (c : ℝ) (hc : 1 ≤ c) :
    Tendsto (fun n : ℕ => (Fc c n : ℝ) / n) atTop (nhds (c - 1 / 2)) :=
  _root_.Erdos361Asymptotics.Fc_limit_cge1 c hc

theorem erdos361_irregular (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ¬ ∃ L : ℝ, Tendsto (fun n : ℕ => (Fc c n : ℝ) / n) atTop (nhds L) :=
  _root_.Erdos361.erdos361_irregular c hc0 hc1

theorem erdos361_upper_half (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → (Fc c n : ℝ) ≤ (c / 2 + ε) * n :=
  _root_.Erdos361Asymptotics.Fc_upper_s1 c hc0 hc1 ε hε

theorem erdos361_odd_limit (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun k : ℕ => (Fc c (2 * k + 1) : ℝ) / ((2 * k + 1 : ℕ) : ℝ)) atTop
      (nhds (c / 2)) :=
  _root_.Erdos361Asymptotics.Fc_limit_odd c hc0 hc1

theorem erdos361_mod6_limit_low (c : ℝ) (hc0 : 0 < c) (hc12 : c ≤ 1 / 2) (r : ℕ)
    (hr : r = 2 ∨ r = 4) :
    Tendsto (fun k : ℕ => (Fc c (6 * k + r) : ℝ) / ((6 * k + r : ℕ) : ℝ)) atTop
      (nhds (c / 3)) :=
  _root_.Erdos361Asymptotics.Fc_limit_mod6_low c hc0 hc12 r hr

theorem erdos361_mod6_limit_high (c : ℝ) (hc12 : 1 / 2 < c) (hc1 : c < 1) (r : ℕ)
    (hr : r = 2 ∨ r = 4) :
    Tendsto (fun k : ℕ => (Fc c (6 * k + r) : ℝ) / ((6 * k + r : ℕ) : ℝ)) atTop
      (nhds (2 * c / 3 - 1 / 6)) :=
  _root_.Erdos361Asymptotics.Fc_limit_mod6_high c hc12 hc1 r hr

theorem erdos361_two_limit_points (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ L₁ L₂ : ℝ, L₁ ≠ L₂ ∧
      Tendsto (fun k : ℕ => (Fc c (2 * k + 1) : ℝ) / ((2 * k + 1 : ℕ) : ℝ)) atTop (nhds L₁) ∧
      Tendsto (fun k : ℕ => (Fc c (6 * k + 2) : ℝ) / ((6 * k + 2 : ℕ) : ℝ)) atTop
        (nhds L₂) :=
  _root_.Erdos361Asymptotics.Fc_two_limit_points c hc0 hc1

theorem inverse_s1 (ε : ℝ) (hε : 0 < ε) (K : ℕ) :
    ∃ E₀ : ℕ, ∀ E : ℕ, E₀ ≤ E → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 E →
      (1 / 2 + ε) * E ≤ (A.card : ℝ) → ∀ t : ℕ, E ≤ t → t ≤ K * E → ¬ Avoids A t :=
  _root_.Erdos361Asymptotics.inverse_s1 ε hε K

theorem inverse_s2 (ε : ℝ) (hε : 0 < ε) (K : ℕ) :
    ∃ E₀ : ℕ, ∀ E : ℕ, E₀ ≤ E → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 E →
      (1 / 3 + ε) * E ≤ (A.card : ℝ) →
      ∀ t : ℕ, 2 ∣ t → 2 * E ≤ t → t ≤ K * E → ¬ Avoids A t :=
  _root_.Erdos361Asymptotics.inverse_s2 ε hε K

theorem inverse_s2_restricted (ε : ℝ) (hε : 0 < ε) :
    ∃ E₀ : ℕ, ∀ E : ℕ, E₀ ≤ E → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 E →
      (1 / 3 + ε) * E ≤ (A.card : ℝ) →
      ∀ t : ℕ, 2 * E < t → t < 3 * E → 2 ∣ t → ¬ 3 ∣ t → ¬ Avoids A t :=
  _root_.Erdos361InverseMain.inverse_restricted ε hε

end Erdos361.Statement

#print axioms Erdos361.Statement.erdos361_cge1
#print axioms Erdos361.Statement.erdos361_cge1_limit
#print axioms Erdos361.Statement.erdos361_irregular
#print axioms Erdos361.Statement.erdos361_upper_half
#print axioms Erdos361.Statement.erdos361_odd_limit
#print axioms Erdos361.Statement.erdos361_mod6_limit_low
#print axioms Erdos361.Statement.erdos361_mod6_limit_high
#print axioms Erdos361.Statement.erdos361_two_limit_points
#print axioms Erdos361.Statement.inverse_s1
#print axioms Erdos361.Statement.inverse_s2
#print axioms Erdos361.Statement.inverse_s2_restricted
