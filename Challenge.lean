/-
TRUSTED CHALLENGE FILE — the statements, without proofs.

This file is the audit surface. Comparator (github.com/leanprover/comparator) checks that
the corresponding declarations in `Solution.lean` prove EXACTLY these statements, using no
axioms beyond the permitted list in `comparator/*.json` (`propext`, `Quot.sound`,
`Classical.choice`).

The `sorry`s below are deliberate and are the only `sorry`s in the repository.

IMPORT CLOSURE: Mathlib only. The definitions in the first namespace block are a verbatim copy
of `Erdos361/Statement.lean`; Comparator checks that the two copies agree.

WHAT EACH STATEMENT SAYS, in words (`f_c(n) = Fc c n = F ⌊cn⌋ n`):

  erdos361_cge1            For 1 ≤ n ≤ M, F M n = M − ⌈n/2⌉ (here `(n+1)/2` = ⌈n/2⌉).
  erdos361_cge1_limit      For c ≥ 1, f_c(n)/n → c − 1/2.                          [new]
  erdos361_irregular       For 0 < c < 1, f_c(n)/n does not converge.
  erdos361_upper_half      For 0 < c ≤ 1 and ε > 0, eventually f_c(n) ≤ (c/2 + ε)n.  [new]
  erdos361_odd_limit       For 0 < c ≤ 1, f_c(n)/n → c/2 along odd n.              [new]
  erdos361_mod6_limit_low  For 0 < c ≤ 1/2, f_c(n)/n → c/3 along n ≡ 2,4 (mod 6).  [new]
  erdos361_mod6_limit_high For 1/2 < c < 1, f_c(n)/n → 2c/3 − 1/6 along n ≡ 2,4 (mod 6). [new]
  erdos361_two_limit_points For 0 < c < 1, two distinct subsequential limits.        [new]
  inverse_s1               Dense (> 1/2) subsets of [1,E] represent every t ∈ [E, K·E].   [new]
  inverse_s2               Dense (> 1/3) subsets of [1,E] represent every even t ∈ [2E, K·E]. [new]
  inverse_s2_restricted    Dense (> 1/3) subsets of [1,E] represent every even t ∈ (2E,3E), 3∤t.

Statements marked [new] are proved in `Erdos361/Asymptotics.lean`.
-/
import Mathlib
set_option autoImplicit false

namespace Erdos361.Statement
open Finset
open scoped Classical
def Avoids (A : Finset ℕ) (n : ℕ) : Prop := ∀ B ⊆ A, B.sum id = n → B = ∅
noncomputable def Avoiders (M n : ℕ) : Finset (Finset ℕ) :=
  (Icc 1 M).powerset.filter (fun A => Avoids A n)
noncomputable def F (M n : ℕ) : ℕ := (Avoiders M n).sup Finset.card
noncomputable def Fc (c : ℝ) (n : ℕ) : ℕ := F ⌊c * n⌋₊ n
end Erdos361.Statement

namespace Erdos361.Statement
open Filter Topology
open scoped Pointwise

/-- **Erdős #361, regular range.** For `1 ≤ n ≤ M`, `F M n = M − ⌈n/2⌉`. -/
theorem erdos361_cge1 (M n : ℕ) (hn : 1 ≤ n) (hM : n ≤ M) :
    F M n = M - (n + 1) / 2 := by
  sorry

/-- **Erdős #361, regular range, limit form.** For `c ≥ 1`, `f_c(n)/n → c − 1/2`. -/
theorem erdos361_cge1_limit (c : ℝ) (hc : 1 ≤ c) :
    Tendsto (fun n : ℕ => (Fc c n : ℝ) / n) atTop (nhds (c - 1 / 2)) := by
  sorry

/-- **Erdős #361, irregularity (c ∈ (0,1)).** `f_c(n)/n` does not converge. -/
theorem erdos361_irregular (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ¬ ∃ L : ℝ, Tendsto (fun n : ℕ => (Fc c n : ℝ) / n) atTop (nhds L) := by
  sorry

/-- **Sharp upper bound.** For `0 < c ≤ 1`, eventually `f_c(n) ≤ (c/2 + ε) n`. -/
theorem erdos361_upper_half (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → (Fc c n : ℝ) ≤ (c / 2 + ε) * n := by
  sorry

/-- **Odd `n`.** For `0 < c ≤ 1`, `f_c(n)/n → c/2` along odd `n`. -/
theorem erdos361_odd_limit (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun k : ℕ => (Fc c (2 * k + 1) : ℝ) / ((2 * k + 1 : ℕ) : ℝ)) atTop
      (nhds (c / 2)) := by
  sorry

/-- **`n ≡ 2, 4 (mod 6)`, `0 < c ≤ 1/2`.** `f_c(n)/n → c/3`. -/
theorem erdos361_mod6_limit_low (c : ℝ) (hc0 : 0 < c) (hc12 : c ≤ 1 / 2) (r : ℕ)
    (hr : r = 2 ∨ r = 4) :
    Tendsto (fun k : ℕ => (Fc c (6 * k + r) : ℝ) / ((6 * k + r : ℕ) : ℝ)) atTop
      (nhds (c / 3)) := by
  sorry

/-- **`n ≡ 2, 4 (mod 6)`, `1/2 < c < 1`.** `f_c(n)/n → 2c/3 − 1/6`. -/
theorem erdos361_mod6_limit_high (c : ℝ) (hc12 : 1 / 2 < c) (hc1 : c < 1) (r : ℕ)
    (hr : r = 2 ∨ r = 4) :
    Tendsto (fun k : ℕ => (Fc c (6 * k + r) : ℝ) / ((6 * k + r : ℕ) : ℝ)) atTop
      (nhds (2 * c / 3 - 1 / 6)) := by
  sorry

/-- **Irregularity, quantitative.** For `0 < c < 1`, `f_c(n)/n` has two distinct
subsequential limits (along odd `n` and along `n ≡ 2 (mod 6)`). -/
theorem erdos361_two_limit_points (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ L₁ L₂ : ℝ, L₁ ≠ L₂ ∧
      Tendsto (fun k : ℕ => (Fc c (2 * k + 1) : ℝ) / ((2 * k + 1 : ℕ) : ℝ)) atTop (nhds L₁) ∧
      Tendsto (fun k : ℕ => (Fc c (6 * k + 2) : ℝ) / ((6 * k + 2 : ℕ) : ℝ)) atTop
        (nhds L₂) := by
  sorry

/-- **Inverse theorem, density > 1/2.** -/
theorem inverse_s1 (ε : ℝ) (hε : 0 < ε) (K : ℕ) :
    ∃ E₀ : ℕ, ∀ E : ℕ, E₀ ≤ E → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 E →
      (1 / 2 + ε) * E ≤ (A.card : ℝ) → ∀ t : ℕ, E ≤ t → t ≤ K * E → ¬ Avoids A t := by
  sorry

/-- **Inverse theorem, density > 1/3, even targets.** -/
theorem inverse_s2 (ε : ℝ) (hε : 0 < ε) (K : ℕ) :
    ∃ E₀ : ℕ, ∀ E : ℕ, E₀ ≤ E → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 E →
      (1 / 3 + ε) * E ≤ (A.card : ℝ) →
      ∀ t : ℕ, 2 ∣ t → 2 * E ≤ t → t ≤ K * E → ¬ Avoids A t := by
  sorry

/-- **Inverse theorem, `s = 2`, restricted range (the first formalised case).** For every `ε > 0` there is an `E₀` such that
for all `E ≥ E₀`, every `A ⊆ [1,E]` of density `≥ 1/3 + ε` represents every even `t ∈ (2E, 3E)`
with `3 ∤ t`. (The hypothesis `3 ∤ t` is superfluous; see `inverse_s2`.) -/
theorem inverse_s2_restricted (ε : ℝ) (hε : 0 < ε) :
    ∃ E₀ : ℕ, ∀ E : ℕ, E₀ ≤ E → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 E →
      (1 / 3 + ε) * E ≤ (A.card : ℝ) →
      ∀ t : ℕ, 2 * E < t → t < 3 * E → 2 ∣ t → ¬ 3 ∣ t → ¬ Avoids A t := by
  sorry

end Erdos361.Statement
