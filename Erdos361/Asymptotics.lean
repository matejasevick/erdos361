/-
DEVELOPMENT — Erdős #361: sharp asymptotics of `f_c(n)/n` on arithmetic classes of `n`.

It builds on the declarations of `Erdos361.Core`, `Erdos361.GoodCore`, `Erdos361.Covering` and
`Erdos361.Freiman`.

Contents.
* Part 1 — generalised good core / distinctification (Alon 1987, Prop. 2.5 idea) with an arbitrary
  multiplicity threshold `m`, and the Roth-based existence of a large good core.
* Part 2 — "zero-padded" coverings.  Putting `0` into the normalised set makes the `h`-fold sumsets
  increasing in `h`, so ONE value of `h` covers a whole range of targets (no interval chains).
  `cover_s1` (density > 1/2) and `cover_s2` (density > 1/3, Freiman 3k-3 in the sparse case).
* Part 3 — the inverse theorems `inverse_s1`, `inverse_s2` (uniform in the target `t` with
  `E ≤ t ≤ K·E`, resp. `2E ≤ t ≤ K·E`, `2 ∣ t`).  `inverse_s2` contains `inverse_s2_restricted`
  (take `K = 3`; the hypothesis `3 ∤ t` is not needed).
* Part 4 — consequences for `Fc c n = F ⌊c n⌋ n`:
    `Fc_upper_s1`      : `Fc c n ≤ (c/2 + ε) n` eventually (0 < c ≤ 1)        — sharp lim sup
    `Fc_limit_odd`     : `Fc c n / n → c/2` along odd `n` (0 < c ≤ 1)
    `Fc_limit_mod6_low`: `→ c/3` along `n ≡ 2, 4 (mod 6)` (0 < c ≤ 1/2)
    `Fc_limit_mod6_high`: `→ 2c/3 - 1/6` along `n ≡ 2, 4 (mod 6)` (1/2 < c < 1)
    `Fc_limit_cge1`    : `Fc c n / n → c - 1/2` (c ≥ 1)
    `Fc_two_limit_points` : two distinct subsequential limits for every `0 < c < 1`.
-/
import Erdos361.Core
import Erdos361.InverseMain
set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset Filter Topology
open scoped Pointwise Classical

namespace Erdos361Asymptotics

open Erdos361.Statement

/-! ## Part 1. Good cores with an arbitrary multiplicity threshold -/

/-- Left ends `x < g` of three-term progressions `x, g, 2g - x` of `A` centred at `g`. -/
def apPairs (A : Finset ℕ) (g : ℕ) : Finset ℕ := A.filter (fun x => x < g ∧ 2 * g - x ∈ A)

/-- `G` is an `m`-good core of `A`: `G ⊆ A` and every `g ∈ G` is the midpoint of at least `m`
three-term progressions of `A`. -/
def GoodCoreM (A G : Finset ℕ) (m : ℕ) : Prop := G ⊆ A ∧ ∀ g ∈ G, m ≤ (apPairs A g).card

/-- A good element has a pair `{x, 2g - x} ⊆ A` avoiding any set `S` with `|S| < m`. -/
lemma goodcoreM_fresh_pair (A G : Finset ℕ) (m : ℕ) (hgood : GoodCoreM A G m) {g : ℕ}
    (hg : g ∈ G) (S : Finset ℕ) (hS : S.card + 1 ≤ m) :
    ∃ x, x ∈ A ∧ (2 * g - x) ∈ A ∧ x < g ∧ x ∉ S ∧ (2 * g - x) ∉ S := by
  set P : Finset ℕ := apPairs A g with hP
  have hPcard : m ≤ P.card := hgood.2 g hg
  have hmem : ∀ x ∈ P, x ∈ A ∧ x < g ∧ 2 * g - x ∈ A := by
    intro x hx
    rw [hP, apPairs, Finset.mem_filter] at hx
    exact ⟨hx.1, hx.2.1, hx.2.2⟩
  set Bl : Finset ℕ := P.filter (fun x => x ∈ S ∨ 2 * g - x ∈ S) with hBl
  have hBlcard : Bl.card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (fun x => if x ∈ S then x else 2 * g - x)
    · intro x hx
      simp only [Finset.mem_coe, hBl, Finset.mem_filter] at hx
      by_cases hxS : x ∈ S
      · simpa [hxS] using hxS
      · rcases hx.2 with h | h
        · exact absurd h hxS
        · simpa [hxS] using h
    · intro x₁ hx₁ x₂ hx₂ heq
      simp only [Finset.mem_coe, hBl, Finset.mem_filter] at hx₁ hx₂
      have hlt₁ := (hmem x₁ hx₁.1).2.1
      have hlt₂ := (hmem x₂ hx₂.1).2.1
      by_cases h1 : x₁ ∈ S <;> by_cases h2 : x₂ ∈ S <;> simp only [h1, h2, if_true, if_false] at heq <;> omega
  have hfree : (P \ Bl).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    have := Finset.card_le_card hsub
    omega
  obtain ⟨x, hx⟩ := hfree
  rw [Finset.mem_sdiff] at hx
  obtain ⟨hxP, hxnBl⟩ := hx
  have hxm := hmem x hxP
  refine ⟨x, hxm.1, hxm.2.2, hxm.2.1, ?_, ?_⟩
  · intro hxS; exact hxnBl (by rw [hBl, Finset.mem_filter]; exact ⟨hxP, Or.inl hxS⟩)
  · intro hxS; exact hxnBl (by rw [hBl, Finset.mem_filter]; exact ⟨hxP, Or.inr hxS⟩)

/-- Multiset distinctification with threshold `m`: a multiset over `A` of size `≤ m` whose repeated
elements lie in an `m`-good core has the same sum and size as some `Nodup` multiset over `A`. -/
lemma goodcoreM_distinctify_ms (A G : Finset ℕ) (m : ℕ) (hgood : GoodCoreM A G m) :
    ∀ M : Multiset ℕ, M.card ≤ m → (∀ x ∈ M, x ∈ A) → (∀ x, 2 ≤ M.count x → x ∈ G) →
      ∃ N : Multiset ℕ, N.Nodup ∧ (∀ x ∈ N, x ∈ A) ∧ N.sum = M.sum ∧ N.card = M.card := by
  suffices H : ∀ e : ℕ, ∀ M : Multiset ℕ, M.card - M.toFinset.card ≤ e → M.card ≤ m →
      (∀ x ∈ M, x ∈ A) → (∀ x, 2 ≤ M.count x → x ∈ G) →
      ∃ N : Multiset ℕ, N.Nodup ∧ (∀ x ∈ N, x ∈ A) ∧ N.sum = M.sum ∧ N.card = M.card by
    intro M h1 h2 h3; exact H _ M le_rfl h1 h2 h3
  intro e
  induction e with
  | zero =>
    intro M he hcard hA hrep
    have hnd : M.Nodup := by
      have h1 := Multiset.toFinset_card_le M
      have hcd : M.toFinset.card = M.dedup.card := rfl
      have hded : M.dedup = M :=
        Multiset.eq_of_le_of_card_le (Multiset.dedup_le M) (by omega)
      exact (Multiset.dedup_eq_self).mp hded
    exact ⟨M, hnd, hA, rfl, rfl⟩
  | succ e ih =>
    intro M he hcard hA hrep
    by_cases hnd : M.Nodup
    · exact ⟨M, hnd, hA, rfl, rfl⟩
    · rw [Multiset.nodup_iff_count_le_one] at hnd
      push_neg at hnd
      obtain ⟨g, hgc⟩ := hnd
      have hg2 : 2 ≤ M.count g := by omega
      have hgG : g ∈ G := hrep g hg2
      have hgM : g ∈ M := Multiset.count_pos.mp (by omega)
      have hg_in_e : g ∈ M.erase g := by
        rw [← Multiset.count_pos, Multiset.count_erase_self]; omega
      set M0 : Multiset ℕ := (M.erase g).erase g with hM0
      have hMeq : M = g ::ₘ g ::ₘ M0 := by
        rw [hM0, Multiset.cons_erase hg_in_e, Multiset.cons_erase hgM]
      have hM0le : M0 ≤ M := (Multiset.erase_le _ _).trans (Multiset.erase_le _ _)
      have hM0card : M0.card + 2 = M.card := by
        rw [hMeq]; simp only [Multiset.card_cons]
      have hScard : M0.toFinset.card + 1 ≤ m := by
        have h1 := Multiset.toFinset_card_le M0
        omega
      obtain ⟨x, hxA, hyA, hxg, hxS, hyS⟩ :=
        goodcoreM_fresh_pair A G m hgood hgG M0.toFinset hScard
      set y : ℕ := 2 * g - x with hy
      have hxM0 : x ∉ M0 := fun h => hxS (Multiset.mem_toFinset.mpr h)
      have hyM0 : y ∉ M0 := fun h => hyS (Multiset.mem_toFinset.mpr h)
      have hxney : x ≠ y := by rw [hy]; omega
      set M' : Multiset ℕ := x ::ₘ y ::ₘ M0 with hM'
      have hM'card : M'.card = M.card := by
        rw [hM', Multiset.card_cons, Multiset.card_cons]; omega
      have hxy : x + y = 2 * g := by rw [hy]; omega
      have hM'sum : M'.sum = M.sum := by
        rw [hM', hMeq, Multiset.sum_cons, Multiset.sum_cons, Multiset.sum_cons,
          Multiset.sum_cons]; omega
      have hcx0 : M0.count x = 0 := Multiset.count_eq_zero.mpr hxM0
      have hcy0 : M0.count y = 0 := Multiset.count_eq_zero.mpr hyM0
      have hM'A : ∀ z ∈ M', z ∈ A := by
        intro z hz
        rw [hM', Multiset.mem_cons, Multiset.mem_cons] at hz
        rcases hz with rfl | rfl | hz
        · exact hxA
        · exact hyA
        · exact hA z (Multiset.mem_of_le hM0le hz)
      have hM'rep : ∀ z, 2 ≤ M'.count z → z ∈ G := by
        intro z hz2
        have hcount : M'.count z =
            M0.count z + (if z = x then 1 else 0) + (if z = y then 1 else 0) := by
          rw [hM', Multiset.count_cons, Multiset.count_cons]; ring
        rw [hcount] at hz2
        have hle : M0.count z ≤ M.count z := Multiset.count_le_of_le z hM0le
        by_cases hzx : z = x
        · have hzny : ¬ z = y := fun h => hxney (by rw [← hzx]; exact h)
          rw [if_pos hzx, if_neg hzny, hzx, hcx0] at hz2; omega
        · by_cases hzy : z = y
          · rw [if_neg hzx, if_pos hzy, hzy, hcy0] at hz2; omega
          · rw [if_neg hzx, if_neg hzy] at hz2
            exact hrep z (by omega)
      have hMtf : M.toFinset.card ≤ M0.toFinset.card + 1 := by
        rw [hMeq, Multiset.toFinset_cons, Multiset.toFinset_cons, Finset.insert_idem]
        exact Finset.card_insert_le _ _
      have hxni : x ∉ insert y M0.toFinset := by
        rw [Finset.mem_insert]; push_neg; exact ⟨hxney, hxS⟩
      have hM'tf : M'.toFinset.card = M0.toFinset.card + 2 := by
        rw [hM', Multiset.toFinset_cons, Multiset.toFinset_cons,
          Finset.card_insert_of_notMem hxni, Finset.card_insert_of_notMem hyS]
      have hexc : M'.card - M'.toFinset.card ≤ e := by
        rw [hM'card, hM'tf]; omega
      obtain ⟨N, hNnd, hNA, hNsum, hNcard⟩ :=
        ih M' hexc (by omega) hM'A hM'rep
      exact ⟨N, hNnd, hNA, by rw [hNsum, hM'sum], by rw [hNcard, hM'card]⟩

/-- Distinctification: an `h`-fold sum (`h ≤ m`, repetitions allowed) of elements of an `m`-good
core of `A` is a sum of distinct elements of `A`. -/
theorem goodcoreM_distinctify (A G : Finset ℕ) (m : ℕ) (hgood : GoodCoreM A G m) {h t : ℕ}
    (hh : h ≤ m) (ht : 0 < t) (hrep : Erdos361Covering.hfold G h t) :
    ∃ B ⊆ A, B.Nonempty ∧ B.sum id = t := by
  obtain ⟨f, hfG, hfsum⟩ := hrep
  set M : Multiset ℕ := (Finset.univ : Finset (Fin h)).val.map f with hM
  have hMcard : M.card ≤ m := by
    rw [hM]; simpa using hh
  have hMsum : M.sum = t := by
    rw [hM]; simpa [Finset.sum] using hfsum
  have hMA : ∀ x ∈ M, x ∈ A := by
    intro x hx; rw [hM] at hx; simp only [Multiset.mem_map, Finset.mem_val,
      Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx; exact hgood.1 (hfG i)
  have hMrep : ∀ x, 2 ≤ M.count x → x ∈ G := by
    intro x hx2
    by_cases hxM : x ∈ M
    · rw [hM] at hxM; simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ,
        true_and] at hxM; obtain ⟨i, rfl⟩ := hxM; exact hfG i
    · exact absurd (Multiset.count_pos.mp (by omega)) hxM
  obtain ⟨N, hNnodup, hNA, hNsum, hNcard⟩ :=
    goodcoreM_distinctify_ms A G m hgood M hMcard hMA hMrep
  have hNt : N.sum = t := by rw [hNsum, hMsum]
  have hNne : N ≠ 0 := by
    rintro rfl; simp only [Multiset.sum_zero] at hNt; omega
  refine ⟨N.toFinset, ?_, ?_, ?_⟩
  · intro x hx; exact hNA x (Multiset.mem_toFinset.mp hx)
  · obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero hNne
    exact ⟨a, Multiset.mem_toFinset.mpr ha⟩
  · calc N.toFinset.sum id
        = (N.toFinset.val.map id).sum := rfl
      _ = N.toFinset.val.sum := by rw [Multiset.map_id]
      _ = N.dedup.sum := by rw [Multiset.toFinset_val]
      _ = N.sum := by rw [Multiset.Nodup.dedup hNnodup]
      _ = t := hNt

open scoped Classical in
/-- Good/bad split with threshold `ℓ` (generalises `good_core_split`, which is the case `ℓ = 10`):
the elements of `A ⊆ [1,E]` that are midpoints of at most `ℓ` three-term progressions of `A` number
at most `(36ℓ+2)·r₃(E+1)`. -/
lemma roth_core_split (E : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 E) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (A.filter (fun a => (A.filter (fun x => x < a ∧ 2 * a - x ∈ A)).card ≤ ℓ)).card
      ≤ (36 * ℓ + 2) * rothNumberNat (E + 1) := by
  set C : Finset ℕ := A.filter (fun a => (A.filter (fun x => x < a ∧ 2 * a - x ∈ A)).card ≤ ℓ)
    with hCdef
  have hCA : C ⊆ A := Finset.filter_subset _ _
  set D : Finset (Finset ℕ) :=
    C.biUnion (fun y => (C.filter (fun x => x < y ∧ 2 * y - x ∈ C)).image
      (fun x => ({x, y, 2 * y - x} : Finset ℕ))) with hDdef
  have hd3 : ∀ e ∈ D, e ⊆ C ∧ e.card = 3 := by
    intro e he
    rw [hDdef, Finset.mem_biUnion] at he
    obtain ⟨y, hyC, he⟩ := he
    rw [Finset.mem_image] at he
    obtain ⟨x, hx, rfl⟩ := he
    rw [Finset.mem_filter] at hx
    obtain ⟨hxC, hxy, hzC⟩ := hx
    refine ⟨?_, ?_⟩
    · intro a ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · exact hxC
      · exact hyC
      · exact hzC
    · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
      · simp only [Finset.mem_singleton]; omega
      · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hDcard : D.card ≤ ℓ * C.card := by
    calc D.card ≤ ∑ y ∈ C, ((C.filter (fun x => x < y ∧ 2 * y - x ∈ C)).image
              (fun x => ({x, y, 2 * y - x} : Finset ℕ))).card := Finset.card_biUnion_le
      _ ≤ ∑ y ∈ C, (C.filter (fun x => x < y ∧ 2 * y - x ∈ C)).card :=
            Finset.sum_le_sum (fun y _ => Finset.card_image_le)
      _ ≤ ∑ y ∈ C, ℓ := by
            refine Finset.sum_le_sum (fun y hyC => ?_)
            have hsub : C.filter (fun x => x < y ∧ 2 * y - x ∈ C)
                ⊆ A.filter (fun x => x < y ∧ 2 * y - x ∈ A) := by
              intro x hx
              rw [Finset.mem_filter] at hx ⊢
              exact ⟨hCA hx.1, hx.2.1, hCA hx.2.2⟩
            have hle := Finset.card_le_card hsub
            have hℓy := (Finset.mem_filter.mp hyC).2
            omega
      _ = ℓ * C.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  obtain ⟨I, hIC, hIind, hIcard⟩ := hypergraph_indep C D ℓ hℓ hd3 hDcard
  have hIfree : ThreeAPFree (I : Set ℕ) := by
    rw [threeAPFree_iff_eq_right]
    intro a ha b hb c hc habc
    by_contra hac
    have hkey : ∀ x z : ℕ, x ∈ I → z ∈ I → x < z → x + z = b + b → False := by
      intro x z hx hz hxz hxz2
      have hzeq : 2 * b - x = z := by omega
      have hmem : ({x, b, z} : Finset ℕ) ∈ D := by
        rw [hDdef, Finset.mem_biUnion]
        refine ⟨b, hIC hb, ?_⟩
        rw [Finset.mem_image]
        exact ⟨x, Finset.mem_filter.mpr ⟨hIC hx, by omega, by rw [hzeq]; exact hIC hz⟩, by rw [hzeq]⟩
      have hsub : ({x, b, z} : Finset ℕ) ⊆ I := by
        intro w hw; simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl
        exacts [hx, hb, hz]
      exact hIind _ hmem hsub
    rcases lt_or_gt_of_ne hac with h | h
    · exact hkey a c ha hc h habc
    · exact hkey c a hc ha h (by omega)
  have hIlt : ∀ x ∈ I, x < E + 1 := by
    intro x hx
    have := hA (hCA (hIC hx))
    rw [Finset.mem_Icc] at this; omega
  have hIroth : I.card ≤ rothNumberNat (E + 1) :=
    ThreeAPFree.le_rothNumberNat I hIfree hIlt rfl
  calc C.card ≤ (36 * ℓ + 2) * I.card := hIcard
    _ ≤ (36 * ℓ + 2) * rothNumberNat (E + 1) := Nat.mul_le_mul_left _ hIroth

/-- Large good core with threshold `ℓ+1`: for every `α`, a set `A ⊆ [1,E]` of size `≥ (α+ε)E`
contains `G` of size `≥ (α+ε/2)E` all of whose elements are midpoints of `≥ ℓ+1` three-term
progressions of `A` (for all large `E`). -/
lemma roth_core_exists (α ε : ℝ) (hε : 0 < ε) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ E₀ : ℕ, ∀ E : ℕ, E₀ ≤ E → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 E →
      (α + ε) * E ≤ (A.card : ℝ) →
      ∃ G ⊆ A, (∀ g ∈ G, ℓ + 1 ≤ (A.filter (fun x => x < g ∧ 2 * g - x ∈ A)).card)
        ∧ (α + ε / 2) * E ≤ (G.card : ℝ) := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = 36 * ℓ + 2 := ⟨_, rfl⟩
  obtain ⟨E₀, hE₀⟩ := roth_small_nat K ε hε
  refine ⟨E₀, fun E hE A hA hden => ?_⟩
  set G : Finset ℕ :=
    A.filter (fun a => ℓ + 1 ≤ (A.filter (fun x => x < a ∧ 2 * a - x ∈ A)).card) with hG
  set C : Finset ℕ :=
    A.filter (fun a => (A.filter (fun x => x < a ∧ 2 * a - x ∈ A)).card ≤ ℓ) with hC
  have hsplit : C.card ≤ K * rothNumberNat (E + 1) := by
    rw [hK]; exact roth_core_split E A hA ℓ hℓ
  have hCeq : C = A.filter
      (fun a => ¬ (ℓ + 1 ≤ (A.filter (fun x => x < a ∧ 2 * a - x ∈ A)).card)) := by
    rw [hC]; apply Finset.filter_congr; intro a _; constructor <;> intro h <;> omega
  have hGC : G.card + C.card = A.card := by
    rw [hG, hCeq]; exact Finset.filter_card_add_filter_neg_card_eq_card _
  have hCle : (C.card : ℝ) ≤ (K : ℝ) * (rothNumberNat (E + 1) : ℝ) := by exact_mod_cast hsplit
  have hroth := hE₀ E hE
  refine ⟨G, Finset.filter_subset _ _, fun g hg => (Finset.mem_filter.mp hg).2, ?_⟩
  have hGCr : (G.card : ℝ) + (C.card : ℝ) = (A.card : ℝ) := by exact_mod_cast hGC
  linarith [hden, hCle, hroth, hGCr]

/-! ## Part 2. Zero-padded coverings -/

/-- Strip zeros and rescale: an `h`-fold sum of `insert 0 G'` lifts, after multiplication by `d`,
to a sum of at most `h` elements of `G`, provided `d·b ∈ G` for every `b ∈ G'`. -/
lemma strip_zeros {G' G : Finset ℕ} {d : ℕ} (hlift : ∀ b ∈ G', d * b ∈ G) :
    ∀ {h x : ℕ}, Erdos361Covering.hfold (insert 0 G') h x →
      ∃ h', h' ≤ h ∧ Erdos361Covering.hfold G h' (d * x) := by
  intro h
  induction h with
  | zero =>
    intro x H
    obtain ⟨f, hf, hfs⟩ := H
    have hx0 : x = 0 := by rw [← hfs]; simp
    refine ⟨0, le_refl 0, ?_⟩
    rw [hx0, mul_zero]
    exact Erdos361Covering.hfold_zero G
  | succ k ih =>
    intro x H
    obtain ⟨c, hc, x', Hx', hcx⟩ := Erdos361Covering.hfold_uncons H
    obtain ⟨h', hh', Hh'⟩ := ih Hx'
    rcases Finset.mem_insert.mp hc with hc0 | hcG
    · refine ⟨h', by omega, ?_⟩
      have hxx : d * x = d * x' := by rw [← hcx, hc0, zero_add]
      rw [hxx]; exact Hh'
    · refine ⟨h' + 1, by omega, ?_⟩
      have hstep := Erdos361Covering.hfold_cons (hlift c hcG) Hh'
      have hxx : d * c + d * x' = d * x := by rw [← hcx, mul_add]
      rw [hxx] at hstep
      exact hstep

/-- If every element of `G ⊆ [1,E]` is divisible by `d ≥ 1`, then `d·|G| ≤ E`. -/
lemma dvd_card_bound (E d : ℕ) (G : Finset ℕ) (hGsub : G ⊆ Finset.Icc 1 E) (hd : 0 < d)
    (hdvd : ∀ g ∈ G, d ∣ g) : d * G.card ≤ E := by
  have hmaps : ∀ g ∈ G, g / d ∈ Finset.Icc 1 (E / d) := by
    intro g hg
    have hg' := Finset.mem_Icc.mp (hGsub hg)
    obtain ⟨k, rfl⟩ := hdvd g hg
    rw [Finset.mem_Icc, Nat.mul_div_cancel_left k hd]
    constructor
    · rcases Nat.eq_zero_or_pos k with hk | hk
      · rw [hk, mul_zero] at hg'; omega
      · exact hk
    · rw [Nat.le_div_iff_mul_le hd, mul_comm]; exact hg'.2
  have hinj : Set.InjOn (fun g => g / d) G := by
    intro a ha b hb hab
    have hab' : a / d = b / d := hab
    obtain ⟨k, rfl⟩ := hdvd a ha
    obtain ⟨l, rfl⟩ := hdvd b hb
    rw [Nat.mul_div_cancel_left k hd, Nat.mul_div_cancel_left l hd] at hab'
    rw [hab']
  have hcard := Finset.card_le_card_of_injOn (fun g => g / d) hmaps hinj
  rw [Nat.card_Icc] at hcard
  have hmd : d * (E / d) ≤ E := by rw [mul_comm]; exact Nat.div_mul_le_self E d
  calc d * G.card ≤ d * (E / d + 1 - 1) := Nat.mul_le_mul_left d hcard
    _ = d * (E / d) := by rw [Nat.add_sub_cancel]
    _ ≤ E := hmd

/-- Common facts about `insert 0 G` for `G ⊆ [1, L]` with `L = max G`. -/
lemma insert_zero_facts (G : Finset ℕ) (L : ℕ) (hleL : ∀ g ∈ G, g ≤ L) (hLG : L ∈ G)
    (h0G : (0 : ℕ) ∉ G) :
    (insert 0 G).card = G.card + 1 ∧ insert 0 G ⊆ Finset.Icc 0 L ∧ (0 : ℕ) ∈ insert 0 G ∧
      L ∈ insert 0 G ∧ G.card ≤ L := by
  refine ⟨Finset.card_insert_of_notMem h0G, ?_, Finset.mem_insert_self 0 G,
    Finset.mem_insert_of_mem hLG, ?_⟩
  · intro b hb
    rw [Finset.mem_insert] at hb
    rw [Finset.mem_Icc]
    rcases hb with hb | hb
    · constructor <;> omega
    · exact ⟨Nat.zero_le _, hleL b hb⟩
  · have hsub : G ⊆ Finset.Icc 1 L := by
      intro g hg
      rw [Finset.mem_Icc]
      refine ⟨?_, hleL g hg⟩
      rcases Nat.eq_zero_or_pos g with h | h
      · exact absurd (h ▸ hg) h0G
      · exact h
    have := Finset.card_le_card hsub
    simpa [Nat.card_Icc] using this

/-- **Covering, density `> 1/2`.** If `G ⊆ [1,E]` and `2|G| ≥ E + 4`, then every `t ∈ [E, K·E]`
is a sum of at most `2K+2` elements of `G` (repetitions allowed). -/
lemma cover_s1 (E : ℕ) (G : Finset ℕ) (hGsub : G ⊆ Finset.Icc 1 E) (hGne : G.Nonempty)
    (hdense : E + 4 ≤ 2 * G.card) (K t : ℕ) (htlo : E ≤ t) (hthi : t ≤ K * E) :
    ∃ h', h' ≤ 2 * K + 2 ∧ Erdos361Covering.hfold G h' t := by
  set L := G.max' hGne with hL
  have hLG : L ∈ G := G.max'_mem hGne
  have hleL : ∀ g ∈ G, g ≤ L := fun g hg => G.le_max' g hg
  have hLE : L ≤ E := by
    have := hGsub hLG; rw [Finset.mem_Icc] at this; omega
  have h0G : (0 : ℕ) ∉ G := by
    intro h0; have := hGsub h0; rw [Finset.mem_Icc] at this; omega
  obtain ⟨hBcard, hBsub, h0B, hLB, hGL⟩ := insert_zero_facts G L hleL hLG h0G
  have hB3 : 3 ≤ (insert 0 G).card := by omega
  have hBdense : L ≤ 2 * (insert 0 G).card - 4 := by omega
  have hcov := Erdos361Covering.lemma2_dense (insert 0 G) L hBsub h0B hLB hB3 hBdense
  have hmul : (K + 1) * E ≤ (2 * K + 2) * L := by
    have h1 : (2 * K + 2) * L = (K + 1) * (2 * L) := by ring
    rw [h1]
    exact Nat.mul_le_mul_left (K + 1) (by omega)
  have hKE : (K + 1) * E = K * E + E := by ring
  have hrep := hcov (2 * K + 2) (by omega) t (by omega) (by omega)
  obtain ⟨h', hh', Hh'⟩ := strip_zeros (G' := G) (G := G) (d := 1)
    (fun b hb => by rw [one_mul]; exact hb) hrep
  refine ⟨h', hh', ?_⟩
  rw [one_mul] at Hh'
  exact Hh'

/-- **Covering, density `> 1/3`.** If `G ⊆ [1,E]` and `3|G| ≥ E + 30`, then every even
`t ∈ [2E, K·E]` is a sum of at most `6K+6` elements of `G` (repetitions allowed).
Normalisation: `d = gcd G ∈ {1,2}`; for `d = 2` divide by `2` (then the set is dense); for `d = 1`
use `insert 0 G` directly, dense case by `lemma2_dense`, sparse case by Freiman `3k-3`
(`freiman_3k3`) + `lemma3_third`. -/
lemma cover_s2 (E : ℕ) (G : Finset ℕ) (hGsub : G ⊆ Finset.Icc 1 E) (hGne : G.Nonempty)
    (hsize : E + 30 ≤ 3 * G.card) (K t : ℕ) (ht2 : 2 ∣ t) (htlo : 2 * E ≤ t)
    (hthi : t ≤ K * E) :
    ∃ h', h' ≤ 6 * K + 6 ∧ Erdos361Covering.hfold G h' t := by
  set d := G.gcd id with hd
  have hdvd : ∀ g ∈ G, d ∣ g := fun g hg => Finset.gcd_dvd hg
  have hGne' : G.Nonempty := hGne
  obtain ⟨g0, hg0⟩ := hGne'
  have hg0pos : 1 ≤ g0 := (Finset.mem_Icc.mp (hGsub hg0)).1
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h0
    · exfalso
      have h1 := hdvd g0 hg0
      rw [h0] at h1
      have h2 := Nat.eq_zero_of_zero_dvd h1
      omega
    · exact h0
  have hd2 : d ≤ 2 := by
    by_contra hcon
    push_neg at hcon
    have hle := dvd_card_bound E d G hGsub hdpos hdvd
    have h3 : 3 * G.card ≤ d * G.card := Nat.mul_le_mul_right _ (by omega)
    omega
  set L := G.max' hGne with hL
  have hLG : L ∈ G := G.max'_mem hGne
  have hleL : ∀ g ∈ G, g ≤ L := fun g hg => G.le_max' g hg
  have hLE : L ≤ E := by
    have := hGsub hLG; rw [Finset.mem_Icc] at this; omega
  have h0G : (0 : ℕ) ∉ G := by
    intro h0; have := hGsub h0; rw [Finset.mem_Icc] at this; omega
  have hKE : (K + 1) * E = K * E + E := by ring
  have hd12 : d = 1 ∨ d = 2 := by omega
  rcases hd12 with hd1 | hd2'
  · -- d = 1 : work with `insert 0 G`
    obtain ⟨hBcard, hBsub, h0B, hLB, hGL⟩ := insert_zero_facts G L hleL hLG h0G
    have hB3 : 3 ≤ (insert 0 G).card := by omega
    by_cases hdense : L ≤ 2 * (insert 0 G).card - 4
    · have hcov := Erdos361Covering.lemma2_dense (insert 0 G) L hBsub h0B hLB hB3 hdense
      have hmul : (K + 1) * E ≤ (3 * K + 3) * L := by
        have h1 : (3 * K + 3) * L = (K + 1) * (3 * L) := by ring
        rw [h1]
        exact Nat.mul_le_mul_left (K + 1) (by omega)
      have hrep := hcov (3 * K + 3) (by omega) t (by omega) (by omega)
      obtain ⟨h', hh', Hh'⟩ := strip_zeros (G' := G) (G := G) (d := 1)
        (fun b hb => by rw [one_mul]; exact hb) hrep
      refine ⟨h', by omega, ?_⟩
      rw [one_mul] at Hh'
      exact Hh'
    · push_neg at hdense
      have hLlo : 2 * (insert 0 G).card - 3 ≤ L := by omega
      have hLhi : L ≤ 3 * (insert 0 G).card - 6 := by omega
      have hgcdB : (insert 0 G).gcd id = 1 := by
        have hdvd1 : (insert 0 G).gcd id ∣ G.gcd id :=
          Finset.dvd_gcd (fun g hg => Finset.gcd_dvd (Finset.mem_insert_of_mem hg))
        rw [← hd, hd1] at hdvd1
        exact Nat.eq_one_of_dvd_one hdvd1
      have hF := Erdos361Freiman.freiman_3k3 (insert 0 G) L hBsub h0B hLB hB3 hgcdB hLlo
      have hcov :=
        Erdos361Covering.lemma3_third (insert 0 G) L hBsub h0B hLB hB3 hLlo hLhi hF
      have hmul : 2 * (K + 1) * E ≤ 2 * (3 * K + 3) * L := by
        have h1 : 2 * (3 * K + 3) * L = 2 * (K + 1) * (3 * L) := by ring
        rw [h1]
        exact Nat.mul_le_mul_left (2 * (K + 1)) (by omega)
      have hKE2 : 2 * (K + 1) * E = 2 * (K * E) + 2 * E := by ring
      have hrep := hcov (3 * K + 3) (by omega) t (by omega) (by omega)
      obtain ⟨h', hh', Hh'⟩ := strip_zeros (G' := G) (G := G) (d := 1)
        (fun b hb => by rw [one_mul]; exact hb) hrep
      refine ⟨h', by omega, ?_⟩
      rw [one_mul] at Hh'
      exact Hh'
  · -- d = 2 : every element is even; divide by 2
    have hev : ∀ g ∈ G, 2 ∣ g := by
      intro g hg
      have h1 := hdvd g hg
      rw [hd2'] at h1
      exact h1
    set G2 : Finset ℕ := G.image (fun g => g / 2) with hG2
    set L2 : ℕ := L / 2 with hL2
    have hlift : ∀ b ∈ G2, 2 * b ∈ G := by
      intro b hb
      rw [hG2, Finset.mem_image] at hb
      obtain ⟨g, hg, rfl⟩ := hb
      rw [Nat.mul_div_cancel' (hev g hg)]
      exact hg
    have hG2card : G2.card = G.card := by
      rw [hG2]
      apply Finset.card_image_of_injOn
      intro a ha b hb hab
      have hab' : a / 2 = b / 2 := hab
      have h1 := Nat.mul_div_cancel' (hev a ha)
      have h2 := Nat.mul_div_cancel' (hev b hb)
      omega
    have h0G2 : (0 : ℕ) ∉ G2 := by
      intro h0
      rw [hG2, Finset.mem_image] at h0
      obtain ⟨g, hg, hg0'⟩ := h0
      have h1 := Nat.mul_div_cancel' (hev g hg)
      have h2 := (Finset.mem_Icc.mp (hGsub hg)).1
      omega
    have hleL2 : ∀ b ∈ G2, b ≤ L2 := by
      intro b hb
      rw [hG2, Finset.mem_image] at hb
      obtain ⟨g, hg, rfl⟩ := hb
      exact Nat.div_le_div_right (hleL g hg)
    have hL2G2 : L2 ∈ G2 := by
      rw [hG2, Finset.mem_image]; exact ⟨L, hLG, rfl⟩
    have h2L2 : 2 * L2 ≤ E := by omega
    obtain ⟨hBcard, hBsub, h0B, hLB, hG2L⟩ := insert_zero_facts G2 L2 hleL2 hL2G2 h0G2
    have hB3 : 3 ≤ (insert 0 G2).card := by omega
    have hdense : L2 ≤ 2 * (insert 0 G2).card - 4 := by omega
    have hcov := Erdos361Covering.lemma2_dense (insert 0 G2) L2 hBsub h0B hLB hB3 hdense
    obtain ⟨y, hy⟩ := ht2
    have hmul : (K + 1) * E ≤ (3 * K + 3) * L2 := by
      have h1 : (3 * K + 3) * L2 = (K + 1) * (3 * L2) := by ring
      rw [h1]
      exact Nat.mul_le_mul_left (K + 1) (by omega)
    have hrep := hcov (3 * K + 3) (by omega) y (by omega) (by omega)
    obtain ⟨h', hh', Hh'⟩ := strip_zeros hlift hrep
    refine ⟨h', by omega, ?_⟩
    rw [hy]
    exact Hh'

/-! ## Part 3. Inverse theorems in the linear regime -/

/-- **Inverse theorem, `s = 1`.** For every `ε > 0` and `K`, for all large `E`: if `A ⊆ [1,E]`
and `|A| ≥ (1/2+ε)E`, then every `t` with `E ≤ t ≤ K·E` is a subset sum of `A`. -/
theorem inverse_s1 (ε : ℝ) (hε : 0 < ε) (K : ℕ) :
    ∃ E₀ : ℕ, ∀ E : ℕ, E₀ ≤ E → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 E →
      (1 / 2 + ε) * E ≤ (A.card : ℝ) → ∀ t : ℕ, E ≤ t → t ≤ K * E → ¬ Avoids A t := by
  obtain ⟨E₁, hgce⟩ := roth_core_exists (1 / 2) ε hε (2 * K + 2) (by omega)
  refine ⟨max E₁ (⌈16 / ε⌉₊ + 1), fun E hE A hAsub hden t htlo hthi => ?_⟩
  have hE1 : E₁ ≤ E := le_trans (le_max_left _ _) hE
  have hEbig : ⌈16 / ε⌉₊ + 1 ≤ E := le_trans (le_max_right _ _) hE
  have hεE : (16 : ℝ) ≤ ε * E := by
    have hc : (16 / ε) ≤ (⌈16 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have hlt : (⌈16 / ε⌉₊ : ℝ) < (E : ℝ) := by exact_mod_cast (by omega : ⌈16 / ε⌉₊ < E)
    have h16 : 16 / ε < (E : ℝ) := lt_of_le_of_lt hc hlt
    rw [div_lt_iff₀ hε] at h16
    linarith [h16]
  obtain ⟨G, hGA, hmid, hGsize⟩ := hgce E hE1 A hAsub hden
  have hGsub : G ⊆ Finset.Icc 1 E := hGA.trans hAsub
  have hsizeR : (E : ℝ) + 4 ≤ 2 * (G.card : ℝ) := by linarith [hGsize, hεE]
  have hsizeN : E + 4 ≤ 2 * G.card := by exact_mod_cast hsizeR
  have hGne : G.Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨h', hh', Hh'⟩ := cover_s1 E G hGsub hGne hsizeN K t htlo hthi
  have hgood : GoodCoreM A G (2 * K + 3) := ⟨hGA, fun g hg => by
    have hg' := hmid g hg
    unfold apPairs
    omega⟩
  have ht0 : 0 < t := by omega
  obtain ⟨B, hBA, hBne, hBsum⟩ := goodcoreM_distinctify A G (2 * K + 3) hgood (by omega) ht0 Hh'
  intro hav
  exact (Finset.nonempty_iff_ne_empty.mp hBne) (hav B hBA hBsum)

/-- **Inverse theorem, `s = 2`.** For every `ε > 0` and `K`, for all large `E`: if `A ⊆ [1,E]`
and `|A| ≥ (1/3+ε)E`, then every even `t` with `2E ≤ t ≤ K·E` is a subset sum of `A`.
(With `K = 3` this contains `inverse_s2_restricted`; no hypothesis `3 ∤ t` is needed.) -/
theorem inverse_s2 (ε : ℝ) (hε : 0 < ε) (K : ℕ) :
    ∃ E₀ : ℕ, ∀ E : ℕ, E₀ ≤ E → ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 E →
      (1 / 3 + ε) * E ≤ (A.card : ℝ) →
      ∀ t : ℕ, 2 ∣ t → 2 * E ≤ t → t ≤ K * E → ¬ Avoids A t := by
  obtain ⟨E₁, hgce⟩ := roth_core_exists (1 / 3) ε hε (6 * K + 6) (by omega)
  refine ⟨max E₁ (⌈60 / ε⌉₊ + 1), fun E hE A hAsub hden t ht2 htlo hthi => ?_⟩
  have hE1 : E₁ ≤ E := le_trans (le_max_left _ _) hE
  have hEbig : ⌈60 / ε⌉₊ + 1 ≤ E := le_trans (le_max_right _ _) hE
  have hεE : (60 : ℝ) ≤ ε * E := by
    have hc : (60 / ε) ≤ (⌈60 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have hlt : (⌈60 / ε⌉₊ : ℝ) < (E : ℝ) := by exact_mod_cast (by omega : ⌈60 / ε⌉₊ < E)
    have h60 : 60 / ε < (E : ℝ) := lt_of_le_of_lt hc hlt
    rw [div_lt_iff₀ hε] at h60
    linarith [h60]
  obtain ⟨G, hGA, hmid, hGsize⟩ := hgce E hE1 A hAsub hden
  have hGsub : G ⊆ Finset.Icc 1 E := hGA.trans hAsub
  have hsizeR : (E : ℝ) + 30 ≤ 3 * (G.card : ℝ) := by linarith [hGsize, hεE]
  have hsizeN : E + 30 ≤ 3 * G.card := by exact_mod_cast hsizeR
  have hGne : G.Nonempty := by rw [← Finset.card_pos]; omega
  obtain ⟨h', hh', Hh'⟩ := cover_s2 E G hGsub hGne hsizeN K t ht2 htlo hthi
  have hgood : GoodCoreM A G (6 * K + 7) := ⟨hGA, fun g hg => by
    have hg' := hmid g hg
    unfold apPairs
    omega⟩
  have ht0 : 0 < t := by omega
  obtain ⟨B, hBA, hBne, hBsum⟩ := goodcoreM_distinctify A G (6 * K + 7) hgood (by omega) ht0 Hh'
  intro hav
  exact (Finset.nonempty_iff_ne_empty.mp hBne) (hav B hBA hBsum)

/-! ## Part 4. Consequences for `f_c(n) = Fc c n` -/

/-- Lower bound by an explicit avoider. -/
lemma F_ge_card {M n : ℕ} (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 M) (hav : Avoids A n) :
    A.card ≤ F M n := by
  rw [F]
  have hmem : A ∈ Avoiders M n := by
    simp only [Avoiders, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hA, hav⟩
  exact Finset.le_sup hmem

/-- Size facts for `E = ⌊c n⌋₊` once `c n > E₀ + 2`, with `K = ⌈2/c⌉₊`. -/
lemma floor_facts361 (c : ℝ) (hc0 : 0 < c) (n E₀ K : ℕ) (hK : K = ⌈2 / c⌉₊)
    (hcn : (E₀ : ℝ) + 2 < c * n) :
    E₀ ≤ ⌊c * (n : ℝ)⌋₊ ∧ ((⌊c * (n : ℝ)⌋₊ : ℕ) : ℝ) ≤ c * n ∧
      c * n - 1 < ((⌊c * (n : ℝ)⌋₊ : ℕ) : ℝ) ∧ n ≤ K * ⌊c * (n : ℝ)⌋₊ := by
  have hcn0 : (0 : ℝ) ≤ c * n := by positivity
  have hEle : ((⌊c * (n : ℝ)⌋₊ : ℕ) : ℝ) ≤ c * n := Nat.floor_le hcn0
  have hEgt : c * n - 1 < ((⌊c * (n : ℝ)⌋₊ : ℕ) : ℝ) := Nat.sub_one_lt_floor _
  have hE0 : (0 : ℝ) ≤ (E₀ : ℝ) := Nat.cast_nonneg _
  refine ⟨?_, hEle, hEgt, ?_⟩
  · have h1 : (E₀ : ℝ) < ((⌊c * (n : ℝ)⌋₊ : ℕ) : ℝ) := by linarith
    exact_mod_cast h1.le
  · have hK2 : 2 / c ≤ (K : ℝ) := by rw [hK]; exact Nat.le_ceil _
    have hKc : 2 ≤ (K : ℝ) * c := (div_le_iff₀ hc0).mp hK2
    have h2E : c * n ≤ 2 * ((⌊c * (n : ℝ)⌋₊ : ℕ) : ℝ) := by linarith
    have hkey : (n : ℝ) ≤ (K : ℝ) * ((⌊c * (n : ℝ)⌋₊ : ℕ) : ℝ) := by
      by_contra hcon
      push_neg at hcon
      have h1 := mul_lt_mul_of_pos_right hcon hc0
      have h2 : 2 * ((⌊c * (n : ℝ)⌋₊ : ℕ) : ℝ) ≤ ((K : ℝ) * c) * ((⌊c * (n : ℝ)⌋₊ : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hKc (Nat.cast_nonneg _)
      linarith
    exact_mod_cast hkey

/-- **Sharp upper bound (all `n`).** For `0 < c ≤ 1`: eventually `f_c(n) ≤ (c/2 + ε) n`. -/
theorem Fc_upper_s1 (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → (Fc c n : ℝ) ≤ (c / 2 + ε) * n := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈2 / c⌉₊ := ⟨_, rfl⟩
  obtain ⟨E₀, hinv⟩ := inverse_s1 ε hε K
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (((E₀ : ℝ) + 2) / c)
  refine ⟨N₁, fun n hn => ?_⟩
  have hcn : (E₀ : ℝ) + 2 < c * n := by
    have hnR : ((E₀ : ℝ) + 2) / c < n := lt_of_lt_of_le hN₁ (by exact_mod_cast hn)
    rw [div_lt_iff₀ hc0] at hnR
    linarith
  obtain ⟨hE₀E, hEle, hEgt, hnKE⟩ := floor_facts361 c hc0 n E₀ K hK hcn
  set E : ℕ := ⌊c * (n : ℝ)⌋₊ with hE
  have hEn : E ≤ n := by
    have h1 : c * (n : ℝ) ≤ 1 * n := mul_le_mul_of_nonneg_right hc1 (Nat.cast_nonneg n)
    have h2 : (E : ℝ) ≤ n := by linarith
    exact_mod_cast h2
  have hbound : ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 E → Avoids A n →
      (A.card : ℝ) ≤ (c / 2 + ε) * n := by
    intro A hAsub hAv
    by_contra hlt
    push_neg at hlt
    have hEn' : (E : ℝ) ≤ n := by exact_mod_cast hEn
    have hden : (1 / 2 + ε) * E ≤ (A.card : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_left hEn' hε.le
      linarith [hEle, h1]
    exact hinv E hE₀E A hAsub hden n hEn hnKE hAv
  have hFcE : Fc c n = F E n := by rw [Fc, hE]
  rw [hFcE]
  exact Erdos361.F_le_of_bound E n _ hbound

/-- **Upper bound for even `n`, `c ≤ 1/2`:** eventually `f_c(n) ≤ (c/3 + ε) n`. -/
theorem Fc_upper_s2_direct (c : ℝ) (hc0 : 0 < c) (hc12 : c ≤ 1 / 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → 2 ∣ n → (Fc c n : ℝ) ≤ (c / 3 + ε) * n := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈2 / c⌉₊ := ⟨_, rfl⟩
  obtain ⟨E₀, hinv⟩ := inverse_s2 ε hε K
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (((E₀ : ℝ) + 2) / c)
  refine ⟨N₁, fun n hn hn2 => ?_⟩
  have hcn : (E₀ : ℝ) + 2 < c * n := by
    have hnR : ((E₀ : ℝ) + 2) / c < n := lt_of_lt_of_le hN₁ (by exact_mod_cast hn)
    rw [div_lt_iff₀ hc0] at hnR
    linarith
  obtain ⟨hE₀E, hEle, hEgt, hnKE⟩ := floor_facts361 c hc0 n E₀ K hK hcn
  set E : ℕ := ⌊c * (n : ℝ)⌋₊ with hE
  have h2En : 2 * E ≤ n := by
    have h1 : c * (n : ℝ) ≤ 1 / 2 * n := mul_le_mul_of_nonneg_right hc12 (Nat.cast_nonneg n)
    have h2 : (2 : ℝ) * (E : ℝ) ≤ n := by linarith
    exact_mod_cast h2
  have hbound : ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 E → Avoids A n →
      (A.card : ℝ) ≤ (c / 3 + ε) * n := by
    intro A hAsub hAv
    by_contra hlt
    push_neg at hlt
    have h2E' : (2 : ℝ) * (E : ℝ) ≤ n := by exact_mod_cast h2En
    have hE0 : (0 : ℝ) ≤ (E : ℝ) := Nat.cast_nonneg E
    have hEn' : (E : ℝ) ≤ n := by linarith
    have hden : (1 / 3 + ε) * E ≤ (A.card : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_left hEn' hε.le
      linarith [hEle, h1]
    exact hinv E hE₀E A hAsub hden n hn2 h2En hnKE hAv
  have hFcE : Fc c n = F E n := by rw [Fc, hE]
  rw [hFcE]
  exact Erdos361.F_le_of_bound E n _ hbound

/-- **Upper bound for even `n`, `1/2 < c < 1`:** eventually `f_c(n) ≤ (2c/3 - 1/6 + ε) n`.
Split `A = A ∩ [1,D-1] ∪ A ∩ [D,M]` (`M = ⌊cn⌋`, `D = n - M`): the top part is bounded by the
pairs `{x, n-x}`, the bottom part by `inverse_s2`. -/
theorem Fc_upper_s2_split (c : ℝ) (hc12 : 1 / 2 < c) (hc1 : c < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → 2 ∣ n → (Fc c n : ℝ) ≤ (2 * c / 3 - 1 / 6 + ε) * n := by
  have hd0 : 0 < 1 - c := by linarith
  have hc0 : 0 < c := by linarith
  have hpos_c : (0 : ℝ) < 2 * c - 1 := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈2 / (1 - c)⌉₊ := ⟨_, rfl⟩
  obtain ⟨E₀, hinv⟩ := inverse_s2 (ε / 2) (by linarith) K
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt
    (((E₀ : ℝ) + 3) / (1 - c) + 4 / (2 * c - 1) + 2 / ε + 4 / (1 - c))
  refine ⟨N₁, fun n hn hn2 => ?_⟩
  have hnR : (N₁ : ℝ) ≤ n := by exact_mod_cast hn
  have hT1 : 0 ≤ ((E₀ : ℝ) + 3) / (1 - c) := div_nonneg (by positivity) hd0.le
  have hT2 : 0 ≤ (4 : ℝ) / (2 * c - 1) := div_nonneg (by norm_num) hpos_c.le
  have hT3 : 0 ≤ (2 : ℝ) / ε := div_nonneg (by norm_num) hε.le
  have hT4 : 0 ≤ (4 : ℝ) / (1 - c) := div_nonneg (by norm_num) hd0.le
  have hA1 : ((E₀ : ℝ) + 3) / (1 - c) < n := by linarith
  have hA2 : (4 : ℝ) / (2 * c - 1) < n := by linarith
  have hA3 : (2 : ℝ) / ε < n := by linarith
  have hA4 : (4 : ℝ) / (1 - c) < n := by linarith
  have hB1 : (E₀ : ℝ) + 3 < n * (1 - c) := (div_lt_iff₀ hd0).mp hA1
  have hB2 : (4 : ℝ) < n * (2 * c - 1) := (div_lt_iff₀ hpos_c).mp hA2
  have hB3 : (2 : ℝ) < n * ε := (div_lt_iff₀ hε).mp hA3
  have hB4 : (4 : ℝ) < n * (1 - c) := (div_lt_iff₀ hd0).mp hA4
  have hcn0 : (0 : ℝ) ≤ c * n := by positivity
  set M : ℕ := ⌊c * (n : ℝ)⌋₊ with hM
  have hMle : (M : ℝ) ≤ c * n := by rw [hM]; exact Nat.floor_le hcn0
  have hMgt : c * n - 1 < (M : ℝ) := by rw [hM]; exact Nat.sub_one_lt_floor _
  have hMlt : M < n := by
    have h1 : (M : ℝ) < n := by linarith
    exact_mod_cast h1
  set D : ℕ := n - M with hD
  have hDR : (D : ℝ) = (n : ℝ) - (M : ℝ) := by rw [hD, Nat.cast_sub hMlt.le]
  have hn2M : n ≤ 2 * M := by
    have h1 : (n : ℝ) ≤ 2 * (M : ℝ) := by linarith
    exact_mod_cast h1
  have hDM : D ≤ M := by omega
  have hDge : (E₀ : ℝ) + 2 ≤ (D : ℝ) - 1 := by rw [hDR]; linarith
  have hE0R : (0 : ℝ) ≤ (E₀ : ℝ) := Nat.cast_nonneg _
  have hD1 : 1 ≤ D := by
    have h1 : (1 : ℝ) ≤ (D : ℝ) := by linarith
    exact_mod_cast h1
  have hDm1R : ((D - 1 : ℕ) : ℝ) = (D : ℝ) - 1 := by push_cast [Nat.cast_sub hD1]; ring
  have hE₀ : E₀ ≤ D - 1 := by
    have h1 : (E₀ : ℝ) ≤ ((D - 1 : ℕ) : ℝ) := by rw [hDm1R]; linarith
    exact_mod_cast h1
  have hDle : ((D - 1 : ℕ) : ℝ) ≤ (1 - c) * n := by rw [hDm1R, hDR]; linarith
  have h2E : 2 * (D - 1) ≤ n := by
    have h1 : (2 : ℝ) * ((D - 1 : ℕ) : ℝ) ≤ n := by linarith
    exact_mod_cast h1
  have hnKE : n ≤ K * (D - 1) := by
    have hK2 : 2 / (1 - c) ≤ (K : ℝ) := by rw [hK]; exact Nat.le_ceil _
    have hKc : 2 ≤ (K : ℝ) * (1 - c) := (div_le_iff₀ hd0).mp hK2
    have h2D : (1 - c) * n ≤ 2 * ((D - 1 : ℕ) : ℝ) := by rw [hDm1R, hDR]; linarith
    have hkey : (n : ℝ) ≤ (K : ℝ) * ((D - 1 : ℕ) : ℝ) := by
      by_contra hcon
      push_neg at hcon
      have h1 := mul_lt_mul_of_pos_right hcon hd0
      have h2 : 2 * ((D - 1 : ℕ) : ℝ) ≤ ((K : ℝ) * (1 - c)) * ((D - 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hKc (Nat.cast_nonneg _)
      linarith
    exact_mod_cast hkey
  have hbound : ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 M → Avoids A n →
      (A.card : ℝ) ≤ (2 * c / 3 - 1 / 6 + ε) * n := by
    intro A hAsub hAv
    have hsplit := Erdos361.split_card_bound (by omega : 1 ≤ n) hD hDM hMlt hAv hAsub
    have hlosub : A ∩ Finset.Icc 1 (D - 1) ⊆ Finset.Icc 1 (D - 1) := by
      intro a ha; exact (Finset.mem_inter.mp ha).2
    have hloav : Avoids (A ∩ Finset.Icc 1 (D - 1)) n :=
      Erdos361.Avoids.subset hAv (by intro a ha; exact (Finset.mem_inter.mp ha).1)
    have hlo : ((A ∩ Finset.Icc 1 (D - 1)).card : ℝ)
        < (1 / 3 + ε / 2) * ((D - 1 : ℕ) : ℝ) := by
      by_contra hcon
      push_neg at hcon
      exact hinv (D - 1) hE₀ (A ∩ Finset.Icc 1 (D - 1)) hlosub hcon n hn2 h2E hnKE hloav
    have hcastsplit : (A.card : ℝ) ≤ ((A ∩ Finset.Icc 1 (D - 1)).card : ℝ) +
        (((M - D + 2) / 2 : ℕ) : ℝ) := by exact_mod_cast hsplit
    have hMval : (((M - D + 2) / 2 : ℕ) : ℝ) ≤ (c - 1 / 2) * n + 1 := by
      have h3 : 2 * ((M - D + 2) / 2) + n ≤ 2 * M + 2 := by omega
      have h3' : 2 * (((M - D + 2) / 2 : ℕ) : ℝ) + n ≤ 2 * (M : ℝ) + 2 := by exact_mod_cast h3
      linarith
    have hlo2 : (1 / 3 + ε / 2) * ((D - 1 : ℕ) : ℝ) ≤ (1 / 3 + ε / 2) * ((1 - c) * n) :=
      mul_le_mul_of_nonneg_left hDle (by linarith)
    have hεd : ε * ((1 - c) * n) ≤ ε * (n / 2) := by
      have h1 : (1 - c) * n ≤ n / 2 := by linarith
      exact mul_le_mul_of_nonneg_left h1 hε.le
    linarith [hcastsplit, hlo, hMval, hlo2, hεd, hB3]
  have hFcM : Fc c n = F M n := by rw [Fc, hM]
  rw [hFcM]
  exact Erdos361.F_le_of_bound M n _ hbound

/-! ### Lower bounds (explicit avoiders) -/

/-- The multiples of `3` in `[1,M]`. -/
def threes (M : ℕ) : Finset ℕ := (Finset.Icc 1 M).filter (fun x => 3 ∣ x)

lemma threes_subset (M : ℕ) : threes M ⊆ Finset.Icc 1 M := Finset.filter_subset _ _

lemma threes_card (M : ℕ) : (threes M).card = M / 3 := by
  have himg : threes M = (Finset.Icc 1 (M / 3)).image (fun k => 3 * k) := by
    apply Finset.ext; intro a
    simp only [threes, Finset.mem_filter, Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨ha1, ha2⟩, ⟨k, hk⟩⟩
      exact ⟨k, ⟨by omega, by omega⟩, by omega⟩
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      exact ⟨⟨by omega, by omega⟩, ⟨k, rfl⟩⟩
  rw [himg, Finset.card_image_of_injective _ (by
    intro x y hxy; have h3 : 3 * x = 3 * y := hxy; omega), Nat.card_Icc]
  omega

lemma threes_avoids {M n : ℕ} (hn : ¬ 3 ∣ n) : Avoids (threes M) n := by
  intro B hB hsum
  exfalso
  have hdvd : 3 ∣ B.sum id := by
    apply Finset.dvd_sum
    intro x hx
    have hx' := hB hx
    simp only [threes, Finset.mem_filter] at hx'
    exact hx'.2
  rw [hsum] at hdvd
  exact hn hdvd

/-- Upper residue class: `x ≡ 3 - (n mod 3) (mod 3)` with `(n+1)/2 ≤ x ≤ M`. -/
def upper3 (M n : ℕ) : Finset ℕ :=
  (Finset.Icc (((n + 1) / 2 + 2) / 3) ((M - (3 - n % 3)) / 3)).image
    (fun k => 3 * k + (3 - n % 3))

lemma upper3_mem {M n x : ℕ} (hn3 : ¬ 3 ∣ n) (hx : x ∈ upper3 M n) :
    (n + 1) / 2 ≤ x ∧ x ≤ M ∧ x % 3 ≠ 0 ∧ x % 3 ≠ n % 3 := by
  rw [upper3, Finset.mem_image] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  rw [Finset.mem_Icc] at hk
  obtain ⟨hk1, hk2⟩ := hk
  refine ⟨by omega, by omega, by omega, by omega⟩

lemma upper3_card (M n : ℕ) :
    (upper3 M n).card = (M - (3 - n % 3)) / 3 + 1 - ((n + 1) / 2 + 2) / 3 := by
  rw [upper3, Finset.card_image_of_injective _ (by
    intro a b hab
    have h3 : 3 * a + (3 - n % 3) = 3 * b + (3 - n % 3) := hab
    omega), Nat.card_Icc]

/-- Mixed construction (for `1/2 < c < 1`, `3 ∤ n`): multiples of 3, plus the residue class
`≢ 0, n (mod 3)` in the top half `[(n+1)/2, M]`. -/
def mixed3 (M n : ℕ) : Finset ℕ := threes M ∪ upper3 M n

lemma mixed3_subset {M n : ℕ} (hn3 : ¬ 3 ∣ n) : mixed3 M n ⊆ Finset.Icc 1 M := by
  intro x hx
  rw [mixed3, Finset.mem_union] at hx
  rcases hx with hx | hx
  · exact threes_subset M hx
  · have h := upper3_mem hn3 hx
    rw [Finset.mem_Icc]
    constructor <;> omega

lemma mixed3_avoids {M n : ℕ} (hn3 : ¬ 3 ∣ n) : Avoids (mixed3 M n) n := by
  intro B hB hsum
  by_contra hBne
  have hsum' : (∑ z ∈ B, z) = n := hsum
  have hmemB : ∀ z ∈ B, ¬ 3 ∣ z → (n + 1) / 2 ≤ z ∧ z % 3 ≠ n % 3 := by
    intro z hz hz3
    have hzm := hB hz
    rw [mixed3, Finset.mem_union] at hzm
    rcases hzm with hzm | hzm
    · simp only [threes, Finset.mem_filter] at hzm
      exact absurd hzm.2 hz3
    · have h := upper3_mem hn3 hzm
      exact ⟨h.1, h.2.2.2⟩
  by_cases hex : ∃ x ∈ B, ¬ 3 ∣ x
  · obtain ⟨x, hxB, hx3⟩ := hex
    have hx := hmemB x hxB hx3
    by_cases hex2 : ∃ y ∈ B, y ≠ x ∧ ¬ 3 ∣ y
    · obtain ⟨y, hyB, hyx, hy3⟩ := hex2
      have hy := hmemB y hyB hy3
      have hpair : ({x, y} : Finset ℕ) ⊆ B := by
        intro a ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha
        rcases ha with h | h <;> subst h <;> assumption
      have hle : x + y ≤ ∑ z ∈ B, z := by
        have h : ∑ z ∈ ({x, y} : Finset ℕ), z ≤ ∑ z ∈ B, z := Finset.sum_le_sum_of_subset hpair
        rwa [Finset.sum_pair (Ne.symm hyx)] at h
      omega
    · push_neg at hex2
      have hrest : ∀ y ∈ B.erase x, 3 ∣ y := by
        intro y hy
        rw [Finset.mem_erase] at hy
        exact hex2 y hy.2 hy.1
      have hdvd : 3 ∣ ∑ y ∈ B.erase x, y := Finset.dvd_sum hrest
      have hsplit : x + ∑ z ∈ B.erase x, z = ∑ z ∈ B, z :=
        Finset.add_sum_erase B (fun z => z) hxB
      obtain ⟨m, hm⟩ := hdvd
      omega
  · push_neg at hex
    have hdvd : 3 ∣ ∑ z ∈ B, z := Finset.dvd_sum hex
    rw [hsum'] at hdvd
    exact hn3 hdvd

lemma mixed3_card {M n : ℕ} (hn3 : ¬ 3 ∣ n) :
    (mixed3 M n).card = M / 3 + ((M - (3 - n % 3)) / 3 + 1 - ((n + 1) / 2 + 2) / 3) := by
  have hdisj : Disjoint (threes M) (upper3 M n) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [threes, Finset.mem_filter] at hx1
    have h3x : 3 ∣ x := hx1.2
    have h := upper3_mem hn3 hx2
    have h0x : x % 3 ≠ 0 := h.2.2.1
    omega
  rw [mixed3, Finset.card_union_of_disjoint hdisj, threes_card, upper3_card]

/-- Odd `n`: `f_c(n) ≥ ⌊cn⌋/2 ≥ (c/2) n - 1`. -/
lemma Fc_lower_odd (c : ℝ) (hc0 : 0 < c) (k : ℕ) :
    c / 2 * ((2 * k + 1 : ℕ) : ℝ) - 1 ≤ (Fc c (2 * k + 1) : ℝ) := by
  have hcn0 : (0 : ℝ) ≤ c * ((2 * k + 1 : ℕ) : ℝ) := by positivity
  set M : ℕ := ⌊c * ((2 * k + 1 : ℕ) : ℝ)⌋₊ with hM
  have hMgt : c * ((2 * k + 1 : ℕ) : ℝ) - 1 < (M : ℝ) := by
    rw [hM]; exact Nat.sub_one_lt_floor _
  have hF : M / 2 ≤ Fc c (2 * k + 1) := by
    rw [Fc, ← hM]; exact Erdos361.oddn_lower' ⟨k, rfl⟩
  have hF' : ((M / 2 : ℕ) : ℝ) ≤ (Fc c (2 * k + 1) : ℝ) := by exact_mod_cast hF
  have h2 : M ≤ 2 * (M / 2) + 1 := by omega
  have h2' : (M : ℝ) ≤ 2 * ((M / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast h2
  linarith

/-- `3 ∤ n`: `f_c(n) ≥ ⌊cn⌋/3 ≥ (c/3) n - 1`. -/
lemma Fc_lower_threes (c : ℝ) (hc0 : 0 < c) (n : ℕ) (hn3 : ¬ 3 ∣ n) :
    c / 3 * (n : ℝ) - 1 ≤ (Fc c n : ℝ) := by
  have hcn0 : (0 : ℝ) ≤ c * n := by positivity
  set M : ℕ := ⌊c * (n : ℝ)⌋₊ with hM
  have hMgt : c * n - 1 < (M : ℝ) := by rw [hM]; exact Nat.sub_one_lt_floor _
  have hF : M / 3 ≤ Fc c n := by
    have h1 : (threes M).card ≤ F M n := F_ge_card (threes M) (threes_subset M) (threes_avoids hn3)
    rw [threes_card] at h1
    rw [Fc, ← hM]
    exact h1
  have hF' : ((M / 3 : ℕ) : ℝ) ≤ (Fc c n : ℝ) := by exact_mod_cast hF
  have h3 : M ≤ 3 * (M / 3) + 2 := by omega
  have h3' : (M : ℝ) ≤ 3 * ((M / 3 : ℕ) : ℝ) + 2 := by exact_mod_cast h3
  linarith

/-- `3 ∤ n`: `f_c(n) ≥ |mixed3| ≥ (2c/3 - 1/6) n - 6`. -/
lemma Fc_lower_mixed (c : ℝ) (hc0 : 0 < c) (n : ℕ) (hn3 : ¬ 3 ∣ n) :
    (2 * c / 3 - 1 / 6) * (n : ℝ) - 6 ≤ (Fc c n : ℝ) := by
  have hcn0 : (0 : ℝ) ≤ c * n := by positivity
  set M : ℕ := ⌊c * (n : ℝ)⌋₊ with hM
  have hMgt : c * n - 1 < (M : ℝ) := by rw [hM]; exact Nat.sub_one_lt_floor _
  obtain ⟨V, hV⟩ : ∃ V : ℕ, V = (mixed3 M n).card := ⟨_, rfl⟩
  have hVf : V = M / 3 + ((M - (3 - n % 3)) / 3 + 1 - ((n + 1) / 2 + 2) / 3) := by
    rw [hV, mixed3_card hn3]
  have hF : V ≤ Fc c n := by
    rw [hV, Fc, ← hM]
    exact F_ge_card (mixed3 M n) (mixed3_subset hn3) (mixed3_avoids hn3)
  obtain ⟨h2, hh2⟩ : ∃ h2 : ℕ, h2 = n / 2 := ⟨_, rfl⟩
  have hnat : 2 * M ≤ 3 * V + h2 + 14 := by omega
  have hh2' : 2 * h2 ≤ n := by omega
  have hnat' : 2 * (M : ℝ) ≤ 3 * (V : ℝ) + (h2 : ℝ) + 14 := by exact_mod_cast hnat
  have hh2R : 2 * (h2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hh2'
  have hF' : (V : ℝ) ≤ (Fc c n : ℝ) := by exact_mod_cast hF
  linarith

/-! ### Limits -/

/-- A squeeze lemma for ratios along a subsequence `u k`. -/
lemma tendsto_ratio_of_bounds (u : ℕ → ℕ) (hu : ∀ k, k ≤ u k) (hu1 : ∀ k, 1 ≤ u k)
    (g : ℕ → ℝ) (L C : ℝ) (hlow : ∀ k, L * (u k : ℝ) - C ≤ g k)
    (hup : ∀ ε > 0, ∃ N₀ : ℕ, ∀ k, N₀ ≤ k → g k ≤ (L + ε) * (u k : ℝ)) :
    Tendsto (fun k => g k / (u k : ℝ)) atTop (𝓝 L) := by
  rw [tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · have hδ : 0 < L - b := by linarith
    obtain ⟨N₁, hN₁⟩ := exists_nat_gt ((|C| + 1) / (L - b))
    filter_upwards [eventually_ge_atTop N₁] with k hk
    show b < g k / (u k : ℝ)
    have hpos : (0 : ℝ) < (u k : ℝ) := by exact_mod_cast hu1 k
    have hkN : (N₁ : ℝ) ≤ (u k : ℝ) := by exact_mod_cast le_trans hk (hu k)
    have h5 : |C| + 1 < (u k : ℝ) * (L - b) := by
      have h6 := lt_of_lt_of_le hN₁ hkN
      rwa [div_lt_iff₀ hδ] at h6
    rw [lt_div_iff₀ hpos]
    have hC : C ≤ |C| := le_abs_self C
    have h7 := hlow k
    linarith
  · obtain ⟨N₀, hN₀⟩ := hup ((b - L) / 2) (by linarith)
    filter_upwards [eventually_ge_atTop N₀] with k hk
    show g k / (u k : ℝ) < b
    have hpos : (0 : ℝ) < (u k : ℝ) := by exact_mod_cast hu1 k
    have h8 := hN₀ k hk
    rw [div_lt_iff₀ hpos]
    have h9 : 0 < (b - L) / 2 * (u k : ℝ) := mul_pos (by linarith) hpos
    linarith

/-- **Odd `n`:** `f_c(n)/n → c/2` (`0 < c ≤ 1`). -/
theorem Fc_limit_odd (c : ℝ) (hc0 : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun k : ℕ => (Fc c (2 * k + 1) : ℝ) / ((2 * k + 1 : ℕ) : ℝ)) atTop (𝓝 (c / 2)) := by
  apply tendsto_ratio_of_bounds (fun k => 2 * k + 1) (fun k => by show k ≤ 2 * k + 1; omega)
    (fun k => by show 1 ≤ 2 * k + 1; omega) (fun k => (Fc c (2 * k + 1) : ℝ)) (c / 2) 1
  · intro k; exact Fc_lower_odd c hc0 k
  · intro ε hε
    obtain ⟨N₀, hN₀⟩ := Fc_upper_s1 c hc0 hc1 ε hε
    exact ⟨N₀, fun k hk => hN₀ (2 * k + 1) (by omega)⟩

/-- **`n ≡ 2, 4 (mod 6)`, `0 < c ≤ 1/2`:** `f_c(n)/n → c/3`. -/
theorem Fc_limit_mod6_low (c : ℝ) (hc0 : 0 < c) (hc12 : c ≤ 1 / 2) (r : ℕ) (hr : r = 2 ∨ r = 4) :
    Tendsto (fun k : ℕ => (Fc c (6 * k + r) : ℝ) / ((6 * k + r : ℕ) : ℝ)) atTop
      (𝓝 (c / 3)) := by
  have hr3 : ∀ k : ℕ, ¬ 3 ∣ 6 * k + r := by intro k; rcases hr with rfl | rfl <;> omega
  have hr2 : ∀ k : ℕ, 2 ∣ 6 * k + r := by intro k; rcases hr with rfl | rfl <;> omega
  apply tendsto_ratio_of_bounds (fun k => 6 * k + r) (fun k => by show k ≤ 6 * k + r; omega)
    (fun k => by show 1 ≤ 6 * k + r; rcases hr with rfl | rfl <;> omega)
    (fun k => (Fc c (6 * k + r) : ℝ)) (c / 3) 1
  · intro k; exact Fc_lower_threes c hc0 (6 * k + r) (hr3 k)
  · intro ε hε
    obtain ⟨N₀, hN₀⟩ := Fc_upper_s2_direct c hc0 hc12 ε hε
    exact ⟨N₀, fun k hk => hN₀ (6 * k + r) (by omega) (hr2 k)⟩

/-- **`n ≡ 2, 4 (mod 6)`, `1/2 < c < 1`:** `f_c(n)/n → 2c/3 - 1/6`. -/
theorem Fc_limit_mod6_high (c : ℝ) (hc12 : 1 / 2 < c) (hc1 : c < 1) (r : ℕ)
    (hr : r = 2 ∨ r = 4) :
    Tendsto (fun k : ℕ => (Fc c (6 * k + r) : ℝ) / ((6 * k + r : ℕ) : ℝ)) atTop
      (𝓝 (2 * c / 3 - 1 / 6)) := by
  have hc0 : 0 < c := by linarith
  have hr3 : ∀ k : ℕ, ¬ 3 ∣ 6 * k + r := by intro k; rcases hr with rfl | rfl <;> omega
  have hr2 : ∀ k : ℕ, 2 ∣ 6 * k + r := by intro k; rcases hr with rfl | rfl <;> omega
  apply tendsto_ratio_of_bounds (fun k => 6 * k + r) (fun k => by show k ≤ 6 * k + r; omega)
    (fun k => by show 1 ≤ 6 * k + r; rcases hr with rfl | rfl <;> omega)
    (fun k => (Fc c (6 * k + r) : ℝ)) (2 * c / 3 - 1 / 6) 6
  · intro k; exact Fc_lower_mixed c hc0 (6 * k + r) (hr3 k)
  · intro ε hε
    obtain ⟨N₀, hN₀⟩ := Fc_upper_s2_split c hc12 hc1 ε hε
    exact ⟨N₀, fun k hk => hN₀ (6 * k + r) (by omega) (hr2 k)⟩

/-- Pointwise bounds in the regular range `c ≥ 1`. -/
lemma Fc_bounds_cge1 (c : ℝ) (hc : 1 ≤ c) (n : ℕ) (hn : 1 ≤ n) :
    (c - 1 / 2) - (3 / 2) * (1 / (n : ℝ)) ≤ (Fc c n : ℝ) / n ∧
      (Fc c n : ℝ) / n ≤ c - 1 / 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hc0 : (0 : ℝ) < c := by linarith
  have hcn0 : (0 : ℝ) ≤ c * n := by positivity
  set M : ℕ := ⌊c * (n : ℝ)⌋₊ with hM
  have hnM : n ≤ M := by
    rw [hM]
    apply Nat.le_floor
    have h1 : 1 * (n : ℝ) ≤ c * n := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg n)
    linarith
  have hF : Fc c n = M - (n + 1) / 2 := by
    rw [Fc, ← hM]; exact Erdos361.erdos361_cge1 M n hn hnM
  have hle : (n + 1) / 2 ≤ M := by omega
  have hFR : (Fc c n : ℝ) = (M : ℝ) - (((n + 1) / 2 : ℕ) : ℝ) := by
    rw [hF, Nat.cast_sub hle]
  have hMle : (M : ℝ) ≤ c * n := by rw [hM]; exact Nat.floor_le hcn0
  have hMgt : c * n - 1 < (M : ℝ) := by rw [hM]; exact Nat.sub_one_lt_floor _
  have hh1 : (n : ℝ) ≤ 2 * (((n + 1) / 2 : ℕ) : ℝ) := by
    have h1 : n ≤ 2 * ((n + 1) / 2) := by omega
    exact_mod_cast h1
  have hh2 : 2 * (((n + 1) / 2 : ℕ) : ℝ) ≤ (n : ℝ) + 1 := by
    have h1 : 2 * ((n + 1) / 2) ≤ n + 1 := by omega
    exact_mod_cast h1
  constructor
  · rw [le_div_iff₀ hnpos]
    have h1n : (1 / (n : ℝ)) * n = 1 := by rw [one_div]; exact inv_mul_cancel₀ hnpos.ne'
    have hexp : ((c - 1 / 2) - (3 / 2) * (1 / (n : ℝ))) * n = (c - 1 / 2) * n - 3 / 2 := by
      rw [sub_mul, mul_assoc, h1n, mul_one]
    rw [hexp, hFR]
    linarith
  · rw [div_le_iff₀ hnpos, hFR]
    linarith

/-- **Regular range:** for `c ≥ 1`, `f_c(n)/n → c - 1/2`. -/
theorem Fc_limit_cge1 (c : ℝ) (hc : 1 ≤ c) :
    Tendsto (fun n : ℕ => (Fc c n : ℝ) / n) atTop (𝓝 (c - 1 / 2)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun n : ℕ => (c - 1 / 2) - (3 / 2) * (1 / (n : ℝ))) (h := fun _ : ℕ => c - 1 / 2)
  · have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have h2 := (tendsto_const_nhds (x := c - 1 / 2)).sub (h1.const_mul (3 / 2))
    simpa using h2
  · exact tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (Fc_bounds_cge1 c hc n hn).1
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (Fc_bounds_cge1 c hc n hn).2

/-- **Irregularity, quantitative form:** for every `0 < c < 1`, `f_c(n)/n` has two distinct
subsequential limits, along odd `n` and along `n ≡ 2 (mod 6)`. -/
theorem Fc_two_limit_points (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ L₁ L₂ : ℝ, L₁ ≠ L₂ ∧
      Tendsto (fun k : ℕ => (Fc c (2 * k + 1) : ℝ) / ((2 * k + 1 : ℕ) : ℝ)) atTop (𝓝 L₁) ∧
      Tendsto (fun k : ℕ => (Fc c (6 * k + 2) : ℝ) / ((6 * k + 2 : ℕ) : ℝ)) atTop (𝓝 L₂) := by
  rcases le_or_gt c (1 / 2) with h | h
  · refine ⟨c / 2, c / 3, ?_, Fc_limit_odd c hc0 hc1.le,
      Fc_limit_mod6_low c hc0 h 2 (Or.inl rfl)⟩
    intro heq; linarith
  · refine ⟨c / 2, 2 * c / 3 - 1 / 6, ?_, Fc_limit_odd c hc0 hc1.le,
      Fc_limit_mod6_high c h hc1 2 (Or.inl rfl)⟩
    intro heq; linarith

end Erdos361Asymptotics
