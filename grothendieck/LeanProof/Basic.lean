import Mathlib.Tactic

/-- **Theorem**: The sum of two odd integers is even.

Recall the definitions:
- `Odd a` means `∃ k, a = 2 * k + 1`
- `Even n` means `∃ k, n = k + k`  (i.e., `∃ k, n = 2 * k`)
-/
theorem sum_of_two_odds_is_even (a b : ℤ) (ha : Odd a) (hb : Odd b) : Even (a + b) := by
  -- `ha : Odd a` is really `∃ k, a = 2 * k + 1`.
  -- `obtain ⟨k, rfl⟩` does two things:
  --   1. Extracts the witness `k` from the existential.
  --   2. `rfl` pattern-matches on the proof that `a = 2 * k + 1`,
  --      and *rewrites* every occurrence of `a` in the goal with `2 * k + 1`.
  --      (rfl stands for "reflexivity" — it unifies `a` with `2 * k + 1`.)
  -- After this line, `a` is gone; the goal now mentions `2 * k + 1` directly.
  obtain ⟨k, rfl⟩ := ha

  -- Same thing for `b`: extract witness `l` and rewrite `b ↦ 2 * l + 1`.
  -- The goal is now: `Even ((2 * k + 1) + (2 * l + 1))`
  obtain ⟨l, rfl⟩ := hb

  -- We need to provide a witness `m` such that `(2*k+1) + (2*l+1) = m + m`.
  -- Choosing `m = k + l + 1` works because `2*(k+l+1) = 2k + 2l + 2`.
  -- `⟨k + l + 1, by ring⟩` builds the existential proof:
  --   - `k + l + 1` is the witness
  --   - `by ring` automatically verifies the algebraic identity
  exact ⟨k + l + 1, by ring⟩
