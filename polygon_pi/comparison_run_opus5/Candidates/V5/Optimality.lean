import ProofRefinement.PolygonPi.Proof.Main
import ProofRefinement.PolygonPi.Candidates.V5.DeficitMonotone
import ProofRefinement.PolygonPi.Candidates.V5.CubicDeficit
import ProofRefinement.PolygonPi.Candidates.V5.QuinticDeficit
import ProofRefinement.PolygonPi.Candidates.V5.CosineAnchor

/-!
# The optimality certificate: what the scored contract *is*

Derived theorems for candidate `V5`. Theorems and lemmas only — no `axiom`,
no `sorry`, no oracle.

Every sprint so far has proved a statement about **one** candidate. This file
proves statements about **all** of them. Write

    D n := 4 ^ n * (π - polygonLower n).

`V5/CubicDeficit.lean` and `V5/QuinticDeficit.lean` between them sandwich `D`:

    π ^ 3 / 96 - π ^ 5 / (30720 · 4 ^ n)  ≤  D n  ≤  π ^ 3 / 96,      (§1)

and `V5/DeficitMonotone.lean` shows `D` is non-decreasing with `D 0 = π - 2√2`.
Those three facts determine the admissible set of `ValidPolygonBound` exactly,
up to one boundary point.

## The two directions

**Necessity (§2–§3).** If `ValidPolygonBound lam kap` then

    lam < π - 2√2        (instantiate the contract at `n = 0`; one line), and
    π ^ 3 / 96 ≤ kap.

The second is the first genuinely *asymptotic* statement this workspace has
needed. It is **false at every finite `n`**: for each individual `n` the
contract only gives `D n < kap`, and `D n < π ^ 3 / 96` strictly. What forces
`kap` above the floor is the left half of the sandwich together with an
Archimedean step: if `kap` were below the floor by `ε > 0`, choose `n` with
`4 ^ n > π ^ 5 / (30720 ε)`; then the `π ^ 5` tail of `deficit_ge` is smaller
than `ε` and `D n` has already overtaken `kap`. Nothing numeric about `π`
enters: `admissible_kappa_ge` is proved with `π ^ 3` and `π ^ 5` symbolic, and
every quantity in the argument cancels. It is therefore *sharper* than any
rational certification could make it, and it is what makes `π ^ 3 / 96` a
theorem rather than a docstring.

**Sufficiency (§5).** Conversely `0 ≤ lam`, `lam < π - 2√2` and
`π ^ 3 / 96 < kap` suffice. This is `V4`'s inline contract proof lifted out and
stated once, with the two numeric literals abstracted away.

Together:

    (0 ≤ lam ∧ lam < π − 2√2 ∧ π ^ 3 / 96 < kap)  →  ValidPolygonBound lam kap
    ValidPolygonBound lam kap  →  (0 ≤ lam ∧ lam < π − 2√2 ∧ π ^ 3 / 96 ≤ kap)

so the admissible set is pinned except at the single boundary point
`kap = π ^ 3 / 96`, which is irrational and therefore unreachable by any
rational literal the evaluator will accept. Closing that boundary case means
proving `D n < π ^ 3 / 96` *strictly* for every `n`, which needs a septic Taylor
rung; it is deliberately left open.

## The consequence for the score

    inf { kap - lam : ValidPolygonBound lam kap } = π ^ 3 / 96 - (π - 2√2),

approached but never attained. §4 certifies that real number from below with the
rational bounds this candidate proves, giving the permanent floor

    9816488/1000000000 < kap - lam       for every admissible pair.

No candidate in this benchmark, past or future, can score below that.
-/

noncomputable section

namespace ProofRefinement.PolygonPi.Candidates.V5

open ProofRefinement.PolygonPi PolygonCore

/-! ### 1. The two deficit bounds, scaled by `4 ^ n`

`deficit_le` and `deficit_ge` are stated as bounds on `π - polygonLower n`, with
the `4 ^ n` living in the denominators on the right. Every argument below wants
them the other way round, as bounds on the scaled deficit
`D n = 4 ^ n * (π - polygonLower n)`. `deficit_ge`'s tail carries
`4 ^ n * 4 ^ n`, so exactly one factor cancels. -/

/-- **The scaled deficit never exceeds the floor.** `D n ≤ π ^ 3 / 96`,
uniformly in `n`. -/
lemma deficit_scaled_le (n : ℕ) :
    4 ^ n * (Real.pi - polygonLower n) ≤ Real.pi ^ 3 / 96 := by
  have h4n : (0 : ℝ) < 4 ^ n := by positivity
  calc 4 ^ n * (Real.pi - polygonLower n)
      ≤ 4 ^ n * (Real.pi ^ 3 / (96 * 4 ^ n)) :=
        mul_le_mul_of_nonneg_left (deficit_le n) h4n.le
    _ = Real.pi ^ 3 / 96 := by field_simp

/-- **The scaled deficit approaches the floor.** `D n ≥ π ^ 3 / 96 -
π ^ 5 / (30720 · 4 ^ n)`: the gap to the floor is `O(4 ^ (-n))`, and this is the
only place the whole optimality argument needs. -/
lemma deficit_scaled_ge (n : ℕ) :
    Real.pi ^ 3 / 96 - Real.pi ^ 5 / (30720 * 4 ^ n)
      ≤ 4 ^ n * (Real.pi - polygonLower n) := by
  have h4n : (0 : ℝ) < 4 ^ n := by positivity
  have h := mul_le_mul_of_nonneg_left (deficit_ge n) h4n.le
  have hE : (4 : ℝ) ^ n * (Real.pi ^ 3 / (96 * 4 ^ n)
        - Real.pi ^ 5 / (30720 * 4 ^ n * 4 ^ n))
      = Real.pi ^ 3 / 96 - Real.pi ^ 5 / (30720 * 4 ^ n) := by
    field_simp
  rw [hE] at h
  exact h

/-- The contract's upper conjunct, read as a statement about the scaled
deficit: at every depth, `D n < kap`. -/
lemma scaled_lt_kappa {lam kap : ℝ} (h : ValidPolygonBound lam kap) (n : ℕ) :
    4 ^ n * (Real.pi - polygonLower n) < kap := by
  have h4n : (0 : ℝ) < 4 ^ n := by positivity
  have hn := (h.2.2 n).2
  have hlt : Real.pi - polygonLower n < kap / 4 ^ n := by linarith
  have h2 : (Real.pi - polygonLower n) * 4 ^ n < kap := (lt_div_iff₀ h4n).mp hlt
  calc (4 : ℝ) ^ n * (Real.pi - polygonLower n)
      = (Real.pi - polygonLower n) * 4 ^ n := by ring
    _ < kap := h2

/-! ### 2. The Archimedean step, and the floor for `kap`

The only property of `ℝ` used here is that it is Archimedean. `exists_nat_gt`
produces a natural number above a given real; `nat_le_four_pow` converts that
into a power of `4`, by a five-line induction rather than by hunting for a
library lemma. -/

/-- `(n : ℝ) ≤ 4 ^ n`. Induction: `k + 1 ≤ 4 ^ k + 4 ^ k ≤ 4 · 4 ^ k`. -/
lemma nat_le_four_pow (n : ℕ) : (n : ℝ) ≤ 4 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
    have h1 : (1 : ℝ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)
    have hsucc : (4 : ℝ) ^ (k + 1) = 4 * 4 ^ k := by ring
    push_cast
    rw [hsucc]
    linarith

/-- **No admissible `kap` lies below `π ^ 3 / 96`.**

This is the converse half of the upper side and the first asymptotic statement
in the workspace: it is *false* at every fixed depth, since `D n < π ^ 3 / 96`
for each `n`, and only the limit forces it.

The proof is entirely symbolic — `π ^ 3` and `π ^ 5` never receive a numeric
value, and every occurrence of them cancels. Suppose `kap < π ^ 3 / 96` and put
`ε := π ^ 3 / 96 - kap > 0`. Pick `n` with `π ^ 5 / (30720 ε) < n ≤ 4 ^ n`.
Then

* `π ^ 5 < 4 ^ n · 30720 ε`                  (clearing the choice of `n`), while
* `ε < π ^ 5 / (30720 · 4 ^ n)`              (from `deficit_scaled_ge n` and
                                              `scaled_lt_kappa`), i.e.
  `ε · 30720 · 4 ^ n < π ^ 5`.

Contradiction. -/
theorem admissible_kappa_ge {lam kap : ℝ} (h : ValidPolygonBound lam kap) :
    Real.pi ^ 3 / 96 ≤ kap := by
  by_contra hcon
  push_neg at hcon
  have hε : (0 : ℝ) < Real.pi ^ 3 / 96 - kap := by linarith
  obtain ⟨n, hn⟩ :=
    exists_nat_gt (Real.pi ^ 5 / (30720 * (Real.pi ^ 3 / 96 - kap)))
  have hn4 : Real.pi ^ 5 / (30720 * (Real.pi ^ 3 / 96 - kap)) < 4 ^ n :=
    lt_of_lt_of_le hn (nat_le_four_pow n)
  have hpos : (0 : ℝ) < 30720 * (Real.pi ^ 3 / 96 - kap) := by linarith
  have hA : Real.pi ^ 5 < 4 ^ n * (30720 * (Real.pi ^ 3 / 96 - kap)) :=
    (div_lt_iff₀ hpos).mp hn4
  have hpos2 : (0 : ℝ) < 30720 * (4 : ℝ) ^ n := by positivity
  have hD : Real.pi ^ 3 / 96 - kap < Real.pi ^ 5 / (30720 * 4 ^ n) := by
    linarith [deficit_scaled_ge n, scaled_lt_kappa h n]
  have hE : (Real.pi ^ 3 / 96 - kap) * (30720 * 4 ^ n) < Real.pi ^ 5 :=
    (lt_div_iff₀ hpos2).mp hD
  linarith

/-! ### 3. The ceiling for `lam`

Nothing asymptotic here: the lower conjunct is binding *and attained* at
`n = 0`, by `DeficitMonotone.lean`, so the contract instantiated at `n = 0` is
already the whole statement. -/

/-- `polygonLower 0 = 2√2`: the square inscribed in the unit circle. -/
lemma polygonLower_zero_eq : polygonLower 0 = 2 * Real.sqrt 2 := by
  simp [polygonLower]

/-- **No admissible `lam` reaches `π - 2√2`.** One line from the contract at
`n = 0`. Combined with `deficit_ge_zero_deficit` (which says `n = 0` is the
binding depth) this is exactly the ceiling. -/
theorem admissible_lambda_lt {lam kap : ℝ} (h : ValidPolygonBound lam kap) :
    lam < Real.pi - 2 * Real.sqrt 2 := by
  have h0 := (h.2.2 0).1
  rw [polygonLower_zero_eq, pow_zero, div_one] at h0
  linarith

/-- **The optimality certificate, in exact form.** Every admissible pair scores
strictly above `π ^ 3 / 96 - (π - 2√2)`. Equivalently, that real number is the
infimum of the score, and it is not attained. -/
theorem admissible_score_gt {lam kap : ℝ} (h : ValidPolygonBound lam kap) :
    Real.pi ^ 3 / 96 - (Real.pi - 2 * Real.sqrt 2) < kap - lam := by
  linarith [admissible_kappa_ge h, admissible_lambda_lt h]

/-! ### 4. Certifying the optimum from below

The exact optimum is `0.009816519909519985…`. Here it is bounded below by a
rational, from three one-sided bounds: `pi_ge_depth_three`
(`3.141592652724 ≤ π`, the new depth-3 lower anchor) for the cube,
`pi_le_sharp` (`π ≤ 3.1415926848`, the cosine anchor) for the subtraction, and
`s1_gt` (`1.414213562373 < √2`, the first stage of the anchor's radical chain).

    (3.141592652724) ^ 3 / 96         ≥ 0.32298204848
    3.1415926848 - 2 · 1.414213562373 = 0.313165560054
    difference                        = 0.009816488426…   (margin 4.26e-10)

The floor is `2.7e-11 + 3.1e-8` short of the true optimum: essentially all of
the remaining error is `pi_le_sharp`'s, i.e. the quartic truncation of the
cosine anchor at `π/64`. -/

/-- `1.414213562373 < √2`, from the cosine anchor's first radical stage.
`Real.sqrtTwoAddSeries_one` is the identification `sqrtTwoAddSeries 0 1 = √2`. -/
theorem sqrt_two_gt_sharp : (1414213562373/1000000000000 : ℝ) < Real.sqrt 2 := by
  have h := s1_gt
  rwa [Real.sqrtTwoAddSeries_one] at h

/-- `π ^ 3 / 96 > 0.32298204848` (true value `0.3229820487531…`, so this is
`2.7e-11` low). The cube of a thirteen-digit numerator; `norm_num` compares the
39-digit intermediates exactly. -/
theorem pi_cube_div_gt : (32298204848/100000000000 : ℝ) < Real.pi ^ 3 / 96 := by
  have h3 : ((3141592652724/1000000000000 : ℝ)) ^ 3 ≤ Real.pi ^ 3 :=
    pow_le_pow_left₀ (by norm_num) pi_ge_depth_three 3
  have hb : (96 : ℝ) * (32298204848/100000000000)
      < ((3141592652724/1000000000000 : ℝ)) ^ 3 := by norm_num
  rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 96)]
  linarith

/-- **The certified floor of the benchmark.** The exact optimum
`π ^ 3 / 96 - (π - 2√2) = 0.009816519909…` is above `0.009816488`. -/
theorem optimum_gt :
    (9816488/1000000000 : ℝ) < Real.pi ^ 3 / 96 - (Real.pi - 2 * Real.sqrt 2) := by
  linarith [pi_cube_div_gt, pi_le_sharp, sqrt_two_gt_sharp]

/-- **The headline theorem of the sprint.** *Every* candidate satisfying the
scored contract — past, present or future — has score strictly above
`9816488/1000000000`. -/
theorem admissible_score_gt_rat {lam kap : ℝ} (h : ValidPolygonBound lam kap) :
    (9816488/1000000000 : ℝ) < kap - lam :=
  optimum_gt.trans (admissible_score_gt h)

/-! ### 5. The converse: the bracket is sufficient

`V4` proved the contract inline, with its two rational literals baked into the
argument. Stated once with the literals abstracted, the same proof becomes a
characterization: everything about polygons, deficits, monotonicity and Taylor
order is consumed here and never has to be mentioned again. All a successor
candidate has to do is exhibit rationals inside the bracket. -/

/-- **Sufficiency.** Any `lam` in `[0, π - 2√2)` and any `kap` above the floor
`π ^ 3 / 96` give an admissible pair.

Lower conjunct: monotonicity of the scaled deficit (`deficit_ge_zero_deficit`)
reduces every depth to `n = 0`, where the deficit is `π - 2√2`.
Upper conjunct: the uniform cubic bound `deficit_scaled_le`. -/
theorem valid_of_bracket {lam kap : ℝ} (h0 : 0 ≤ lam)
    (hlam : lam < Real.pi - 2 * Real.sqrt 2)
    (hkap : Real.pi ^ 3 / 96 < kap) :
    ValidPolygonBound lam kap := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi3 : (0 : ℝ) < Real.pi ^ 3 / 96 := by positivity
  refine ⟨h0, by linarith, fun n => ⟨?_, ?_⟩⟩
  · have h4n : (0 : ℝ) < 4 ^ n := by positivity
    have hd : Real.pi - polygonLower 0 ≤ 4 ^ n * (Real.pi - polygonLower n) :=
      deficit_ge_zero_deficit n
    rw [polygonLower_zero_eq] at hd
    have hlt : lam / 4 ^ n < Real.pi - polygonLower n := by
      rw [div_lt_iff₀' h4n]
      linarith
    linarith
  · have h4n : (0 : ℝ) < 4 ^ n := by positivity
    have hstrict : (Real.pi - polygonLower n) * 4 ^ n < kap := by
      linarith [deficit_scaled_le n]
    have hfin : Real.pi - polygonLower n < kap / 4 ^ n := by
      rw [lt_div_iff₀ h4n]
      exact hstrict
    linarith

/-- The two directions side by side, as a single statement. The admissible set
is determined except on the boundary `kap = π ^ 3 / 96`, which is irrational and
so cannot be hit by any rational literal the evaluator accepts. -/
theorem valid_iff_bracket_of_ne {lam kap : ℝ} (hne : Real.pi ^ 3 / 96 ≠ kap) :
    ValidPolygonBound lam kap ↔
      (0 ≤ lam ∧ lam < Real.pi - 2 * Real.sqrt 2 ∧ Real.pi ^ 3 / 96 < kap) := by
  constructor
  · intro h
    exact ⟨h.1, admissible_lambda_lt h, lt_of_le_of_ne (admissible_kappa_ge h) hne⟩
  · rintro ⟨h0, hlam, hkap⟩
    exact valid_of_bracket h0 hlam hkap

end ProofRefinement.PolygonPi.Candidates.V5
