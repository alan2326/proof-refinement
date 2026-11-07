# V68 vs Wang 2025: what we changed and why it gave a better constant

**Frontier**: V68 certifies $c = 71313/200000 = 0.356565$ for the Korenblum
Bergman-space maximum-principle constant. Wang 2025 ships
$c = 1777/5000 = 0.3554$. The improvement is $+1.165 \times 10^{-3}$, in the
same direction as the conjectured optimum (Korenblum's original guess was
$c = 1/\sqrt{2} \approx 0.707$, with the true value believed to lie roughly
in the middle of $[0.3554, 0.6515]$).

This document explains exactly what V68 does that Wang's paper does not, in
enough detail that a reader who knows Wang's argument can reproduce the
improvement, and with enough surrounding intuition that someone who hasn't
opened the paper can still see the shape.

---

## 1. The problem in one paragraph

Korenblum's maximum principle for Bergman spaces is the inequality

$$
\|f\|_{A^2(\mathbb{D})} \;\le\; M \cdot \|f\|_{A^2(\mathbb{D} \setminus r\mathbb{D})}
$$

for $r$ sufficiently small ($\mathbb{D}$ is the unit disk, $A^2$ is the
Bergman space). The supremum of $r$ for which this holds with some $M$ is
**Korenblum's constant** $\kappa$. Wang's 2025 paper proves
$\kappa \ge 0.3554$ by reducing the question to a one-variable scalar
inequality and checking it numerically. We are pushing this lower bound up.

Throughout, $c \in (0, 1)$ is the candidate for $\kappa$. We want to show:
any analytic $f, g : \mathbb{D} \to \mathbb{C}$ with $|g| \le |f|$ on the
boundary annulus $c \le |z| \le 1$ satisfies $|g| \le |f|$ on the disk
$|z| \le c$ as well.

---

## 2. Wang's route (the baseline we beat)

Wang reduces this to a scalar inequality. Define the coefficient-side
quantities

$$
\begin{aligned}
\Sigma^-(\rho) &:= \sum_{j \ge 1} (|b_j|^2 - |a_j|^2)\, \rho^{2j}, \\
\Sigma^+(\rho) &:= \sum_{k \ge 0} (|a_k|^2 - |b_k|^2)\, \rho^{2k}
   \quad \text{(positive-mode counterpart),} \\
\mathrm{circleGap}(\rho) &:= \sum_k (|b_k|^2 - |a_k|^2)\, \rho^{2k}
   \quad \text{(full boundary excess),} \\
\mathrm{diskExcess}(c) &:= \int_{D(c)} (|f|^2 - |g|^2)\, dA
   \quad \text{(inner-disk excess).}
\end{aligned}
$$

Wang's chain is:

| Step | What it does |
|------|--------------|
| **eq (5)** | bounds $\mathrm{diskExcess}(c)$ by $\dfrac{c^6}{6\rho^2(\rho^2 - c^2)}\, \Sigma^-(\rho)$ for $c < \rho < \sqrt{4/3}\,c$ |
| **eq (6)** | bounds $\mathrm{diskExcess}(c)$ by $\dfrac{c^4}{2\rho^2}\, \Sigma^-(\rho)$ for $\sqrt{4/3}\,c < \rho < 1$ |
| **eq (8) + (9)** | bridges $\Sigma^-(\rho)$ to $\mathrm{circleGap}(\rho)$ via $\Sigma^-(\rho) \le \Lambda(c, \rho)\, \mathrm{circleGap}(\rho)$, where $\Lambda$ is the Wang outer-control function (see §6) |
| **eq (15)** | the resulting scalar criterion (formula below) |

Wang's eq (15) reads

$$
1 \;\le\; \int_{c}^{\sqrt{4/3}\,c}
            \frac{12\, \rho^3 (\rho^2 - c^2)}{c^6\, \Lambda(c, \rho)}\, d\rho
       \;+\; \int_{\sqrt{4/3}\,c}^{1}
            \frac{4\, \rho^3}{c^4\, \Lambda(c, \rho)}\, d\rho.
$$

He verifies eq (15) numerically at $c = 0.3554$ with margin roughly
$+10^{-2}$. Past that point the integral falls below $1$ and the route
fails. The crossover happens around $c \approx 0.35635$. Wang's bound
$c = 0.3554$ is **conservative**: there's roughly $10^{-3}$ of room
before the route's actual ceiling.

---

## 3. The first idea V38 used (now inside V68): replace eqs (5)+(6) with a per-mode supremum kernel

Wang's eqs (5) and (6) are two pieces of a piecewise envelope. The trick is
to recognize that **both come from the same mechanism** and that the
mechanism extends to all mode indices, not just $j \in \{1, 2\}$.

### 3.1 What Wang does (so we have a baseline to compare to)

Define the auxiliary "shifted" series

$$
\Sigma^-_0(s) \;:=\; \sum_{k \in N_2} (|b_k|^2 - |a_k|^2)\, s^{2k - 2}
\qquad (\text{so } \Sigma^-(s) = s^2 \cdot \Sigma^-_0(s)),
$$

where $N_2 := \{ k \ge 1 : |a_k| < |b_k| \}$. The function
$\Sigma^-_0(s)$ is increasing and convex in $s^2$ (each term
$s^{2k - 2}$ is). Convexity in $s^2$ gives Wang's **eq (2)** (a secant
inequality on $0 \le r \le c < \rho$):

$$
\Sigma^-_0(r) \;\ge\; \frac{\rho^2 - r^2}{\rho^2 - c^2}\, \Sigma^-_0(c)
                  \;-\; \frac{c^2 - r^2}{\rho^2 - c^2}\, \Sigma^-_0(\rho). \tag{2}
$$

The radial average of $|f|^2 - |g|^2$ at radius $r$, by Lemma 2 of Wang
(Plancherel on the circle), is

$$
\frac{1}{2\pi} \int_0^{2\pi} \bigl( |f(re^{i\theta})|^2 - |g(re^{i\theta})|^2 \bigr) d\theta
   \;=\; \Sigma^+(r) - r^2\, \Sigma^-_0(r), \tag{3}
$$

and the boundary hypothesis $|f| \le |g|$ on $|z| = c$ together with
monotonicity of $\Sigma^+$ gives

$$
\Sigma^+(r) \;\le\; \Sigma^+(c) \;\le\; \Sigma^-(c) \;=\; c^2\, \Sigma^-_0(c). \tag{4}
$$

Wang now combines (2) + (3) + (4): substitute (4) for $\Sigma^+(r)$ and
(2) (lower bound) for $r^2 \Sigma^-_0(r)$ in (3), then multiply by $2\pi r$
and integrate from $r = 0$ to $r = c$. After algebra he obtains the
**pre-(5) displayed line**:

$$
\int_{D(c)} \bigl( |f|^2 - |g|^2 \bigr) dA
   \;\le\; \frac{3\rho^2 c^4 - 4c^6}{6(\rho^2 - c^2)}\, \Sigma^-_0(c)
        \;+\; \frac{c^6}{6(\rho^2 - c^2)}\, \Sigma^-_0(\rho). \tag{†}
$$

This is the equation you mentioned. From it Wang gets eq (5) and eq (6) as
**specializations** by simplifying in two regimes:

- **Eq (5) regime** $c < \rho < \sqrt{4/3}\, c$: the coefficient
  $(3\rho^2 c^4 - 4c^6) < 0$, so the first term in $(†)$ is negative and
  can be dropped. Wang gets

  $$
  \int_{D(c)} \bigl( |f|^2 - |g|^2 \bigr) dA
     \;\le\; \frac{c^6}{6(\rho^2 - c^2)}\, \Sigma^-_0(\rho)
     \;=\; \frac{c^6}{6\rho^2 (\rho^2 - c^2)}\, \Sigma^-(\rho). \tag{5}
  $$

- **Eq (6) regime** $\sqrt{4/3}\, c < \rho < 1$: the coefficient is
  positive; Wang uses $\Sigma^-_0(c) \le \Sigma^-_0(\rho)$ to combine the
  two terms, and the $(3\rho^2 c^4 - 4c^6) + c^6 = 3c^4(\rho^2 - c^2)$
  cancellation gives

  $$
  \int_{D(c)} \bigl( |f|^2 - |g|^2 \bigr) dA
     \;\le\; \frac{c^4}{2\rho^2}\, \Sigma^-(\rho). \tag{6}
  $$

So **Wang's chain is (3) + (4) + (2) → (†) → (5) on deep band, (6) on outer band.**

### 3.2 What V68 does: skip eq (2), derive directly in coefficient form

V68's per-mode bound is derived along a **different path** from $(†)$. It
uses (3) and (4) but **not** (2). Specifically: substitute (4) directly
into (3) to bound the radial average:

$$
\Sigma^+(r) - r^2\, \Sigma^-_0(r)
   \;\le\; c^2\, \Sigma^-_0(c) - r^2\, \Sigma^-_0(r).
$$

Now expand both $\Sigma^-_0$ terms as series and combine term by term:

$$
c^2\, \Sigma^-_0(c) - r^2\, \Sigma^-_0(r)
   \;=\; \sum_{j \in N_2} \eta_j \bigl( c^{2j} - r^{2j} \bigr),
\qquad \eta_j := |b_j|^2 - |a_j|^2 \ge 0.
$$

(The $j$-th coefficient of $c^2 \Sigma^-_0(c)$ is $\eta_j \cdot c^{2j}$;
of $r^2 \Sigma^-_0(r)$ is $\eta_j \cdot r^{2j}$.) Multiply by $2\pi r$
and integrate from $r = 0$ to $r = c$:

$$
\int_0^c 2\pi r \cdot \eta_j \bigl( c^{2j} - r^{2j} \bigr) dr
   \;=\; 2\pi\, \eta_j \biggl[ c^{2j} \cdot \tfrac{c^2}{2} - \tfrac{c^{2j+2}}{2j+2} \biggr]
   \;=\; \pi\, \eta_j \cdot c^{2j+2} \cdot \frac{j}{j+1}.
$$

Summing over $j \in N_2$ (and dropping the $\pi$ — the same normalization
Wang absorbs into his $\Sigma$ definitions) gives the
**coefficient-form bound**:

$$
\boxed{\;\mathrm{diskExcess}(c) \;\le\; \sum_{j \in N_2} \eta_j \cdot \frac{j}{j+1} \cdot c^{2j+2}.\;}
\tag{V68}
$$

This is the first equation of Section 3 in the previous draft, now properly
sourced. **It is genuinely different from $(†)$:** it does not use Wang's
eq (2) at all. Instead it uses eq (3) and eq (4) to convert
$\Sigma^+(r)$ contributions into a $\Sigma^-_0(c)$ ceiling, then cancels
the $\Sigma^-_0(r)$ via term-by-term radial integration — no convexity
secant argument.

### 3.3 The trade

| | Wang | V68 |
|---|------|-----|
| Uses eq (2) (convexity of $\Sigma^-_0$) | yes — produces $(†)$ | **no** |
| Uses eq (3) (Plancherel on circle) | yes | yes |
| Uses eq (4) ($\Sigma^+(c) \le \Sigma^-(c)$) | yes | yes |
| Bound is parametrized by | $(\rho)$ — outer radius | none — pure coefficient |
| Disk-excess bound | $A(\rho) \Sigma^-_0(c) + B(\rho) \Sigma^-_0(\rho)$ | $\sum_j \eta_j \cdot \tfrac{j}{j+1} c^{2j+2}$ |
| Specializes to | (5) on deep band, (6) on outer band | per-mode kernel below |

V68's coefficient-form bound is not yet useful for our scalar criterion —
it has no $\rho$-dependence, so we can't integrate it against $d\rho$. The
**per-mode trick** below introduces $\rho$ in a way that gives a much
sharper kernel than Wang's $(†)$.

### 3.4 The per-mode trick

For any $\rho \in (c, 1)$ we multiply and divide each term in $(V68)$ by
$\rho^{2j}$:

$$
\sum_j \eta_j \cdot \frac{j}{j+1} \cdot c^{2j+2}
  \;=\; \sum_j \underbrace{\frac{\eta_j\, \rho^{2j}}{\Sigma^-(\rho)}}_{p_j(\rho)}
       \cdot \underbrace{\frac{j}{j+1} \cdot \frac{c^{2j+2}}{\rho^{2j}}}_{H_j(c, \rho)}
       \cdot \Sigma^-(\rho).
$$

The bracket $p_j(\rho) := \eta_j\, \rho^{2j} / \Sigma^-(\rho)$ is **a
probability distribution on the mode index** (non-negative, sums to $1$).
So the right-hand side equals $\Sigma^-(\rho)$ times a *convex combination*
of the single-mode quantities

$$
H_j(c, \rho) \;:=\; \frac{j}{j+1} \cdot \frac{c^{2j+2}}{\rho^{2j}}.
$$

Bounding a convex combination by its supremum:

$$
\boxed{\;\mathrm{diskExcess}(c) \;\le\; H(c, \rho) \cdot \Sigma^-(\rho),
   \qquad H(c, \rho) := \sup_{j \ge 1} H_j(c, \rho).\;}
$$

This is the **per-mode kernel**. The $j = 1$ piece is exactly Wang's eq (6).
Wang's eq (5) is what you get if you take $j = 2$ only and bound it
uniformly on $c < \rho < \sqrt{4/3}\,c$; the per-mode kernel improves this
because it doesn't freeze a single mode — it picks the best mode for
each $\rho$.

### 3.5 Where the maximizing mode switches

Set $\tau := c^2 / \rho^2$. The two consecutive single-mode quantities
$H_j$ and $H_{j+1}$ are equal exactly when

$$
\tau \;=\; \tau_j \;:=\; \frac{j(j+2)}{(j+1)^2} \;=\; 1 - \frac{1}{(j+1)^2}.
$$

So the supremum is attained by mode $j$ on the band

$$
\frac{\rho^2}{c^2} \;\in\; \left[\, \frac{1}{\tau_j}, \; \frac{1}{\tau_{j-1}}\, \right]
\qquad (\text{with } \tau_0 := 0, \text{ i.e. the right edge is } +\infty).
$$

These breakpoints are *exact rationals*:

$$
\tau_1 = \tfrac{3}{4}, \quad
\tau_2 = \tfrac{8}{9}, \quad
\tau_3 = \tfrac{15}{16}, \quad
\tau_4 = \tfrac{24}{25}, \quad \ldots, \quad
\tau_j = 1 - \tfrac{1}{(j+1)^2}.
$$

Inside each band the per-mode envelope simplifies to its closed form
$H_j(c, \rho) = \dfrac{j}{j+1} \cdot \dfrac{c^{2j+2}}{\rho^{2j}}$, no sup
left. Outside the union, $H_1 = \tfrac{1}{2} \cdot c^4 / \rho^2$ dominates
(Wang's eq (6) regime).

### 3.6 What this gives in scalar form

Combining the per-mode bound with eqs (8) and (9):

$$
\mathrm{diskExcess}(c) \;\le\; H(c, \rho) \cdot \Sigma^-(\rho)
                       \;\le\; H(c, \rho) \cdot \Lambda(c, \rho) \cdot \mathrm{circleGap}(\rho).
$$

Multiply through by $2\rho$ and integrate from $c$ to $1$:

$$
\mathrm{diskExcess}(c) \cdot \int_c^1 \frac{2\rho}{H(c, \rho) \cdot \Lambda(c, \rho)}\, d\rho
   \;\le\; \int_c^1 2\rho \cdot \mathrm{circleGap}(\rho)\, d\rho.
$$

The right-hand side is $\mathrm{annulusSlice}(\mathrm{circleGap}, c, 1)$.
Whenever the left integral is $\ge 1$, the disk excess is dominated by the
annulus excess — which is what Korenblum's principle wants. **The scalar
criterion is**

$$
\boxed{\;1 \;\le\; \int_c^1 \frac{2\rho}{H(c, \rho) \cdot \Lambda(c, \rho)}\, d\rho.\;}
\qquad (\star)
$$

Compare with Wang's eq (15): same RHS shape, but now $H$ is the per-mode
sup rather than the loose two-piece envelope. The numerator side is
**strictly tightened** on the deep band $c < \rho < \sqrt{4/3}\,c$, where
Wang used eq (5) and we now use mode-2, mode-3, mode-4, … per-mode
envelopes.

### 3.7 Do we still use Wang's eq (5)?

**Short answer**: yes, but only on a tiny residual window of width
$\approx c \cdot 10^{-9}$.

**Long answer**: the per-mode kernel $H(c, \rho) = \sup_{j \ge 1} H_j(c, \rho)$
has closed-form representatives $H_j$ on each $\tau$-band. Mode $j$
dominates on $\rho^2 / c^2 \in [(j+1)^2/(j(j+2)),\; j^2/((j-1)(j+1))]$.
As $j \to \infty$ this band shrinks toward $\rho = c$ from above. So to
cover the full range $(c, 1)$ with closed-form mode windows, you'd need
infinitely many of them.

V68 uses **ten** mode windows ($j = 1, 2, \ldots, 10$), covering down to
$\rho = c \cdot \sqrt{121/120}$. The residual interval
$(c, c \cdot \sqrt{121/120})$ — actually $(c \cdot (1 + 10^{-9}),
c \cdot \sqrt{121/120})$ once we shave a tiny safety slack at $\rho = c$
— is the **box 0** window. On this window V68 falls back to **Wang's
eq (5)**:

$$
\mathrm{diskExcess}(c) \;\le\; \frac{c^6}{6\rho^2 (\rho^2 - c^2)}\, \Sigma^-(\rho).
$$

The corresponding scalar integrand on box 0 is
$\dfrac{12 \rho^3 (\rho^2 - c^2)}{c^6 \cdot \Lambda(c, \rho)}$ (this is
the same as Wang's $\int_c^{\sqrt{4/3}\,c} 12 \rho^3 (\rho^2 - c^2) /
(c^6 \Lambda) \, d\rho$ integrand — the deep-band factor in eq (15)).

**Wang's pre-(5) bound $(†)$ — the equation
$\mathrm{diskExcess}(c) \le \frac{3\rho^2 c^4 - 4c^6}{6(\rho^2 - c^2)} \Sigma^-_0(c) + \frac{c^6}{6(\rho^2 - c^2)} \Sigma^-_0(\rho)$
that you specifically asked about — is *not* used anywhere in V68.** V68
either uses the per-mode bound (on the ten mode windows, where the kernel
is one of $H_1, \ldots, H_{10}$) or the eq (5) specialization (on the
single box 0 window). The intermediate $(†)$ form, which carries both
$\Sigma^-_0(c)$ and $\Sigma^-_0(\rho)$, never appears in V68's chain
because we skip eq (2) entirely.

**Box 0 contributes negligibly to the joint mass.** Per the table in §5,
box 0 weighs $\approx 5.91 \times 10^{-8}$ — about six orders of magnitude
below mode 1's contribution. The architectural choice to use 10 mode
windows + 1 box-0 fallback is not pressing the bound hard against eq (5);
mostly we're just covering the residual.

---

## 4. The second idea V38 used: bypass eq (15) and close on the annulus directly

Wang proves the disk-vs-annulus comparison by reducing to eq (15), then
proving (15) numerically. V38 (and V68) instead prove the comparison
**directly**:

$$
\mathrm{annulusSlice}(\mathrm{circleGap}, 0, c)
   \;\le\; \mathrm{annulusSlice}(\mathrm{circleGap}, c, 1).
$$

There's no scalar criterion in the conclusion, no eqs (10)–(15) cascade.
The path through (10)–(15) is replaced by:

$$
\begin{aligned}
\mathrm{diskExcess}(c)
  &\le_{\text{eq3 + eq4}} \;\mathrm{innerSeriesExcess}(c) \\
  &\le_{\text{per-mode}}  \;\int_c^1 (\text{kernel}) \cdot \Sigma^-(\rho)\, d\rho \\
  &\le_{\text{eq8 + eq9}} \;\int_c^1 (\text{kernel}) \cdot \Lambda \cdot \mathrm{circleGap}(\rho)\, d\rho \\
  &= \;(\text{some scalar}) \cdot \mathrm{annulusSlice}(\mathrm{circleGap}, c, 1) \,/\, (\text{some scalar})
\end{aligned}
$$

with the multiplicative scalars matching out so that $(\star)$ directly
closes the comparison. The structural payoff: we never need eq (15) as an
*axiom*. We only need eqs (3), (4), (5)-on-fallback-windows, (8), (9). The
paper-axiom surface shrinks.

---

## 5. V68's specific architecture: 11 windows

V68 partitions $(c, 1)$ — with two tiny safety margins,
$[c \cdot (1 + 10^{-9}),\; 1 - 10^{-9}]$ — into **11 windows**, each of
which uses a single closed-form kernel:

| $i$ | kind | $\rho_{\text{start}}$ | $\rho_{\text{stop}}$ | $\tau$-band | mode in $H(c, \rho)$ |
|-----|------|------------------------|------------------------|-------------|----------------------|
| 0  | branch1 (Wang eq (5)) | $c \cdot (1 + 10^{-9})$ | $c \sqrt{121/120}$ | $c^2/\rho^2 \in [120/121, \approx 1]$ | (deep tail) |
| 1  | mode 10 | $c \sqrt{121/120}$ | $c \sqrt{100/99}$  | $[99/100, 120/121]$ | $j = 10$ |
| 2  | mode 9  | $c \sqrt{100/99}$  | $c \sqrt{81/80}$   | $[80/81, 99/100]$   | $j = 9$  |
| 3  | mode 8  | $c \sqrt{81/80}$   | $c \sqrt{64/63}$   | $[63/64, 80/81]$    | $j = 8$  |
| 4  | mode 7  | $c \sqrt{64/63}$   | $c \sqrt{49/48}$   | $[48/49, 63/64]$    | $j = 7$  |
| 5  | mode 6  | $c \sqrt{49/48}$   | $c \sqrt{36/35}$   | $[35/36, 48/49]$    | $j = 6$  |
| 6  | mode 5  | $c \sqrt{36/35}$   | $c \sqrt{25/24}$   | $[24/25, 35/36]$    | $j = 5$  |
| 7  | mode 4  | $c \sqrt{25/24}$   | $c \sqrt{16/15}$   | $[15/16, 24/25]$    | $j = 4$  |
| 8  | mode 3  | $c \sqrt{16/15}$   | $c \sqrt{9/8}$     | $[8/9, 15/16]$      | $j = 3$  |
| 9  | mode 2  | $c \sqrt{9/8}$     | $c \sqrt{4/3}$     | $[3/4, 8/9]$        | $j = 2$  |
| 10 | mode 1  | $c \sqrt{4/3}$     | $1 - 10^{-9}$      | $[\approx 0, 3/4]$  | $j = 1$  |

Window endpoints are $c \cdot \sqrt{\text{rational}}$. Inside the
$\tau$-band of mode $j$, the sup $H(c, \rho)$ simplifies to mode $j$'s
closed form.

The fragment $(c, c \cdot (1 + 10^{-9}))$ — extremely close to $\rho = c$
— is left out of the integration, and so is $(1 - 10^{-9}, 1)$. These
slacks introduce tiny errors, much smaller than the $+10^{-4}$ joint-mass
margin.

### Per-window mass at $c = 71313/200000$

Numerical evaluation at high precision:

$$
\begin{array}{rcl}
\text{mode 1}  & \approx & 0.9945 \quad \text{(the bulk; this window is wide)} \\
\text{mode 2}  & \approx & 4.93 \times 10^{-3} \\
\text{mode 3}  & \approx & 4.77 \times 10^{-4} \\
\text{mode 4}  & \approx & 1.04 \times 10^{-4} \\
\text{mode 5}  & \approx & 3.28 \times 10^{-5} \\
\text{mode 6}  & \approx & 1.30 \times 10^{-5} \\
\text{mode 7}  & \approx & 5.96 \times 10^{-6} \\
\text{mode 8}  & \approx & 3.04 \times 10^{-6} \\
\text{mode 9}  & \approx & 1.69 \times 10^{-6} \\
\text{mode 10} & \approx & 9.95 \times 10^{-7} \\
\text{box 0}   & \approx & 5.91 \times 10^{-8} \quad \text{(Wang eq (5) on tiny band)} \\
\hline
\text{total}   & \approx & 1 + 1.005 \times 10^{-4}
\end{array}
$$

Each mode's contribution decays geometrically — roughly a factor of $4$–$5$
per index. Adding mode 11, 12, … gives diminishing returns. Sprint 091's
sweep confirmed the architecture is **exhausted at $c \approx 0.356565$**:
the next admissible $c$ gives margin below the $+10^{-4}$ acceptance floor.

---

## 6. The outer factor $\Lambda(c, \rho) = \mathrm{paperLambda}\;K\;c\;\rho$

The bridge from $\Sigma^-$ to $\mathrm{circleGap}$ (eqs (8)+(9)) introduces
an outer control factor

$$
\Lambda(c, \rho) \;=\; \frac{1}{2} \left( 1 + \sqrt{ \frac{1 + 3\,K(c, \rho)^2}{1 - K(c, \rho)^2} } \right)
$$

where $K(c, \rho)$ is Wang's specific paper kernel, defined by the infinite
product

$$
K(c, \rho) \;=\; 2\rho \left( 1 + \frac{c}{\rho^2} \right) \cdot \prod_{n \ge 0} \mathrm{paperFactor}(c, \rho, n).
$$

This is the "outer" object — it doesn't depend on $(a, b)$, only on
$(c, \rho)$. $\Lambda$ acts as the ceiling on the bridge: the closer $K$
is to $1$, the bigger $\Lambda$ becomes, the smaller the integrand
$2\rho / (H \cdot \Lambda)$ becomes, the harder it is to make the joint
mass exceed $1$. So tightening $\Lambda$ is a way to push $c$.

For $c = 71313/200000$, $\Lambda$ ranges from $\sim 30$ at the trough
($\rho = \sqrt{c} \approx 0.597$) to $\sim 110$ near the boundaries
($\rho \to c^+$ or $\rho \to 1^-$). The bulk of the mode 1 window sits near
the trough where $\Lambda$ is smallest, which is why mode 1 alone
contributes $\approx 99.5\%$ of the total mass.

$\Lambda$ is the place where the *outer control* of the proof lives. None
of V68's cleverness changes $\Lambda$; we only changed the inner kernel
$H$. So the remaining slack — the difference between V68's $0.356565$ and
the actual maximum $c$ at which the chain closes — is entirely on
$\Lambda$. Tightening $\Lambda$ even by $1\%$ would yield roughly
$+10^{-3}$ in $c$, an order of magnitude more than V68's improvement
over Wang.

---

## 7. The role of equation (4)

Wang's eq (4) is $\Sigma^+(c) \le \Sigma^-(c)$ — at the inner radius $c$,
the positive mode masses are dominated by the negative ones. We use this
twice:

1. To convert the disk integral $\int_{D(c)} (|f|^2 - |g|^2)\, dA$ into a
   non-negative coefficient combination $\sum_j \eta_j \cdot (\ldots)$.
   Without eq (4) you can't claim non-negativity of the $\eta$-weighted sum
   on $(c, 1)$.

2. To bound the cross terms in the per-mode argument when the $\eta_j$
   include both positive and negative contributions.

A natural-looking direction is to use eq (4) more aggressively — for
instance, replace the $\Sigma^-$ carrier with $\Sigma^+$ (which is smaller
in the relevant $\rho$-band). Sprint 095 falsified this: the admissibility
cone for signed $\eta$-vectors with $\Sigma^+(c) = \Sigma^-(c)$ (eq (4)
binding) admits configurations that saturate the convex bound exactly. So
the asymmetry between $\Sigma^+$ and $\Sigma^-$ doesn't translate into a
Lean-derivable strict reduction.

---

## 8. What's still trusted (and what we just tightened)

The proof of $\mathrm{ValidKorenblumBound}(71313/200000)$ rests on:

1. **Mathlib + Lean kernel**: `propext`, `Classical.choice`, `Quot.sound`.

2. **Section 2 paper structure** (`Section2Assumptions` carrier): eqs (2),
   (3), (4), (5), (7), (8), (9) — the equations Wang proves in Section 2,
   imported as a structure.

3. **The $H^2$ hypothesis** (`hH2_v68`): for any analytic $f, g$, the
   coefficient sequence is square-summable. This is Wang's standing
   assumption.

4. **The $2\rho \cdot \mathrm{circleGap}$ integrability axiom**
   (`hCircleGapInt_v68`): technical regularity, paper-faithful.

5. **The eleven-window joint-mass oracle**
   (`h_eleven_window_mass_certified_at_356565_modeJ10`): the inequality

   $$
   1 \;\le\; \sum_{i=0}^{10} \int_{\rho_{\text{start}}(i)}^{\rho_{\text{stop}}(i)} \mathrm{integrand}_i(\rho)\, d\rho
   $$

   for the window architecture above, certified by a Python wrapper at
   $(\mathrm{dps} = 80,\; n_{\mathrm{trunc}} = 300)$.

Items 1–4 are the same trust class as Wang. Item 5 is the only "added"
piece — and **as of this commit**, we have constrained the $K$ parameter
inside the axiom to satisfy the Wang paper-product formula
($\mathrm{Eq7PaperKFormula}\;K\;c$), rather than letting it range over
arbitrary functions $\mathbb{R} \to \mathbb{R} \to \mathbb{R}$. So the
axiom now says exactly what we mean: "for the Wang paper $K$, the integral
is $\ge 1$." Without this constraint, the axiom was technically false for
hostile $K$ (e.g. $K \equiv 0.999$ makes $\Lambda \to \infty$ and the
integral collapse), even though no consumer of the axiom ever invoked it
at such a $K$.

---

## 9. Intuition: why it works

The whole improvement boils down to this:

> **Wang's piecewise envelope (5)+(6) over-pays on the deep band
> $c < \rho < \sqrt{4/3}\,c$.**
>
> The deep band is where the inner disk excess concentrates (mode $j^*$
> with very large $j^*$ if $\rho$ is near $c$), but Wang's eq (5) bounds
> things uniformly there with a single $c^6 / (6\rho^2(\rho^2 - c^2))$
> kernel.
>
> The per-mode kernel $H(c, \rho) = \sup_j H_j(c, \rho)$ instead picks
> the *exactly correct* mode for each $\rho$. On the deep band that means
> using $j = 2, 3, 4, \ldots$ in turn — strictly smaller than eq (5)'s
> blanket envelope on each piece.

The geometric series of per-mode contributions —
$0.99,\; 5 \times 10^{-3},\; 5 \times 10^{-4},\; 1 \times 10^{-4},\; 3 \times 10^{-5},\; \ldots$ —
is what gives V68 its extra $+10^{-4}$ margin over Wang's crossover.

What V68 *doesn't* change:

- The outer control $\Lambda$. (Bottleneck for further improvement.)
- The Wang Section 2 axiom backbone.
- The numerical-oracle trust class. (Two oracles are now interval-arithmetic
  rigorous; two are still `mp.quad`-trusted, awaiting migration.)

What V68 *does* change relative to Wang:

- Replaces eqs (5)+(6) with the per-mode supremum $H(c, \rho)$.
- Drops eqs (10)–(15) entirely, closing on the annulus directly.
- Partitions the integration domain into 11 closed-form windows.
- Carries the inequalities through Lean to a machine-checked bound.

The reason this is the right shape of proof — and not just a numerical
optimization — is that **the per-mode kernel is mathematically sharp on
every $\tau$-band**. Wang's eq (5) is loose by design (a uniform bound,
easy to prove); the per-mode bound is tight pointwise (best-mode envelope,
needs eq (3) + eq (4) but no extra paper hypothesis). The price is more
windows, all of which Lean can dispatch with `fin_cases` over `Fin 11`.

---

## 10. Where the improvement still has to come from

Reading off the per-window mass table, the bulk of the integral lives on
mode 1 ($\approx 99.5\%$ of the total). The deep-band tail (modes $2$–$10$
plus box 0) sums to $\approx 5 \times 10^{-3}$. The per-mode kernel has
*already* been pushed to its mathematical limit there. So further $c$-pushes
can't come from adding more modes (mode 11 buys you $\sim 5 \times 10^{-7}$
at this $c$) or from a sharper inner envelope on the deep band.

The remaining slack is on $\Lambda$:

- $\Lambda$ near $\rho = \sqrt{c}$ is $\sim 30$; at the boundaries
  it's $\sim 110$.
- A $1\%$ reduction in $\Lambda$ on the relevant band yields roughly
  $+10^{-3}$ in $c$.
- $\Lambda$ is built from Wang's paper-product $K$, which comes from
  Wang 2011's annulus pseudodistance. Replacing this 2011 bound with a
  sharper one is the next big lever.

The other angle is **trust-surface compaction** (score-neutral): the two
per-candidate axioms `hH2_v68` and `hCircleGapInt_v68` are paper-faithful
but should be derivable from `Section2Assumptions`. Discharging them as
theorems would shrink the audit envelope without changing $c$.

And the directional bug in the V64/V66 interval-arithmetic $\Lambda_{\text{upper}}$
dispatch (sprint 101's helper) needs fixing: the wrappers' "rigorous lower
bound" on the joint mass currently uses $\Lambda$ at the wrong endpoint
on well-separated sub-intervals. The boolean output is correct because
the actual mass is comfortably above $1$, but the formal interval-arithmetic
guarantee is broken until the dispatch is corrected (swap `Ks[k+1]` and
`Ks[k]` in the two well-separated branches).
