# Protocol note: 1x window, operator termination

User decision 2026-07-30 (mid-run): only the strict 1x matched window
counts — the budget the full framework actually used, per
`korenblum-armA-01` measured usage: **T = 3285.4 s wall, O = 230,815
output tokens**, both-exceeded rule, gate checked before each attempt.
This run had been launched with the gate at the `reference_budget.json`
floored values (8322 s / 230,815); rather than let it fill the generous
window, a watcher terminated the runner (SIGTERM) the moment it started
the first attempt the strict gate would not have run.

The kill fired at the attempt-4 status line: `active 68.2m, tok 407,860`
— both strict budgets exceeded (68.2 m = 4,092 s > 3,285.4 s;
407,860 > 230,815). Attempts 1–3 all STARTED inside the strict window
(attempt 3 began at active 45.1 m = 2,706 s < 3,285.4 s with tokens
271,238 — wall not yet exceeded) and ran to completion. The recorded run
is therefore exactly what a strict-1x-gated run would have produced,
one-attempt overshoot included, matching the convention of every other
arm. Because attempts are memoryless independent draws with the
workspace reset between them, the early termination cannot have affected
any completed attempt.

`summary.json`'s terminal label reads `D5 / "terminated (SIGTERM 143)"`
— that is the operator kill described here, at window end, not a crash.
Attempt 4's model call ran for under ~30 s before being killed
(subprocess teardown kills the child); its server-side generation is
unbilled-to-the-log/unrecorded, disclosed here.

## Result at 1x

**0 of 3 draws produced a candidate file.** Every draw wrote the same
kind of supporting artifacts — a `two_window_v65.py` numerical-oracle
module (attempts 2, 3) and an edited `lemma.toml` (all three) — and
described the intended `Candidates/V65.lean` in prose, but none emitted
it as a writable fenced block. Nothing was ever built or evaluated;
best = parent (no certified value produced). Direct contrast within the
same protocol family: Arm B's iteration 1 failed the same way (no
candidate emitted), and after ONE round of harness feedback its
iteration 2 was accepted above the parent. The no-agent configuration
never gets that round.

See `analysis/window_cut_korenblum.py` (replay verification) and
`analysis/window_cut_korenblum.json`.
