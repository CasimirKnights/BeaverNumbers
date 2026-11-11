# BeaverStructural — exact step counts of four busy-beaver machines, formalized

**Construction and claims: C. Forrester.**\
Formalized in Lean 4 with Mathlib under her direction.\
Copyright © 2026 C. Forrester. Licensed under the [PolyForm Small Business License 1.0.0](LICENSE.md); uses outside its terms require a separate licence from the copyright holder.

## 1. What this is

Three of the four machines treated here hold the busy-beaver record of their class today: BB(6), BB(7) and BB(3,4), as listed on the [BusyBeaverWiki Champions page](https://wiki.bbchallenge.org/wiki/Champions) on 10 November 2026. The fourth held the BB(7) record until October 2026. Each record is published as a bound: more than 10↑↑10↑↑10↑↑8 steps for BB(6), more than 3↑²⁰3 for BB(7), more than 2↑¹⁵5 for BB(3,4). This repository replaces each bound by the number: the exact step count, proved in Lean to be the step of the first halt, with its last 200 decimal digits. **To our knowledge these are the largest numbers ever proved to be the exact running time of a computation.**

A bound survives small errors in the analysis that produced it. An exact step count does not: it is right only if every rule, every configuration and every single-step cost in the analysis is right.

Each machine halts after a number of steps far too large to write down, so the count is given as a closed recursion. For each machine the repository contains:

1. a **Lean 4 proof** that, started on the blank tape, the machine's first halt occurs at exactly the step count τ;
2. a **Lean 4 proof** of the last 200 decimal digits of τ, and of the score σ where the score is proved;
3. a **standalone Python program** (standard library only) that rebuilds the machine from its transition rows, checks every rule used on the machine itself, and recomputes the digits with its own code.

In the table, `BB6.exactN`, `BB7.tau`, `BB7b.tau` and `BB34.tau` are the names of the step counts in the Lean sources; their definitions are the closed forms of section 3. The step counts include the halting transition.

| Machine | Record status, 10 Nov 2026 | Rows | First halt proved | Halted tape proved | τ mod 10²⁰⁰ | σ mod 10²⁰⁰ |
|---|---|---|---|---|---|---|
| BB(6) | current record | `1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE` | at `BB6.exactN` | not included | proved | not included |
| BB(7), earlier | record until October 2026 | `1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_0RG0RF` | at `BB7.tau` | σ ones | proved | proved |
| BB(7), October 2026 | current record | `1RB0RG_1RC1RB_0RD1RZ_0LE0LD_0LF1LE_1RA1LF_1LC0RB` | at `BB7b.tau` | σ ones | proved | proved |
| BB(3,4) | current record | `1RB3LB1RZ2RA_2LC3RB1LC2RA_3RB1LB3LC2RC` | at `BB34.tau` | σ nonblank cells | proved | proved |

### What is new here

- **The standing records, as numbers.** The best known lower bounds for S(6), S(7) and S(3,4), and for Σ(7) and Σ(3,4), are now exact integers with 200 known digits.
- **An exact step count for each machine, as a theorem.** Not a bound: the first halt from the blank tape is at exactly τ, and at no earlier step.
- **Its trailing digits, as a theorem.** The last 200 decimal digits of each τ, and of the score for three of the machines, are derived inside Lean by evaluating a function proved equal to the residue. No digit is taken from an external computation.
- **Two independent routes that agree.** A standalone program per machine, sharing no code with the proofs, rebuilds the machine from its rows and arrives at the same 200 digits.
- **Two machines of different classes on one arithmetic.** The BB(3,4) machine and the earlier BB(7) machine are driven by the same hierarchy of maps once one parameter is doubled; they differ only in the cost of a step (section 3).
- **Two corrections to the published analysis** of the earlier BB(7) machine, forced by exactness (section 5).

**The state of the published record.** As of 10 November 2026 we found no published exact step count, and no published trailing digit of a step count, for any of these four machines, other than the BB(6) result of this project's first release ([Orbital](https://github.com/CasimirKnights/Orbital), DOI 10.5281/zenodo.23182375). The sources for each machine give the running time as a bound or an approximation; where an exact closed form is published, it is for the score. Section 5 lists what was consulted. To our knowledge these are the first formally proved exact step counts of machines whose running time cannot be written down, and the largest numbers proved to be the exact running time of any computation; the exact step count proved for BB(5), 47,176,870, is of a run short enough to simulate. Larger numbers have been named, and larger machine classes have champions with larger bounds; none of those is an exact, proved count of steps.

**What is and is not claimed about the busy beaver function.** Nothing here proves that any of these machines is the champion of its class; that is a statement about every other machine of the class. What is proved is exact and conditional: if one of the three current record holders attains the maximum number of steps for its class, then τ as proved here is S(6), S(7) or S(3,4) itself, and if it attains the maximum score, σ as proved here is Σ(7) or Σ(3,4) itself, in each case with 200 of its digits already known.

## 2. The statements and the digits

[`BeaverStructural/Statements.lean`](BeaverStructural/Statements.lean) holds one theorem per machine, each a conjunction of theorems proved in that machine's own files:

| Theorem | Says |
|---|---|
| `bb6_first_stop_and_digits` | `FirstHit BB6.table BB6.exactN BB6.blank` and `BB6.exactN % 10^200 =` the literal |
| `bb7_first_stop_and_digits` | the state after `BB7.tau` steps is the halted state and after no fewer; the number of cells holding 1 is `BB7.sigma`; both residues |
| `bb7b_first_stop_and_digits` | the same for the October machine, the halted tape given as a finite two-sided list holding `BB7b.sigma` ones |
| `bb34_first_stop_and_digits` | the same for BB(3,4), the halted tape holding `BB34.sigma` nonblank cells |

Each depends on `[propext, Classical.choice, Quot.sound]` and on nothing else; the sources contain no `sorry`, no `native_decide` and no `axiom`.

**What must be read to trust a statement.** The machine model is [`Model.lean`](BeaverStructural/Model.lean): a tape `ℤ → Bool`, a head, a state that is `none` once halted, one row applied per step. BB(3,4) has its own four-symbol copy at the top of [`BB34/Machine.lean`](BeaverStructural/BB34/Machine.lean). Each machine's `table` is its rows, in `BB6/Machine.lean`, `BB7/Machine.lean`, `BB7b/Machine.lean`, `BB34/Machine.lean`. The step counts are defined in `BB6/Clock.lean`, `BB7/Defs.lean`, `BB7b/Numbers.lean`, `BB34/Numbers.lean`. Everything else is proof and is checked by the Lean kernel.

### The digits

BB(6), τ mod 10²⁰⁰:

```
76570746659301988709841908579693588126553130252541952029830709923036761639105158393970989783657593312221169567595808757858120886828361418774062055009809875683743490992412785802436230729390191074641105
```

BB(7), earlier machine, τ mod 10²⁰⁰ and σ mod 10²⁰⁰:

```
10442722074196456773707640344163283107608038313650144315814389328319446910761894323931867085376411580682445199494700647587803129645200041753088294078160945237875590633254874041202959286480341950034543
12897809075781567187510870723274308261486089663242393885290451904435315345520726377730964080560052153267706661570675282053969566167812736363848524885873710436586090617800479560014295845226060298846230
```

BB(7), machine of October 2026, τ mod 10²⁰⁰ and σ mod 10²⁰⁰:

```
73428777837952993932558769478822530186098574054291312567353699908846487228941494006822946829647472038108444008989374401252315208961679286188413869309976773701212302531357930057713528229743458345356287
38146269853501365410645620969226103723067399102116242894037345432144851507307992961694105209402589140584375632186552499340414462252588919319066067278807809867872153028729243567821670670118939603706013
```

BB(3,4), τ mod 10²⁰⁰ and σ mod 10²⁰⁰ (σ printed to 200 places, leading zero included):

```
66472556816678537004442489651861394493871801061408453005565013967672312146603676135321084747442383169401224698960399961853900728282682573633487960377917913767778012157999678639877282968144064457604929
04299269691927189062503623574424769420495363221080797961763483968145105115173575459243654693520017384422568887190225094017989855389270912121282841628624570145528696872600159853338098615075353432948750
```

## 3. The closed forms

**BB(3,4).** With B(k, n, a) = 0^∞ 3^(a+1) 2^k A> 1^n (a is twice Ligocki's m), g₀(x) = 2x + 4 and g_(j+1)(x) = g_j^(x+2)(0):

```
W1(n, a)      = n (4a + 4n + 5)                                        n units at k = 1
T_0(n, a)     = Σ_(i<n) C1(a_i),   C1(a) = 4a² + 26a + 37,   a_(i+1) = g_0(a_i)
T_(j+1)(n, a) = Σ_(i<n) [C2(a_i, j) + T_j(a_i + 2, 0)],   C2(a, j) = (2j+7)a + 4j + 15,   a_(i+1) = g_(j+1)(a_i)
τ = 241 + T_14(3, 0) + 1          σ = g_14^3(0) + 18
```

**BB(7), earlier machine.** The same hierarchy g with C1(a) = 36a² + 318a + 590, C2(a, k) = (24 + 8k)(3a + 1) + 226 + 48k, CH(a, k) = (2 + 8k)(3a + 1) + 27 + 21k, A₀ = 4, A_(j+1) = g_j(A_j):

```
τ = 8574 + Σ_(j<12) T_j(1, A_j) + CH(A_12, 12)          σ = 3·A_12 + 34
```

**One hierarchy, two machines.** In Ligocki's parameter m the BB(3,4) machine iterates g′₀(m) = m + 1, g′_(k+1)(m) = g′_k^(2m+2)(0). Writing a = 2m gives 2·g′_(k+1)(m) = g_k(2m): the same hierarchy g as the earlier BB(7) machine, two levels apart. The two clocks then have one recursion and differ only in the polynomials C1 and C2. Every residue of an iterate is therefore common to both, and the BB(3,4) digit proof imports the BB(7) proof's tower lemmas unchanged.

**BB(7), October 2026.** With V₀(x) = 3x + 3, s₀ = 1, s_(k+1) = V_k(s_k), V_(k+1)(x) = V_k^(3x+2−k)(s_k):

```
T_0(n, a)     = Σ_(i<n) [12x_i² + 66x_i + 58],   x_i = V_0^i(a)
T_(k+1)(n, a) = Σ_(i<n) [cB(x_i, k+1) + P_k + T_k(3x_i + 2 − k, s_k)],   x_i = V_(k+1)^i(a),   P_(k+1) = P_k + T_k(1, s_k)
cB(a, k)      = 12a² + 18a + 8(k+2)(3a − k) + 4k² + 40k + 58
Acc_0 = 8,  Acc_(i+1) = V_(i+1)(Acc_i)
τ = 3959 + Σ_(i<19) T_(i+1)(1, Acc_i) + [48·Acc_19² + 198·Acc_19 − 456]          σ = 6·Acc_19 + 7
```

**BB(6).** `BB6.exactN = clockFor seed stage1 stage2` (`BB6/Clock.lean`), the clock of three phases of a binary counter. This part is the proof of the first release, carried here without that release's other content.

## 4. How to verify

### 4.1 The Lean proofs

Requires [elan](https://github.com/leanprover/elan). The toolchain (`leanprover/lean4:v4.30.0-rc1`) and the Mathlib revision are pinned in `lean-toolchain` and `lake-manifest.json`.

```
lake exe cache get      # fetch the prebuilt Mathlib for the pinned revision
lake build
```

The build succeeds with `Build completed successfully`. Its output lists the axioms of the principal theorems; the four of `Statements.lean` must read `[propext, Classical.choice, Quot.sound]`. To confirm that nothing is assumed:

```
grep -rnw "sorry\|native_decide" BeaverStructural --include="*.lean"     # no output
grep -rn  "^axiom " BeaverStructural --include="*.lean"                  # no output
```

The build made for this release completed with 3530 jobs; its result is recorded in `MANIFEST.txt`.

Some of the Lean files were written by programs. That does not affect the check: every file, however it was produced, is verified by the kernel in the build above.

### 4.2 The standalone programs

Python 3, standard library only, no dependence on Lean or on any other file here:

```
python3 verify/verify_bb6_champion_digits.py
python3 verify/verify_bb7_champion_digits.py
python3 verify/verify_bb7_2026_champion_digits.py
python3 verify/verify_bb34_champion_digits.py
```

The last three accept `--rows <transition rows>` and `--digits <D>`. Each builds the machine from the rows and reports, before printing the digits:

- the blank tape at the entry step is the stated configuration;
- every rule lands on the predicted configuration at exactly the predicted step count, on a grid of small instances and under more than one right context;
- the halting rule halts at its predicted step with the predicted number of marks;
- the clock agrees with whole runs of the machine wherever the run fits in memory;
- the residue computation agrees with exact integers wherever the integer can be stored (the largest has more than 131,000 bits);
- the digits computed at 10¹⁰, 10⁵⁰ and 10¹⁰⁰ are the reductions of those computed at 10²⁰⁰ (each uses a different chain of moduli).

The outputs of the runs made for this release are the `.log` files beside the programs. A program exits non-zero if any check fails.

### 4.3 What each route does and does not establish

The Lean proofs establish the statements of section 2 for the machines as defined in the `table` of each `Machine.lean`; a reader checks that those tables are the rows. The Python programs are an independent computation with separately written code; they test the rules on finitely many instances and do not prove them. Agreement of the two on all 200 digits is the cross-check between them.

## 5. Relation to earlier work

What each published source gives, as consulted on 10 November 2026. The record status of each machine and the bounds quoted in section 1 are those of the [BusyBeaverWiki Champions page](https://wiki.bbchallenge.org/wiki/Champions) on that date, which lists the BB(6), October 2026 BB(7) and BB(3,4) machines as the champions of their classes, the BB(7) entry as claimed and its analysis as not yet verified.

- **BB(3,4).** Machine: P. Kropitz, 2024. Rules and the score as a closed form: S. Ligocki, ["BB(3, 4) > Ack(14)"](https://www.sligocki.com/2024/05/22/bb-3-4-a14.html), 22 May 2024. Neither that post nor the [BusyBeaverWiki page](https://wiki.bbchallenge.org/wiki/BB(3,4)) gives a step count; the running time appears as a bound. The step count and its digits are derived here.
- **BB(7), earlier machine.** Machine: P. Kropitz, 10 May 2025. Rules: S. Ligocki's analysis of 13 May 2025 on the [BusyBeaverWiki page of the machine](https://wiki.bbchallenge.org/wiki/1RB0RA_1LC1LF_1RD0LB_1RA1LE_1RZ0LC_1RG1LD_0RG0RF), which gives the running time as a bound and the score as a formula. Two statements of that page do not hold on the machine. The stated start, B(2; 1¹²) at step 8,178, does not occur: the configuration with twelve 1-blocks first occurs as B(4; 1¹²) at step 8,574. And the halting rule leaves 3a + 2k + 10 ones, not 3a + 2k + 9. With both, the score is σ = 3·A₁₂ + 34 with A₀ = 4, where the page has 3·a₁₂ + 33 from a₀ = 2. The page's lower bound is unaffected. The rules, the clock and the digits for this machine were derived here from its rows.
- **BB(7), October 2026.** Machine, configuration family, rules and a Coq proof of halting and of the score: J. Ketchersid, October 2026 ([`jeff87654/busy-beaver`](https://github.com/jeff87654/busy-beaver)). That repository gives no step count for the machine. The step count, the costs of the rules as formulas, and the digits are derived here; no text of that repository is reproduced.
- **BB(6).** Machine and analysis: mxdys, 2025; the [BusyBeaverWiki page of the machine](https://wiki.bbchallenge.org/wiki/1RB1RA_1RC1RZ_1LD0RF_1RA0LE_0LD1RC_1RA0RE) gives the time and score as approximations and bounds and links a Rocq proof. The exact step count and its digits are those of this project's first release.

Nearby formal work, for comparison: the bbchallenge Collaboration's Coq proof that S(5) = 47,176,870 ([arXiv:2509.12337](https://arxiv.org/abs/2509.12337)) is an exact step count of a run short enough to simulate; halting proofs of other six-state machines in Lean and Coq establish that a machine halts, without a step count. A web search for published trailing digits of any tower-sized halting time returned none. Discussion on the bbchallenge Discord is not indexed and was not consulted.

## 6. Layout

```
BeaverStructural/Model.lean          the machine model
BeaverStructural/Statements.lean     one theorem per machine
BeaverStructural/BB6/                BB(6): machine, counter execution, clock, first hit, residue certificate
BeaverStructural/BB7/                earlier BB(7): machine, rules, first halt, score, residues, digits
BeaverStructural/BB7b/               October 2026 BB(7): machine, rules, first halt, residues, digits
BeaverStructural/BB34/               BB(3,4): machine, rules, first halt, digits
verify/                              the four standalone programs and their logs
```
