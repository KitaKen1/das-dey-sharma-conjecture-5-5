# A Lean proof of Das–Dey–Sharma Conjecture 5.5

This repository formalizes the affirmative answer to **Conjecture 5.5 of Das, Dey and Sharma**,
registered in
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/8323e878b83fcd7f4a448256069352a265460d75/FormalConjectures/Arxiv/2604.08040/Conjecture5_5.lean)
as `Arxiv.«2604.08040».solvable_of_cyc_lt`. For a finite group `G` put

```text
cyc(G)  = number of cyclic subgroups of G, including the trivial subgroup,
ω(|G|)  = number of distinct prime divisors of |G|.
```

The theorem is that, for every finite group `G`,

```text
cyc(G) < 2 ^ (ω(|G|) + 2)   →   G is solvable.
```

The bound is sharp: $`A_5`$ has $`1+15+10+6=32=2^{3+2}`$ cyclic subgroups.

**Try it in Lean4Web:**
[open the standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fdas-dey-sharma-conjecture-5-5%2Frefs%2Fheads%2Fmain%2Flean4web%2FConjecture55FTOnly.lean)
(select "Latest Mathlib" with Lean v4.35.0-rc3). This file takes the Feit–Thompson odd order
theorem as a hypothesis, stated exactly as the Lean Eval problem `feit_thompson`; see the
[Appendix](#appendix-the-lean4web-target).

Das, Dey and Sharma stated the conjecture in the first version of
[arXiv:2604.08040](https://arxiv.org/abs/2604.08040v1) (April 2026). Das and Sharma showed that
a nonsolvable group with fewer than 50 cyclic subgroups is $`A_5`$ or $`\mathrm{SL}(2,5)`$
([arXiv:2604.23664](https://arxiv.org/abs/2604.23664)), which settles the conjecture in that
range. The second version of arXiv:2604.08040 (September 2026, with C. Galindo) proves the
conjecture in general as Theorem 7.1, through a lower bound for every finite nonabelian simple
group obtained family by family from the classification of finite simple groups. The Lean proofs
here do not use the classification: the `lean/` development uses the Feit–Thompson and
Gorenstein–Walter theorems, and the Lean4Web file uses only the Feit–Thompson theorem.

## Formal Conjectures target

The file `lean/Conjecture55FC.lean` imports the Formal Conjectures statement file at revision
`8323e878...` and proves the exact proposition with the answer `True`:

```lean
theorem solvable_of_cyc_lt_solved :
    answer(True) ↔ ∀ (G : Type) [Group G] [Fintype G],
      cyc G < 2 ^ (numPrimeFactors G + 2) → Group.IsSolvable G :=
  Conjecture55Lean4Web.solvable_of_cyc_lt
```

Here `cyc G = Nat.card {H : Subgroup G // IsCyclic H}` and
`numPrimeFactors G = (Fintype.card G).primeFactors.card` are the definitions imported from
Formal Conjectures. The proof does not use the upstream placeholder theorem as a premise.

## Mathematical explanation (AI generated)

This section follows the Lean4Web file, which uses only the odd order theorem. The differences
in `lean/` are noted at the end.

**Notation.** Write $`c(G)`$ for the number of cyclic subgroups, $`\omega(n)`$ for the number of
distinct prime divisors of $`n`$ and $`\tau(n)`$ for its number of divisors. Write
$`|G|=2^a m`$ with $`m`$ odd, and let $`P`$ be a Sylow 2-subgroup. When $`a\ge1`$ the threshold
is

```math
2^{\omega(|G|)+2}=8\cdot2^{\omega(m)}\le8\,\tau(m).
```

### 0. A least counterexample has no solvable normal subgroup

Let $`G`$ be a nonsolvable group of least order with $`c(G)\lt2^{\omega(|G|)+2}`$, and let
$`N\ne1`$ be a normal $`p`$-subgroup. If $`p`$ divides $`|G/N|`$, then
$`\omega(|G/N|)=\omega(|G|)`$ and $`c(G/N)\le c(G)`$, contradicting minimality. Otherwise $`N`$
is a normal Hall subgroup, $`G=N\rtimes H`$ by Schur–Zassenhaus, and every cyclic subgroup
$`\langle h\rangle`$ of $`H\cong G/N`$ has two distinct cyclic lifts $`\langle h\rangle`$ and
$`\langle nh\rangle`$. Hence $`c(G)\ge2\,c(G/N)\ge2\cdot2^{\omega(|G|)+1}`$, again a
contradiction. A nontrivial solvable normal subgroup would contain a nontrivial characteristic
$`p`$-subgroup, so $`G`$ has none.

### 1. Where the odd order theorem enters

If $`P`$ is cyclic, then $`N_G(P)/C_G(P)`$ embeds in the 2-group $`\mathrm{Aut}(P)`$ and has odd
order, so it is trivial, and Burnside's transfer theorem gives a normal 2-complement $`K`$. By the
odd order theorem $`K`$ is solvable, hence so is $`G`$. Therefore $`P`$ is not cyclic and
$`a\ge2`$. The same argument shows that every nonabelian simple group has a noncyclic Sylow
2-subgroup, so its order is divisible by 4.

### 2. Root counts

By Frobenius' theorem, $`n`$ divides $`\#\{x\in G: x^n=1\}`$ for every $`n\mid|G|`$. Writing
$`c(G)=\sum_{x\in G}1/\varphi(\operatorname{ord}x)`$ and grouping elements by order turns such
root counts into lower bounds for cyclic subgroup counts:

- for $`n\mid|G|`$, at least $`\tau(n)`$ cyclic subgroups have order dividing $`n`$;
- since $`P`$ is not cyclic, $`c(G)\ge(a+2)\,\tau(m)`$.

Against $`c(G)\lt8\cdot2^{\omega(m)}`$ the second bound gives $`a\le5`$, and $`m`$ is squarefree
when $`a\ge4`$. A sharper root count shows that for $`a\ge3`$ some element of $`P`$ has order
$`2^{a-1}`$, so $`P`$ has a cyclic subgroup of index 2.

### 3. A simple normal subgroup with trivial centralizer

$`G`$ has a nonabelian simple normal subgroup $`S`$ with $`C_G(S)=1`$ and $`4\mid|S|`$. A minimal
normal subgroup of $`G`$ is a direct product of nonabelian simple groups, and a second minimal
normal subgroup inside $`C_G(S)`$ would commute with $`S`$. It is therefore enough to exclude two
commuting nonabelian simple subgroups $`S_1,S_2`$ with $`S_1\cap S_2=1`$:

- if $`a\le3`$, both orders are divisible by 4 (Step 1), so $`16\mid|G|`$, which is impossible;
- if $`a\in\{4,5\}`$, a noncyclic Sylow 2-subgroup $`Q`$ of $`S_1`$ and an involution
  $`z\in S_2`$ give a subgroup $`Q\times\langle z\rangle`$. It maps onto $`C_2^3`$, so it has no
  cyclic subgroup of index at most 2, whereas every subgroup of $`P`$ has one.

### 4. Families with a fixed 2-part

Let $`A\ne1`$ be a cyclic 2-subgroup normalized by $`P`$. Then $`n=|G:N_G(A)|`$ is odd; write
$`m=c\,n`$. Since $`N_G(A)/C_G(A)`$ embeds in the 2-group $`\mathrm{Aut}(A)`$, the odd part of
$`|C_G(A)|`$ is $`c`$, so $`C_G(A)`$ has at least $`\tau(c)`$ cyclic subgroups $`B`$ of odd order
(Step 2), and each $`AB`$ is cyclic with 2-part $`|A|`$. Doing this for the $`n`$ conjugates of
$`A`$ gives

```math
\#\{\text{cyclic subgroups with 2-part }|A|\}\ \ge\ n\,\tau(c). \qquad(\star)
```

Cyclic subgroups with different 2-parts are distinct, and at least $`\tau(m)`$ have odd order.

**The normalizer has index at least 5.** $`S`$ does not normalize $`A`$: otherwise the map
$`S\to\mathrm{Aut}(A)`$ into an abelian group would be trivial, because $`S`$ is nonabelian
simple, and $`A\le C_G(S)=1`$. So the core of $`N_G(A)`$ meets $`S`$ trivially, centralizes
$`S`$, and is trivial. Then $`G`$ acts faithfully on the $`n`$ cosets of $`N_G(A)`$ and $`|G|`$
divides $`n!`$. As $`4\mid|G|`$ and $`n`$ is odd, $`n\ge5`$.

### 5. The case $`|P|\ge16`$

Here $`m`$ is squarefree and $`P`$ has an element $`x`$ of order $`2^{a-1}`$. The subgroups of
$`\langle x\rangle`$ of orders 2, 4 and 8 are normalized by $`P`$, since $`\langle x\rangle`$ has
index 2 in $`P`$. For each of them $`(\star)`$ holds with $`n\ge5`$ odd and squarefree, so
$`\tau(c)=\tau(m)/2^{\omega(n)}`$ and $`n\ge\frac52\,2^{\omega(n)}`$. Each family therefore has at
least $`\frac52\,\tau(m)`$ members, and

```math
c(G)\ \ge\ \tau(m)+3\cdot\tfrac52\,\tau(m)=\tfrac{17}{2}\,\tau(m)\ \gt\ 8\cdot2^{\omega(m)},
```

a contradiction.

### 6. The case $`|P|=8`$

Now $`x`$ has order 4, and $`(\star)`$ applies to $`\langle x^2\rangle`$ and $`\langle x\rangle`$
with odd indices $`n_1,n_2\ge5`$, where $`m=c_in_i`$. Since $`2^{\omega(m)}\le2^{\omega(n_i)}\tau(c_i)`$
and $`7\cdot2^{\omega(n)}\le2n`$ for odd $`n\ge7`$, if $`n_1,n_2\ge7`$ each family has at least
$`\frac72\,2^{\omega(m)}`$ members and $`c(G)\ge2^{\omega(m)}+7\cdot2^{\omega(m)}`$, a
contradiction. Otherwise some $`n_i=5`$, so $`G`$ embeds in $`S_5`$ and $`m\in\{5,15\}`$. For
$`|G|=40`$ the Sylow 5-subgroup is normal. For $`|G|=120`$ there are six Sylow 5-subgroups and at
least ten Sylow 3-subgroups (four would embed $`G`$ in $`S_4`$), and each family has at least ten
members, so $`c(G)\ge(1+10+6)+10+10=37\gt32`$.

### 7. The case $`|P|=4`$

Then $`P\cong C_2\times C_2`$. Burnside's transfer theorem and the odd order theorem show
$`N_G(P)\ne C_G(P)`$, so an element of $`N_G(P)`$ permutes the three involutions of $`P`$
cyclically, and all involutions of $`G`$ are conjugate. Fix an involution $`t\in P`$, let
$`i=|G:C_G(t)|`$ be the number of involutions and $`f`$ the number of involutions commuting with
$`t`$. By $`(\star)`$ for $`\langle t\rangle`$ there are at least $`i\,\tau(m/i)`$ cyclic subgroups with
2-part 2, and $`i\ge5`$. If $`7\cdot2^{\omega(i)}\le i`$, then $`c(G)\ge8\cdot2^{\omega(m)}`$ as
before; otherwise $`i\in\{5,7,9,11,13,15,21\}`$. Three facts constrain $`i`$ and $`f`$:

- The Sylow 2-subgroups of $`C_G(t)`$ are Klein four groups through $`t`$, any two meeting in
  $`\langle t\rangle`$, so $`f=1+2j`$ with $`j=|\mathrm{Syl}_2(C_G(t))|`$ odd.
- An involution outside $`P`$ that commutes with two involutions of $`P`$ centralizes $`P`$ and
  gives an elementary abelian subgroup of order 8. So the involutions outside $`P`$ commuting with
  the three involutions of $`P`$ form three disjoint sets: $`3(f-3)\le i-3`$.
- $`P`$ acts by conjugation on the $`i-3`$ involutions outside $`P`$ without fixed points, and
  Burnside's lemma gives $`4\mid(i-3)+3(f-3)`$.

These leave $`j\in\{1,3\}`$. If $`j=1`$, then $`C_G(t)\le N_G(P)`$, which forces $`i\ge15`$.
Hence $`i=15`$, $`|G:N_G(P)|=5`$ and $`|G|=60`$, and

```math
c(G)\ \ge\ (1+10+6)+15\ =\ 32\ =\ 8\cdot2^{\omega(15)},
```

which is the equality case, attained by $`A_5`$. If $`j=3`$, then $`i=15`$ and $`3\mid m/15`$, so
the family has at least $`\frac{15}{2}\,2^{\omega(m)}`$ members and $`c(G)`$ again exceeds the
threshold. $`\square`$

**The `lean/` development** shares Steps 0–2 and the family count of Step 5, which there handles
dihedral and semidihedral Sylow subgroups of orders 16 and 32. For Sylow subgroups isomorphic to
$`C_2\times C_2`$ or $`D_8`$ it applies the Gorenstein–Walter theorem instead of Steps 6 and 7.

## Files

| Directory | Lean version | Purpose |
|---|---:|---|
| `lean/` | `v4.33.1` | Formal Conjectures version, pinned to commit `8323e878...`; the complete development, including the vendored Feit–Thompson and Gorenstein–Walter closure (1,850 files, about 1.23 million lines) |
| `lean4web/` | `v4.35.0-rc3` | Standalone Mathlib-only file for Lean4Web (Mathlib `5e0c4e52...`), assuming the odd order theorem (about 7,000 lines) |

Each directory contains its Lean sources, `lakefile.toml`, `lean-toolchain`, and the generated
`lake-manifest.json`. `lean/vendor/` contains the Gorenstein–Walter closure (with its
Feit–Thompson closure) from
[Qiuzhen-CFSG/CFSG](https://github.com/Qiuzhen-CFSG/CFSG/tree/96b2a02085dc678f3e0a97b334c31ada599c55fd)
and subnormality modules from [yawara/odd-order](https://github.com/yawara/odd-order), with
compatibility changes for Lean `v4.33.1`.

## Verification

Formal Conjectures version:

```bash
cd lean
lake update
lake exe cache get
lake build Conjecture55FC
```

Standalone Mathlib/Lean4Web version:

```bash
cd lean4web
lake update
lake exe cache get
lake build
```

The Lean4Web file was checked on 26 September 2026 with Lean `v4.35.0-rc3` and Mathlib
`5e0c4e52` (a few minutes on a laptop). It compiles with no errors and contains
no `sorry`, `admit`, custom axiom, `native_decide`, or `unsafe` declaration. Its final
`#print axioms` commands report only Lean's standard axioms:

```text
'conjecture55_of_oddOrder_unfolded' depends on axioms: [propext, Classical.choice, Quot.sound]
'conjecture55_of_leanEval_feit_thompson' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The odd order theorem is an argument of these theorems, not an axiom, so it does not appear in
this list.

For `lean/`, an earlier snapshot of the development was built and its final theorem reported only
the same three axioms. The current tree has been refactored since then and is being re-verified;
the earlier result does not certify it.

## Status boundary

What is proved:

```text
lean4web/:  (odd order theorem)  →  for every finite group G,
            cyc(G) < 2^(ω(|G|)+2)  →  G is solvable.
lean/:      the same statement with no hypothesis, using the vendored
            Feit–Thompson and Gorenstein–Walter theorems.
```

What is not claimed:

```text
The Lean4Web file does not prove the odd order theorem; it is a hypothesis.
A fresh complete verification of the current lean/ tree (in progress).
The other results of arXiv:2604.08040, such as the bounds for the number of all subgroups.
```

## Sources

- A. Das, H. K. Dey and K. Sharma, [*Group Structure via Subgroup Counts*](https://arxiv.org/abs/2604.08040v1),
  arXiv:2604.08040v1 (Conjecture 5.5)
- A. Das, H. K. Dey, C. Galindo and K. Sharma, *Group Structure from Subgroup and Cyclic Subgroup
  Counts*, [arXiv:2604.08040v2](https://arxiv.org/abs/2604.08040v2) (Theorem 7.1)
- A. Das and K. Sharma, *Solvability of groups via cyclic subgroup count*,
  [arXiv:2604.23664](https://arxiv.org/abs/2604.23664)
- [Formal Conjectures: `Arxiv/2604.08040/Conjecture5_5.lean`](https://github.com/google-deepmind/formal-conjectures/blob/8323e878b83fcd7f4a448256069352a265460d75/FormalConjectures/Arxiv/2604.08040/Conjecture5_5.lean)
- [Lean Eval: `feit_thompson`](https://github.com/leanprover/lean-eval/blob/d0cdd1b68639174cac91cb06e2e47431b9567dbb/LeanEval/GroupTheory/FeitThompson.lean)
  and its [submission records](https://github.com/leanprover/lean-eval-submissions/tree/6420467aaae70cffb9db2fd3e97bb91e93223595/results)
- [Qiuzhen-CFSG/CFSG](https://github.com/Qiuzhen-CFSG/CFSG/tree/96b2a02085dc678f3e0a97b334c31ada599c55fd)
  and [yawara/odd-order](https://github.com/yawara/odd-order)
- W. Feit and J. G. Thompson, *Solvability of groups of odd order*, Pacific J. Math. 13 (1963)
- D. Gorenstein and J. H. Walter, *The characterization of finite groups with dihedral Sylow
  2-subgroups*, J. Algebra 2 (1965)
- G. Gonthier et al., *A Machine-Checked Proof of the Odd Order Theorem*, ITP 2013
- [Repository layout used as a model](https://github.com/KitaKen1/erdos-522-strong-law)

## AI usage disclosure

This formalization, mathematical exploration, proof development, and documentation were produced
by Kenta Kitamura with assistance from OpenAI Codex, and Claude Code using Claude Opus 5.5.

## Appendix: The Lean4Web target

This appendix explains why the Lean4Web file differs from the complete development, and where its
single hypothesis comes from.

### A.1 The complete development does not run in Lean4Web

The proof in `lean/` depends on the Gorenstein–Walter theorem, which in turn depends on the
Feit–Thompson theorem. With these closures the development has 1,845 modules and 53.9 MB of Lean
source, and a standalone version with only `import Mathlib` has 1,209,867 lines (52 MB). Of the
53.9 MB, the Feit–Thompson closure accounts for 27.7 MB (536 modules) and the rest of the
Gorenstein–Walter closure for another 24.6 MB. The part specific to Conjecture 5.5 is about
1.8 MB (157 modules).

Lean4Web checks one file in a browser session. A file of 1.2 million lines cannot be pasted,
and in our tests on the public server a 0.58 MB slice of the development already took 15.6
minutes, while longer sessions were disconnected after about 17 minutes. The complete development
therefore cannot be checked there.

### A.2 The lighter file assumes the odd order theorem

Almost all of the source is classification input, and the Conjecture 5.5 part itself is small. The
Lean4Web file takes the Feit–Thompson theorem as an explicit hypothesis, and avoids the
Gorenstein–Walter theorem altogether: the Klein four and $`D_8`$ cases are handled by the counting
of Steps 6 and 7 above. The file has about 7,000 lines (314 KB).

The odd order theorem is used in only two places: to show that a group with a cyclic Sylow
2-subgroup is solvable (Step 1), and to show that $`N_G(P)\ne C_G(P)`$ in the Klein four case
(Step 7). No other theorem is assumed; the Frobenius, Burnside, Schur–Zassenhaus and Sylow
arguments are proved in the file or taken from Mathlib.

### A.3 The hypothesis is the Lean Eval statement

The hypothesis is copied from the Lean Eval problem
[`feit_thompson`](https://github.com/leanprover/lean-eval/blob/d0cdd1b68639174cac91cb06e2e47431b9567dbb/LeanEval/GroupTheory/FeitThompson.lean):

```lean
theorem feit_thompson {G : Type*} [Group G] [Finite G]
    (_h : Odd (Nat.card G)) : Group.IsSolvable G
```

The final theorem of the Lean4Web file takes exactly this statement as its argument, for
`G : Type`:

```lean
theorem conjecture55_of_leanEval_feit_thompson
    (feit_thompson : ∀ {G : Type} [Group G] [Finite G],
      Odd (Nat.card G) → Group.IsSolvable G) :
    ∀ (G : Type) [Group G] [Fintype G],
      Nat.card {H : Subgroup G // IsCyclic H} <
        2 ^ ((Fintype.card G).primeFactors.card + 2) → Group.IsSolvable G
```

The conclusion is the Formal Conjectures proposition with `cyc` and `numPrimeFactors` unfolded.
The file also proves the same conclusion from the hypothesis written with explicit binders,
`conjecture55_of_oddOrder_unfolded`.

Taking the hypothesis from Lean Eval means that its meaning does not depend on this repository: it
is a published benchmark statement, and a proof of it is exactly what would discharge the
assumption. The public Lean Eval
[submission records](https://github.com/leanprover/lean-eval-submissions/tree/6420467aaae70cffb9db2fd3e97bb91e93223595/results)
list accepted proofs of `feit_thompson` from five submitters as of 26 September 2026. Those proofs
target Lean Eval's own Lean and Mathlib versions and are not included here.

### A.4 How the file was produced

The file concatenates 50 modules in dependency order: 37 taken from `lean/` and ported from Lean
`v4.33.1` to `v4.35.0-rc3`, and 13 new modules for the odd-order-only route. Each
module is wrapped in its own `section`, so that `open`, `variable` and `universe` commands stay
local, as in the modular build. Declarations that the final theorems cannot reach (265 of 577)
were then removed, and the result was compiled again from Mathlib alone.
