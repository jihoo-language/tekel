# Tekel

*MENE, MENE, TEKEL*: you have been weighed in the balances.

[jihoo](https://github.com/jihoo-language/jihoo) and [Ruach](https://github.com/jihoo-language/ruach) are as fast as C. Tekel tells you how fast your program is, before you run it. In Tekel, **the type of a function includes its cost**. The compiler infers, for every function, an exact polynomial bound on its cost in terms of the sizes of its arguments. It proves the bound with nothing but a linear program, so there are no loop invariants to write and no annotations unless you want them:

```text
$ tekel bound examples/sort.tk
metric: steps
  insert(x, l)      ≤ |l| + 1    O(|l|)
  isort(l)          ≤ 1/2·|l|² + 3/2·|l| + 1    O(|l|²)
                      within its budget |l|² + |l| + 1
  append(xs, ys)    ≤ |xs| + 1    O(|xs|)
  partition(p, l)   ≤ |l| + 1    O(|l|)
  quicksort(l)      ≤ |l|² + 3·|l| + 1    O(|l|²)
```

These bounds are not estimates. Each one is a theorem about every input, and most of them are **exact**: some input reaches them. `weigh` runs a function on growing inputs and compares:

```text
$ tekel weigh examples/sort.tk isort
isort(l) ≤ 1/2·|l|² + 3/2·|l| + 1    [steps]

      n      worst seen           bound
      0               1               1  tight
      1               3               3  tight
      2               6               6  tight
      3              10              10  tight
      4              15              15  tight
      8              45              45  tight
     16             153             153  tight
     32             561             561  tight
     64            2145            2145  tight

11225 call(s) audited; the bound is reached at every size
```

*Audited* means that the interpreter checked **every call** of the run, including each of the 2,080 recursive calls of `insert` at `n = 64`, against that function's own bound, evaluated at that call's arguments.

## A budget is a type

A function can declare what it may cost. If Tekel cannot prove the budget, the program is rejected, just as it would be for a type error:

```tekel
fn reverse(l: List<a>) -> List<a> costs 1 + 2 * |l| =
  match l {
    [] => []
    x :: xs => append(reverse(xs), [x])
  }
```

```text
$ tekel bound examples/rejected/budget.tk
metric: steps
  append(xs, ys)   ≤ |xs| + 1    O(|xs|)
  reverse(l)       ≤ 1/2·|l|² + 3/2·|l| + 1    O(|l|²)
                     EXCEEDS its budget 2·|l| + 1: weighed and found wanting
```

The exit status is nonzero, so a budget works in CI the way a test does. Unlike a benchmark, it cannot pass by luck: it holds for inputs no one tried.

## Amortized costs come out on their own

A functional queue keeps a front list and a reversed back list. Dequeuing from an empty front reverses the whole back list, which costs `|back|` steps. A worst-case analysis of each operation gives `O(n²)` for `n` operations. Tekel finds the real bound:

```text
$ tekel bound examples/queue.tk
metric: steps
  rev_onto(l, acc)        ≤ |l| + 1    O(|l|)
  dequeue(front, back)    ≤ |back| + 2    O(|back|)
  run(ops, front, back)   ≤ 3·|ops| + |back| + 1    O(|ops| + |back|)
  simulate(ops)           ≤ 3·|ops| + 2    O(|ops|)
```

The term `|back|` in the bound of `run` is the credit that the textbook argument invents: every element in the back list has prepaid its own move. Nobody wrote that argument down. The linear program found it, and `simulate` is tight at every size up to 256. [Queue](examples/queue.tk)

## Several sizes at once

A bound is a polynomial in all of the argument sizes together, so nested loops over two lists cost the product of their lengths. Bounds compose through intermediate data whose size the caller never sees:

```text
$ tekel bound examples/product.tk
  product(xs, ys)         ≤ 2·|xs|·|ys| + 3·|xs| + 1    O(|xs|·|ys|)
                            within its budget 2·|xs|·|ys| + 3·|xs| + 1
  count_product(xs, ys)   ≤ 3·|xs|·|ys| + 3·|xs| + 3    O(|xs|·|ys|)
  sort_onto(xs, ys)       ≤ |xs|·|ys| + 1/2·|xs|² + 1/2·|ys|² + 5/2·|xs| + 3/2·|ys| + 3
```

`count_product` counts a list that `product` built. `sort_onto` sorts `rev_onto(xs, ys)`, whose length is `|xs| + |ys|`, so its quadratic sort costs `(|xs| + |ys|)²/2`. That is where the mixed term `|xs|·|ys|` comes from. Sorting all `C(n, 2)` pairwise sums of a list is `O(n⁴)`, and Tekel derives `1/8·|l|⁴ − 1/4·|l|³ + …` from the bounds of the parts. [Products](examples/product.tk) · [Composition](examples/compose.tk)

Potential also lives inside data. Flattening a list of lists pays one step for each inner element:

```text
  concat(ls)        ≤ Σ_{x∈ls} |x| + 2·|ls| + 1    O(|ls| + Σ_{x∈ls} |x|)
```

## Run a program

```sh
nix run path:. -- bound examples/sort.tk
nix run path:. -- weigh examples/queue.tk simulate
nix run path:. -- run examples/sort.tk quicksort "[3, 1, 4, 1, 5, 9, 2, 6]"
```

```text
[1, 1, 2, 3, 4, 5, 6, 9]
cost 53 steps (bound 89), 53 call(s) audited
```

For development, use the flake's shell. Tekel has no dependencies beyond the Rust standard library.

```sh
nix develop -c cargo test
printf 'fn len(l: List<Int>) -> Int = match l { [] => 0  _ :: t => 1 + len(t) }' | nix develop -c cargo run -q -- bound -
```

| Command | |
| --- | --- |
| `tekel bound FILE` | infer a bound for every function and check budgets; fails if a budget is exceeded |
| `tekel run FILE FN ARGS…` | call `FN` with literal arguments, audit every call, print the cost and the bound |
| `tekel weigh FILE FN` | run `FN` on ascending, descending, constant and random inputs of growing size, and compare the worst cost seen with the bound |
| `--metric steps\|alloc\|ticks` | what costs (default: the file's `metric` line, else `steps`) |
| `--degree D` | the highest degree to try (default 4) |

## The language

Tekel is a small first-order functional language with integers, booleans, pairs, lists and type parameters. Function signatures are written out, and everything inside a body is inferred.

```tekel
metric steps                          // or alloc, or ticks

fn partition(p: Int, l: List<Int>) -> (List<Int>, List<Int>) =
  match l {
    [] => ([], [])
    x :: xs => {
      let (lo, hi) = partition(p, xs)
      if x < p then (x :: lo, hi) else (lo, x :: hi)
    }
  }

fn head(l: List<a>) -> a costs 1 =
  match l {
    [] => fail("empty list")
    x :: _ => x
  }
```

- **Types**: `Int`, `Bool`, `Unit`, `(A, B)`, `List<A>`, and lowercase type parameters such as `a`.
- **Expressions**: integer arithmetic and comparisons, `&&`, `||`, `!`, `if … then … else …`, `x :: xs`, `[a, b, c]`, pairs, calls, `match`, and blocks `{ let p = e  …  result }`.
- **`match`** on a list has a `[]` arm and an `x :: xs` arm. A pattern takes one cell at a time; nest a `match` to take more. A pair is taken apart with `let (a, b) = …` or with `match`.
- **`fail("…")`** stops the program. **`tick(q)`** costs `q`, a nonnegative rational such as `1/2`, under the `ticks` metric.
- **`costs`** declares a budget: a sum of terms `c · |x|^k · |y|^j …` over the list parameters.

There are three metrics. **`steps`** counts function calls. **`alloc`** counts the list cells a program builds; reusing a cell that a `match` took apart is free. **`ticks`** counts only what `tick` says, which is how [comparisons.tk](examples/comparisons.tk) counts the comparisons made by a sort. Under `steps` a bound is also a proof of termination, because every call costs one and the bound is finite. A function that loops forever gets no bound.

## How it works

Tekel implements **automatic amortized resource analysis** (AARA), the method of Hofmann and Jost, with the polynomial and multivariate potential of Hoffmann, Aehlig and Hofmann that underlies [RAML](https://www.raml.co/). [Analysis](src/aara.rs)

Every list in scope has a length, and the analysis gives the whole context a **potential**: a polynomial in all of those lengths, written in the basis of products of binomial coefficients `C(n₁, k₁) · C(n₂, k₂) ⋯`. Its coefficients are unknowns. The typing rules say that potential must pay for every step and for the potential of each result. That only takes linear relations among coefficients, because the binomial basis behaves well under the two operations that matter:

- **Taking a cell off a list.** `C(n + 1, k) = C(n, k) + C(n, k − 1)`, so the potential of the tail is a shift of the potential of the list, and the difference pays for the step.
- **Using a list twice.** `C(n, i) · C(n, j)` is a fixed combination of `C(n, k)` for `max(i, j) ≤ k ≤ i + j`, so shared potential splits linearly.

The rules become a linear program, and an exact simplex solver over the rationals minimizes it: the highest-degree coefficients first, then the lower ones, then the constant. The cheapest annotation that type-checks *is* the bound. Two mechanisms make the bounds compose:

- A recursive call may use the function's own type plus a **cost-free** type of lower degree, which carries potential through the call without paying for steps. Without it, insertion sort could not be quadratic: each `insert` consumes potential that the recursive `isort` has to pass along.
- In `let x = e₁ in e₂`, potential that **mixes** the variables of `e₁` with those of `e₂` passes through `e₁` by one cost-free typing per mixed term, and becomes potential that mixes `x` with the variables of `e₂`. This is how `|xs| · |ys|` survives `rev_onto(xs, ys)` to pay for the sort that follows.

A run checks this analysis independently. With the bounds in hand, the interpreter evaluates each function's potential at each call's actual arguments and compares it with the call's actual cost. The test suite does this for every function in the examples under all three metrics, on inputs of every size up to 7 and eight input shapes, which audits over 100,000 calls. A violation would be a bug in Tekel, and the interpreter reports it as one.

## What Tekel cannot weigh

- **Costs that are not polynomial in list lengths.** `2ⁿ` (all subsets of a list) is reported as *no polynomial bound*, not guessed. Logarithms cannot be written either, so mergesort is bounded by its quadratic worst case `C(n, 2)` comparisons, not `n log n`.
- **Recursion on integers.** An `Int` carries no potential, so a loop that counts `n` down to 0 has no bound. Recurse on a list instead.
- **Higher-order functions.** Tekel is first-order, like the RAML system it follows; there are no closures to pass.
- **Potential through type parameters.** A generic function such as `id(l: List<a>)` cannot carry the potential inside its elements, so a caller with a `List<List<Int>>` pays for the inner lists before the call.
- **Element potential is one list at a time.** The potential of the elements of a list is a sum over the elements, and does not mix an element's length with other lengths.
- **Bounds are upper bounds.** Most are reached, but not all: `minimum(l)` makes `|l| − 1` comparisons, and Tekel says `|l|`, because coefficients cannot be negative.
- **Budgets.** A budget is checked exactly when it and the bound are sums of one-list polynomials. Otherwise it is checked coefficient by coefficient in the binomial basis, which is sufficient but stricter.

## References

- M. Hofmann and S. Jost. *Static prediction of heap space usage for first-order functional programs.* POPL 2003.
- J. Hoffmann and M. Hofmann. *Amortized resource analysis with polynomial potential.* ESOP 2010.
- J. Hoffmann, K. Aehlig and M. Hofmann. *Multivariate amortized resource analysis.* POPL 2011; TOPLAS 34(3), 2012.

## License

Apache License 2.0. See [LICENSE](LICENSE).
