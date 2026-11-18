# nfield command guide

Choose a command by the question you want to investigate. The command catalog, shell completion and focused help share the contracts below. Use `nfield help FAMILY ACTION` or `nfield FAMILY ACTION --help` to read one operation without running it.

Search the catalog by task or quantity. Search ignores letter case and requires every term to match. `--examples` adds up to three matching starts per family; it does not run them.

```sh
nfield commands digits --examples
nfield commands spectrum --examples
nfield commands weighted law-window --examples
nfield commands covariance --json
```

Ordinary operations return mathematical objects or values. Fixed reference data remain available as reference operations. `nfield verify FAMILY [CHECK]` runs implementation assertions, including a few checks whose finite model is selected by parameters. A printed residual can accompany a useful calculation; it does not turn that calculation into an assertion panel.

The CLI and daemon share the same calculations. `nfield commands --json` exposes the versioned discovery contract, with family descriptions, ordinary actions, verification actions and a complete guide for each. `actionDetails` follows `actions`; `verificationDetails` follows `verificationActions`; `defaultAction` describes argument-only operations when present. Action kinds are `utility`, `reference`, `service` and `verification`. Each action's `formatOptions` lists its accepted `--json` and `--csv` switches. Existing fields remain available.

The website can use the same syntax, inputs and result descriptions. A printed table is not automatically a structured JSON API. The local service uses JSON over TCP; see `nfield help daemon`.

## Start with a calculation

```sh
nfield field 7
nfield collision-table compare 13 113 --base 10
nfield boundary-spectrum inspect 9 --support 0,4,8
nfield reset-forest 31 --returns 3 --json
nfield reset-forest project 6 --divisor 2 --weights 1,-1,2,0,1,1 --json
nfield field-observation clocks 25 0 1,2 0,0 1,1 --matrix
nfield native-refinement kernel 2 3
nfield help weighted-remainder-state law-window
```

The general reset projection accepts your own signed rational source. Its default selection is divisor 1 with modulus N^N; use `--modulus 0` for the identity. Sampling defaults to grid (N+1)^2; `--grid 0` returns coordinates only, with energy, mixed and boundary work unavailable. Arbitrary masks retain all mixed terms and have their own interpretation.

Request a format only where the action supports it. Unsupported `--json` or `--csv` switches fail before calculation. A command that already prints a CSV table does not necessarily accept a `--csv` switch. Exact rational results remain strings in JSON, so downstream tools can preserve their precision.

## Implementation checks

```sh
nfield verify families
nfield verify collision-characters examples
nfield verify collision-centering gate --base 5 --lag 1
nfield verify centered-collision-table complete 5 1
nfield verify reset-forest contracts --json
```

The family checks are ordinary C executable tests and require neither Lean nor proof sources. `verify reset-forest` runs its original finite suite and 75 source and forest contract checks. The `contracts` subcheck runs those 75 checks alone, returning mathematical check IDs, finite domains, cases, assertions and failures. It accepts `--json`; optional `--time` writes timing to stderr. Other named checks retain their documented output formats. Formal proofs and manuscript correspondence belong to the separate proof project.

Retired spellings are `verify all`, `verify coverage`, `verify list`, `verify theorem` and `verify work`, together with the old `--require-complete` and `--source-root` verification options. They return an explanatory error with exit code 2 and run no checks. Use `verify families` to choose a named check. There is no aggregate replacement command.

## Research operations

### analyze

Choose denominators worth studying before opening their complete digit fields.

**Inputs.** Denominator n and digit base.

**Result.** Period, reference alignment and the field invariants in one summary.

```sh
nfield analyze 7 --base 10
```

Compare summaries, then use field for the words or decompose for the signed residual.

**Scope.** The summary includes numerical values; use the corresponding exact operation when an exact rational is needed.

**Default usage.** `nfield analyze <n> [--base <b>]`

### field

Inspect the actual repeating words of all fractions with your chosen denominator.

**Inputs.** Denominator n and digit base.

**Result.** A row for each proper fraction, with its terminating or repeating expansion.

```sh
nfield field 7
```

Change --base to compare the same rational field across digit systems; use div for the corresponding long-division steps.

**Scope.** The displayed field grows with its denominator and period; start with a modest n.

**Default usage.** `nfield field <n> [--base <b>]`

### reset-forest

Measure how a chosen reset family and its complement contribute to one sampling defect.

**Inputs.** Prime-square work/source: odd prime p and divisor or return window. General project: cutoff N, signed rational weights, a modulus/divisor/mask and optional grid.

**Result.** Exact rational energies, selected/complementary work, complete mixed terms, contact, curvature, reset masses and source coefficients.

```sh
nfield reset-forest 31 --returns 3 --json
```

Compare --divisor choices, inspect source for the prime-square collapse map, or use project for your own weighted source. Export --json or --csv for further calculations.

**Scope.** Prime-square work/source accepts odd primes 3..251; project accepts N=0..64. Every reset reads the complete source. Finite values do not establish the open uniform complementary bound.

**Default usage.** `nfield reset-forest <prime> [--returns L | --divisor D] [--json | --csv]`

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `source`. Recover the source and collapse map for a selected reset forest. | Arguments: <prime> [--returns L \| --divisor D] [--json \| --csv]. | Original coefficients, collapsed coefficients, selected denominators and source energies. | `nfield reset-forest source 31 --divisor 3 --json` |
| `project`. Select a reset projection of your own weighted finite source. | N=0..64; N signed rational weights (default 1). Default selection is divisor D=1, with modulus N^N. Choose --modulus, --divisor or --mask to change it. Grid Q defaults to (N+1)^2; Q=0 requests coordinates only. | Exact source, projection and complement coefficients, ordered work, twice the mixed work, reset masses and optional sampled work. | `nfield reset-forest project 6 --divisor 2 --weights 1,-1,2,0,1,1 --json` |

**Implementation subcheck.** `nfield verify reset-forest contracts [--json] [--time]`
runs the 75 finite source-selection, projection, energy and forest checks.
It returns mathematical check IDs, tested domains, cases, assertions, failures
and outcomes. It uses its declared input panels and needs no proof files.


### native-refinement

Price a change of sampling or test how much of a response a chosen detector can capture.

**Inputs.** Detector size, clock pair, transport size, divisor family or supplied rational response bounds.

**Result.** Gram data, signed pairings, projection costs and exact or enclosed quantities for the selected action.

```sh
nfield native-refinement kernel 2 3
```

Use kernel to inspect a pair before detector/transport; trace retains every old row and can write a new JSON result.

**Scope.** Input caps differ by action. Some projections are numerical; a computed gain does not prove the remaining uniform lower bound.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `detector`. Measure how much refinement a finite detector observes. | Arguments: N [--json]. | Residuals, eligible depths, Gram costs, signed responses and joint capture. | `nfield native-refinement detector 2 --json` |
| `transport`. Compare copied and refitted source responses. | Arguments: N [--json]. | Projection gain, copied energy, refitting correction and coefficients. | `nfield native-refinement transport 2 --json` |
| `probe-transport`. Follow paired detector depths through fourfold refinement. | Arguments: N [--json]. | Signed response drift, paired probes and complete Gram loss. | `nfield native-refinement probe-transport 2 --json` |
| `packet`. Price a tapered packet while retaining its boundary. | Arguments: scale [--json]. | Coarse and fine energy, old-new pairing and signed work. | `nfield native-refinement packet 2 --json` |
| `copy-cost`. Bound the cost of combining copies at a chosen spacing. | Arguments: ratio count. | Neighbor overlap, universal synthesis bound and equal-weight energy. | `nfield native-refinement copy-cost 2 4` |
| `kernel`. Compute the complete native Gram entry of two clocks. | Arguments: left-clock right-clock. | Independent complete-period and short-sum evaluations. | `nfield native-refinement kernel 2 3` |
| `mask-capture`. Compare the response captured by masks and addresses. | Arguments: first last [base]. | Numerical Gram ranks, capture energies, fractions and updated error. | `nfield native-refinement mask-capture 2 4 3` |
| `trace`. Follow refinement with all old clocks retained. | Arguments: FIRST LAST [--json]. | Optimizer coefficients, signed steps, complete costs, Gram entries and pair terms. | `nfield native-refinement trace 2 4 --json` |
| `collision4` (reference). Obtain the fixed base-two collision calibration as reference data. | Arguments: [--json]. | Native mean and norm, shell cost, signed response, capture fraction and innovation coefficients. | `nfield native-refinement collision4 --json` |
| `collision-families`. Compare translated collision families on a chosen clock interval. | Arguments: [FIRST LAST] [--json]. | Family projections, correlated Gram data, capture and missed target work. | `nfield native-refinement collision-families 2 4 --json` |
| `carry`. Resolve a ceiling gap through your chosen sequence of digit bases. | Arguments: denominator address bases. | Exact carry at each radix step, carry sum and terminal gap. | `nfield native-refinement carry 2 3 2,3` |
| `detail`. Resolve a finite native detail into its clock coefficients. | Arguments: cutoff. | Exact detail and lift coefficients, arithmetic mass and complete-error enclosure. | `nfield native-refinement detail 4` |
| `polarity`. Inspect the carry bits behind a digit-polarity mask. | Arguments: base address. | Polarity, three bits, carry, disagreement, spoke responses and cost bounds. | `nfield native-refinement polarity 3 2` |
| `stable-correction`. Price a correction from supplied response, cost and error bounds. | Arguments: response cost error. | Exact conditional step size and guaranteed gain. | `nfield native-refinement stable-correction 1/2 1/3 1/4` |
| `divisor-family`. Compare one arithmetic divisor family before and after refinement. | Arguments: scale odd-core address. | Exact parent and child readings, their difference, changed reset mass and reciprocal balance. | `nfield native-refinement divisor-family 2 3 16` |
| `divisor-work`. Measure exact work over a specified divisor range. | Arguments: scale cutoff. | Divisor coefficients, signed pairings and complete work. | `nfield native-refinement divisor-work 2 16` |
| `parent-credit`. Compare the parent contribution with its divisor descendants. | Arguments: scale. | Exact parent and descendant work in the declared eightfold window. | `nfield native-refinement parent-credit 2` |

### align

Compare a fractional field with its synchronized reference word.

**Inputs.** Denominator n and digit base.

**Result.** The synchronized reference-alignment score for that field.

```sh
nfield align 7 --base 10
```

Compare bases or denominators; use coherence-decomposition when the pairwise score and signed difference are also needed.

**Scope.** The short command prints a decimal score. Reference and pairwise alignment have different sample spaces.

**Default usage.** `nfield align <n> [--base <b>]`

### field-observation

Experiment with your own finite fields, endpoint readings, sampling grids and observation weights.

**Inputs.** Comma-separated rational or complex component data, grid size, shift and optional matrix request.

**Result.** Continuous and sampled work, their defect, and component/mixed matrices where supported.

```sh
nfield field-observation clocks 25 0 1,2 0,0 1,1 --matrix
```

Choose clocks, pulses, harmonics or segments; vary the observation while keeping the same source inputs.

**Scope.** Lists must match. Endpoint readings and cross terms are part of the input; finite identities do not supply uniform limit estimates.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `clocks`. Sample a sum of clocks with your own phases and amplitudes. | Arguments: q shift frequencies phases amplitudes [--matrix]. | Exact continuous and sampled energy, defect, contact and boundary terms. | `nfield field-observation clocks 25 0 1,2 0,0 1,1 --matrix` |
| `pulses`. Sample overlapping pulses with explicit endpoint readings. | Arguments: q shift lefts rights amplitudes left-readings right-readings [--matrix]. | Exact work, defect, boundary corrections and optional mixed matrices. | `nfield field-observation pulses 4 0 0 1/2 1 1/2 1/2` |
| `harmonics`. Inspect exact Fourier aliasing on a chosen grid. | Arguments: q shift frequencies amplitudes [--matrix]. | Continuous energy, sampled energy, defect and optional Hermitian matrices. | `nfield field-observation harmonics 4 0 1,5 1,1 --matrix` |
| `segments`. Sample a piecewise affine field with specified boundary values. | Arguments: q shift boundaries starts slopes readings. | Exact energy and defect, including point, jump and regular-curvature corrections. | `nfield field-observation segments 4 0 0 0 1 0` |
| `native-cycle`. Enclose the complete native energy of a periodic reading. | Arguments: cutoff readings. | Directed lower and upper energy bounds with period and cutoff. | `nfield field-observation native-cycle 4 0,1,-1` |
| `tail-bound`. Price an omitted native tail using your supplied envelopes. | Arguments: cutoff old-envelope new-envelope head [tolerance]. | Conditional complete-change bounds and an optional sufficient cutoff. | `nfield field-observation tail-bound 4 1 2 0` |
| `work`. Separate source change from observation change. | Arguments: old-weights new-weights field addition. | Old and new energy, observation work, signed interaction and addition energy. | `nfield field-observation work 1,1 1,2 1,2 1,-1` |
| `native-boundary`. Resolve a finite native weighted sum at its endpoints. | Arguments: first-address readings. | Weighted sum, endpoint terms, interior term and identity residual. | `nfield field-observation native-boundary 1 1,2,3` |
| `native-variation`. Measure the complete work of changing a native field. | Arguments: first-address first-field second-field. | Old and new work, signed interaction, correction work and residual. | `nfield field-observation native-variation 1 1,2 2,1` |
| `invariants`. Find the minimum energy compatible with specified readings. | Arguments: weights field row [row ...]. | Actual energy, minimum energy, unmeasured energy and independent readings. | `nfield field-observation invariants 1,1 2,3 1,0` |
| `register`. Compute overlap among congruence-address components. | Arguments: moduli residues amplitudes weights. | Exact diagonal, ordered-pair, cross and total energy. | `nfield field-observation register 2,3 0,1 1,1 1,1,1,1,1,1` |
| `shells`. Convert primitive shells and square-prefix readings. | Arguments: values [--from-prefixes]. | Exact shell and prefix values with formal prime-log coefficients. | `nfield field-observation shells 1,2,3` |

### div

Inspect the long-division steps that produce a digit field.

**Inputs.** Denominator n and digit base.

**Result.** The division table connecting each remainder to its emitted digit and next remainder.

```sh
nfield div 7 --base 10
```

Use it to explain a word from field or compare the same fraction in another base.

**Scope.** Requires n>=2; large denominators produce large tables.

**Default usage.** `nfield div <n> [--base <b>]`

### decompose

Separate reference alignment from mutual alignment inside the same field.

**Inputs.** Denominator n and digit base.

**Result.** Alpha, pairwise sigma and the signed residual F=alpha-sigma.

```sh
nfield decompose 13 --base 10
```

Compare denominators or bases, then use coherence-decomposition pairs to locate the contributing pairs.

**Scope.** Pairwise alignment requires at least two proper fractions; the residual can have either sign.

**Default usage.** `nfield decompose <n> [--base <b>]`

### polar

Inspect digit words alongside their cumulative polarity coordinates.

**Inputs.** Denominator n and digit base.

**Result.** The closed digit field, cumulative orientation and accumulated digit-phase rows.

```sh
nfield polar 7 --base 10
```

Use analyze for a scalar summary, then compare polar output across related denominators.

**Scope.** These are finite field diagnostics; coordinate patterns alone do not imply a uniform law.

**Default usage.** `nfield polar <n> [--base <b>]`

### survey

Find trends or exceptional denominators over an initial range.

**Inputs.** Maximum denominator, base and optional CSV format.

**Result.** One row of field invariants for each surveyed denominator.

```sh
nfield survey 20 --base 10 --csv
```

Export rows for plotting, then investigate selected denominators with field or decompose.

**Scope.** Runtime grows with the number and periods of denominators; use range to restrict a later scan.

**Default usage.** `nfield survey <max> [--base <b>] [--csv]`

### range

Compare field invariants over a specific interval rather than restarting at the first denominator.

**Inputs.** Minimum and maximum denominators, base and optional CSV format.

**Result.** Rows of field invariants over the requested interval.

```sh
nfield range 10 20 --base 10 --csv
```

Use adjacent intervals to extend a survey and retain machine-readable rows.

**Scope.** A finite trend is evidence about the requested interval, not a limiting estimate.

**Default usage.** `nfield range <min> <max> [--base <b>] [--csv]`

### table

Inspect the collision-deviation table for a chosen digit base.

**Inputs.** Base, supplied positionally or with --base, and optional --pairs.

**Result.** Finite residue-class collision values and optional reflected pairs.

```sh
nfield table 5 --pairs
```

Look for a residue pattern, then use collision-table inspect or finite-determination on a particular integer.

**Scope.** The table is periodic in the stated finite modulus; prime-frequency behavior requires a separate calculation.

**Default usage.** `nfield table [base] [--pairs]`

### spectral

Find which additive frequencies carry digit-bin agreement for a prime field.

**Inputs.** Prime modulus and digit base.

**Result.** Digit-bin Fourier power and its finite spectral summary.

```sh
nfield spectral 13 --base 10
```

Use spectral-power overlap for interval overlap data; use spectral-structure for multiplicative orbit frequencies.

**Scope.** Additive and multiplicative spectra are different coordinates. Fourier values are numerical with the stated residuals.

**Default usage.** `nfield spectral <p> [--base <b>]`

### equations

Look up the definitions behind the quantities printed by the field commands.

**Inputs.** No numerical inputs.

**Result.** A reference sheet of the principal invariants and relations.

```sh
nfield equations
```

Use beside analyze, align or decompose when checking a symbol or normalization.

**Scope.** This is mathematical reference help, not an execution or verification result.

**Default usage.** `nfield equations`

### tables

Locate the registered fixed reference tables.

**Inputs.** An optional registered table name.

**Result.** A list of available tables or the requested reference rows.

```sh
nfield tables
```

Use the associated mathematical family for calculations on your own parameters.

**Scope.** This compatibility entry uses fixed fixtures rather than an arbitrary-input calculation.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `reciprocal-square-selection` (reference). Read the decimal reciprocal-golden threshold reference table. | Fixed reference inputs; no model parameters. | Ten supported resolutions with exact alignment and threshold side. | `nfield tables reciprocal-square-selection` |

### reciprocal-square-selection

Compare exact alignment with the reciprocal-golden threshold for your prime and supported multiplier.

**Inputs.** Prime p, supported multiplier m, base, or a prime scan limit.

**Result.** Exact alignment, rational threshold comparison and cubic factor/remainder information.

```sh
nfield reciprocal-square-selection inspect 3 4 --base 10
```

Use inspect for a field, cubic for its polynomial, and scan to compare the prime parameter.

**Scope.** The alignment formula requires its one-digit support hypotheses; the fixed table is a reference fixture.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Compare a supported field with the reciprocal-golden threshold. | Arguments: <p> <m> [--base <b>]. | Exact alignment, direct row counts and an exact threshold sign. | `nfield reciprocal-square-selection inspect 3 4 --base 10` |
| `cubic`. Examine the threshold cubic attached to a chosen prime. | Arguments: <p>. | Polynomial values, rational factorization status and roots in the admissible window. | `nfield reciprocal-square-selection cubic 3` |
| `table` (reference). Read the fixed decimal threshold table. | Fixed reference inputs; no model parameters. | Ten supported resolutions with exact alignment and threshold side. | `nfield reciprocal-square-selection table` |
| `scan`. Find which primes satisfy the threshold selection conditions. | Arguments: <maximum-prime>. | Prime-by-prime limit, factorization and admissible-root classifications. | `nfield reciprocal-square-selection scan 31` |

### weighted-reference-profile

Change the weight of a reference population and study the resulting alignment or branch.

**Inputs.** Integer modulus, supported multiplier, rational weight and base; branch/order parameters for other actions.

**Result.** Exact weighted scores, quadratic-field coordinates and finite substitution counts.

```sh
nfield weighted-reference-profile inspect 3 4 1 1 --base 10
```

Compare inspect at several weights; use branch or reflection-product to examine the associated projective map.

**Scope.** Supported blocks and congruence assumptions are checked. Torsion and transport fixtures belong to focused verification.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Compute a profile with your chosen terminating-row weight. | Arguments: <q> <m> <weight-num> <weight-den> [--base <b>]. | Exact weighted score, block sizes and profile parameters. | `nfield weighted-reference-profile inspect 3 4 1 1 --base 10` |
| `branch`. Follow a reciprocal-golden weight branch. | Arguments: <q> <r>. | Exact quadratic-field weight, decimal value and admissible-window status. | `nfield weighted-reference-profile branch 3 3` |
| `reflection-product`. Form the ordered reflection product for a chosen modulus. | Arguments: <q>. | Integer matrix, trace, determinant, discriminant and fixed-point classification. | `nfield weighted-reference-profile reflection-product 2` |
| `oriented-words`. Compare the two orders of the profile transformations. | Arguments: <q>. | Raw and positive-action matrices and the resulting cone classifications. | `nfield weighted-reference-profile oriented-words 2` |
| `finite-orbit`. Follow a finite Fibonacci block orbit. | Arguments: <m> <steps> [--base <b>]. | Block counts, reconstructed scale and alternating signed error at each step. | `nfield weighted-reference-profile finite-orbit 7 8 --base 7` |

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `torsion` | `nfield verify weighted-reference-profile torsion [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |
| `transport` | `nfield verify weighted-reference-profile transport [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |

### digit-partition

Determine how base-supported and coprime factors organize a fractional field.

**Inputs.** Denominator, base and optional synchronized depth.

**Result.** Support split, clearing depth, digit-bin populations and synchronized alignment.

```sh
nfield digit-partition inspect 6 --base 2
```

Start with a composite denominator; change the base to see which factors move into the supported part.

**Scope.** The requested depth must admit the synchronized construction; printed fixed tables are examples.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Find the synchronized digit matches in your field. | Arguments: <n> [--base <b>] [--depth <t>]. | Per-numerator word, match count and exact alignment at the chosen depth. | `nfield digit-partition inspect 6 --base 2` |
| `primes`. List the digit-partitioning primes of your base. | Arguments: [--base <b>]. | Prime divisors and the exact finite prime criterion. | `nfield digit-partition primes --base 10` |
| `table` (reference). Read selected prime and alignment-limit reference rows. | Fixed reference inputs; no model parameters. | Digit bases, digit-partitioning primes and exact limits 2/p. | `nfield digit-partition table` |

### alignment-limit

Measure the orbit/coset correction to alignment for a prime core and supported multiplier.

**Inputs.** Prime, multiplier, base and optional depth or scan limit.

**Result.** Coset data, finite alignment and limiting comparison for the specified inputs.

```sh
nfield alignment-limit inspect 3 4 --base 10
```

Inspect one case, use cosets to resolve its correction, then table to compare eligible primes.

**Scope.** The limit formula retains its prime-core/support hypotheses; a finite scan is not a new limit proof.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Compare finite alignment with its coset limit. | Arguments: <p> <m> [--base <b>] [--depth <t>]. | Synchronized depth, coset counts, exact alignment and limit values. | `nfield alignment-limit inspect 53 2 --base 10` |
| `cosets`. Find whether the multiplicative cosets have one alignment limit. | Arguments: <p> [--base <b>]. | Coset populations, equidistribution and exact distinct limits. | `nfield alignment-limit cosets 53 --base 10` |
| `table`. Compare alignment limits across a prime range. | Arguments: [--base <b>] [--max-prime <P>]. | Prime, period, equidistribution flag and rational subgroup or alternative limits. | `nfield alignment-limit table --base 10 --max-prime 61` |
| `sharpness`. Examine how a fixed sharpness family approaches its limit. | Arguments: [--steps <N>]. | Powers of two, exact finite alignment and the gap to 3/5. | `nfield alignment-limit sharpness --steps 6` |

### three-tier

Classify how a denominator behaves after its supported factors are removed.

**Inputs.** Denominator or maximum denominator, base and optional depth.

**Result.** Tier, rough/support split and alignment values for requested finite cases.

```sh
nfield three-tier classify 30 --base 10
```

Use classify to locate a tier, inspect a representative, and scan to compare its range.

**Scope.** Composite rough parts have their own domain and signed behavior; do not apply a prime-core formula indiscriminately.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Classify a denominator by its synchronized alignment. | Arguments: <n> [--base <b>] [--depth <D>]. | Supported and rough factors, depth, exact alignment and tier. | `nfield three-tier inspect 6 --base 10` |
| `classify`. Classify all denominators in your chosen range. | Arguments: <max> [--base <b>]. | One row per denominator with exact alignment and threshold classification. | `nfield three-tier classify 15 --base 10` |
| `scan`. Summarize tier populations and endpoint hits. | Arguments: <max> [--base <b>]. | Tier counts, endpoint counts and exceptions over the requested range. | `nfield three-tier scan 200 --base 10` |

### deficit-lattice

Construct exact alignment-deficit ratios and compare arithmetic tuning intervals.

**Inputs.** Prime, supported multiplier or pair of multipliers, base and scale factor.

**Result.** Exact deficit values, ratios and supported scale tables.

```sh
nfield deficit-lattice inspect 3 4 --base 10
```

Use inspect to establish a value, ratio to compare two fields, then the scale actions for musical interval tables.

**Scope.** Support conditions and common scaling matter; scale examples are specified constructions.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Compute the alignment-deficit coordinates of a supported denominator. | Arguments: <p> <m> [--base <b>]. | Exact row counts, alignment, deficit and its lattice coordinates. | `nfield deficit-lattice inspect 29 24 --base 30` |
| `ratio`. Compare two supported deficit scales. | Arguments: <p> <u> <v> [--base <b>] [--factor <t>]. | Exact finite ratio, limiting lattice ratio and signed error. | `nfield deficit-lattice ratio 29 24 36 --base 30` |
| `pythagorean`. Resolve the Pythagorean comma at finite resolution. | Arguments: [--factor <t>]. | Exact deficit ratio, target comma and relative error. | `nfield deficit-lattice pythagorean` |
| `major-scale`. Compute the just major scale from finite deficit ratios. | Arguments: [--factor <t>]. | Note ratios, lattice targets and finite-resolution errors. | `nfield deficit-lattice major-scale` |
| `chromatic-scale`. Compute the five-limit chromatic scale from deficit ratios. | Arguments: [--factor <t>]. | Chromatic note ratios, target lattice values and finite errors. | `nfield deficit-lattice chromatic-scale` |

### coherence-decomposition

Find whether a field statistic comes from its reference word or from agreements between its fractions.

**Inputs.** Denominator, prime/support factors, base and synchronized depth.

**Result.** Exact alpha, sigma, signed F and optionally every nonzero unordered pair score.

```sh
nfield coherence-decomposition pairs 13 --base 10
```

Inspect the aggregate, then use pairs to identify the contributing word pairs.

**Scope.** Alpha and sigma average different sample spaces. Their difference remains signed.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Separate synchronized reference and pairwise alignment. | Arguments: <n> [--base <b>] [--depth <D>]. | Exact alpha, sigma, signed residual and row populations. | `nfield coherence-decomposition inspect 77 --base 10` |
| `prime-core`. Resolve the contribution of a supported prime core. | Arguments: <p> <s> [--base <b>] [--depth <D>]. | Terminating and repeating block populations, pair score and exact coherence. | `nfield coherence-decomposition prime-core 3 4 --base 10` |
| `pairs`. Locate the numerator pairs contributing to coherence. | Arguments: <n> [--base <b>] [--depth <D>]. | Nonzero pair scores, aggregate matching positions and sigma. | `nfield coherence-decomposition pairs 11 --base 10` |
| `sigma-zero`. Find prime fields with injective digit maps. | Arguments: <max-prime> [--base <b>]. | Prime-by-prime period, injectivity and exact sigma. | `nfield coherence-decomposition sigma-zero 31 --base 10` |
| `golden-gap`. Identify eligible prime cores around the reciprocal-golden gap. | Arguments: [--base <b>]. | Available prime cores and the exact inequalities defining the gap. | `nfield coherence-decomposition golden-gap --base 10` |

### cross-alignment

Retain every pairwise agreement when a single mean hides the structure of a field.

**Inputs.** Denominator or prime, base and synchronized depth.

**Result.** Cross-alignment matrix, orbit blocks and finite Fourier decomposition.

```sh
nfield cross-alignment matrix 7 --base 10
```

Inspect matrix first, then prime/fourier/block for compatible structural coordinates.

**Scope.** Matrix size grows with the field; numerical spectral calculations retain the stated tolerance.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `matrix`. Build the synchronized pairwise alignment matrix. | Arguments: <n> [--base <b>] [--depth <D>]. | Exact matrix entries, rank, eigenvalues and recovered scalar readings. | `nfield cross-alignment matrix 12 --base 10` |
| `prime`. Inspect the orbit structure behind a prime-field matrix. | Arguments: <p> [--base <b>]. | Multiplicative cosets, digit-map injectivity and matrix classification. | `nfield cross-alignment prime 13 --base 10` |
| `fourier`. Resolve the matrix into frequency blocks. | Arguments: <p> [--base <b>]. | Hermitian block eigenvalues and numerical full-spectrum discrepancy. | `nfield cross-alignment fourier 13 --base 10` |
| `block`. Build the supported-lift block decomposition. | Arguments: <p> <s> [--base <b>] [--depth <D>]. | Terminating and repeating block sizes, rank and block spectrum. | `nfield cross-alignment block 3 4 --base 10` |

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `examples` | `nfield verify cross-alignment examples [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |

### spectral-structure

Find rank, null directions and frequency fibers in a prime field's alignment matrix.

**Inputs.** Prime modulus and digit base.

**Result.** Orbit words, occupied bins, fiber ranks and multiplicative character energies.

```sh
nfield spectral-structure inspect 7 --base 2
```

Compare inspect with two-coset where eligible; use character to resolve the multiplicative frequencies.

**Scope.** Fourier ranks and spectra are numerical at the reported tolerance. These are not Dirichlet L-values.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Resolve digit words into multiplicative orbit frequencies. | Arguments: <p> [--base <b>]. | Coset words, occupied bins, frequency ranks and spectral values. | `nfield spectral-structure inspect 7 --base 2` |
| `two-coset`. Compare the two spectral branches of a two-coset field. | Arguments: <p> [--base <b>]. | Orbit words, per-frequency branch eigenvalues and degeneracy data. | `nfield spectral-structure two-coset 13 --base 10` |
| `character`. Measure the harmonic energy of each multiplicative character. | Arguments: <p> [--base <b>]. | Character energy and normalized eigenvalue by frequency. | `nfield spectral-structure character 17 --base 10` |

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `examples` | `nfield verify spectral-structure examples [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |

### spectral-power

Inspect how digit intervals distribute additive Fourier power and overlap.

**Inputs.** Prime modulus and digit base.

**Result.** Digit-bin powers, interval kernels and overlap profiles.

```sh
nfield spectral-power overlap 13 --base 10
```

Use inspect for the spectrum and overlap to explain it from finite bin intersections.

**Scope.** Finite counts are exact; Fourier values use the reported numerical convention.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Measure additive Fourier power of digit bins. | Arguments: <p> [--base <b>]. | Bin sizes, overlap profile and finite Fourier power. | `nfield spectral-power inspect 13 --base 10` |
| `overlap`. Compare digit labels under every additive shift. | Arguments: <p> [--base <b>]. | Direct and triangular same-bin overlap at each shift. | `nfield spectral-power overlap 13 --base 10` |

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `examples` | `nfield verify spectral-power examples [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |

### autocorrelation

Compare a digit field with its additive shifts or multiplicative slices.

**Inputs.** Prime, base and optional shift/multiplier or orbit coset.

**Result.** Same-bin cross-spectrum, correlations and orbit harmonics.

```sh
nfield autocorrelation slice 13 2 --base 10
```

Use inspect for the full profile, slice for one multiplier, and orbit for a multiplicative family.

**Scope.** Additive displacement and multiplicative multiplier are distinct inputs; numerical transforms are finite.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Relate same-bin cross-spectrum to multiplicative autocorrelation. | Arguments: <p> [--base <b>]. | Digit bins, orbit sizes, cross-spectrum and numerical residuals. | `nfield autocorrelation inspect 7 --base 10` |
| `slice`. Evaluate one multiplicative same-bin slice. | Arguments: <p> <a> [--base <b>]. | Direct count, inverse count, Fourier line sum and error. | `nfield autocorrelation slice 13 10 --base 10` |
| `orbit`. Trace autocorrelation within one multiplicative orbit. | Arguments: <p> <c> [--base <b>]. | Orbit residues, digits and per-lag direct and subgroup values. | `nfield autocorrelation orbit 41 1 --base 10` |
| `harmonics`. Measure the cyclic harmonic energies of one orbit. | Arguments: <p> [--coset <c>] [--base <b>]. | Eigenvalue and imaginary residual for each Fourier mode. | `nfield autocorrelation harmonics 13 --coset 1 --base 10` |

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `examples` | `nfield verify autocorrelation examples [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |

### phase-gate

Locate phase and multiplier combinations that admit or suppress digit collisions.

**Inputs.** Prime, multiplier, base or a chosen bin-word action.

**Result.** Ramanujan selectors, phase-gate data and finite multiplier/cell structure.

```sh
nfield phase-gate inspect 13 2 --base 10
```

Inspect one multiplier, then compare the complete multipliers or bin-word output.

**Scope.** Use the printed prime/base hypotheses; zero gates describe finite collisions, not prime-pair existence.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Measure the collision gate for a chosen multiplier. | Arguments: <p> <a> [--base <b>]. | Direct collision count, bin intersections and spectral gate value. | `nfield phase-gate inspect 7 3 --base 10` |
| `multipliers`. Find the open and closed gates across all multipliers. | Arguments: <p> [--base <b>]. | Collision count and gate response for every nonzero multiplier. | `nfield phase-gate multipliers 7 --base 10` |
| `bin-word`. Inspect the Euclidean pattern of digit-bin sizes. | Arguments: <p> [--base <b>]. | Bin sizes, excess word and continued-fraction data. | `nfield phase-gate bin-word 43 --base 10` |
| `density`. Compare the cell density with finite prime counts. | Arguments: <a> [--base <b>] [--max-prime <P>]. | Exact cell count, predicted density and finite discrepancy range. | `nfield phase-gate density 7 --base 10 --max-prime 997` |
| `power-lag`. Evaluate the cell identity for a power multiplier. | Arguments: <ell> [--base <b>] [--max-prime <P>]. | Cell count and the resulting finite prime-density comparison. | `nfield phase-gate power-lag 2 --base 10 --max-prime 997` |
| `prime-sum`. Compute the finite prime-sum boundary at a chosen power lag. | Arguments: <ell> [--base <b>] [--max-prime <P>]. | Prime sum, leading coefficient, harmonic term and discrepancy correction. | `nfield phase-gate prime-sum 2 --base 10 --max-prime 997` |

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `examples` | `nfield verify phase-gate examples [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |

### bin-derangements

Find multipliers that move every residue out of its original digit bin.

**Inputs.** Prime modulus and digit base.

**Result.** The zero-collision family, counts, constructive mean and selected lag data.

```sh
nfield bin-derangements family 13 --base 10
```

Use family to obtain the multipliers, inspect for their counts, and mean for the complementary population.

**Scope.** The base/prime domain controls the gate formula; a zero multiplier collision is not a primality claim.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Find which multipliers preserve or destroy digit-bin matches. | Arguments: <p> [--base <b>]. | Digit bins, nonidentity collision counts and zero/positive classification. | `nfield bin-derangements inspect 13 --base 10` |
| `family`. Construct and inspect the bin-deranging multiplier family. | Arguments: <p> [--base <b>]. | Multiplier pairs, products, collision counts and the observed zero set. | `nfield bin-derangements family 13 --base 10` |
| `mean`. Compute the mean constructive collision count. | Arguments: <p> [--base <b>]. | Exact total mass, population and rational mean. | `nfield bin-derangements mean 13 --base 10` |
| `lags`. Locate the zero lags of a primitive-root word. | Arguments: <p> [--base <b>]. | Multipliers and collision counts at every nonzero lag. | `nfield bin-derangements lags 17 --base 10` |

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `examples` | `nfield verify bin-derangements examples [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |

### collision-characters

Decompose your finite prime-weighted collision sum into residue and character channels.

**Inputs.** Cutoff or prime, base, lag and complex exponent.

**Result.** Exact collision deviations plus numerical channel sums, transforms and reconstruction residuals.

```sh
nfield collision-characters inspect 1000 --base 5 --lag 1
```

Inspect a finite cutoff, vary it to compare channels, and use prime for a single exact deviation.

**Scope.** Character transforms are numerical. Finite cutoff behavior does not establish convergence.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `prime`. Compute the collision deviation at one prime and lag. | Arguments: <p> [--base <b>] [--lag <ell>]. | Multiplier, collision count, constructive mean and exact deviation. | `nfield collision-characters prime 13 --base 10 --lag 1` |
| `inspect`. Resolve a finite prime sum into character coordinates. | Arguments: <x> [--base <b>] [--lag <ell>]. | Residue streams and complex character components at the chosen exponent. | `nfield collision-characters inspect 100 --base 10 --lag 1 --sigma 1 --tau 0.25` |

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `examples` | `nfield verify collision-characters examples [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |
| `snapshot` | `nfield verify collision-characters snapshot [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |

### silent-primes

Find primes with zero prescribed digit collision and inspect their variance.

**Inputs.** Prime or base, lag, and the recipe/variance action.

**Result.** Silence candidates, exact collision values and variance components.

```sh
nfield silent-primes prime 13 --base 10 --lag 1
```

Use recipe to enumerate the specified candidate mechanism, prime to inspect one case, and variance to compare nonzero behavior.

**Scope.** Silence concerns a digit statistic at the selected lag; it does not remove the prime from other statistics.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `recipe`. Construct candidates for globally silent primes. | Arguments: [--base <b>] [--lag <ell>]. | Progression terms, factorizations and eligible prime divisors. | `nfield silent-primes recipe --base 10 --lag 1` |
| `prime`. Compare global and repetend silence at one prime. | Arguments: <p> [--base <b>] [--lag <ell>]. | Collision count, autocorrelation and both silence classifications. | `nfield silent-primes prime 13 --base 10 --lag 1` |
| `variance`. Compute the exact constructive collision variance. | Arguments: <p> [--base <b>]. | Exact mass, mean, variance and normalized variance. | `nfield silent-primes variance 97 --base 10` |

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `examples` | `nfield verify silent-primes examples [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |
| `snapshot` | `nfield verify silent-primes snapshot [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |

### collision-fluctuation

Measure a prime's collision deviation and compare it with its residue class.

**Inputs.** Prime, base or requested table/class action.

**Result.** Finite deviations, class means and prime-weighted finite sums.

```sh
nfield collision-fluctuation prime 13 --base 10
```

Start with prime; table and classes expose the periodic baseline before interpreting a sum.

**Scope.** Fixed snapshots are verification fixtures. Finite fluctuations do not supply an infinite asymptotic.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `prime`. Separate a prime's finite-table deviation and correction. | Arguments: <p> [--base <b>]. | Collision count, integer deviation, correction and exact fluctuation. | `nfield collision-fluctuation prime 191 --base 10` |
| `table`. Summarize the exact lag-one table in a chosen base. | Arguments: [--base <b>]. | Entry population, minimum, maximum, sum and mean. | `nfield collision-fluctuation table --base 3` |
| `classes`. Compare the means carried by residue families. | Arguments: [--base <b>]. | Lift counts, exact class means and limiting fluctuation targets. | `nfield collision-fluctuation classes --base 10` |
| `sum`. Accumulate the finite reciprocal-prime collision sum. | Arguments: <x> [--base <b>]. | Sum, drift-removed residual, mean fluctuation and sign counts. | `nfield collision-fluctuation sum 1000 --base 10` |

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `examples` | `nfield verify collision-fluctuation examples [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |
| `snapshot` | `nfield verify collision-fluctuation snapshot [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |

### collision-centering

Remove the predictable fiber bias from a collision value before comparing residuals.

**Inputs.** Integer, base, lag or a finite sum cutoff.

**Result.** Direct and centered collision values, fiber means and centered prime sums.

```sh
nfield collision-centering inspect 113 --base 10 --lag 1
```

Inspect one value, use fibers to see its baseline, then sum to study the remaining finite fluctuations.

**Scope.** Centering uses the whole reduction fiber, not a fitted mean from the chosen prime sample.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Center an individual collision by its complete reduction fiber. | Arguments: <n> [--base <b>] [--lag <ell>]. | Direct count, table value, exact fiber mean and centered value. | `nfield collision-centering inspect 1009 --base 10 --lag 2` |
| `table`. Obtain every centered unit-table entry. | Arguments: [--base <b>] [--lag <ell>]. | Residue, reduction fiber, raw value, fiber mean and centered value. | `nfield collision-centering table --base 3 --lag 1` |
| `fibers`. Compare complete reduction-fiber populations. | Arguments: [--base <b>] [--lag <ell>]. | Entry counts, raw sums, exact means and centered sums. | `nfield collision-centering fibers --base 10 --lag 1` |
| `sum`. Accumulate a finite centered reciprocal-prime sum. | Arguments: <x> [--base <b>] [--lag <ell>]. | Included-prime population and the centered partial sum. | `nfield collision-centering sum 1000 --base 10 --lag 1` |

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `examples` | `nfield verify collision-centering examples [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |
| `snapshot` | `nfield verify collision-centering snapshot [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |
| `gate` | `nfield verify collision-centering gate [--base B] [--lag L] [--time]` | Positive integer base and lag selecting a finite gate model; flags default to base 10 and lag 1. |

### collision-table

Compare integers through the exact periodic collision table they share.

**Inputs.** Integer or pair of integers, digit base and requested table view.

**Result.** Residue labels, collision values, reflected pairs, extrema and table summaries.

```sh
nfield collision-table compare 13 113 --base 10
```

Use compare to test a suspected periodic relation; table exposes every unit class.

**Scope.** Residue-table equality does not imply the represented integers share other arithmetic properties.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Find the finite-table fingerprint of an integer. | Arguments: <n> [--base <b>]. | Residue class, multiplier, direct count and table value. | `nfield collision-table inspect 9 --base 10` |
| `compare`. Compare two integers through their finite-table fingerprints. | Arguments: <n1> <n2> [--base <b>]. | Both residue classes and values, with equality indicators. | `nfield collision-table compare 109 1009 --base 10` |
| `table`. Obtain the complete lag-one unit table. | Arguments: [--base <b>]. | Unit class, value, complementary class and complementary value. | `nfield collision-table table --base 3` |
| `summary`. Measure the population and range of a lag-one table. | Arguments: [--base <b>]. | Unit count, extrema, sign populations, sum and exact mean. | `nfield collision-table summary --base 10` |

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `examples` | `nfield verify collision-table examples [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |

### collision-transform

Study the character support that survives centering and compare a specified prime interval.

**Inputs.** Integer or interval, base, lag and optional real exponent.

**Result.** Centered values, support/conductors, finite spectrum and prime-window sums.

```sh
nfield collision-transform window 100 1000 --base 5 --lag 1
```

Inspect the table and gate first; spectrum identifies channels, then window evaluates the same centered object on primes.

**Scope.** Spectra are numerical; table and window size limits are separate. No critical-strip estimate follows from a finite window.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Locate an integer in the centered collision transform. | Arguments: <n> [--base <b>] [--lag <ell>]. | Direct count, finite-table value, reduction fiber and exact centered value. | `nfield collision-transform inspect 191 --base 10` |
| `table`. Obtain the complete centered transform table. | Arguments: [--base <b>] [--lag <ell>]. | Residue, fiber, raw value, rational mean and centered value. | `nfield collision-transform table --base 3 --lag 1` |
| `spectrum`. Resolve the centered table into finite characters. | Arguments: [--base <b>] [--lag <ell>]. | Character coordinates, parity, conductor and complex coefficient. | `nfield collision-transform spectrum --base 10 --lag 1` |
| `window`. Compute one declared finite prime-window contribution. | Arguments: <low> <high> [--base <b>]. | Prime count and weighted contribution at the specified real exponent. | `nfield collision-transform window 1000 10000 --base 10 --sigma 1` |

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `examples` | `nfield verify collision-transform examples [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |
| `snapshot` | `nfield verify collision-transform snapshot [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |
| `gate` | `nfield verify collision-transform gate [--base B] [--lag L] [--time]` | Positive integer base and lag selecting a finite gate model; flags default to base 10 and lag 1. |

### residue-three-neutrality

Separate true residue-three contributions from the residue labels inside a digit table.

**Inputs.** Integer or prime interval, base, lag and optional exponent.

**Result.** Quotient carry, lifted channel sums and the nontrivial modulo-three twist.

```sh
nfield residue-three-neutrality inspect 113 --base 10 --lag 1
```

Use inspect to see the quotient shift, channels for the full lift, then split for a finite prime interval.

**Scope.** An internal table slice is not automatically the same as the represented integer's true residue class.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Compare representative and true residue-three coordinates. | Arguments: <n> [--base <b>] [--lag <ell>]. | Quotient carry, both class labels and raw and centered values. | `nfield residue-three-neutrality inspect 101 --base 10` |
| `canonical`. Inspect internal residue-three slices of the finite table. | Arguments: [--base <b>] [--lag <ell>]. | Slice populations, sums and the reflection-fixed class. | `nfield residue-three-neutrality canonical --base 10` |
| `channels`. Measure the actual residue-three channels. | Arguments: [--base <b>] [--lag <ell>]. | Joint modulus, channel populations and raw and centered sums. | `nfield residue-three-neutrality channels --base 10` |
| `split`. Split a finite prime sum into its two true channels. | Arguments: <low> <high> [--base <b>]. | Channel counts and contributions, total, twist and decomposition residuals. | `nfield residue-three-neutrality split 1000 10000 --base 10 --sigma 1` |

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `examples` | `nfield verify residue-three-neutrality examples [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |
| `snapshot` | `nfield verify residue-three-neutrality snapshot [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |

### compatible-residue-channels

Resolve collision data into true prime or squarefree residue channels.

**Inputs.** Integer, channel prime or squarefree modulus, base, lag and finite cutoff.

**Result.** Reconstructed true residues, lifted channel sums and finite character statistics.

```sh
nfield compatible-residue-channels channels 3 --base 5 --lag 1
```

Compare internal and true channels; simultaneous joins several compatible prime channels in one modulus.

**Scope.** Exact channel identities and numerical finite correlations have separate scope; cutoff-uniform behavior remains separate.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Track the carry between internal and true prime coordinates. | Arguments: <integer> <prime>. | Quotient, internal class, carry shift and actual class. | `nfield compatible-residue-channels inspect 101 7 --base 10` |
| `internal`. Inspect one reflection-fixed internal slice. | Arguments: <prime>. | Slice label, population, raw sum and centered numerator sum. | `nfield compatible-residue-channels internal 7 --base 10` |
| `channels`. Measure each true channel for a chosen prime modulus. | Arguments: <prime>. | Channel population and raw and centered sums. | `nfield compatible-residue-channels channels 2 --base 10` |
| `simultaneous`. Compare simultaneous channels at a squarefree modulus. | Arguments: <squarefree>. | Joint modulus, all unit-channel populations and sums. | `nfield compatible-residue-channels simultaneous 30 --base 10` |
| `character-signs`. Measure signed character contributions over a chosen prime cutoff. | Arguments: [--cutoff <X>]. | Positive, negative and zero populations, net contribution and correlations. | `nfield compatible-residue-channels character-signs --cutoff 10000` |
| `magnitude-correlations`. Measure magnitude association across active character channels. | Arguments: [--cutoff <X>]. | Finite magnitude moments, covariance and Pearson correlations. | `nfield compatible-residue-channels magnitude-correlations --cutoff 10000` |
| `assignment-null`. Compare observed channel pairing with its finite permutation baseline. | Arguments: [--cutoff <X>]. | Observed statistic, null moments and normalized departure. | `nfield compatible-residue-channels assignment-null --cutoff 10000` |

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `snapshot` | `nfield verify compatible-residue-channels snapshot [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |

### centered-collision-table

Obtain an exact centered value or complete centered table at a specified lag.

**Inputs.** Base, lag and optional unit residue.

**Result.** Rational centered values, reflections and reduction-fiber sums.

```sh
nfield centered-collision-table inspect 5 1 7
```

Use inspect for values at your selected residue; verify centered-collision-table complete checks the full finite table.

**Scope.** Only supported finite moduli are admitted; centered class data do not count prime occurrences.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Read one exact unit entry and its reflection. | Arguments: <base> <lag> <unit-residue>. | Raw and rational centered values, fiber and reflected entry. | `nfield centered-collision-table inspect 3 1 5` |

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `complete` | `nfield verify centered-collision-table complete BASE LAG [--time]` | Positive integer base and lag selecting the finite collision table. |

### finite-character-pairing

Measure character pairing in a finite prime window for your chosen base and lag.

**Inputs.** Base, lag and prime cutoff.

**Result.** Pairing, channel energies, correlations and direct-sum comparison at that cutoff.

```sh
nfield finite-character-pairing one 3 1 --cutoff 1000
```

Change --cutoff on the same base/lag before comparing different tables.

**Scope.** Long-double numerical data at sigma=1/2; a trend is not a cutoff-uniform bound.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `one`. Compare direct and character readings for one finite model. | Arguments: <base> <lag> [--cutoff <X>]. | Channel counts, prime-window sums, pairing values and residuals. | `nfield finite-character-pairing one 3 2 --cutoff 10000` |
| `declared-rows`. Compare prescribed bases at your chosen cutoff. | Arguments: [--cutoff <X>]. | Finite character-pairing rows and associated prime populations. | `nfield finite-character-pairing declared-rows --cutoff 2000000` |

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `cutoff-trend` | `nfield verify finite-character-pairing cutoff-trend [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |

### coprime-base-orthogonality

Measure cross-work between two centered digit tables, including shared-factor cases.

**Inputs.** Two bases and their lags.

**Result.** Exact cross term, table energies, common-quotient data and recovery/splitting values.

```sh
nfield coprime-base-orthogonality pair 3 1 5 1
```

Use pair for coprime bases; common-quotient explains what survives when the bases share factors.

**Scope.** Choose domains small enough for the finite tables. Coprime zero work is not assumed for a shared-factor pair.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `pair`. Compute the joint pairing of two chosen base tables. | Arguments: <base-a> <lag-a> <base-b> <lag-b>. | Exact common-modulus populations, means and centered pairing. | `nfield coprime-base-orthogonality pair 3 2 5 3` |
| `common-quotient`. Inspect the shared character quotient of two tables. | Arguments: <base-a> <lag-a> <base-b> <lag-b>. | Quotient dimensions, common character data and orthogonality quantities. | `nfield coprime-base-orthogonality common-quotient 6 1 15 1` |

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `audit` | `nfield verify coprime-base-orthogonality audit [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |

### natural-prime-sum-window

Compare several bases on equal prime windows without mixing their lower boundaries.

**Inputs.** Explicit upper cutoff and, for common-tail, a common lower endpoint.

**Result.** Per-base finite sums, combined values and summation-order residuals.

```sh
nfield natural-prime-sum-window common-tail --lower 997 --cutoff 2000
```

Contrast common-tail with base-boundaries to see the contribution of unequal starting points.

**Scope.** The base set is fixed by this operation; the endpoints are adjustable. Sums are numerical and finite.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `base-boundaries`. Compare finite sums from each base's natural boundary. | Arguments: [--cutoff <X>]. | Prime populations, direct contributions and character readings by base. | `nfield natural-prime-sum-window base-boundaries --cutoff 250000` |
| `common-tail`. Compare bases on the same finite tail window. | Arguments: [--lower <L>] [--cutoff <X>]. | Common lower cutoff, per-base contributions and pairing data. | `nfield natural-prime-sum-window common-tail --lower 997 --cutoff 2000000` |

### primitive-odd-sector

Measure how a prime-base collision spectrum occupies its primitive odd character sector.

**Inputs.** Odd prime base and finite prime cutoff.

**Result.** Character counts, pair energies, relabeling variance, displacement and entropy support.

```sh
nfield primitive-odd-sector inspect 5 --cutoff 1000
```

Compare the same base at several cutoffs or different bases at the same cutoff.

**Scope.** Finite energy/correlation data do not establish a limiting overlap or repulsion constant.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Resolve a finite response into primitive and induced odd channels. | Arguments: <odd-prime-base> [--cutoff <X>]. | Character populations, sector energies and prime-sum factorization data. | `nfield primitive-odd-sector inspect 13 --cutoff 2000000` |

### additive-reflection-well

Locate the negative reflection well and compensating mass of a centered digit table.

**Inputs.** Digit base.

**Result.** Full cyclic convolution, exact well/compensation values and finite Fourier square.

```sh
nfield additive-reflection-well inspect 5
```

Compare bases while retaining the complete convolution, rather than only its most negative entry.

**Scope.** Integer convolution values are exact; Fourier corroboration is numerical.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Compute the cyclic self-convolution of a centered table. | Arguments: <base>. | Exact convolution, energy and reflection-well values. | `nfield additive-reflection-well inspect 10` |

### reflected-prime-pair-sign

Evaluate centered-table weights on every prime pair in a chosen finite even-target range.

**Inputs.** Base and maximum even target.

**Result.** Target sums, pair counts and signed square-sum comparisons.

```sh
nfield reflected-prime-pair-sign sweep 3 --max-even 100
```

Increase the target range for a fixed base and inspect where the weighted contributions occur.

**Scope.** Targets are multiples of b^2, with a finite maximum of 100000; these weights are not a proof of Goldbach or twin primes.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `sweep`. Count the weighted reflected prime pairs in a finite target range. | Arguments: <base> [--max-even <N>]. | Target and pair populations, signed weighted terms and sum identities. | `nfield reflected-prime-pair-sign sweep 10 --max-even 100000` |

### collision-spectrum-factorization

Resolve a collision coefficient into primitive character and Bernoulli factors.

**Inputs.** Odd prime base, primitive odd character index and optional unit multiplier.

**Result.** Direct coefficient, fiber cancellations and finite Bernoulli transform/factorization values.

```sh
nfield collision-spectrum-factorization inspect 5 1
```

Inspect a channel first; transform then tests its dependence on a selected multiplier.

**Scope.** Supported odd prime bases through 127; numerical character values do not locate L-function zeros.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Factor one primitive odd collision channel. | Arguments: <base> <character-index>. | Bernoulli value, short initial sum and the resulting complex coefficient. | `nfield collision-spectrum-factorization inspect 5 1` |
| `transform`. Compare direct and factored floor transforms. | Arguments: <base> <character-index> <unit-multiplier>. | Fractional-part and floor transforms with their complex residuals. | `nfield collision-spectrum-factorization transform 73 1 74` |

### weighted-remainder-state

Build and compare finite weighted clock states, boundary work and distribution data.

**Inputs.** Resolution, cutoff and action-specific rational phases, weights, moduli or intervals.

**Result.** Exact state/mass/kernel quantities or explicitly numerical/enclosed spectra and finite laws.

```sh
nfield weighted-remainder-state inspect 8 16
```

Start with inspect, boundary or conductor; use clock/finite-weights for custom clock data, and pairing/gram for signed work. Detailed actions below cover transforms, distributions and inversion.

**Scope.** This large family has action-specific limits and arithmetic conventions. Infinite laws and uniform estimates are distinct from a finite evaluation.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Measure a remainder field with its omitted mass retained. | Arguments: <resolution> <cutoff>. | Finite mass, stationary mean, centered age, variance, deficit and capacity. | `nfield weighted-remainder-state inspect 6 6` |
| `conductor`. Resolve a chosen conductor into its exact residue rows. | Arguments: <q> <cutoff>. | Finite amplitude, totient, Jordan weight and age, odd and endpoint rows. | `nfield weighted-remainder-state conductor 6 12` |
| `boundary`. Enumerate the reset boundary of a finite source. | Arguments: <resolution>. | Exact capacity, deficit, reduced addresses and reset multiplicities. | `nfield weighted-remainder-state boundary 6` |
| `ramp`. Integrate two affine ramp clocks directly. | Arguments: <first> <second>. | Exact rational overlap integral. | `nfield weighted-remainder-state ramp 6 4` |
| `floor`. Evaluate the original prime-square floor response. | Arguments: <prime> <address>. | Exact response at the canonicalized signed address. | `nfield weighted-remainder-state floor 7 5` |
| `straighten`. Compare original floors with their midpoint representation. | Arguments: <prime> <address>. | Transformed address, both exact responses and their difference. | `nfield weighted-remainder-state straighten 7 5` |
| `clock`. Read a finite weighted clock at any integer address. | Arguments: <cutoff> <address>. | Exact retained-mass clock, centered age and reset increment. | `nfield weighted-remainder-state clock 6 17` |
| `clock-law`. Enumerate the full finite distribution of a weighted clock. | Arguments: <cutoff>. | Exact clock values with multiplicities and total period. | `nfield weighted-remainder-state clock-law 4` |
| `age-budget`. Price the stationary age of a finite source. | Arguments: <cutoff>. | Exact harmonic cross sum, Mobius first moment and age budget. | `nfield weighted-remainder-state age-budget 6` |
| `finite-weights`. Explore clocks built from your own signed rational weights. | Arguments: <address> [period:weight ...]. | Exact clocks, forcing, amplitudes, Gram variance and Jordan variance. | `nfield weighted-remainder-state finite-weights 5 2:1/2 3:1/3` |
| `variance`. Enclose the variance of the full collision field. | Arguments: <cutoff>. | Finite variance, rational full-variance bounds and squared L2 tail budget. | `nfield weighted-remainder-state variance 6` |
| `rows`. Resolve a conductor at every residue or at one address. | Arguments: <conductor> [address]. | Exact age, odd, endpoint and increment row values. | `nfield weighted-remainder-state rows 6` |
| `increment-covariance`. Enclose increment covariance at a chosen shift. | Arguments: <cutoff> <shift>. | Exact finite covariance, full bounds and potential and increment errors. | `nfield weighted-remainder-state increment-covariance 6 2` |
| `increment-recurrence`. Price an increment return through a cutoff period. | Arguments: <cutoff>. | Exact return covariance and complete recurrence loss bounds. | `nfield weighted-remainder-state increment-recurrence 6` |
| `fourier`. Enclose a primitive additive Fourier coefficient. | Arguments: <conductor> <frequency> <cutoff> <finite\|full>. | Rational real and imaginary coefficient bounds and spectral masses. | `nfield weighted-remainder-state fourier 3 1 6 full` |
| `amplitude-refinement`. Sharpen a conductor amplitude using separate cutoffs. | Arguments: <conductor> <period-cutoff> <zeta-cutoff> <mobius-cutoff>. | Full amplitude, harmonic seed and explicit rational remainder intervals. | `nfield weighted-remainder-state amplitude-refinement 3 6 6 6` |
| `expansion-constants`. Enclose the constants used in the amplitude expansion. | Arguments: <cutoff>. | Rational constant intervals and cutoff-dependent errors. | `nfield weighted-remainder-state expansion-constants 6` |
| `harmonic-expansion`. Expand a conductor's harmonic seed with an explicit error. | Arguments: <conductor> <cutoff>. | Leading terms, seed interval and a uniform remainder bound. | `nfield weighted-remainder-state harmonic-expansion 3 6` |
| `amplitude-expansion`. Resolve a full conductor amplitude into its leading terms. | Arguments: <conductor> <cutoff>. | Amplitude interval, expansion terms and remainder bounds. | `nfield weighted-remainder-state amplitude-expansion 3 6` |
| `deficit-series`. Enclose a positive Dirichlet deficit series. | Arguments: <rational-exponent> <cutoff>. | Exact finite prefix and full-series rational bounds. | `nfield weighted-remainder-state deficit-series 2 6` |
| `deficit-diagnostic`. Compare deficit positivity at two specified exponents. | Arguments: <cutoff>. | Finite prefixes, enclosures and positive comparison quantities. | `nfield weighted-remainder-state deficit-diagnostic 6` |
| `spectral-product`. Enclose the full spectral Euler-product constant. | Arguments: <prime-cutoff>. | Exact rational lower and upper product bounds. | `nfield weighted-remainder-state spectral-product 7` |
| `spectral-mean`. Compute finite spectral means at a rational scale. | Arguments: <rational-x> <prime-cutoff>. | Finite harmonic and signed-correction means with full prime-moment bounds. | `nfield weighted-remainder-state spectral-mean 12 7` |
| `spectral-energy`. Enclose the energy of one full conductor. | Arguments: <conductor> <period-cutoff>. | Amplitude and energy intervals, with finite-prefix lower endpoints. | `nfield weighted-remainder-state spectral-energy 3 6` |
| `spectral-tail`. Price omitted conductors and their leading terms. | Arguments: <Q> <B> <M> <P> <N>. | Rational full-tail bounds and explicitly cut off leading approximations. | `nfield weighted-remainder-state spectral-tail 3 4 6 7 6` |
| `character-phase`. Enclose a specified root-of-unity phase. | Arguments: <denominator> <numerator>. | Rational lower and upper real and imaginary coordinates. | `nfield weighted-remainder-state character-phase 5 1` |
| `character-table`. List the finite characters of a chosen modulus. | Arguments: <modulus>. | Group structure, character coordinates and parity data. | `nfield weighted-remainder-state character-table 5` |
| `character-l`. Enclose the L-value of a specified odd character. | Arguments: <modulus> <odd-index> <series-cutoff>. | Character metadata, complex L-value intervals and truncation bounds. | `nfield weighted-remainder-state character-l 5 1 6` |
| `mixed-moment`. Enclose mixed short-sum and L-value moments. | Arguments: <modulus> <series-cutoff> <zeta-cutoff> <period-cutoff>. | Complex channel moments and rational error budgets. | `nfield weighted-remainder-state mixed-moment 5 6 6 6` |
| `cotangent-sums`. Evaluate finite cotangent sums with certified bounds. | Arguments: <modulus> <series-cutoff> <zeta-cutoff>. | Exact or enclosed cotangent-weighted quantities and comparison errors. | `nfield weighted-remainder-state cotangent-sums 5 6 6` |
| `harmonic-polylog`. Enclose the harmonic polylogarithm at your complex point. | Arguments: <real> <imaginary> <series-cutoff>. | Rational real and imaginary intervals with a series-tail bound. | `nfield weighted-remainder-state harmonic-polylog 1/4 1/4 6` |
| `harmonic-root`. Evaluate a harmonic series at a chosen root of unity. | Arguments: <denominator> <numerator> <series-cutoff> <zeta-cutoff>. | Root-phase, harmonic value and explicit interval errors. | `nfield weighted-remainder-state harmonic-root 5 1 6 6` |
| `harmonic-root-average`. Average harmonic values over a finite root system. | Arguments: <modulus> <series-cutoff>. | Exact or enclosed root average and finite-prefix error. | `nfield weighted-remainder-state harmonic-root-average 5 6` |
| `sine-transform`. Compute a finite sine transform at a signed frequency. | Arguments: <modulus> <signed-frequency>. | Exact finite transform data and rational numerical enclosures. | `nfield weighted-remainder-state sine-transform 5 1` |
| `small-amplitudes`. Resolve the low-conductor amplitudes with explicit cutoffs. | Arguments: <series-cutoff> <zeta-cutoff>. | Rational enclosures for the displayed small-conductor amplitudes. | `nfield weighted-remainder-state small-amplitudes 6 6` |
| `alignment`. Enclose full reset and alignment readings of a supplied modulus. | Arguments: <modulus> <M> <N> <P>. | Exact factor data, finite sums and full rational alignment bounds. | `nfield weighted-remainder-state alignment 12 6 6 6` |
| `alignment-local`. Compute one prime-power alignment factor. | Arguments: <prime> <valuation>. | Exact local factor and valuation-dependent correction. | `nfield weighted-remainder-state alignment-local 3 2` |
| `harmonic-local`. Enclose the harmonic factor attached to one period. | Arguments: <period> <constant-cutoff>. | Rational local constant and harmonic bounds. | `nfield weighted-remainder-state harmonic-local 6 6` |
| `alignment-lcm`. Evaluate alignment on a least-common-multiple scale. | Arguments: <scale> <M> <N> <P>. | Constructed modulus, prime factors and full alignment bounds. | `nfield weighted-remainder-state alignment-lcm 6 6 6 6` |
| `alignment-growth`. Compare alignment before and after a chosen scale change. | Arguments: <modulus> <scale> <M> <N> <P>. | Prime products, bounded leading terms and normalized losses when defined. | `nfield weighted-remainder-state alignment-growth 12 6 6 6 6` |
| `law-moment`. Compute an exact moment of the finite stationary law. | Arguments: <M> <degree>. | Exact moment, full-law bounds and cutoff error. | `nfield weighted-remainder-state law-moment 4 2` |
| `law-cdf`. Bound a full-law cumulative probability from a finite quotient. | Arguments: <M> <threshold> <margin>. | Finite CDF and lower and upper probability bounds. | `nfield weighted-remainder-state law-cdf 4 0 1/10` |
| `law-window`. Bound the probability of a specified closed window. | Arguments: <M> <lower> <upper> <margin>. | Finite window mass and full-law bounds with the supplied margin. | `nfield weighted-remainder-state law-window 4 -1/4 1/4 1/10` |
| `law-concentration`. Find the heaviest finite window at a chosen width. | Arguments: <M> <width> <margin>. | Maximizing window, exact finite mass and full concentration bounds. | `nfield weighted-remainder-state law-concentration 4 1/4 1/10` |
| `law-characteristic`. Enclose the law's characteristic function. | Arguments: <M> <frequency>. | Directed real and imaginary intervals and an explicit cutoff error. | `nfield weighted-remainder-state law-characteristic 4 1` |
| `law-recurrence`. Measure finite returns into a specified value window. | Arguments: <M> <lower> <upper> <horizon>. | Exact finite recurrence data and error through the chosen horizon. | `nfield weighted-remainder-state law-recurrence 4 -1/4 1/4 10` |
| `law-tail-bound`. Enclose a one-sided stationary tail. | Arguments: <M> <threshold> <modulus>. | Lower and upper tail probability, variance and cylinder-mean bounds. | `nfield weighted-remainder-state law-tail-bound 4 1/4 2` |
| `law-activation`. Measure the activation supplied by a selected prime block. | Arguments: <prime-cutoff> <block-length> <width>. | Prime population, reset increments and an interval-probability bound. | `nfield weighted-remainder-state law-activation 11 2 1/100` |
| `clock-difference`. Compare retained and completed clocks at one address. | Arguments: <M> <address>. | Exact finite difference and complete-error bounds. | `nfield weighted-remainder-state clock-difference 6 17` |
| `mass-inverse`. Recover period weights from supplied conductor amplitudes. | Arguments: <cutoff> <period> [q:amplitude ...]. | Exact finite inverse weights and reconstruction data. | `nfield weighted-remainder-state mass-inverse 6 2 2:1/4 3:1/9` |
| `mass-recovery`. Enclose a period weight recovered from conductor data. | Arguments: <period> <conductor-cutoff> <period-cutoff>. | Finite recovered mass and explicit omitted-conductor bounds. | `nfield weighted-remainder-state mass-recovery 2 6 6` |
| `perturbation`. Test the effect of a small signed weight perturbation. | Arguments: <cutoff> <address> <epsilon>. | Perturbed masses, clocks, forcing and variance differences. | `nfield weighted-remainder-state perturbation 6 5 1/100` |
| `cycle`. Compare orbit and Cesaro masses on a chosen residue cycle. | Arguments: <period> <residue> <address> <last>. | Exact stationary and finite-time masses and residue transitions. | `nfield weighted-remainder-state cycle 3 1 5 10` |
| `cycle-tv`. Bound finite-time convergence of retained cycles. | Arguments: <cutoff> <last>. | Exact total-variation terms and an omitted-mass bound. | `nfield weighted-remainder-state cycle-tv 6 10` |
| `covariance`. Measure the overlap of two periodic age clocks. | Arguments: <first> <second>. | Exact rational covariance and period data. | `nfield weighted-remainder-state covariance 3 4` |
| `amplitude`. Enclose the full amplitude of one conductor. | Arguments: <conductor> <cutoff>. | Exact lower and upper amplitude bounds and interval width. | `nfield weighted-remainder-state amplitude 2 2` |
| `tree`. Enumerate the coprime mass tree through a chosen cutoff. | Arguments: <cutoff>. | Exact square mass, outgoing mass and harmonic upper bounds. | `nfield weighted-remainder-state tree 6` |
| `tree-node`. Read one coprime mass-tree node. | Arguments: <first> <second>. | Exact node mass and its child contributions. | `nfield weighted-remainder-state tree-node 2 3` |
| `weight`. Compute a period's primitive weight and finite inverse. | Arguments: <period>. | Exact rational weight and its Mobius reconstruction. | `nfield weighted-remainder-state weight 6` |
| `budget`. Price the reciprocal-address divisor budget. | Arguments: <resolution>. | Exact divisor sum and its finite resolution. | `nfield weighted-remainder-state budget 6` |
| `mass`. Separate retained mass from its complete unit-mass complement. | Arguments: <cutoff>. | Exact retained mass, complement, first moment and deficit bound. | `nfield weighted-remainder-state mass 6` |
| `sawtooth`. Evaluate one centered sawtooth row. | Arguments: <period> <slope> <residue>. | Exact rational value at the canonicalized signed residue. | `nfield weighted-remainder-state sawtooth 5 2 3` |
| `dedekind`. Compute an exact Dedekind sum. | Arguments: <period> <slope>. | Rational sum for the supplied period and unit slope. | `nfield weighted-remainder-state dedekind 5 2` |
| `gram`. Compute the exact pairing of two sawtooth rows. | Arguments: <first-period> <first-slope> <second-period> <second-slope>. | Rational Gram entry, retaining any common period factor. | `nfield weighted-remainder-state gram 3 1 4 1` |
| `sawtooth-mean`. Measure a sawtooth on a specified residue cylinder. | Arguments: <period> <slope> <cylinder-period> <residue>. | Exact conditional mean on the admitted cylinder. | `nfield weighted-remainder-state sawtooth-mean 6 1 3 1` |
| `reset`. Read the complete reset increment at a finite resolution. | Arguments: <resolution>. | Exact rational reset increment. | `nfield weighted-remainder-state reset 1` |
| `pairing`. Enclose a finite clock-cylinder pairing. | Arguments: <length> <period> <residue> <cutoff>. | Finite average, Haar center, radius and complete bounds. | `nfield weighted-remainder-state pairing 6 2 0 2` |
| `forcing`. Compute the full reset forcing at a chosen address. | Arguments: <resolution>. | Exact rational forcing from the complete mass system. | `nfield weighted-remainder-state forcing 6` |
| `block`. Accumulate a signed block of reset forcing. | Arguments: <start> <length>. | Exact block sum and the corresponding deficit difference. | `nfield weighted-remainder-state block 6 4` |
| `crt`. Intersect your own periodic residue conditions. | Arguments: [period:shift ...]. | Compatibility, combined period, canonical residue and Haar probability. | `nfield weighted-remainder-state crt 4:0 6:2` |
| `moment`. Compute a finite mixed moment of shifted clocks. | Arguments: <length> <f\|g> [shift:power ...]. | Exact rational moment for the selected shifts and powers. | `nfield weighted-remainder-state moment 6 g 0:1 1:2` |
| `haar-moment`. Compute a finite Haar moment of shifted reset fields. | Arguments: <cutoff> [shift ...]. | Exact rational moment over the complete finite quotient. | `nfield weighted-remainder-state haar-moment 4 0 1` |
| `cylinder`. Enclose the clock mean on a chosen residue cylinder. | Arguments: <modulus> <address> <cutoff>. | Finite alignment and mean with complete rational bounds. | `nfield weighted-remainder-state cylinder 2 0 2` |
| `position`. Bound exceedance probability inside a residue cylinder. | Arguments: <modulus> <address> <cutoff> <threshold>. | Relative-gap and exceedance-probability intervals. | `nfield weighted-remainder-state position 2 1 2 1/2` |
| `position-weight`. Resolve a period's contribution inside a cylinder. | Arguments: <modulus> <address> <period> <cutoff>. | Exact conditional weight and finite-cutoff comparison. | `nfield weighted-remainder-state position-weight 2 1 2 2` |
| `conductor-full`. Enclose a conductor-truncated reading at any integer address. | Arguments: <Q> <address> <M>. | Value, endpoint and gap intervals with the full period. | `nfield weighted-remainder-state conductor-full 2 -1 2` |
| `conductor-beta`. Enclose the coefficient of one conductor row. | Arguments: <d> <Q> <M>. | Rational lower and upper coefficient bounds. | `nfield weighted-remainder-state conductor-beta 2 2 2` |
| `conductor-prime`. Construct an exact prime-selected CRT address. | Arguments: <Q> <prime>. | Combined period, candidate residue and its symbolic gap. | `nfield weighted-remainder-state conductor-prime 7 7` |
| `conductor-extrema`. Enclose the extrema over a complete conductor period. | Arguments: <Q> <M>. | Minimum and maximum intervals and the unresolved gap. | `nfield weighted-remainder-state conductor-extrema 7 240` |
| `conductor-minimizers`. List every address not excluded as a minimizer. | Arguments: <Q> <M>. | Candidate residues and rigorous value intervals; overlapping candidates stay unresolved. | `nfield weighted-remainder-state conductor-minimizers 7 240` |
| `activation`. Measure an increasing event on your finite probability cube. | Arguments: <n> <a> <u> <v> <probabilities> <values>. | Exact event and coupled probabilities, active-count moments and Sperner bounds. | `nfield weighted-remainder-state activation 2 1 1 1 1/2,1/3 0,1,1,2` |

### capacity-resolution

Measure how capacity changes with integer resolution and the observation window.

**Inputs.** Resolution and truncation, dyadic window, progression or sample count.

**Result.** Capacity, diagonal/residual terms, boundary corrections and finite conditional means.

```sh
nfield capacity-resolution inspect 30 60
```

Inspect one resolution, then use sample for CSV over a window or progression to condition by residue class.

**Scope.** Long-double numerical evaluations. Prime observations use continuous capacity at p-1, not finite digit-grid energy.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `constants` (reference). Read the centering constants used by the capacity model. | Fixed reference inputs; no model parameters. | Named numerical zeta-derived constants. | `nfield capacity-resolution constants` |
| `inspect`. Separate a capacity reading into its diagonal and residual. | Arguments: n [M]. | Capacity, deficit, diagonal, centered value, cutoff field and boundary correction. | `nfield capacity-resolution inspect 12 6` |
| `window`. Compare capacity statistics on integers and prime predecessors. | Arguments: X. | Population, means, second moments and variance on the chosen dyadic window. | `nfield capacity-resolution window 12` |
| `sample`. Export capacity samples across a chosen window. | Arguments: X M count. | Address, phase, diagonal, residual, correction and prime-predecessor flag. | `nfield capacity-resolution sample 12 6 4` |
| `unit`. Compare the unit-phase and full finite variance. | Arguments: M. | Retained mass, mean, unit variance, character moment and Haar variance. | `nfield capacity-resolution unit 6` |
| `spectrum`. Resolve a finite capacity by conductor. | Arguments: n M. | Conductor amplitude, row value, contribution and endpoint classification. | `nfield capacity-resolution spectrum 12 6` |
| `progression`. Measure the conditional capacity mean on an arithmetic progression. | Arguments: X L a. | Selected population, conditional means and progression parameters. | `nfield capacity-resolution progression 12 3 1` |

### capacity-generation

Construct capacity from explicit digit sources, carry cells and finite recovery data.

**Inputs.** Source base/lag, carry residues, rational amplitudes, finite cutoff or profile coefficients.

**Result.** Exact source rows, carry covariance, recovered weights, rational bounds and profile values.

```sh
nfield capacity-generation source 3 1
```

Build a source, inspect its carry response, then ledger/refine to examine how primitive weights are assembled.

**Scope.** Limits and positivity hypotheses differ by action. A raw profile is not automatically positive or normalized.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `source`. Compare original digit cells and their straightened rows. | Arguments: base lag [phase]. | Exact cell response and affine sample at each selected phase. | `nfield capacity-generation source 3 1 2` |
| `carry`. Resolve the covariance of a unit carry triple. | Arguments: modulus a b. | Row and carry variance, parent and child pairings and midpoint defect. | `nfield capacity-generation carry 7 1 2` |
| `measurement`. Compare local power measurements with a quartic control. | Modulus m, two addresses a and b, an integer power, and rational amplitude. | Exact local-power and nonlocal-control responses for your amplitude. | `nfield capacity-generation measurement 7 1 2 4 1/2` |
| `ledger`. Recover primitive weights from finite capacity values. | Arguments: cutoff. | Capacity, weight, recovered weight, row value and increment at each cutoff. | `nfield capacity-generation ledger 6` |
| `refine`. Compute the child masses of a Farey interval. | Arguments: a b. | Exact endpoints, mediant and parent and child masses. | `nfield capacity-generation refine 2 3` |
| `control`. Construct a normalized finite perturbation with two prime markers. | Arguments: r s cutoff. | Signed changes in mass, row and capacity at each cutoff. | `nfield capacity-generation control 7 11 12` |
| `current`. Recover formal prime-log coefficients of the source. | Arguments: cutoff [r s]. | Exact coefficient for each nonzero prime term at each cutoff. | `nfield capacity-generation current 12` |
| `seed`. Enclose a harmonic seed and selector. | Arguments: q length. | Rational seed and selector intervals at the chosen period and length. | `nfield capacity-generation seed 3 6` |
| `profile`. Evaluate a supplied symmetric polynomial angular profile. | Arguments: period lambda c0,c1,.... | Exact primitive, row and grid readings. | `nfield capacity-generation profile 3 1/2 1,0,1` |
| `lattice`. Enclose a positive rational lattice seed. | Arguments: x cutoff. | Finite prefix, upper tail bound and reciprocal comparison. | `nfield capacity-generation lattice 1/2 6` |

### collision-sampling

Compare continuous collision work with a specified finite sampler and resolve its error by carriers.

**Inputs.** Odd prime or source cutoff, sampling grid/shift, carrier and explicit finite prefixes.

**Result.** Exact capacity, sampled work, contact and carrier decompositions; selected transforms are numerical.

```sh
nfield collision-sampling inspect 7
```

Inspect the defect first; carrier and prefix localize contributions, grid changes the observation, and source/decomposition retain the original source.

**Scope.** Most prime operations use 3..251. The sampled action has a larger domain with numerical capacity; finite output does not prove the global rate.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Resolve a prime-square sampling defect into its exact components. | Arguments: <odd-prime>. | Exact sampled, reservoir, alias and common-contact quantities. | `nfield collision-sampling inspect 7` |
| `sampled`. Measure the prime-square sampled energy directly. | Arguments: <odd-prime>. | Exact sampled energy and numerical continuous-capacity comparison. | `nfield collision-sampling sampled 7` |
| `carrier`. Inspect one carrier's contribution to the sampling defect. | Arguments: <odd-prime> <k>. | Exact carrier work, reservoir, aliases and displacement. | `nfield collision-sampling carrier 7 3` |
| `poles`. Separate the two collision-energy poles. | Arguments: <odd-prime>. | Exact diagonal and pole masses and their sum. | `nfield collision-sampling poles 7` |
| `collar`. Measure mass in a specified cutoff collar. | Arguments: <odd-prime> <displacement-cutoff>. | Exact absolute and signed collar masses. | `nfield collision-sampling collar 7 3` |
| `prefix`. Read a truncated carrier contribution. | Arguments: <odd-prime> <k> <X>. | Exact rational prefix value. | `nfield collision-sampling prefix 7 3 2` |
| `correlation`. Compute a finite sawtooth correlation. | Arguments: <k> <prefix> <slope>. | Exact rational correlation at the chosen slope and prefix. | `nfield collision-sampling correlation 5 3 2` |
| `state`. Read the burden and fresh contribution of one source state. | Arguments: <odd-prime> <X>. | Exact burden and fresh work. | `nfield collision-sampling state 7 3` |
| `switching`. Compare a source under your selected carrier mask. | Arguments: <odd-prime> [--carriers 2,3,...]. | Exact switched components with the omitted carrier work retained. | `nfield collision-sampling switching 7 --carriers 2,3` |
| `convolution`. Resolve primitive and full source convolution. | Arguments: <odd-prime> <X>. | Exact primitive, full and elementary values. | `nfield collision-sampling convolution 7 3` |
| `capacity`. Compute the continuous capacity at a finite cutoff. | Arguments: <N>. | Exact rational continuous energy. | `nfield collision-sampling capacity 6` |
| `dedekind`. Evaluate the Dedekind pairing used by a collision carrier. | Arguments: <modulus> <slope>. | Exact rational Dedekind sum. | `nfield collision-sampling dedekind 5 2` |
| `transform`. Evaluate the full and unit inverse-frequency transforms. | Arguments: <modulus> <frequency>. | Complex transforms, inverse-series reading and numerical errors. | `nfield collision-sampling transform 5 2` |
| `inverse`. Enclose an inverse-frequency prefix. | Arguments: <modulus> <frequency> <X>. | Exact prefix, harmonic prefix and a rigorous tail bound. | `nfield collision-sampling inverse 5 2 6` |
| `grid`. Sample a finite source on your chosen shifted grid. | Arguments: N q shift. | Exact continuous and sampled work with endpoint corrections. | `nfield collision-sampling grid 4 9 0` |
| `source`. Read a finite source at a rational address. | Arguments: N k Q. | Exact source value, including its assigned reset reading. | `nfield collision-sampling source 4 9 2` |
| `decomposition`. Separate a prime-square source by its stopping threshold. | Arguments: prime H. | Exact small-pair, first-cost, remainder, stopped-cost and terminal contributions. | `nfield collision-sampling decomposition 7 2` |
| `descent`. Follow a coprime pair through its Euclidean descent. | Arguments: k c H. | Quotients, remainders and exact descent contributions. | `nfield collision-sampling descent 7 2 4` |
| `prefix-word`. Resolve a signed source prefix into its finite word. | Arguments: A B. | Exact prefix word and accumulated response. | `nfield collision-sampling prefix-word 7 2` |
| `prefix-population`. Count source-prefix states over a chosen range. | Arguments: first last. | State populations and exact aggregate prefix statistics. | `nfield collision-sampling prefix-population 2 4` |
| `stopped-cost`. Price a stopped descent at every residue of a modulus. | Arguments: modulus threshold. | Exact costs and terminal contributions, retaining nonunits and endpoint jumps. | `nfield collision-sampling stopped-cost 7 2` |
| `fold`. Compute one folded arithmetic contribution. | Arguments: A B u e Q L. | Exact folded coefficients and signed prefix work. | `nfield collision-sampling fold 4 1 7 2 3 2` |
| `folded-source`. Evaluate the source after a specified arithmetic fold. | Arguments: L Q K u e. | Exact folded source reading and correction terms. | `nfield collision-sampling folded-source 4 10 3 7 2` |
| `rectangle`. Price a finite source rectangle with its boundary convention. | Arguments: Q X Y parity. | Exact rectangular work and boundary contributions. | `nfield collision-sampling rectangle 10 2 3 0` |
| `cubic`. Extract the finite cubic sampling quantities at a prime. | Arguments: prime. | Exact cubic components and common-reset correction. | `nfield collision-sampling cubic 7` |
| `dedekind-mass`. Compute the finite Dedekind mass of a source cutoff. | Arguments: modulus. | Exact total mass and component readings. | `nfield collision-sampling dedekind-mass 6` |
| `phase-sum`. Accumulate a reciprocal-phase sawtooth sum over your interval. | Arguments: gamma X beta first last. | Exact signed sum and rational derivative-range bounds through order fourteen. | `nfield collision-sampling phase-sum 0 4 0 2 6` |
| `completion`. Complete a supplied cyclic reading against the inverse source. | Arguments: N k Q weights. | Exact completed-source sum and cyclic variation of your weights. | `nfield collision-sampling completion 4 3 10 0,1,-1` |
| `kernel`. Read the arithmetic boundary kernel at a chosen pair and grid. | Arguments: Q left right. | Exact rational boundary-kernel value. | `nfield collision-sampling kernel 5 2 3` |
| `shells`. Resolve arithmetic kernel work through a finite cutoff. | Arguments: Q cutoff. | Exact primitive shells, square prefixes and prime-log coefficients. | `nfield collision-sampling shells 5 4` |
| `reciprocal`. Compare reciprocal readings at a coprime pair. | Arguments: left right numerator. | Exact reciprocal transform and signed correction. | `nfield collision-sampling reciprocal 3 4 1` |
| `interior`. Measure the interior contribution at an admitted prime. | Arguments: prime. | Exact or bounded interior work with the boundary retained separately. | `nfield collision-sampling interior 257` |

### boundary-spectrum

Transform a boundary or weighted cell rule on a complete finite unit group.

**Inputs.** Modulus and selected cells or signed/complex cell weights; optional character index.

**Result.** Character phases, conductors, transformed values, energies and factorization residuals.

```sh
nfield boundary-spectrum inspect 9 --support 0,4,8
```

Use inspect for the full transform and channel to examine a selected CRT-indexed character.

**Scope.** Moduli 2..512, including noncyclic unit groups. Complex transforms are numerical; not every composite modulus has a prime-power flux factorization.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Resolve a supplied boundary into all finite character channels. | Arguments: <modulus> --support <cells\|none>. | Boundary coefficients, conductor energies and total work. | `nfield boundary-spectrum inspect 9 --support 0,1` |
| `channel`. Read one character channel of a supplied boundary. | Arguments: <modulus> <index> --support <cells\|none>. | Complex channel response and conductor information. | `nfield boundary-spectrum channel 9 1 --support 0,1` |

### short-sum-bernoulli-correlation

Compare finite short sums with Bernoulli character values at your chosen prime base.

**Inputs.** Odd prime base for moments.

**Result.** Normalized moments, the twist at two and variance from finite Bernoulli sums.

```sh
nfield short-sum-bernoulli-correlation moments 5
```

Repeat moments across supported bases; use the separate ledger check for the recorded reference rows.

**Scope.** Odd prime bases 5..127; finite character moments do not establish their limiting correlation.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `moments`. Measure how short sums and L-values vary together. | Arguments: <base>. | Magnitude means, second and mixed moments and correlation quantities. | `nfield short-sum-bernoulli-correlation moments 7` |

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `ledger` | `nfield verify short-sum-bernoulli-correlation ledger [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |

### primitive-character-cancellation

Inspect which lower congruence fibers cancel for a chosen primitive odd character.

**Inputs.** Base, lag and character index in the documented prime-power coordinates.

**Result.** Rows of character, depth, residue, fiber size and complex sum, followed by cancellation residuals.

```sh
nfield primitive-character-cancellation inspect 3 1 1
```

Choose one character and examine all its lower fibers before comparing another conductor.

**Scope.** Membership is exact; complex character sums use long-double roots of unity.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Resolve one primitive odd character's cancellation. | Arguments: <base> <lag> <character-index>. | Rows of character, depth, residue, fiber size and complex sum, followed by cancellation residuals. | `nfield primitive-character-cancellation inspect 5 1 1` |

### periodic-zeta-factorization

Evaluate a finite periodic-zeta collision model at a chosen complex argument.

**Inputs.** Base, lag, primitive odd character index, real part and imaginary part.

**Result.** Unit/nonunit sums, centered transform, factorized values and residuals.

```sh
nfield periodic-zeta-factorization inspect 3 1 1 --sigma 0.5 --tau 0
```

Vary sigma or tau on the same channel, keeping the finite model and numerical error report together.

**Scope.** Base^(lag+1)<=4096; Lanczos/Euler-Maclaurin values are numerical, with no zero-location or uniform estimate certified.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Compare two complex factorizations at your chosen strip point. | Arguments: <base> <lag> <character-index> [--sigma <x>] [--tau <y>]. | Direct transform, periodic-zeta and L-value readings with numerical errors. | `nfield periodic-zeta-factorization inspect 5 1 1 --sigma 0.5 --tau 0.2` |

### collision-boundary-recovery

Recover a collision coefficient from a character boundary reading and compare the two boundary orientations.

**Inputs.** Base, lag and primitive odd character index.

**Result.** Direct left/right transforms, Bernoulli/Gauss expressions and eligible collision recovery.

```sh
nfield collision-boundary-recovery inspect 3 1 1
```

Use one channel to compare the left and right readings before combining them with an active-channel classification.

**Scope.** Base^(lag+1)<=4096. Logarithms, cotangents and roots of unity are numerical.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Recover both endpoints of a primitive odd collision channel. | Arguments: <base> <lag> <character-index>. | Direct, Bernoulli, Gauss and cotangent values with relative errors. | `nfield collision-boundary-recovery inspect 5 1 1` |

### active-collision-channel

Determine whether a character channel is visible to the chosen collision boundary.

**Inputs.** Base, lag and character index, or a census over the eligible characters.

**Result.** Finite diagonal boundary and active/inactive classification.

```sh
nfield active-collision-channel census 3 1
```

Use census to find channels, then inspect a specific index and examine its factorization.

**Scope.** The finite visibility gate does not search for or certify L-function zeros.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Decide whether a specified finite collision channel is active. | Arguments: <base> <lag> <character-index>. | Complex boundary amplitude, magnitude and active/inactive classification. | `nfield active-collision-channel inspect 5 1 1` |
| `census`. Measure the active channel population for a finite model. | Arguments: <base> <lag>. | Primitive count, active count, smallest active magnitude and conjugate residual. | `nfield active-collision-channel census 5 2` |

### collision-coordinate

Compute a multiplier's collision count from its exact coordinate and inspect zero-collision multipliers.

**Inputs.** Modulus or prime, multiplier and digit base.

**Result.** Coordinate, direct count, conjugation data and the rational zero family.

```sh
nfield collision-coordinate inspect 13 2 --base 10
```

Inspect one multiplier, gate for the full zero family, or conjugation for a composite coprime modulus.

**Scope.** Prime coordinate formulas and composite conjugation have different domains; the command checks eligibility.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `conjugation`. Compare digit bins through multiplication by the base. | Arguments: <N> <g> [--base <b>]. | Direct collision count and transformed congruence count. | `nfield collision-coordinate conjugation 21 8 --base 10` |
| `inspect`. Compute a multiplier's wrapping coordinate and collision count. | Arguments: <p> <g> [--base <b>]. | Coordinate, wrapping population and direct and reconstructed counts. | `nfield collision-coordinate inspect 13 6 --base 10` |
| `gate`. Count the collision-free multipliers of a prime field. | Arguments: <p> [--base <b>]. | Observed zero population and the exact gate width. | `nfield collision-coordinate gate 13 --base 10` |

### finite-determination

Reduce a large eligible integer's collision value to its finite residue class.

**Inputs.** Integer N, digit base and lag.

**Result.** Direct deviation, determining modulus, residue-table value and optional minimal-modulus witnesses.

```sh
nfield finite-determination inspect 113 --base 10 --lag 1
```

Compare integers differing by b^(lag+1); optimal shows witnesses against a smaller base power.

**Scope.** N must be coprime to the base for this unit-table operation; all-prime-collision-label handles base primes separately.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Compute an integer's collision label from its finite determining modulus. | Arguments: <N> [--base <b>] [--lag <ell>]. | Modulus, diagonal slices, direct count and finite-table label. | `nfield finite-determination inspect 191 --base 10 --lag 1` |
| `optimal`. Construct two classes that distinguish successive determining powers. | Arguments: [--base <b>] [--lag <ell>]. | Witness classes, their common coarse residue and distinct collision values. | `nfield finite-determination optimal --base 10 --lag 2` |

### reflection-identity

Inspect the complementary collision values at a reflected pair of residue classes.

**Inputs.** Residue, base and lag, or the complete table action.

**Result.** Exact reflected pair values, their sum and the complete-table mean.

```sh
nfield reflection-identity inspect 13 --base 10 --lag 1
```

Use inspect for one pair, then table to inspect all unit pairs in the same modulus.

**Scope.** Reflection is in the specified finite modulus; endpoint conventions remain part of the identity.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Read a collision class together with its reflected class. | Arguments: <a> [--base <b>] [--lag <ell>]. | Both exact values, floor-complement count and endpoint information. | `nfield reflection-identity inspect 9 --base 10 --lag 1` |
| `table`. Measure the aggregate reflection statistics of a complete unit table. | Arguments: [--base <b>] [--lag <ell>]. | Unit population, exact table sum, mean and reflection-failure count. | `nfield reflection-identity table --base 10 --lag 1` |

### half-group

Count the wrapping residues on either side of a chosen interior cut.

**Inputs.** Modulus and interior cut index.

**Result.** The wrapping count and its complement-bijection comparison.

```sh
nfield half-group inspect 11 3
```

Move the cut while holding the modulus fixed to inspect how the pairing changes.

**Scope.** Only interior cuts in the admitted modulus domain are meaningful; endpoint cuts are excluded.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Count the units on one side of an interior multiplication cut. | Arguments: <m> <n>. | Totient, side population and reflected complement count. | `nfield half-group inspect 10 3` |

### all-prime-collision-label

Assign a collision label to a prime even when it divides the digit base.

**Inputs.** Prime, base and lag.

**Result.** The direct label and either its unit-table coordinate or base-prime zero case.

```sh
nfield all-prime-collision-label inspect 5 --base 10 --lag 1
```

Compare a base prime with a coprime prime using the same base and lag.

**Scope.** This labels the given prime; it does not predict which residue classes contain future primes.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Compute the collision label for an ordinary or exceptional prime. | Arguments: <p> [--base <b>] [--lag <ell>]. | Direct label, determining residue or exact exceptional value. | `nfield all-prime-collision-label inspect 13 --base 10 --lag 1` |

### finite-spectral-quotient

Compress a finite prime-label matrix while retaining its block action.

**Inputs.** Base, lag, number of primes and positive heat scale.

**Result.** Label populations, quotient matrix, bulk multiplicity, numerical modes and heat data.

```sh
nfield finite-spectral-quotient inspect 3 --prime-count 30 --tau 1
```

Compare prime populations at the same base, then inspect the quotient rather than building every matrix entry by hand.

**Scope.** Label populations are exact; inverse kernels and spectral values are numerical with reported tolerance.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Reduce a chosen prime-label system to its finite spectral quotient. | Arguments: <base> [--lag <ell>]. | Label states, multiplicities, quotient modes and numerical spectral residuals. | `nfield finite-spectral-quotient inspect 10 --lag 1 --prime-count 40 --tau 1` |

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `declared` | `nfield verify finite-spectral-quotient declared [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |

### finite-prefix-slice

Measure how a custom digit-prefix support is seen by an arithmetic sampling phase.

**Inputs.** Denominator, base, prefix depth and selected cells.

**Result.** Exact support/carry counts, bulk and endpoint corrections, or transport-collapse data.

```sh
nfield finite-prefix-slice inspect 11 --base 3 --depth 2 --support 0,4,8
```

Use inspect for a coprime phase, all to retain nonunits, and collapse to separate the persistent quotient.

**Scope.** b^N<=50000. The all action has a wider denominator domain than inspect/collision.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Evaluate a selected prefix support at one denominator. | Arguments: <q> --base <b> --depth <N>. | Finite support, sampled response and exact slice data. | `nfield finite-prefix-slice inspect 11 --base 3 --depth 2 --support 0,4,8` |
| `all`. Compute the prefix response at one denominator, including noncoprime base and denominator. | Arguments: <q> --base <b> --depth <N>. | Response, phase-kernel and divisor-related slice data at the requested denominator. | `nfield finite-prefix-slice all 12 --base 3 --depth 2 --support 0,4,8` |
| `collapse`. Find when positional transport loses its transient kernel. | Arguments: <q> --base <b>. | Supported and coprime denominator factors, collapse depth and stable image sizes. | `nfield finite-prefix-slice collapse 28 --base 10` |
| `collision`. Read the prefix support where two specified digits agree. | Arguments: <q> --base <b> --lag <ell>. | Selected cells, collision response and exact prefix-slice quantities. | `nfield finite-prefix-slice collision 11 --base 3 --lag 1` |

### oriented-digit-comparison

Separate ascent, equality and descent in a two-digit reading.

**Inputs.** Base and phase, or prime and row with optional height.

**Result.** Signed digit response, ramified energy and reconstructed ascent/equality/descent counts.

```sh
nfield oriented-digit-comparison inspect 5 5
```

Compare unit and nonunit phases, then trichotomy to combine orientation with mass and collision counts.

**Scope.** Orientation is sign(first digit-second digit); it is not an arbitrary digit-score function.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Compare the first and second digits at a chosen phase. | Arguments: <base> <phase>. | Signed response, divisor formula, phase class and boundary norm. | `nfield oriented-digit-comparison inspect 10 20` |
| `prime`. Resolve unit and ramified phase populations for a prime square. | Arguments: <odd-prime>. | Phase counts, responses and total nonzero-phase energy. | `nfield oriented-digit-comparison prime 5` |
| `trichotomy`. Count ascents, equalities and descents at finite height. | Arguments: <odd-prime> <row-index> [--height H]. | Direct and synthesized counts, collision mass and orientation. | `nfield oriented-digit-comparison trichotomy 5 2` |

### boundary-bernoulli-factorization

Resolve your prime-power cell support into visible boundary flux and conductor energies.

**Inputs.** Odd prime, depth, character exponent and selected support; correlation also takes two units.

**Result.** Boundary derivative, visible norm, Bernoulli transform, conductor energies and correlation data.

```sh
nfield boundary-bernoulli-factorization inspect 3 2 1 --support 0,4,8
```

Inspect a channel, use spectrum for all conductors, then correlation to compare selected unit shifts.

**Scope.** Cyclic odd prime powers p^depth<=20000. Counts are exact; complex transforms and conductor energies use numerical arithmetic.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Factor one chosen boundary-character response. | Arguments: <p> <depth> <exponent>. | Boundary amplitude, Bernoulli factor and numerical comparison. | `nfield boundary-bernoulli-factorization inspect 3 2 1 --support 0,4,8` |
| `terminal`. Read a first-digit/last-digit collision boundary. | Arguments: <p> <depth> <exponent>. | Terminal support and its factored character response. | `nfield boundary-bernoulli-factorization terminal 3 2 1` |
| `spectrum`. Measure boundary energy by conductor depth. | Arguments: <p> <depth>. | Channel populations, per-depth energies, total work and Parseval residual. | `nfield boundary-bernoulli-factorization spectrum 3 2 --support 0,4,8` |
| `correlation`. Compute the unit sawtooth pairing of two indices. | Arguments: <p> <depth> <x> <y>. | Direct correlation, Mobius-Dedekind value and numerical error. | `nfield boundary-bernoulli-factorization correlation 3 2 1 2` |

### boundary-conductor-ledger

Find where the energy of a finite cell boundary sits among exact conductors.

**Inputs.** Modulus and indicator support, or base/depth for terminal collision support.

**Result.** Signed boundary, divisor pushdowns, primitive moments and exact conductor energies.

```sh
nfield boundary-conductor-ledger inspect 9 --support 0,4,8
```

Inspect a custom support and compare its proper pushdowns with the top-conductor contribution.

**Scope.** Modulus 3..200000. CLI input is an indicator support; the library also supports bounded integer weights.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Resolve your chosen support into its conductor contributions. | Arguments: <modulus>. | Boundary row, complete conductor ledger and exact finite totals. | `nfield boundary-conductor-ledger inspect 9 --support 0,4,8` |
| `terminal`. Resolve a terminal-digit collision support by conductor. | Arguments: <base> <depth>. | Constructed boundary and complete conductor contribution table. | `nfield boundary-conductor-ledger terminal 15 2` |

### finite-state-orbit-boundary

Run your own digit-reading automaton along a remainder orbit.

**Inputs.** Base, modulus, state count, initial states and a transition table with accepting states or integer weights.

**Result.** Product orbit, transient, cycle, emitted-state readings and predecessor boundary.

```sh
nfield finite-state-orbit-boundary inspect 2 7 2 1 0 --transition 0,1,1,0 --accepting 1
```

Try parity first, then replace the transition table or state weights with a different finite digit rule.

**Scope.** Coprime base/modulus, base<=64, states<=32 and modulus*states<=4096. A dynamical boundary differs from a full-residue additive boundary.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `parity`. Trace the parity automaton along a rational remainder orbit. | Arguments: <base> <modulus> <start-R>. | Orbit states, parity readings and boundary Fourier data. | `nfield finite-state-orbit-boundary parity 2 7 1` |
| `inspect`. Run your own finite automaton on a rational digit orbit. | Arguments: <base> <modulus> <states>. | Product-orbit states, accepting or weighted readings and boundary response. | `nfield finite-state-orbit-boundary inspect 2 7 2 1 0 --transition 0,1,1,0 --accepting 1` |

### full-orbit-energy

Compute the boundary energy of a full prime-power remainder orbit.

**Inputs.** Base, odd prime and exponent.

**Result.** Multiplicative order, orbit support, thickness, conductor spectrum and exact total energy.

```sh
nfield full-orbit-energy inspect 2 3 2
```

Compare prime-power depths while retaining a base that generates the complete unit group.

**Scope.** The base must be primitive at the requested prime power; coset energies do not follow from the full-orbit law.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Measure the energy of a full prime-power orbit. | Arguments: <base> <p> <depth>. | Orbit size, local thickness and exact full-orbit energy. | `nfield full-orbit-energy inspect 2 3 2` |

### quadratic-orbit-energy

Remove the resonant quadratic channel and measure the remaining subgroup energy.

**Inputs.** Odd prime.

**Result.** Quadratic subgroup, boundary, resonance and exact off-resonance energy.

```sh
nfield quadratic-orbit-energy inspect 7
```

Compare primes in different residue classes modulo eight.

**Scope.** This is the index-two subgroup at prime modulus; higher-index subgroup energy uses a different calculation.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Measure the energy carried by the quadratic orbit. | Arguments: <odd-prime>. | Quadratic orbit population, exact energy and mod-eight comparison. | `nfield quadratic-orbit-energy inspect 7` |

### subgroup-jacobi-expansion

Resolve a subgroup boundary flux into quotient-character contributions.

**Inputs.** Prime modulus, subgroup generator and odd character exponent.

**Result.** Subgroup order/index, annihilator, resonance class, direct flux and Jacobi-type expansion.

```sh
nfield subgroup-jacobi-expansion inspect 7 2 1
```

Change the generator or character to compare resonance and off-resonance on the same prime field.

**Scope.** Subgroup membership is exact; roots of unity and flux sums are numerical. No general higher-index closed energy law is implied.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Resolve an odd character against a multiplicative subgroup. | Arguments: <p> <base> <odd-exponent>. | Subgroup order, resonance classification, direct flux and Jacobi expansion. | `nfield subgroup-jacobi-expansion inspect 7 2 1` |

### prime-base-collision-energy

Compute collision energy and identify which finite carry or pole terms contribute.

**Inputs.** Odd prime digit base.

**Result.** Carry-table energy, exact Dedekind dictionary and diagonal/upper/lower pole masses.

```sh
nfield prime-base-collision-energy inspect 5
```

Use inspect for the total and poles for the mass split; compare with arithmetic-boundary-defect for a normalized residual.

**Scope.** Inspection accepts odd prime bases through 251. The finite energy calculation is distinct from an asymptotic proof.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Compute the complete collision energy of a prime base. | Arguments: <odd-prime-base>. | Exact scaled energy, carry-table statistics and normalized values. | `nfield prime-base-collision-energy inspect 5` |
| `poles`. Separate diagonal and off-diagonal collision-energy poles. | Arguments: <odd-prime-base>. | Exact numerator masses and normalized diagonal, upper, lower and total values. | `nfield prime-base-collision-energy poles 7` |

### arithmetic-boundary-defect

Compare the exact finite collision energy with its cubic and secondary terms.

**Inputs.** Odd prime base or maximum base for a scan.

**Result.** Exact energy plus normalized numerical residuals involving logarithms.

```sh
nfield arithmetic-boundary-defect scan 43
```

Scan a range, then inspect a base whose residual merits a closer carry-table calculation.

**Scope.** Odd prime bases through 251. Only logarithms/normalization are numerical; observed decay does not establish a new rate.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Extract a prime base's normalized arithmetic defect. | Arguments: <odd-prime-base>. | Exact scaled energy, normalized defect and secondary-coefficient comparison. | `nfield arithmetic-boundary-defect inspect 5` |
| `scan`. Compare normalized defects across a finite prime-base range. | Arguments: <maximum-base>. | Prime-by-prime energy, defect and analytic reference coefficient. | `nfield arithmetic-boundary-defect scan 11` |

### carry-completed-carrier

Construct a cyclic carrier with its carry seam or compare a coherent product-clock response.

**Inputs.** Compatible carrier parameters N,p,s; seam size; or product periods and endpoint steps.

**Result.** Exact coordinates, quotients, complement and seam energies; numerical product responses.

```sh
nfield carry-completed-carrier seam 6
```

Use seam independently, inspect for an eligible carrier, and product to resolve its Fourier response.

**Scope.** Carrier inspect requires odd q=ord_p(s), p=2q+1 and q dividing N. Canonical graded assembly remains a separate question.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `inspect`. Construct a source-compatible cyclic carrier. | Arguments: <N> <p> <s>. | Source order, completed cycle size, quotient sizes and successor coordinates. | `nfield carry-completed-carrier inspect 30 7 2` |
| `seam`. Price a two-sheet compression at one seam. | Arguments: <N>. | Exact retained, transverse and translated-origin energies. | `nfield carry-completed-carrier seam 30` |
| `product`. Form the Gram spectrum of two coherent cycles. | Arguments: <L> <q> <a> <b>. | Frequency population, constant response, trace and selected spectral values. | `nfield carry-completed-carrier product 10 3 -3 1` |

## Verification families

### verify

Check implementations against their declared mathematical contracts.

**Inputs.** A named C check family and optional check; `families` lists the available names.

**Result.** Executed checks, tested finite domains and assertion outcomes.

```sh
nfield verify reset-forest
```

Use `families` to find a check, then run that named family. Use `reset-forest contracts --json` for a structured report of the source and forest checks.

**Scope.** These C checks run without Lean or proof sources. A finite PASS applies only to executed assertions; formal proofs remain in the separate proof project.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `families`. Find executable implementation checks. | No numerical inputs; lists checks without running them. | Names and descriptions of the C check families. | `nfield verify families` |

### conjugate-pair-relabeling

Recheck the recorded finite relabeling law and reference character data.

**Inputs.** A registered fixed check; arbitrary populations are not accepted by this family.

**Result.** Mean/variance fixture checks and fixed cutoff reference results.

```sh
nfield verify conjugate-pair-relabeling
```

For adjustable base and cutoff diagnostics, use primitive-odd-sector inspect.

**Scope.** This family is verification, not a user-supplied relabeling operation.

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `exact-law` | `nfield verify conjugate-pair-relabeling exact-law [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |
| `ledger` | `nfield verify conjugate-pair-relabeling ledger [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |
| `cutoffs` | `nfield verify conjugate-pair-relabeling cutoffs [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |

### special-value-moment

Recheck the fixed weighted L-value moment fixtures.

**Inputs.** A registered fixed verification action.

**Result.** Finite moment and Parseval check outcomes.

```sh
nfield verify special-value-moment
```

Use collision-spectrum-factorization or short-sum-bernoulli-correlation moments for adjustable character data.

**Scope.** The fixed panel does not accept a user-selected moment population.

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `ledger` | `nfield verify special-value-moment ledger [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |

### base-five-cyclotomic-identity

Recheck the fixed base-five cyclotomic polynomial and fourth-moment identity.

**Inputs.** A registered fixed verification action.

**Result.** Exact polynomial and moment check outcomes.

```sh
nfield verify base-five-cyclotomic-identity
```

Use spectral or collision-spectrum-factorization for adjustable finite spectral calculations.

**Scope.** This is a specified identity check, not a general cyclotomic algebra calculator.

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `audit` | `nfield verify base-five-cyclotomic-identity audit [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |

### terminal-collision-conductor-ledger

Recheck the fixed terminal-boundary conductor fixtures.

**Inputs.** A registered fixed audit.

**Result.** Exact prime-power and base-15 identity checks.

```sh
nfield verify terminal-collision-conductor-ledger
```

Use boundary-conductor-ledger inspect or terminal to choose your own support or base/depth.

**Scope.** This panel is verification; the parameterized boundary-conductor-ledger is the research operation.

**Implementation subchecks.** Each runs a declared assertion panel.

| Check | Usage | Inputs |
| --- | --- | --- |
| `audit` | `nfield verify terminal-collision-conductor-ledger audit [--time]` | The fixed example or assertion panel declared by this operation; no model parameters. |

## Services and discovery

### daemon

Use nfield calculations from another local program through its JSON/TCP service.

**Inputs.** Listening port and worker count.

**Result.** The same command output and status returned in a JSON response.

```sh
nfield daemon --port 9090 --threads 4
```

Send one JSON request per connection; ordinary mathematical commands use the same executable dispatch.

**Scope.** This existing service is JSON/TCP, not HTTP. Shell operators and quoted shell expressions are not command syntax.

**Default usage.** `nfield daemon [--port <port>] [--threads <count>]`

### completion

Discover commands, actions and supported flags while typing in a shell.

**Inputs.** Shell name bash, zsh or fish.

**Result.** A shell completion script.

```sh
nfield completion bash
```

Load the emitted script using the installation line below; Tab then discovers current names and options.

**Scope.** Completion suggests syntax; numerical domain validation occurs when the command runs.

| Action and purpose | Inputs | Returned quantities | Example |
| --- | --- | --- | --- |
| `bash`. Enable shell completion in Bash. | No further arguments. | A shell completion script using the executable's current command catalog. | `nfield completion bash` |
| `zsh`. Enable shell completion in Zsh. | No further arguments. | A shell completion script using the executable's current command catalog. | `nfield completion zsh` |
| `fish`. Enable shell completion in Fish. | No further arguments. | A shell completion script using the executable's current command catalog. | `nfield completion fish` |

### version

Record which nfield executable produced a result.

**Inputs.** No numerical inputs.

**Result.** The build version derived from link time.

```sh
nfield version
```

Save the version with input parameters when comparing results across builds.

**Scope.** A version identifies the build; it is not a theorem or coverage certificate.

**Default usage.** `nfield version`

### commands

Choose a tool by its research purpose before reading its full syntax.

**Inputs.** Optional search terms; `--examples` shows runnable starts and `--json` returns the catalog.

**Result.** Matching command purposes and optional examples, or structured action contracts.

```sh
nfield commands spectrum --examples
```

Search by a quantity or task, then use `nfield help <name> <action>` for its complete input contract. Multiple terms must all match; search ignores letter case.

**Scope.** The catalog describes interfaces, not computed results. Format support belongs to individual actions.

**Default usage.** `nfield commands [terms ...] [--examples] [--json]`

### help

Find the purpose, inputs, output and syntax of an nfield command.

**Inputs.** A command or help topic.

**Result.** Research guidance followed by the detailed usage and domain notes.

```sh
nfield help reset-forest
```

Use commands to discover a family, help to understand it, and completion to enter its arguments.

**Scope.** Help describes a calculation; it does not execute that calculation.

**Default usage.** `nfield help [command [action]]`

## Compatibility interfaces

### analytic

Evaluate the legacy periodic-zeta example at a chosen base and lag.

**Inputs.** Digit base and positional lag.

**Result.** A primitive odd character factorization at character index 1 and s=1/2.

```sh
nfield analytic 1 --base 5
```

Use periodic-zeta-factorization inspect to choose the character and complex argument explicitly.

**Scope.** Compatibility interface; read the printed normalization before comparing with newer families.

**Default usage.** `nfield analytic [lag] [--base B]`

### scale

Obtain the predefined just major or chromatic interval table in its alignment coordinates.

**Inputs.** Major/chromatic selection, alpha/beta form and optional CSV.

**Result.** Musical interval ratios and their fixed alignment/deficit coordinates.

```sh
nfield scale --chromatic --csv
```

Export the table for tuning comparison; deficit-lattice ratio supports custom supported-field comparisons.

**Scope.** The scale itself is predefined; this is not an arbitrary temperament optimizer.

**Default usage.** `nfield scale [--chromatic] [--alpha | --beta] [--csv]`

### coherence

Explore the spectral geometry of a finite population of prime collision labels.

**Inputs.** Number of primes and digit base.

**Result.** Collision-label table and numerical coherence/eigenvalue diagnostics for the selected prime population.

```sh
nfield coherence 30 --base 10
```

Use finite-spectral-quotient for the explicit label-population quotient and heat-scale calculation.

**Scope.** Compatibility output has its own normalizations; do not infer exact rational values from a printed decimal.

**Default usage.** `nfield coherence [prime-count] [--base B]`

### golden-threshold-table

Read the predefined base-ten reciprocal-square threshold rows.

**Inputs.** No numerical inputs.

**Result.** The ten registered supported-resolution examples.

```sh
nfield golden-threshold-table
```

Use reciprocal-square-selection inspect to choose a different eligible prime, multiplier or base.

**Scope.** Fixed reference table retained for compatibility.

**Default usage.** `nfield golden-threshold-table`

### spectrum

Inspect cross-alignment matrix eigenvalues for a prime field.

**Inputs.** Prime modulus and digit base.

**Result.** Cross-alignment eigenvalues, multiplicities and the number of distinct levels.

```sh
nfield spectrum 13 --base 10
```

Use spectral-structure for orbit-frequency explanations and cross-alignment for the original matrix.

**Scope.** This is the alignment-matrix spectrum, distinct from additive digit-bin power.

**Default usage.** `nfield spectrum [prime] [--base B]`

### gate

Inspect the legacy digit-collision gate at one prime.

**Inputs.** Prime modulus and digit base.

**Result.** Finite collision-gate values for the selected prime.

```sh
nfield gate 13 --base 10
```

Use collision-coordinate gate or bin-derangements family for the explicit mathematical-object interface.

**Scope.** Finite prime/base gate; not a prime-distribution test.

**Default usage.** `nfield gate [prime] [--base B]`

### derangements

List zero-collision multipliers for a prime using the compatibility interface.

**Inputs.** Prime modulus and digit base.

**Result.** The finite deranging multiplier list.

```sh
nfield derangements 13 --base 10
```

Prefer bin-derangements family for the documented current operation.

**Scope.** This legacy route is retained for older scripts.

**Default usage.** `nfield derangements [prime] [--base B]`

### silent_primes

Inspect the legacy silence recipe for a base and lag.

**Inputs.** Digit base and lag.

**Result.** Finite silent-prime recipe and listed cases.

```sh
nfield silent_primes 10 --lag 1
```

Prefer silent-primes recipe or prime for focused current operations.

**Scope.** Compatibility display; silence concerns the selected digit collision only.

**Default usage.** `nfield silent_primes [base] [--lag L]`

### gate_width

Run the fixed legacy gate-width verification sweep.

**Inputs.** No adjustable sweep is supplied by this wrapper.

**Result.** PASS/FAIL results for the registered finite base/prime cases.

```sh
nfield verify gate-width
```

Use bin-derangements family <p> --base <b> to calculate a gate on your own inputs.

**Scope.** The old --base wrapper label does not select the fixed verifier's test set.

**Default usage.** `nfield verify gate-width`

### fluctuation_sum

Measure the legacy prime-weighted collision fluctuation over an explicit finite cutoff.

**Inputs.** Base, lag and prime cutoff.

**Result.** Finite cumulative fluctuation sums and reference comparisons.

```sh
nfield fluctuation_sum --base 5 --lag 1 --primes 1000
```

Vary the finite cutoff; use collision-characters for the corresponding channel decomposition.

**Scope.** Always set --primes for a bounded run. A numerical trend does not prove an asymptotic.

**Default usage.** `nfield fluctuation_sum [--base B] [--lag L] [--primes P]`

### character_components

Inspect the legacy character decomposition of the base-squared collision table.

**Inputs.** Digit base.

**Result.** Finite table character magnitudes in the legacy CRT coordinates.

```sh
nfield character_components --base 5
```

Use collision-transform spectrum for the centered table, or collision-characters for prime-weighted residue streams.

**Scope.** These base-squared table coordinates differ from the prime-cutoff character stream operation.

**Default usage.** `nfield character_components [base] [--base B]`

### class_bias

Compare finite prime-weighted collision bias across residue classes.

**Inputs.** Digit base and prime cutoff.

**Result.** Per-class finite bias values and sample counts.

```sh
nfield class_bias --base 5 --primes 1000
```

Compare several cutoffs at the same base before interpreting a class difference.

**Scope.** Set a finite cutoff explicitly; class bias at one cutoff is not a limiting bias.

**Default usage.** `nfield class_bias [--base B] [--primes P]`

### class_means

Inspect the exact periodic-table means behind the legacy residue-class display.

**Inputs.** Digit base.

**Result.** Class means for the chosen finite collision table.

```sh
nfield class_means --base 5
```

Compare these table means with class_bias on a prime window.

**Scope.** A table mean and a sampled prime mean use different populations.

**Default usage.** `nfield class_means [--base B]`

### centered_sum

Measure a finite prime sum after removing the table's class means.

**Inputs.** Digit base and prime cutoff.

**Result.** Finite centered prime sums in the legacy display.

```sh
nfield centered_sum --base 5 --primes 1000
```

Use class_means to inspect the removed baseline; use collision-centering for lag-aware operations.

**Scope.** The cutoff is finite and the weighted sum numerical.

**Default usage.** `nfield centered_sum [--base B] [--primes P]`

### neutrality

Compare finite residue-three prime contributions with the legacy neutrality display.

**Inputs.** Digit base and prime cutoff.

**Result.** Channel totals and the finite neutrality comparison.

```sh
nfield neutrality --base 5 --primes 1000
```

Use residue-three-neutrality inspect/channels/split for explicit quotient carry and true residue channels.

**Scope.** Set the cutoff explicitly. Internal table slices and actual prime residues must not be conflated.

**Default usage.** `nfield neutrality [base] [--base B] [--primes P]`

### neutrality_sweep

Reproduce the fixed legacy neutrality sweep.

**Inputs.** No caller-selected numerical range.

**Result.** Registered finite neutrality rows.

```sh
nfield neutrality_sweep
```

Use residue-three-neutrality channels or split to choose the actual base and prime interval.

**Scope.** Fixed compatibility reference; it is not a general-purpose sweep interface.

**Default usage.** `nfield neutrality_sweep`

### finite_det

Run the fixed legacy finite-determination checks.

**Inputs.** No caller-selected test domain.

**Result.** Registered finite determination check results.

```sh
nfield verify finite-det
```

Use finite-determination inspect with an integer, base and lag for a usable calculation.

**Scope.** Verification wrapper retained for older scripts.

**Default usage.** `nfield verify finite-det`

### mod3_means

Inspect the legacy residue-three averages of a selected digit table.

**Inputs.** Digit base.

**Result.** The three table-slice means.

```sh
nfield mod3_means 5
```

Use residue-three-neutrality channels to distinguish these internal means from true lifted residue channels.

**Scope.** These are finite table means, not an empirical prime-density calculation.

**Default usage.** `nfield mod3_means [base] [--base B]`

### polarity_field

Inspect the legacy signed collision pattern across the residue classes of a digit base.

**Inputs.** Digit base.

**Result.** The finite polarity table and its signed class structure.

```sh
nfield polarity_field 5
```

Compare with collision-table and collision-centering to identify the underlying values and centering convention.

**Scope.** Polarity here is a table sign, not a Mobius sign or physical emission law.

**Default usage.** `nfield polarity_field [base] [--base B]`

## Spelling aliases

These names resolve to the same contracts and computations. Other compatibility commands above retain their own mathematical normalizations.

| Alias | Preferred spelling |
| --- | --- |
| `collision_table` | `table` |
| `mertens_growth` | `fluctuation_sum` |
| `centered-collision` | `collision-centering` |
| `collision-periodic-table` | `collision-table` |
| `neutrality-theorem` | `residue-three-neutrality` |
| `general-neutrality` | `compatible-residue-channels` |
| `goldbach-obstruction` | `reflected-prime-pair-sign` |
